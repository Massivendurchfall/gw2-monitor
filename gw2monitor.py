import ctypes
import json
import subprocess
import threading
import time
from ctypes import wintypes
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from tkinter import filedialog, messagebox

import customtkinter as ctk
import psutil
import pystray
import requests
from PIL import Image, ImageDraw

CONFIG_FILE = Path("gw2_monitor_config.json")
APP_TITLE = "GW2 Background Monitor"

LEGACY_TEMPLATE = "{mention} {exe_name} {event}\nTime: {time}\nSession: {session_length}\nPID: {pid}"
DEFAULT_TEMPLATE = "{mention} {exe_name} {event}\nTime: {time}\nPID: {pid}"

DEFAULT_CONFIG = {
    "target_exe": "GW2.Main_Win64_Retail.exe",
    "game_path": r"C:\Program Files (x86)\Steam\steamapps\common\PVZGW2\GW2.Main_Win64_Retail.exe",
    "discord_user_id": "",
    "webhook_url": "",
    "poll_interval": "1.0",
    "restart_cooldown": "5.0",
    "timed_restart_enabled": False,
    "timed_restart_hours": "2.0",
    "auto_restart_on_close": False,
    "start_hidden": False,
    "low_resource_mode": False,
    "webhook_template": DEFAULT_TEMPLATE,
    "notify_monitor_events": True,
    "notify_game_started": True,
    "notify_unexpected_close": True,
    "notify_restart_events": True,
    "notify_hide_show": False,
    "notify_manual_launch": False,
}

PALETTE = {
    "bg": "#09090f",
    "panel": "#11111a",
    "panel_2": "#171724",
    "card": "#0d0d16",
    "entry": "#0c0c14",
    "line": "#2d2c44",
    "text": "#f5f7ff",
    "muted": "#b8bdd6",
    "soft": "#8b90aa",
    "accent": "#8b5cf6",
    "accent_hover": "#9f74ff",
    "accent_2": "#22d3ee",
    "accent_2_hover": "#46def5",
    "good": "#6ee7b7",
    "warn": "#f5d36c",
    "bad": "#ff8c8c",
    "blue": "#9ec5ff",
    "button": "#1d1d2e",
    "button_hover": "#27273d",
    "danger": "#4a2444",
    "danger_hover": "#613059",
}

SW_HIDE = 0
SW_SHOW = 5
SW_RESTORE = 9
WM_CLOSE = 0x0010

DETECTION_STABLE_POLLS = 3
MISSED_POLLS_FOR_CLOSE = 3

user32 = ctypes.windll.user32
EnumWindowsProc = ctypes.WINFUNCTYPE(ctypes.c_bool, wintypes.HWND, wintypes.LPARAM)


@dataclass
class RuntimeState:
    monitor_running: bool = False
    game_running: bool = False
    hidden_mode: bool = False
    monitor_started_at: float | None = None
    game_started_at: float | None = None
    current_pid: int | None = None
    current_exe_display: str = "GW2.Main_Win64_Retail.exe (not detected)"
    webhook_sent: int = 0
    close_events: int = 0
    restart_count: int = 0
    webhook_state: str = "Not sent yet"
    restart_state: str = "Idle"
    last_error: str = "None"
    last_restart_at: float = 0.0
    next_timed_restart_at: float | None = None
    last_event: str = "Ready"


class InfoPopup(ctk.CTkToplevel):
    def __init__(self, master, title, text):
        super().__init__(master)
        self.title(title)
        self.geometry("430x220")
        self.resizable(False, False)
        self.transient(master)
        self.attributes("-topmost", True)
        self.configure(fg_color=PALETTE["panel"])

        shell = ctk.CTkFrame(self, fg_color=PALETTE["panel_2"], corner_radius=16, border_width=1, border_color=PALETTE["line"])
        shell.pack(fill="both", expand=True, padx=14, pady=14)

        ctk.CTkLabel(
            shell,
            text=title,
            text_color=PALETTE["text"],
            font=ctk.CTkFont(size=18, weight="bold")
        ).pack(anchor="w", padx=16, pady=(14, 8))

        box = ctk.CTkTextbox(
            shell,
            fg_color=PALETTE["entry"],
            text_color=PALETTE["text"],
            border_width=1,
            border_color=PALETTE["line"],
            corner_radius=12,
            wrap="word"
        )
        box.pack(fill="both", expand=True, padx=16, pady=(0, 16))
        box.insert("1.0", text)
        box.configure(state="disabled")


class StatusCard(ctk.CTkFrame):
    def __init__(self, master, title):
        super().__init__(master, fg_color=PALETTE["card"], corner_radius=16, border_width=1, border_color=PALETTE["line"])
        self.grid_columnconfigure(0, weight=1)

        ctk.CTkLabel(
            self,
            text=title,
            text_color=PALETTE["muted"],
            font=ctk.CTkFont(size=12, weight="bold")
        ).grid(row=0, column=0, sticky="w", padx=14, pady=(12, 4))

        self.value_label = ctk.CTkLabel(
            self,
            text="-",
            text_color=PALETTE["text"],
            font=ctk.CTkFont(size=24, weight="bold")
        )
        self.value_label.grid(row=1, column=0, sticky="w", padx=14, pady=(0, 12))

    def set_value(self, text, color):
        self.value_label.configure(text=text, text_color=color)


class GW2MonitorApp(ctk.CTk):
    def __init__(self):
        super().__init__()
        ctk.set_appearance_mode("dark")
        ctk.set_default_color_theme("blue")

        self.title(APP_TITLE)
        self.geometry("1560x980")
        self.minsize(1420, 900)
        self.configure(fg_color=PALETTE["bg"])
        self.protocol("WM_DELETE_WINDOW", self.on_close)

        self.state_lock = threading.Lock()
        self.runtime = RuntimeState()
        self.monitor_thread = None
        self.monitor_stop_event = threading.Event()
        self.restart_lock = threading.Lock()
        self.auto_save_after_id = None
        self.text_save_after_id = None
        self.expected_game_down = False
        self.expected_game_down_reason = ""
        self.tray_icon = None
        self.tray_thread = None
        self.tray_visible = False
        self.is_quitting = False

        self.pending_pid = None
        self.pending_start_time = None
        self.pending_detection_count = 0
        self.missed_detection_count = 0

        self.raw_config = self.load_config_file()

        self.build_ui()
        self.load_config_into_ui(self.raw_config)
        self.refresh_status_loop()
        self.push_log("INFO", "UI ready")

    def normalize_template(self, template: str) -> str:
        if not template:
            return DEFAULT_TEMPLATE
        template = template.replace("\r\n", "\n")
        template = template.replace("\nSession: {session_length}", "")
        if template.strip() == LEGACY_TEMPLATE.replace("\nSession: {session_length}", "").strip():
            return DEFAULT_TEMPLATE
        return template

    def load_config_file(self):
        if CONFIG_FILE.exists():
            try:
                with CONFIG_FILE.open("r", encoding="utf-8") as file:
                    data = json.load(file)
                if data.get("webhook_template") == LEGACY_TEMPLATE:
                    data["webhook_template"] = DEFAULT_TEMPLATE
                elif "webhook_template" in data:
                    data["webhook_template"] = self.normalize_template(data["webhook_template"])
                merged = DEFAULT_CONFIG.copy()
                merged.update(data)
                return merged
            except Exception:
                return DEFAULT_CONFIG.copy()
        return DEFAULT_CONFIG.copy()

    def save_config_file(self, config):
        try:
            config_to_save = dict(config)
            config_to_save["webhook_template"] = self.normalize_template(config_to_save.get("webhook_template", DEFAULT_TEMPLATE))
            with CONFIG_FILE.open("w", encoding="utf-8") as file:
                json.dump(config_to_save, file, indent=2, ensure_ascii=False)
        except Exception as exc:
            self.push_log("ERROR", f"Config save failed: {exc}")

    def safe_float(self, value, fallback):
        try:
            return float(str(value).replace(",", "."))
        except Exception:
            return fallback

    def push_log(self, level, message):
        timestamp = datetime.now().strftime("%H:%M:%S")
        with self.state_lock:
            self.runtime.last_event = f"{timestamp}  {level}  {message}"

    def get_ui_config(self):
        return {
            "target_exe": self.target_exe_var.get().strip(),
            "game_path": self.game_path_var.get().strip(),
            "discord_user_id": self.discord_user_id_var.get().strip(),
            "webhook_url": self.webhook_url_var.get().strip(),
            "poll_interval": self.poll_interval_var.get().strip(),
            "restart_cooldown": self.restart_cooldown_var.get().strip(),
            "timed_restart_enabled": bool(self.timed_restart_var.get()),
            "timed_restart_hours": self.timed_restart_hours_var.get().strip(),
            "auto_restart_on_close": bool(self.auto_restart_on_close_var.get()),
            "start_hidden": bool(self.start_hidden_var.get()),
            "low_resource_mode": bool(self.low_resource_mode_var.get()),
            "webhook_template": self.normalize_template(self.webhook_template_box.get("1.0", "end").strip() or DEFAULT_TEMPLATE),
            "notify_monitor_events": bool(self.notify_monitor_events_var.get()),
            "notify_game_started": bool(self.notify_game_started_var.get()),
            "notify_unexpected_close": bool(self.notify_unexpected_close_var.get()),
            "notify_restart_events": bool(self.notify_restart_events_var.get()),
            "notify_hide_show": bool(self.notify_hide_show_var.get()),
            "notify_manual_launch": bool(self.notify_manual_launch_var.get()),
        }

    def get_runtime_config(self):
        raw = self.get_ui_config()
        return {
            "target_exe": raw["target_exe"] or DEFAULT_CONFIG["target_exe"],
            "game_path": raw["game_path"] or DEFAULT_CONFIG["game_path"],
            "discord_user_id": raw["discord_user_id"],
            "webhook_url": raw["webhook_url"],
            "poll_interval": max(0.25, self.safe_float(raw["poll_interval"], 1.0)),
            "restart_cooldown": max(0.0, self.safe_float(raw["restart_cooldown"], 5.0)),
            "timed_restart_enabled": raw["timed_restart_enabled"],
            "timed_restart_hours": max(0.1, self.safe_float(raw["timed_restart_hours"], 2.0)),
            "auto_restart_on_close": raw["auto_restart_on_close"],
            "start_hidden": raw["start_hidden"],
            "low_resource_mode": raw["low_resource_mode"],
            "webhook_template": raw["webhook_template"] or DEFAULT_TEMPLATE,
            "notify_monitor_events": raw["notify_monitor_events"],
            "notify_game_started": raw["notify_game_started"],
            "notify_unexpected_close": raw["notify_unexpected_close"],
            "notify_restart_events": raw["notify_restart_events"],
            "notify_hide_show": raw["notify_hide_show"],
            "notify_manual_launch": raw["notify_manual_launch"],
        }

    def load_config_into_ui(self, config):
        self.target_exe_var.set(str(config.get("target_exe", DEFAULT_CONFIG["target_exe"])))
        self.game_path_var.set(str(config.get("game_path", DEFAULT_CONFIG["game_path"])))
        self.discord_user_id_var.set(str(config.get("discord_user_id", DEFAULT_CONFIG["discord_user_id"])))
        self.webhook_url_var.set(str(config.get("webhook_url", DEFAULT_CONFIG["webhook_url"])))
        self.poll_interval_var.set(str(config.get("poll_interval", DEFAULT_CONFIG["poll_interval"])))
        self.restart_cooldown_var.set(str(config.get("restart_cooldown", DEFAULT_CONFIG["restart_cooldown"])))
        self.timed_restart_var.set(bool(config.get("timed_restart_enabled", DEFAULT_CONFIG["timed_restart_enabled"])))
        self.timed_restart_hours_var.set(str(config.get("timed_restart_hours", DEFAULT_CONFIG["timed_restart_hours"])))
        self.auto_restart_on_close_var.set(bool(config.get("auto_restart_on_close", DEFAULT_CONFIG["auto_restart_on_close"])))
        self.start_hidden_var.set(bool(config.get("start_hidden", DEFAULT_CONFIG["start_hidden"])))
        self.low_resource_mode_var.set(bool(config.get("low_resource_mode", DEFAULT_CONFIG["low_resource_mode"])))
        self.notify_monitor_events_var.set(bool(config.get("notify_monitor_events", DEFAULT_CONFIG["notify_monitor_events"])))
        self.notify_game_started_var.set(bool(config.get("notify_game_started", DEFAULT_CONFIG["notify_game_started"])))
        self.notify_unexpected_close_var.set(bool(config.get("notify_unexpected_close", DEFAULT_CONFIG["notify_unexpected_close"])))
        self.notify_restart_events_var.set(bool(config.get("notify_restart_events", DEFAULT_CONFIG["notify_restart_events"])))
        self.notify_hide_show_var.set(bool(config.get("notify_hide_show", DEFAULT_CONFIG["notify_hide_show"])))
        self.notify_manual_launch_var.set(bool(config.get("notify_manual_launch", DEFAULT_CONFIG["notify_manual_launch"])))
        self.webhook_template_box.delete("1.0", "end")
        self.webhook_template_box.insert("1.0", self.normalize_template(str(config.get("webhook_template", DEFAULT_TEMPLATE))))
        self.update_timed_restart_widgets()

    def schedule_auto_save(self):
        if self.auto_save_after_id:
            self.after_cancel(self.auto_save_after_id)
        self.auto_save_after_id = self.after(250, self.auto_save_config)

    def schedule_text_auto_save(self, _event=None):
        if self.text_save_after_id:
            self.after_cancel(self.text_save_after_id)
        self.text_save_after_id = self.after(250, self.auto_save_config)

    def auto_save_config(self):
        self.auto_save_after_id = None
        self.text_save_after_id = None
        config = self.get_ui_config()
        self.raw_config = config
        self.save_config_file(config)
        self.update_timed_restart_widgets()

        with self.state_lock:
            if config["webhook_url"].strip():
                if self.runtime.webhook_state == "Not sent yet":
                    self.runtime.webhook_state = "Webhook configured"
            else:
                self.runtime.webhook_state = "Not sent yet"

    def build_ui(self):
        self.grid_columnconfigure(0, weight=0)
        self.grid_columnconfigure(1, weight=1)
        self.grid_rowconfigure(1, weight=1)

        topbar = ctk.CTkFrame(self, fg_color=PALETTE["panel"], corner_radius=0, height=56)
        topbar.grid(row=0, column=0, columnspan=2, sticky="nsew")
        topbar.grid_columnconfigure(0, weight=1)
        topbar.grid_propagate(False)

        ctk.CTkLabel(
            topbar,
            text="GW2 Background Monitor",
            text_color=PALETTE["text"],
            font=ctk.CTkFont(size=18, weight="bold")
        ).grid(row=0, column=0, sticky="w", padx=18, pady=14)

        ctk.CTkLabel(
            topbar,
            text="made by tape",
            text_color=PALETTE["soft"],
            font=ctk.CTkFont(size=12)
        ).grid(row=0, column=1, sticky="e", padx=18, pady=14)

        sidebar = ctk.CTkFrame(self, fg_color=PALETTE["panel"], corner_radius=0, width=540)
        sidebar.grid(row=1, column=0, sticky="nsew")
        sidebar.grid_propagate(False)
        sidebar.grid_columnconfigure(0, weight=1)

        content = ctk.CTkFrame(self, fg_color=PALETTE["bg"], corner_radius=0)
        content.grid(row=1, column=1, sticky="nsew", padx=18, pady=18)
        content.grid_columnconfigure(0, weight=1)
        content.grid_rowconfigure(3, weight=1)

        self.build_sidebar(sidebar)
        self.build_content(content)

    def build_sidebar(self, parent):
        self.target_exe_var = ctk.StringVar()
        self.game_path_var = ctk.StringVar()
        self.discord_user_id_var = ctk.StringVar()
        self.webhook_url_var = ctk.StringVar()
        self.poll_interval_var = ctk.StringVar()
        self.restart_cooldown_var = ctk.StringVar()
        self.timed_restart_hours_var = ctk.StringVar()
        self.timed_restart_var = ctk.BooleanVar()
        self.auto_restart_on_close_var = ctk.BooleanVar()
        self.start_hidden_var = ctk.BooleanVar()
        self.low_resource_mode_var = ctk.BooleanVar()
        self.notify_monitor_events_var = ctk.BooleanVar()
        self.notify_game_started_var = ctk.BooleanVar()
        self.notify_unexpected_close_var = ctk.BooleanVar()
        self.notify_restart_events_var = ctk.BooleanVar()
        self.notify_hide_show_var = ctk.BooleanVar()
        self.notify_manual_launch_var = ctk.BooleanVar()

        for variable in [
            self.target_exe_var,
            self.game_path_var,
            self.discord_user_id_var,
            self.webhook_url_var,
            self.poll_interval_var,
            self.restart_cooldown_var,
            self.timed_restart_hours_var,
            self.timed_restart_var,
            self.auto_restart_on_close_var,
            self.start_hidden_var,
            self.low_resource_mode_var,
            self.notify_monitor_events_var,
            self.notify_game_started_var,
            self.notify_unexpected_close_var,
            self.notify_restart_events_var,
            self.notify_hide_show_var,
            self.notify_manual_launch_var,
        ]:
            variable.trace_add("write", lambda *_: self.schedule_auto_save())

        settings = self.make_section(parent, "Settings")
        settings.grid(row=0, column=0, sticky="ew", padx=18, pady=(18, 10))
        settings.grid_columnconfigure(0, minsize=175)
        settings.grid_columnconfigure(1, weight=1)
        settings.grid_columnconfigure(2, minsize=84)

        self.make_label(settings, 0, "Target EXE")
        self.target_exe_entry = self.make_entry(settings, 0, self.target_exe_var)

        self.make_label(settings, 1, "Game Path")
        path_row = ctk.CTkFrame(settings, fg_color="transparent")
        path_row.grid(row=2, column=1, columnspan=2, sticky="ew", padx=(12, 14), pady=6)
        path_row.grid_columnconfigure(0, weight=1)
        self.game_path_entry = ctk.CTkEntry(
            path_row,
            textvariable=self.game_path_var,
            height=40,
            fg_color=PALETTE["entry"],
            border_color=PALETTE["line"],
            text_color=PALETTE["text"],
            corner_radius=12
        )
        self.game_path_entry.grid(row=0, column=0, sticky="ew")
        self.make_small_button(path_row, 0, 1, "Browse", self.browse_game_path, 96)

        self.make_label(settings, 2, "Discord User ID")
        self.discord_user_id_entry = self.make_entry(settings, 2, self.discord_user_id_var)
        self.make_help_button(settings, 2, "Optional numeric Discord user ID for mentions.")

        self.make_label(settings, 3, "Webhook URL")
        self.webhook_url_entry = self.make_entry(settings, 3, self.webhook_url_var)
        self.make_help_button(settings, 3, "Discord webhook destination.")

        self.make_label(settings, 4, "Poll Interval")
        poll_row = ctk.CTkFrame(settings, fg_color="transparent")
        poll_row.grid(row=5, column=1, sticky="ew", padx=(12, 0), pady=6)
        poll_row.grid_columnconfigure(0, weight=1)
        self.poll_interval_entry = ctk.CTkEntry(
            poll_row,
            textvariable=self.poll_interval_var,
            height=40,
            fg_color=PALETTE["entry"],
            border_color=PALETTE["line"],
            text_color=PALETTE["text"],
            corner_radius=12
        )
        self.poll_interval_entry.grid(row=0, column=0, sticky="ew")
        ctk.CTkLabel(poll_row, text="sec", text_color=PALETTE["soft"], font=ctk.CTkFont(size=12)).grid(row=0, column=1, sticky="w", padx=(8, 0))

        self.make_label(settings, 5, "Restart Cooldown")
        cooldown_row = ctk.CTkFrame(settings, fg_color="transparent")
        cooldown_row.grid(row=6, column=1, sticky="ew", padx=(12, 0), pady=6)
        cooldown_row.grid_columnconfigure(0, weight=1)
        self.restart_cooldown_entry = ctk.CTkEntry(
            cooldown_row,
            textvariable=self.restart_cooldown_var,
            height=40,
            fg_color=PALETTE["entry"],
            border_color=PALETTE["line"],
            text_color=PALETTE["text"],
            corner_radius=12
        )
        self.restart_cooldown_entry.grid(row=0, column=0, sticky="ew")
        ctk.CTkLabel(cooldown_row, text="sec", text_color=PALETTE["soft"], font=ctk.CTkFont(size=12)).grid(row=0, column=1, sticky="w", padx=(8, 0))

        self.make_label(settings, 6, "Timed Restart")

        timed_row = ctk.CTkFrame(
            settings,
            fg_color=PALETTE["card"],
            corner_radius=14,
            border_width=1,
            border_color=PALETTE["line"]
        )
        timed_row.grid(row=7, column=1, sticky="ew", padx=(12, 0), pady=6)
        timed_row.grid_columnconfigure(0, weight=1)

        self.timed_restart_checkbox = ctk.CTkCheckBox(
            timed_row,
            text="Enable",
            variable=self.timed_restart_var,
            command=self.on_timed_restart_changed,
            fg_color=PALETTE["accent"],
            hover_color=PALETTE["accent_hover"],
            border_color=PALETTE["soft"],
            text_color=PALETTE["text"]
        )
        self.timed_restart_checkbox.grid(row=0, column=0, sticky="w", padx=12, pady=(10, 6))

        timed_input_row = ctk.CTkFrame(timed_row, fg_color="transparent")
        timed_input_row.grid(row=1, column=0, sticky="w", padx=12, pady=(0, 10))

        self.timed_restart_hours_entry = ctk.CTkEntry(
            timed_input_row,
            textvariable=self.timed_restart_hours_var,
            width=150,
            height=36,
            justify="center",
            fg_color=PALETTE["entry"],
            border_color=PALETTE["line"],
            text_color=PALETTE["text"],
            corner_radius=10
        )
        self.timed_restart_hours_entry.grid(row=0, column=0, sticky="w")

        self.timed_restart_suffix = ctk.CTkLabel(
            timed_input_row,
            text="hours",
            text_color=PALETTE["soft"],
            font=ctk.CTkFont(size=12, weight="bold")
        )
        self.timed_restart_suffix.grid(row=0, column=1, sticky="w", padx=(10, 0))

        self.make_help_button(settings, 6, "Closes and launches the game again after the set runtime.")

        self.make_label(settings, 7, "Webhook Template")
        self.webhook_template_box = ctk.CTkTextbox(
            settings,
            height=110,
            wrap="word",
            fg_color=PALETTE["entry"],
            border_width=1,
            border_color=PALETTE["line"],
            text_color=PALETTE["text"],
            corner_radius=12
        )
        self.webhook_template_box.grid(row=8, column=1, columnspan=2, sticky="ew", padx=(12, 14), pady=6)
        self.webhook_template_box.bind("<KeyRelease>", self.schedule_text_auto_save)

        options = self.make_section(parent, "Options")
        options.grid(row=1, column=0, sticky="ew", padx=18, pady=10)
        options.grid_columnconfigure(0, weight=1)

        self.make_toggle(options, 0, "Auto restart on close", self.auto_restart_on_close_var)
        self.make_toggle(options, 1, "Start hidden mode", self.start_hidden_var)
        self.make_toggle(options, 2, "Low resource mode", self.low_resource_mode_var)

    def build_content(self, parent):
        cards = ctk.CTkFrame(parent, fg_color="transparent")
        cards.grid(row=0, column=0, sticky="ew", pady=(0, 14))
        cards.grid_columnconfigure((0, 1, 2, 3), weight=1)

        self.monitor_card = StatusCard(cards, "Monitor")
        self.monitor_card.grid(row=0, column=0, sticky="ew", padx=(0, 7))

        self.game_card = StatusCard(cards, "Game")
        self.game_card.grid(row=0, column=1, sticky="ew", padx=7)

        self.hidden_card = StatusCard(cards, "Hidden")
        self.hidden_card.grid(row=0, column=2, sticky="ew", padx=7)

        self.restart_card = StatusCard(cards, "Next Restart")
        self.restart_card.grid(row=0, column=3, sticky="ew", padx=(7, 0))

        controls = self.make_section(parent, "Controls")
        controls.grid(row=1, column=0, sticky="ew", pady=(0, 14))
        controls.grid_columnconfigure((0, 1, 2, 3), weight=1)

        self.make_action_button_content(controls, 0, 0, "Start Monitor", self.start_monitor, PALETTE["accent"], PALETTE["accent_hover"], 40)
        self.make_action_button_content(controls, 0, 1, "Stop Monitor", self.stop_monitor, PALETTE["danger"], PALETTE["danger_hover"], 40)
        self.make_action_button_content(controls, 0, 2, "Hide Now", self.hide_now, PALETTE["button"], PALETTE["button_hover"], 40)
        self.make_action_button_content(controls, 0, 3, "Show Now", self.show_now, PALETTE["button"], PALETTE["button_hover"], 40)

        self.make_action_button_content(controls, 1, 0, "Test Webhook", self.test_webhook, PALETTE["accent_2"], PALETTE["accent_2_hover"], 40)
        self.make_action_button_content(controls, 1, 1, "Restart Game Now", lambda: self.start_restart_sequence("manual restart"), PALETTE["button"], PALETTE["button_hover"], 40)
        self.make_action_button_content(controls, 1, 2, "Launch Game", self.launch_game_manual, PALETTE["button"], PALETTE["button_hover"], 40)
        self.make_action_button_content(controls, 1, 3, "Load Config", self.reload_config, PALETTE["button"], PALETTE["button_hover"], 40)

        self.make_action_button_content(controls, 2, 0, "Tray Mode", self.minimize_to_tray, PALETTE["button"], PALETTE["button_hover"], 40)

        notifications = self.make_section(parent, "Webhook Notifications")
        notifications.grid(row=2, column=0, sticky="ew", pady=(0, 14))
        notifications.grid_columnconfigure((0, 1, 2), weight=1)

        self.make_toggle_content(notifications, 0, 0, "Monitor Start / Stop", self.notify_monitor_events_var)
        self.make_toggle_content(notifications, 0, 1, "Game Started", self.notify_game_started_var)
        self.make_toggle_content(notifications, 0, 2, "Unexpected Close / Crash", self.notify_unexpected_close_var)
        self.make_toggle_content(notifications, 1, 0, "Restart Events", self.notify_restart_events_var)
        self.make_toggle_content(notifications, 1, 1, "Hide / Show", self.notify_hide_show_var)
        self.make_toggle_content(notifications, 1, 2, "Manual Launch", self.notify_manual_launch_var)

        status = self.make_section(parent, "Status")
        status.grid(row=3, column=0, sticky="nsew")
        status.grid_columnconfigure((0, 1), weight=1)
        status.grid_rowconfigure(1, weight=1)

        left = ctk.CTkFrame(status, fg_color="transparent")
        left.grid(row=1, column=0, sticky="nsew", padx=(16, 12), pady=(0, 16))
        left.grid_columnconfigure(1, weight=1)

        right = ctk.CTkFrame(status, fg_color="transparent")
        right.grid(row=1, column=1, sticky="nsew", padx=(12, 16), pady=(0, 16))
        right.grid_columnconfigure(1, weight=1)

        self.detail_labels = {}

        left_rows = [
            "Uptime",
            "Game Uptime",
            "Process",
            "Session Start",
            "Current PID",
            "Last Event",
        ]

        right_rows = [
            "Webhook Sent",
            "Webhook State",
            "Close Events",
            "Restarts",
            "Restart State",
            "Last Error",
        ]

        for index, title in enumerate(left_rows):
            ctk.CTkLabel(left, text=title, text_color=PALETTE["muted"], font=ctk.CTkFont(size=13)).grid(row=index, column=0, sticky="nw", pady=8)
            value = ctk.CTkLabel(left, text="-", text_color=PALETTE["text"], font=ctk.CTkFont(size=13, weight="bold"), anchor="w", justify="left", wraplength=420)
            value.grid(row=index, column=1, sticky="ew", padx=(24, 0), pady=8)
            self.detail_labels[title] = value

        for index, title in enumerate(right_rows):
            ctk.CTkLabel(right, text=title, text_color=PALETTE["muted"], font=ctk.CTkFont(size=13)).grid(row=index, column=0, sticky="nw", pady=8)
            value = ctk.CTkLabel(right, text="-", text_color=PALETTE["text"], font=ctk.CTkFont(size=13, weight="bold"), anchor="w", justify="left", wraplength=420)
            value.grid(row=index, column=1, sticky="ew", padx=(24, 0), pady=8)
            self.detail_labels[title] = value

    def make_section(self, parent, title):
        frame = ctk.CTkFrame(parent, fg_color=PALETTE["panel_2"], corner_radius=18, border_width=1, border_color=PALETTE["line"])
        frame.grid_columnconfigure(0, weight=1)

        ctk.CTkLabel(
            frame,
            text=title,
            text_color=PALETTE["text"],
            font=ctk.CTkFont(size=16, weight="bold")
        ).grid(row=0, column=0, sticky="w", padx=16, pady=(14, 12))

        return frame

    def make_label(self, parent, row, text):
        ctk.CTkLabel(
            parent,
            text=text,
            text_color=PALETTE["muted"],
            font=ctk.CTkFont(size=13, weight="bold")
        ).grid(row=row + 1, column=0, sticky="w", padx=(16, 0), pady=6)

    def make_entry(self, parent, row, variable):
        entry = ctk.CTkEntry(
            parent,
            textvariable=variable,
            height=40,
            fg_color=PALETTE["entry"],
            border_color=PALETTE["line"],
            text_color=PALETTE["text"],
            corner_radius=12
        )
        entry.grid(row=row + 1, column=1, sticky="ew", padx=(12, 0), pady=6)
        return entry

    def make_help_button(self, parent, row, text):
        button = ctk.CTkButton(
            parent,
            text="?",
            width=34,
            height=34,
            corner_radius=10,
            fg_color=PALETTE["button"],
            hover_color=PALETTE["button_hover"],
            text_color=PALETTE["text"],
            font=ctk.CTkFont(size=14, weight="bold"),
            command=lambda: self.show_help(text)
        )
        button.grid(row=row + 1, column=2, sticky="e", padx=(10, 14), pady=6)
        return button

    def make_small_button(self, parent, row, column, text, command, width):
        button = ctk.CTkButton(
            parent,
            text=text,
            width=width,
            height=36,
            corner_radius=12,
            fg_color=PALETTE["button"],
            hover_color=PALETTE["button_hover"],
            text_color=PALETTE["text"],
            command=command
        )
        button.grid(row=row, column=column, padx=(10, 0), pady=0)
        return button

    def make_toggle(self, parent, row, text, variable):
        toggle = ctk.CTkCheckBox(
            parent,
            text=text,
            variable=variable,
            fg_color=PALETTE["accent"],
            hover_color=PALETTE["accent_hover"],
            border_color=PALETTE["soft"],
            text_color=PALETTE["text"]
        )
        toggle.grid(row=row + 1, column=0, sticky="w", padx=16, pady=8)
        return toggle

    def make_toggle_content(self, parent, row, column, text, variable):
        toggle = ctk.CTkCheckBox(
            parent,
            text=text,
            variable=variable,
            fg_color=PALETTE["accent"],
            hover_color=PALETTE["accent_hover"],
            border_color=PALETTE["soft"],
            text_color=PALETTE["text"]
        )
        toggle.grid(row=row + 1, column=column, sticky="w", padx=16, pady=8)
        return toggle

    def make_action_button_content(self, parent, row, column, text, command, fg, hover, height):
        button = ctk.CTkButton(
            parent,
            text=text,
            height=height,
            corner_radius=12,
            fg_color=fg,
            hover_color=hover,
            text_color=PALETTE["text"],
            font=ctk.CTkFont(size=13, weight="bold"),
            command=command
        )
        button.grid(row=row + 1, column=column, sticky="ew", padx=8, pady=6)
        return button

    def show_help(self, text):
        InfoPopup(self, "Help", text)

    def on_timed_restart_changed(self):
        self.update_timed_restart_widgets()
        self.schedule_auto_save()

    def update_timed_restart_widgets(self):
        enabled = bool(self.timed_restart_var.get())
        self.timed_restart_hours_entry.configure(state="normal" if enabled else "disabled")
        self.timed_restart_suffix.configure(text_color=PALETTE["soft"] if enabled else "#656875")

    def browse_game_path(self):
        path = filedialog.askopenfilename(
            title="Select GW2 executable",
            filetypes=[("Executable", "*.exe"), ("All Files", "*.*")]
        )
        if path:
            self.game_path_var.set(path)
            self.schedule_auto_save()

    def reload_config(self):
        self.raw_config = self.load_config_file()
        self.load_config_into_ui(self.raw_config)
        self.push_log("INFO", "Config reloaded")

    def should_notify(self, event_key):
        config = self.get_runtime_config()
        mapping = {
            "monitor_events": config["notify_monitor_events"],
            "game_started": config["notify_game_started"],
            "unexpected_close": config["notify_unexpected_close"],
            "restart_events": config["notify_restart_events"],
            "hide_show": config["notify_hide_show"],
            "manual_launch": config["notify_manual_launch"],
            "test": True,
        }
        return mapping.get(event_key, True)

    def create_tray_image(self):
        size = 64
        image = Image.new("RGBA", (size, size), (9, 9, 15, 255))
        draw = ImageDraw.Draw(image)
        draw.rounded_rectangle((6, 6, 58, 58), radius=14, fill=(139, 92, 246, 255))
        draw.rounded_rectangle((18, 18, 46, 46), radius=8, fill=(34, 211, 238, 255))
        draw.rounded_rectangle((24, 24, 40, 40), radius=5, fill=(9, 9, 15, 255))
        return image

    def tray_show_window(self, icon=None, item=None):
        self.after(0, self.restore_from_tray)

    def tray_exit_app(self, icon=None, item=None):
        self.after(0, self.exit_from_tray)

    def ensure_tray_icon(self):
        if self.tray_visible:
            return
        image = self.create_tray_image()
        menu = pystray.Menu(
            pystray.MenuItem("Show", self.tray_show_window, default=True),
            pystray.MenuItem("Exit", self.tray_exit_app),
        )
        self.tray_icon = pystray.Icon("gw2_background_monitor", image, APP_TITLE, menu)
        self.tray_thread = threading.Thread(target=self.tray_icon.run, daemon=True)
        self.tray_thread.start()
        self.tray_visible = True

    def stop_tray_icon(self):
        if self.tray_icon:
            try:
                self.tray_icon.stop()
            except Exception:
                pass
        self.tray_icon = None
        self.tray_thread = None
        self.tray_visible = False

    def minimize_to_tray(self):
        self.ensure_tray_icon()
        self.withdraw()
        self.push_log("INFO", "Moved to tray")

    def restore_from_tray(self):
        self.deiconify()
        self.lift()
        self.focus_force()

    def exit_from_tray(self):
        self.is_quitting = True
        self.stop_tray_icon()
        self.on_close()

    def refresh_status_loop(self):
        with self.state_lock:
            snapshot = RuntimeState(
                monitor_running=self.runtime.monitor_running,
                game_running=self.runtime.game_running,
                hidden_mode=self.runtime.hidden_mode,
                monitor_started_at=self.runtime.monitor_started_at,
                game_started_at=self.runtime.game_started_at,
                current_pid=self.runtime.current_pid,
                current_exe_display=self.runtime.current_exe_display,
                webhook_sent=self.runtime.webhook_sent,
                close_events=self.runtime.close_events,
                restart_count=self.runtime.restart_count,
                webhook_state=self.runtime.webhook_state,
                restart_state=self.runtime.restart_state,
                last_error=self.runtime.last_error,
                last_restart_at=self.runtime.last_restart_at,
                next_timed_restart_at=self.runtime.next_timed_restart_at,
                last_event=self.runtime.last_event,
            )

        now = time.time()

        self.monitor_card.set_value("Running" if snapshot.monitor_running else "Stopped", PALETTE["good"] if snapshot.monitor_running else PALETTE["bad"])
        self.game_card.set_value("Running" if snapshot.game_running else "Waiting", PALETTE["warn"] if snapshot.game_running else PALETTE["blue"])
        self.hidden_card.set_value("ON" if snapshot.hidden_mode else "OFF", PALETTE["accent_2"] if snapshot.hidden_mode else PALETTE["soft"])
        self.restart_card.set_value(self.get_next_restart_text(snapshot.next_timed_restart_at, now), PALETTE["text"])

        self.detail_labels["Uptime"].configure(text=self.format_duration(now - snapshot.monitor_started_at) if snapshot.monitor_started_at else "00:00:00")
        self.detail_labels["Game Uptime"].configure(text=self.format_duration(now - snapshot.game_started_at) if snapshot.game_started_at else "00:00:00")
        self.detail_labels["Process"].configure(text=snapshot.current_exe_display or "-")
        self.detail_labels["Session Start"].configure(text=datetime.fromtimestamp(snapshot.game_started_at).strftime("%Y-%m-%d %H:%M:%S") if snapshot.game_started_at else "-")
        self.detail_labels["Current PID"].configure(text=str(snapshot.current_pid) if snapshot.current_pid else "-")
        self.detail_labels["Last Event"].configure(text=snapshot.last_event)
        self.detail_labels["Webhook Sent"].configure(text=str(snapshot.webhook_sent))
        self.detail_labels["Webhook State"].configure(text=snapshot.webhook_state)
        self.detail_labels["Close Events"].configure(text=str(snapshot.close_events))
        self.detail_labels["Restarts"].configure(text=str(snapshot.restart_count))
        self.detail_labels["Restart State"].configure(text=snapshot.restart_state)
        self.detail_labels["Last Error"].configure(text=snapshot.last_error)

        self.after(250, self.refresh_status_loop)

    def get_next_restart_text(self, next_at, now):
        if not next_at:
            return "-"
        if next_at <= now:
            return "due now"
        return f"in {self.format_duration(next_at - now)}"

    def format_duration(self, seconds):
        seconds = max(0, int(seconds))
        hours, remainder = divmod(seconds, 3600)
        minutes, seconds = divmod(remainder, 60)
        return f"{hours:02d}:{minutes:02d}:{seconds:02d}"

    def find_process(self, target_exe, preferred_path):
        preferred_path_norm = str(Path(preferred_path).resolve()).lower() if preferred_path else ""
        candidates = []

        for proc in psutil.process_iter(["pid", "name", "exe"]):
            try:
                name = proc.info.get("name") or ""
                exe = proc.info.get("exe") or ""
                if name.lower() == target_exe.lower() or Path(exe).name.lower() == target_exe.lower():
                    candidates.append(proc)
            except Exception:
                continue

        if not candidates:
            return None

        for proc in candidates:
            try:
                exe = proc.exe() or ""
                if preferred_path_norm and str(Path(exe).resolve()).lower() == preferred_path_norm:
                    return proc
            except Exception:
                continue

        try:
            candidates.sort(key=lambda item: item.create_time())
        except Exception:
            pass

        return candidates[0]

    def enum_windows_for_pid(self, pid):
        handles = []

        def callback(hwnd, _lparam):
            process_id = wintypes.DWORD()
            user32.GetWindowThreadProcessId(hwnd, ctypes.byref(process_id))
            if process_id.value == pid and user32.GetParent(hwnd) == 0:
                handles.append(hwnd)
            return True

        user32.EnumWindows(EnumWindowsProc(callback), 0)
        return handles

    def hide_game_window(self, pid=None, send_webhook=True, silent=False):
        with self.state_lock:
            target_pid = pid or self.runtime.current_pid

        if not target_pid:
            if not silent:
                self.push_log("WARN", "Hide requested but the game is not running")
            return False

        handles = self.enum_windows_for_pid(target_pid)
        if not handles:
            if not silent:
                self.push_log("WARN", "No window found to hide")
            return False

        for hwnd in handles:
            user32.ShowWindow(hwnd, SW_HIDE)

        with self.state_lock:
            self.runtime.hidden_mode = True

        self.push_log("MODE", "Hidden mode enabled")

        if send_webhook:
            self.send_webhook_event("hidden mode enabled", "hide_show", pid=target_pid)

        return True

    def show_game_window(self, pid=None, send_webhook=True):
        with self.state_lock:
            target_pid = pid or self.runtime.current_pid

        if not target_pid:
            self.push_log("WARN", "Show requested but the game is not running")
            return False

        handles = self.enum_windows_for_pid(target_pid)
        if not handles:
            self.push_log("WARN", "No window found to show")
            return False

        for hwnd in handles:
            user32.ShowWindow(hwnd, SW_SHOW)
            user32.ShowWindow(hwnd, SW_RESTORE)

        with self.state_lock:
            self.runtime.hidden_mode = False

        self.push_log("MODE", "Hidden mode disabled")

        if send_webhook:
            self.send_webhook_event("hidden mode disabled", "hide_show", pid=target_pid)

        return True

    def ensure_hidden_after_launch(self, pid):
        deadline = time.time() + 10
        while time.time() < deadline:
            if self.hide_game_window(pid=pid, send_webhook=False, silent=True):
                return
            time.sleep(0.4)
        self.push_log("WARN", "Start hidden enabled but no game window was found")

    def hide_now(self):
        self.hide_game_window()

    def show_now(self):
        self.show_game_window()

    def close_process_orderly(self, pid, timeout=18.0):
        try:
            process = psutil.Process(pid)
        except Exception:
            return True

        handles = self.enum_windows_for_pid(pid)
        if handles:
            for hwnd in handles:
                user32.PostMessageW(hwnd, WM_CLOSE, 0, 0)
        else:
            try:
                process.terminate()
            except Exception:
                pass

        deadline = time.time() + timeout
        while time.time() < deadline:
            if not process.is_running():
                return True
            time.sleep(0.25)

        try:
            process.terminate()
        except Exception:
            pass

        try:
            process.wait(6)
            return True
        except Exception:
            pass

        try:
            process.kill()
            process.wait(4)
            return True
        except Exception:
            return False

    def launch_game(self, path):
        if not path or not Path(path).exists():
            raise FileNotFoundError("Game path does not exist")
        subprocess.Popen([path], cwd=str(Path(path).parent))

    def launch_game_manual(self):
        config = self.get_runtime_config()
        try:
            self.launch_game(config["game_path"])
            self.push_log("OK", "Game launch triggered")
            self.send_webhook_event("manual launch triggered", "manual_launch")
        except Exception as exc:
            with self.state_lock:
                self.runtime.last_error = str(exc)
            self.push_log("ERROR", f"Launch failed: {exc}")

    def start_restart_sequence(self, reason):
        if self.restart_lock.locked():
            self.push_log("WARN", "Restart already in progress")
            return

        threading.Thread(target=self.restart_sequence, args=(reason,), daemon=True).start()

    def restart_sequence(self, reason):
        with self.restart_lock:
            config = self.get_runtime_config()
            self.expected_game_down = True
            self.expected_game_down_reason = reason

            with self.state_lock:
                self.runtime.restart_state = f"Restarting: {reason}"

            self.push_log("INFO", f"Restart sequence started: {reason}")
            self.send_webhook_event(f"restart started ({reason})", "restart_events")

            with self.state_lock:
                current_pid = self.runtime.current_pid

            if current_pid:
                closed_ok = self.close_process_orderly(current_pid)
                if closed_ok:
                    self.push_log("OK", f"Game closed cleanly from PID {current_pid}")
                else:
                    self.push_log("WARN", f"Game needed forced termination on PID {current_pid}")
            else:
                self.push_log("WARN", "Restart requested while the game was not running")

            time.sleep(max(0.5, config["restart_cooldown"]))

            launched_ok = False
            try:
                self.launch_game(config["game_path"])
                launched_ok = True
            except Exception as exc:
                with self.state_lock:
                    self.runtime.last_error = str(exc)
                self.push_log("ERROR", f"Launch failed: {exc}")

            with self.state_lock:
                now = time.time()
                if launched_ok:
                    self.runtime.restart_count += 1
                    self.runtime.last_restart_at = now
                    self.runtime.restart_state = f"Last restart: {reason}"
                else:
                    self.runtime.restart_state = f"Restart failed: {reason}"

            self.pending_pid = None
            self.pending_start_time = None
            self.pending_detection_count = 0
            self.missed_detection_count = 0

            if launched_ok:
                self.push_log("OK", f"Game launch triggered from {config['game_path']}")
                self.send_webhook_event(f"restart completed ({reason})", "restart_events")
            else:
                self.send_webhook_event(f"restart failed ({reason})", "restart_events")

            self.expected_game_down = False
            self.expected_game_down_reason = ""

    def render_webhook_message(self, event, pid=None, session_start=None, session_length=None):
        config = self.get_runtime_config()
        now_text = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        user_id = config["discord_user_id"]
        mention = f"<@{user_id}>" if user_id else ""

        replacements = {
            "mention": mention,
            "user_id": user_id,
            "exe_name": config["target_exe"],
            "event": event,
            "time": now_text,
            "pid": str(pid or "-"),
            "session_length": session_length or "",
            "restart_interval_hours": str(config["timed_restart_hours"]),
        }

        try:
            return self.normalize_template(config["webhook_template"]).format(**replacements).strip()
        except Exception:
            return f"{mention} {config['target_exe']} {event}\nTime: {now_text}\nPID: {pid or '-'}".strip()

    def send_webhook_event(self, event, event_key, pid=None, session_start=None, session_length=None):
        webhook_url = self.get_runtime_config()["webhook_url"]
        if not webhook_url:
            return

        if not self.should_notify(event_key):
            return

        content = self.render_webhook_message(event, pid=pid, session_start=session_start, session_length=session_length)
        threading.Thread(target=self.send_webhook_request, args=(webhook_url, content), daemon=True).start()

    def send_webhook_request(self, webhook_url, content):
        try:
            response = requests.post(webhook_url, json={"content": content}, timeout=10)

            with self.state_lock:
                if 200 <= response.status_code < 300:
                    self.runtime.webhook_sent += 1
                    self.runtime.webhook_state = "Last request successful"
                else:
                    self.runtime.webhook_state = f"HTTP {response.status_code}"

            if 200 <= response.status_code < 300:
                self.push_log("WEBHOOK", "Webhook delivered")
            else:
                self.push_log("ERROR", f"Webhook failed with HTTP {response.status_code}")
        except Exception as exc:
            with self.state_lock:
                self.runtime.webhook_state = "Request failed"
                self.runtime.last_error = str(exc)
            self.push_log("ERROR", f"Webhook failed: {exc}")

    def test_webhook(self):
        config = self.get_runtime_config()
        if not config["webhook_url"]:
            messagebox.showerror(APP_TITLE, "Webhook URL is empty")
            return

        with self.state_lock:
            self.runtime.webhook_state = "Sending test request..."

        self.push_log("INFO", "Sending test webhook")
        self.send_webhook_event("test event", "test")

    def start_monitor(self):
        if self.monitor_thread and self.monitor_thread.is_alive():
            self.push_log("WARN", "Monitor already running")
            return

        config = self.get_runtime_config()
        if not config["target_exe"]:
            messagebox.showerror(APP_TITLE, "Target EXE is required")
            return

        self.monitor_stop_event.clear()
        self.pending_pid = None
        self.pending_start_time = None
        self.pending_detection_count = 0
        self.missed_detection_count = 0

        now = time.time()

        with self.state_lock:
            self.runtime.monitor_running = True
            self.runtime.monitor_started_at = now
            self.runtime.restart_state = "Idle"
            self.runtime.last_error = "None"

        self.monitor_thread = threading.Thread(target=self.monitor_loop, daemon=True)
        self.monitor_thread.start()

        self.push_log("INFO", f"Monitor started for {config['target_exe']}")
        self.send_webhook_event("monitor started", "monitor_events")

    def stop_monitor(self):
        if not (self.monitor_thread and self.monitor_thread.is_alive()):
            self.push_log("WARN", "Monitor is not running")
            return

        self.monitor_stop_event.set()
        with self.state_lock:
            self.runtime.monitor_running = False
            self.runtime.restart_state = "Stopped"

        self.push_log("INFO", "Stopping monitor")
        self.send_webhook_event("monitor stopped", "monitor_events")

    def mark_game_started_stable(self, config, pid, started_at):
        with self.state_lock:
            self.runtime.game_running = True
            self.runtime.current_pid = pid
            self.runtime.current_exe_display = f"{config['target_exe']} (PID {pid})"
            self.runtime.game_started_at = started_at
            self.runtime.next_timed_restart_at = started_at + config["timed_restart_hours"] * 3600 if config["timed_restart_enabled"] else None

        self.push_log("OK", f"Game detected on PID {pid}")
        self.send_webhook_event("game started", "game_started", pid=pid, session_start=started_at)

        if config["start_hidden"]:
            threading.Thread(target=self.ensure_hidden_after_launch, args=(pid,), daemon=True).start()

    def handle_detected_process(self, config, process, now):
        pid = process.pid
        try:
            started_at = process.create_time()
        except Exception:
            started_at = now

        if self.runtime.current_pid == pid and self.runtime.game_running:
            self.missed_detection_count = 0
            with self.state_lock:
                self.runtime.current_exe_display = f"{config['target_exe']} (PID {pid})"
                self.runtime.next_timed_restart_at = started_at + config["timed_restart_hours"] * 3600 if config["timed_restart_enabled"] else None
            return

        if self.pending_pid == pid:
            self.pending_detection_count += 1
        else:
            self.pending_pid = pid
            self.pending_start_time = started_at
            self.pending_detection_count = 1

        self.missed_detection_count = 0

        if self.pending_detection_count >= DETECTION_STABLE_POLLS:
            self.mark_game_started_stable(config, pid, self.pending_start_time)
            self.pending_pid = None
            self.pending_start_time = None
            self.pending_detection_count = 0

    def handle_missing_process(self, config, now):
        if self.pending_pid is not None:
            self.pending_pid = None
            self.pending_start_time = None
            self.pending_detection_count = 0

        if self.runtime.current_pid is None:
            with self.state_lock:
                self.runtime.game_running = False
                self.runtime.current_pid = None
                self.runtime.current_exe_display = f"{config['target_exe']} (not detected)"
                self.runtime.game_started_at = None
                self.runtime.hidden_mode = False
                self.runtime.next_timed_restart_at = None
            return

        self.missed_detection_count += 1
        if self.missed_detection_count < MISSED_POLLS_FOR_CLOSE:
            return

        previous_pid = None
        previous_start = None

        with self.state_lock:
            previous_pid = self.runtime.current_pid
            previous_start = self.runtime.game_started_at
            self.runtime.game_running = False
            self.runtime.current_pid = None
            self.runtime.current_exe_display = f"{config['target_exe']} (not detected)"
            self.runtime.game_started_at = None
            self.runtime.hidden_mode = False
            self.runtime.next_timed_restart_at = None

        self.missed_detection_count = 0

        session_length = self.format_duration(now - previous_start) if previous_start else "00:00:00"

        if self.expected_game_down:
            self.push_log("MODE", f"Game closed for {self.expected_game_down_reason}")
            return

        with self.state_lock:
            self.runtime.close_events += 1

        self.push_log("WARN", f"Game closed after {session_length}")
        self.send_webhook_event("game closed unexpectedly", "unexpected_close", pid=previous_pid)

        if config["auto_restart_on_close"] and not self.restart_lock.locked():
            if now - self.get_last_restart_at() >= config["restart_cooldown"]:
                self.start_restart_sequence("unexpected close")

    def monitor_loop(self):
        while not self.monitor_stop_event.is_set():
            config = self.get_runtime_config()
            process = self.find_process(config["target_exe"], config["game_path"])
            now = time.time()

            if process:
                self.handle_detected_process(config, process, now)

                if config["timed_restart_enabled"] and not self.restart_lock.locked():
                    if self.runtime.game_started_at and now >= self.runtime.game_started_at + config["timed_restart_hours"] * 3600:
                        if now - self.get_last_restart_at() >= config["restart_cooldown"]:
                            self.start_restart_sequence("timed restart")
            else:
                self.handle_missing_process(config, now)

            sleep_time = max(1.0, config["poll_interval"] * 1.8) if config["low_resource_mode"] else config["poll_interval"]
            end_time = time.time() + sleep_time

            while time.time() < end_time:
                if self.monitor_stop_event.is_set():
                    break
                time.sleep(0.1)

        with self.state_lock:
            self.runtime.monitor_running = False
            self.runtime.game_running = False
            self.runtime.next_timed_restart_at = None
            self.runtime.restart_state = "Stopped"

        self.pending_pid = None
        self.pending_start_time = None
        self.pending_detection_count = 0
        self.missed_detection_count = 0

        self.push_log("INFO", "Monitor stopped")

    def get_last_restart_at(self):
        with self.state_lock:
            return self.runtime.last_restart_at

    def on_close(self):
        if not self.is_quitting:
            self.minimize_to_tray()
            return

        try:
            self.auto_save_config()
        except Exception:
            pass

        self.monitor_stop_event.set()
        self.stop_tray_icon()
        self.destroy()


if __name__ == "__main__":
    app = GW2MonitorApp()
    app.mainloop()
