# GW2 Monitor 2.0

Watchdog for **Plants vs. Zombies: Garden Warfare 2**: detects crashes and freezes,
restarts the game automatically, hides the game window and reports everything to Discord.

**One file, nothing to install:** `GW2Monitor.exe` (~185 KB) runs on any Windows 10/11 PC as-is.
No Python, no runtime download.

---

## Quick start

1. Download **[GW2Monitor.exe](https://github.com/Massivendurchfall/gw2-monitor/raw/main/dist/GW2Monitor.exe)**, put it into any folder and run it.
   (If Windows shows "Windows protected your PC": *More info → Run anyway*.)
2. **Settings → Game path**: use *Browse* to pick `GW2.Main_Win64_Retail.exe`.
3. Optional: paste a **Discord → Webhook URL** and click *Send test message*.
4. On the **Overview**, click **Start monitoring**. Done.

> Still have a `gw2_monitor_config.json` from the old Python version?
> Just put it in the same folder – it's imported automatically on first start.
> (The old `gw2monitor.py` is still available in the git history.)

## Fully unattended (PC reboots, Windows Update, …)

Under **Settings**, turn on:

- *Start with Windows*
- *Start monitoring when the app starts*
- *Launch the game when monitoring starts*
- optionally *Hide game window automatically*

After a reboot the monitor starts in the tray, launches the game and watches it – nobody needs to be at the PC.

## Features

| Feature | Details |
|---|---|
| **Crash detection** | Notices instantly when the game exits – including the exit code (e.g. `0xC0000005` = access violation). Tells a *crash* apart from a *normal close*. |
| **Freeze detection** | If the game window stops responding (e.g. for 90 s), the game is killed and restarted. |
| **Automatic restart** | When the game exits: *Never / Only on crash / Always*. Plus an optional scheduled restart (e.g. every 2 h). |
| **Crash-loop protection** | At most X automatic restarts per hour, so a broken game doesn't restart forever. |
| **Launch retries** | If the game doesn't come up after launching, it tries again (3 attempts). |
| **Hide window** | The game keeps running invisibly in the background – also after every restart. Hotkey **Ctrl + Alt + H** toggles it from anywhere. When the monitor exits, the window is made visible again automatically. |
| **Discord** | Clean embeds per event, ping only on problems (optional), PC name in every message, optional status report every X hours. |
| **Tray** | Icon shows the status by color (green = OK, yellow = busy, red = problem, gray = off). Right-click for all actions. |
| **Log** | Every event in the app and in `GW2Monitor.log` next to the EXE. |

## Files next to the EXE

- `GW2Monitor.json` – settings (saved automatically)
- `GW2Monitor.log` – log (rotated at 2 MB)

If the folder isn't writable (e.g. under *Program Files*), both go to `%APPDATA%\GW2Monitor`.

## Building it yourself

Only needs the free **Visual Studio Build Tools** (C# compiler):

```
powershell -ExecutionPolicy Bypass -File build.ps1
```

Output: `dist\GW2Monitor.exe`. Source code is in `src\` (C# / WPF, .NET Framework 4.8).

| File | Contents |
|---|---|
| `src\Watchdog.cs` | Core logic: detection, crash/freeze, restart, hiding |
| `src\Discord.cs` | Webhook queue with rate-limit handling and retries |
| `src\MainWindow.xaml` | The UI (design, colors, layout) |
| `src\MainView.cs` | Connects the UI to the settings and the watchdog |
| `src\Settings.cs` | Settings, saving, import of the old config |
| `src\App.cs`, `src\Tray.cs` | Startup, single instance, autostart, tray icon |
