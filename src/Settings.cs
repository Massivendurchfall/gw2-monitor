using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Reflection;
using System.Text;
using System.Web.Script.Serialization;

namespace GW2Monitor
{
    /// <summary>
    /// All settings. An instance is never modified in place: every change clones and swaps it
    /// (Settings.Current), so the watchdog thread always reads a consistent state.
    /// </summary>
    public sealed class Settings
    {
        // Game
        public string GamePath = @"C:\Program Files (x86)\Steam\steamapps\common\PVZGW2\GW2.Main_Win64_Retail.exe";
        public string ProcessName = "GW2.Main_Win64_Retail.exe";

        // Automation (only applies while monitoring is active)
        public int RestartPolicy = 1;          // 0 = never, 1 = only on crash, 2 = always
        public bool TimedRestart = false;
        public double TimedRestartHours = 2;
        public bool FreezeDetection = true;
        public int FreezeSeconds = 90;
        public bool StartHidden = false;
        public bool LaunchOnArm = false;
        public bool Hotkey = true;

        // App
        public bool StartWithWindows = false;
        public bool ArmOnLaunch = false;
        public bool CloseToTray = true;

        // Advanced
        public double PollSeconds = 1;
        public int RestartCooldownSeconds = 5;
        public int MaxRestartsPerHour = 5;     // 0 = unlimited
        public int LaunchTimeoutSeconds = 180;

        // Discord
        public string WebhookUrl = "";
        public string DiscordUserId = "";
        public string InstanceName = "";
        public bool PingOnlyOnProblems = true;
        public bool NotifyWatchdog = true;
        public bool NotifyGameStarted = true;
        public bool NotifyGameClosed = true;
        public bool NotifyFreeze = true;
        public bool NotifyRestart = true;
        public bool NotifyHideShow = false;
        public bool NotifyHeartbeat = false;
        public double HeartbeatHours = 6;

        // internal
        public bool TrayHintShown = false;

        // ------------------------------------------------------------------

        static volatile Settings _current = new Settings();
        public static Settings Current { get { return _current; } set { _current = value; } }

        public static string AppDir { get; private set; }
        public static string DataDir { get; private set; }
        public static string FilePath { get; private set; }
        public const string LegacyFileName = "gw2_monitor_config.json";

        static readonly CultureInfo Inv = CultureInfo.InvariantCulture;
        static FieldInfo[] Fields { get { return typeof(Settings).GetFields(BindingFlags.Public | BindingFlags.Instance); } }

        public Settings Clone() { return (Settings)MemberwiseClone(); }

        /// <summary>Raised after every change made through Mutate (UI thread).</summary>
        public static event Action Changed;

        /// <summary>Changes settings atomically: copy, modify, swap.</summary>
        public static void Mutate(Action<Settings> change)
        {
            var copy = Current.Clone();
            change(copy);
            Current = copy;
            var h = Changed;
            if (h != null) h();
        }

        /// <summary>Loads the settings. Returns true if an old Python config was imported.</summary>
        public static bool Init()
        {
            AppDir = Path.GetDirectoryName(Assembly.GetEntryAssembly().Location);
            DataDir = CanWrite(AppDir) ? AppDir : Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.ApplicationData), "GW2Monitor");
            Directory.CreateDirectory(DataDir);
            FilePath = Path.Combine(DataDir, "GW2Monitor.json");

            var s = new Settings();
            bool imported = false;
            if (File.Exists(FilePath))
            {
                try { s.Read(Parse(File.ReadAllText(FilePath, Encoding.UTF8))); } catch { }
            }
            else
            {
                string legacy = FindLegacy();
                if (legacy != null)
                {
                    try { s.ImportLegacy(Parse(File.ReadAllText(legacy, Encoding.UTF8))); imported = true; } catch { }
                }
            }
            s.Sanitize();
            Current = s;
            s.Save();
            return imported;
        }

        public bool Save()
        {
            try
            {
                var js = new JavaScriptSerializer();
                var sb = new StringBuilder("{\r\n");
                var fields = Fields;
                for (int i = 0; i < fields.Length; i++)
                {
                    object v = fields[i].GetValue(this);
                    string text;
                    if (v is bool) text = (bool)v ? "true" : "false";
                    else if (v is double) text = ((double)v).ToString("R", Inv);
                    else if (v is int) text = ((int)v).ToString(Inv);
                    else text = js.Serialize(v as string ?? "");
                    sb.Append("  \"").Append(fields[i].Name).Append("\": ").Append(text);
                    sb.Append(i < fields.Length - 1 ? ",\r\n" : "\r\n");
                }
                sb.Append("}\r\n");

                string tmp = FilePath + ".tmp";
                File.WriteAllText(tmp, sb.ToString(), new UTF8Encoding(false));
                if (File.Exists(FilePath)) File.Replace(tmp, FilePath, null);
                else File.Move(tmp, FilePath);
                return true;
            }
            catch { return false; }
        }

        void Read(Dictionary<string, object> d)
        {
            foreach (var f in Fields)
            {
                object v;
                if (!d.TryGetValue(f.Name, out v) || v == null) continue;
                try { f.SetValue(this, Convert(v, f.FieldType)); } catch { }
            }
        }

        void ImportLegacy(Dictionary<string, object> d)
        {
            Action<string, Action<object>> map = (key, apply) =>
            {
                object v;
                if (d.TryGetValue(key, out v) && v != null) { try { apply(v); } catch { } }
            };
            map("game_path", v => GamePath = Str(v));
            map("target_exe", v => ProcessName = Str(v));
            map("discord_user_id", v => DiscordUserId = Str(v));
            map("webhook_url", v => WebhookUrl = Str(v));
            map("poll_interval", v => PollSeconds = Num(v));
            map("restart_cooldown", v => RestartCooldownSeconds = (int)Math.Round(Num(v)));
            map("timed_restart_enabled", v => TimedRestart = Bool(v));
            map("timed_restart_hours", v => TimedRestartHours = Num(v));
            map("auto_restart_on_close", v => RestartPolicy = Bool(v) ? 2 : 0);
            map("start_hidden", v => StartHidden = Bool(v));
            map("notify_monitor_events", v => NotifyWatchdog = Bool(v));
            map("notify_game_started", v => NotifyGameStarted = Bool(v));
            map("notify_unexpected_close", v => NotifyGameClosed = Bool(v));
            map("notify_restart_events", v => NotifyRestart = Bool(v));
            map("notify_hide_show", v => NotifyHideShow = Bool(v));
        }

        void Sanitize()
        {
            GamePath = (GamePath ?? "").Trim();
            ProcessName = (ProcessName ?? "").Trim();
            WebhookUrl = (WebhookUrl ?? "").Trim();
            DiscordUserId = (DiscordUserId ?? "").Trim();
            InstanceName = (InstanceName ?? "").Trim();
            if (ProcessName.Length == 0 && GamePath.EndsWith(".exe", StringComparison.OrdinalIgnoreCase))
                ProcessName = Path.GetFileName(GamePath);
            RestartPolicy = Math.Max(0, Math.Min(2, RestartPolicy));
            TimedRestartHours = Clamp(TimedRestartHours, 0.1, 168);
            FreezeSeconds = (int)Clamp(FreezeSeconds, 10, 3600);
            PollSeconds = Clamp(PollSeconds, 0.25, 10);
            RestartCooldownSeconds = (int)Clamp(RestartCooldownSeconds, 0, 600);
            MaxRestartsPerHour = (int)Clamp(MaxRestartsPerHour, 0, 100);
            LaunchTimeoutSeconds = (int)Clamp(LaunchTimeoutSeconds, 30, 1800);
            HeartbeatHours = Clamp(HeartbeatHours, 0.25, 168);
        }

        static string FindLegacy()
        {
            foreach (var dir in new[] { AppDir, Environment.CurrentDirectory })
            {
                string p = Path.Combine(dir, LegacyFileName);
                if (File.Exists(p)) return p;
            }
            return null;
        }

        static bool CanWrite(string dir)
        {
            try
            {
                string probe = Path.Combine(dir, ".gw2monitor_write_test");
                File.WriteAllText(probe, "");
                File.Delete(probe);
                return true;
            }
            catch { return false; }
        }

        static Dictionary<string, object> Parse(string json)
        {
            var raw = new JavaScriptSerializer().DeserializeObject(json) as Dictionary<string, object>;
            return raw == null
                ? new Dictionary<string, object>()
                : new Dictionary<string, object>(raw, StringComparer.OrdinalIgnoreCase);
        }

        static object Convert(object v, Type t)
        {
            if (t == typeof(string)) return Str(v);
            if (t == typeof(bool)) return Bool(v);
            if (t == typeof(double)) return Num(v);
            if (t == typeof(int)) return (int)Math.Round(Num(v));
            throw new NotSupportedException();
        }

        static string Str(object v) { return System.Convert.ToString(v, Inv) ?? ""; }
        static bool Bool(object v) { return v is bool ? (bool)v : bool.Parse(v.ToString()); }
        static double Num(object v)
        {
            var s = v as string;
            return s != null ? double.Parse(s.Trim().Replace(',', '.'), Inv) : System.Convert.ToDouble(v, Inv);
        }
        static double Clamp(double v, double lo, double hi) { return double.IsNaN(v) ? lo : Math.Max(lo, Math.Min(hi, v)); }
    }
}
