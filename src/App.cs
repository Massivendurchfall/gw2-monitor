using System;
using System.Collections.ObjectModel;
using System.Linq;
using System.Reflection;
using System.Runtime.Versioning;
using System.Threading;
using System.Windows;
using System.Windows.Interop;
using System.Windows.Threading;
using Microsoft.Win32;

[assembly: AssemblyTitle("GW2 Monitor")]
[assembly: AssemblyProduct("GW2 Monitor")]
[assembly: AssemblyDescription("Watchdog for PvZ Garden Warfare 2")]
[assembly: AssemblyVersion("2.0.0.0")]
[assembly: AssemblyFileVersion("2.0.0.0")]
[assembly: TargetFramework(".NETFramework,Version=v4.8", FrameworkDisplayName = ".NET Framework 4.8")]

namespace GW2Monitor
{
    static class Program
    {
        [STAThread]
        static void Main(string[] args)
        {
            bool render = args.Contains("--render");
            bool created;
            using (var mutex = new Mutex(true, render ? @"Local\GW2Monitor.Render" : @"Local\GW2Monitor.Instance", out created))
            {
                if (!created)
                {
                    // Already running: bring the existing window to the front.
                    try { using (var ev = EventWaitHandle.OpenExisting(AppController.ShowEventName)) ev.Set(); } catch { }
                    return;
                }

                var app = new Application { ShutdownMode = ShutdownMode.OnExplicitShutdown };
                var controller = new AppController(args);
                app.DispatcherUnhandledException += (s, e) =>
                {
                    e.Handled = true;
                    controller.ReportCrash(e.Exception);
                };
                AppDomain.CurrentDomain.UnhandledException += (s, e) =>
                    FileLog.Write(Level.Error, "Unhandled error: " + e.ExceptionObject);
                app.Startup += (s, e) => controller.Start();
                app.Run();
                GC.KeepAlive(mutex);
            }
        }
    }

    sealed class AppController
    {
        public const string ShowEventName = @"Local\GW2Monitor.Show";
        const string RunKey = @"Software\Microsoft\Windows\CurrentVersion\Run";
        const string RunValue = "GW2Monitor";

        readonly string[] _args;
        readonly ObservableCollection<LogEntry> _log = new ObservableCollection<LogEntry>();
        readonly ObservableCollection<LogEntry> _recent = new ObservableCollection<LogEntry>();
        Dispatcher _ui;
        DiscordNotifier _discord;
        Watchdog _wd;
        MainView _view;
        Tray _tray;
        DispatcherTimer _timer;
        EventWaitHandle _showEvent;
        bool _exiting, _crashShown;

        public AppController(string[] args) { _args = args; }

        public void Start()
        {
            _ui = Dispatcher.CurrentDispatcher;
            bool imported = Settings.Init();
            FileLog.Init(Settings.DataDir);
            Log(Level.Info, "GW2 Monitor 2.0 started");
            if (imported) Log(Level.Success, "Imported settings from the old version");
            if (!string.Equals(Settings.DataDir, Settings.AppDir, StringComparison.OrdinalIgnoreCase))
                Log(Level.Info, "Settings are stored in " + Settings.DataDir);

            _discord = new DiscordNotifier();
            _discord.Log += Log;
            _wd = new Watchdog(_discord);
            _wd.Log += Log;
            _wd.Alert += (title, text) => _ui.BeginInvoke(new Action(() =>
            {
                if (_tray != null && !_view.Window.IsVisible) _tray.Balloon(title, text, true);
            }));

            string renderDir = ArgValue("--render");
            _view = new MainView(this, _wd, _discord, _log, _recent) { HotkeyAllowed = renderDir == null };
            _tray = new Tray(() => _wd.Snapshot, ShowWindow, () => _wd.SetArmed(!_wd.Snapshot.Armed),
                             _wd.ToggleHidden, _wd.RestartGame, Exit);
            new WindowInteropHelper(_view.Window).EnsureHandle(); // needed for the hotkey, even when starting in the tray

            if (renderDir != null) { StartRender(renderDir); return; }

            ApplyAutostart();
            if (!_args.Contains("--autostart")) ShowWindow();
            if (Settings.Current.ArmOnLaunch) _wd.SetArmed(true);

            _timer = new DispatcherTimer(TimeSpan.FromMilliseconds(500), DispatcherPriority.Background, (s, e) => Tick(), _ui);
            _timer.Start();

            _showEvent = new EventWaitHandle(false, EventResetMode.AutoReset, ShowEventName);
            ThreadPool.RegisterWaitForSingleObject(_showEvent, (st, timedOut) => _ui.BeginInvoke(new Action(ShowWindow)), null, -1, false);
        }

        void Tick()
        {
            var s = _wd.Snapshot;
            if (_view.Window.IsVisible) _view.Refresh(s);

            var now = DateTime.Now;
            bool hung = s.HungSince.HasValue && (now - s.HungSince.Value).TotalSeconds >= 10;
            var state = !s.Armed ? Tray.State.Off
                      : hung ? Tray.State.Problem
                      : s.Phase == Phase.Running ? Tray.State.Ok
                      : Tray.State.Busy;
            string game = s.Phase == Phase.Running ? "Game running (" + Fmt.Human(now - s.GameStart) + ")"
                        : s.Phase == Phase.Launching ? "Game starting"
                        : s.Phase == Phase.Restarting ? "Restarting"
                        : "Game not running";
            _tray.Update(state, "GW2 Monitor – " + game + (s.Armed ? " · monitored" : ""));
        }

        public void ShowWindow()
        {
            var w = _view.Window;
            if (!w.IsVisible) w.Show();
            if (w.WindowState == WindowState.Minimized) w.WindowState = WindowState.Normal;
            w.Activate();
            w.Topmost = true;
            w.Topmost = false;
            _view.Refresh(_wd.Snapshot);
        }

        public void HideToTray()
        {
            _view.Window.Hide();
            if (!Settings.Current.TrayHintShown)
            {
                _tray.Balloon("GW2 Monitor is still running", "The app is now in the tray. Right-click the icon to exit.", false);
                Settings.Mutate(x => x.TrayHintShown = true);
            }
        }

        public void Exit()
        {
            if (_exiting) return;
            _exiting = true;
            if (_timer != null) _timer.Stop();
            _wd.Shutdown();          // makes hidden game windows visible again
            _view.FlushSave();
            Log(Level.Info, "GW2 Monitor closed");
            _tray.Dispose();
            _view.AllowClose = true;
            _view.Window.Close();
            Application.Current.Shutdown();
        }

        public void Log(Level level, string message)
        {
            FileLog.Write(level, message);
            if (_ui == null) return;
            _ui.BeginInvoke(new Action(() =>
            {
                var e = new LogEntry(level, message);
                _log.Insert(0, e);
                if (_log.Count > 500) _log.RemoveAt(_log.Count - 1);
                _recent.Insert(0, e);
                while (_recent.Count > 6) _recent.RemoveAt(_recent.Count - 1);
            }));
        }

        /// <summary>Adds/removes the app in Windows autostart (only touches its own entry).</summary>
        public void ApplyAutostart()
        {
            try
            {
                string exe = Assembly.GetEntryAssembly().Location;
                string want = "\"" + exe + "\" --autostart";
                using (var key = Registry.CurrentUser.CreateSubKey(RunKey))
                {
                    string existing = key.GetValue(RunValue) as string;
                    if (Settings.Current.StartWithWindows)
                    {
                        if (existing != want) key.SetValue(RunValue, want);
                    }
                    else if (existing != null && existing.IndexOf(exe, StringComparison.OrdinalIgnoreCase) >= 0)
                    {
                        key.DeleteValue(RunValue, false);
                    }
                }
            }
            catch (Exception ex)
            {
                Log(Level.Warning, "Couldn't update autostart: " + ex.Message);
            }
        }

        public void ReportCrash(Exception ex)
        {
            FileLog.Write(Level.Error, ex.ToString());
            if (_crashShown) return;
            _crashShown = true;
            MessageBox.Show("Unexpected error:\n\n" + ex.Message + "\n\nDetails are in GW2Monitor.log.",
                            "GW2 Monitor", MessageBoxButton.OK, MessageBoxImage.Error);
        }

        void StartRender(string dir)
        {
            var w = _view.Window;
            w.ShowInTaskbar = false;
            w.ShowActivated = false;
            w.WindowStartupLocation = WindowStartupLocation.Manual;
            w.Left = -32000;
            w.Top = -32000;
            w.Show();
            if (Settings.Current.ArmOnLaunch) _wd.SetArmed(true);
            int delay;
            if (!int.TryParse(ArgValue("--delay") ?? "3", out delay)) delay = 3;
            var t = new DispatcherTimer { Interval = TimeSpan.FromSeconds(delay) };
            t.Tick += (s, e) =>
            {
                t.Stop();
                _view.Refresh(_wd.Snapshot);
                _view.RenderPages(dir);
                Exit();
            };
            t.Start();
        }

        string ArgValue(string name)
        {
            int i = Array.IndexOf(_args, name);
            return i >= 0 && i + 1 < _args.Length ? _args[i + 1] : null;
        }
    }
}
