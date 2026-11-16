using System;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Interop;
using System.Windows.Markup;
using System.Windows.Media;
using System.Windows.Media.Animation;
using System.Windows.Media.Imaging;
using System.Windows.Shapes;
using System.Windows.Threading;
using Microsoft.Win32;

namespace GW2Monitor
{
    /// <summary>Loads MainWindow.xaml from the EXE and wires the UI to the watchdog and settings.</summary>
    sealed class MainView
    {
        const int HotkeyId = 0x4757;
        static readonly string[] Pages = { "Dashboard", "Settings", "Discord", "Log" };
        static readonly Regex WebhookRx = new Regex(@"^https://(ptb\.|canary\.)?discord(app)?\.com/api/webhooks/\d+/[\w-]+/?$", RegexOptions.IgnoreCase);

        readonly Window _w;
        readonly AppController _app;
        readonly Watchdog _wd;
        readonly DiscordNotifier _discord;
        readonly DispatcherTimer _saveTimer;
        readonly Brush _chipOn = Frozen(0x17, 0x33, 0x2A), _chipOff = Frozen(0x26, 0x29, 0x38);

        readonly Ellipse _halo, _dot, _navDot;
        readonly TextBlock _statusTitle, _statusDetail, _chipText, _watchIcon, _watchText, _navStatus, _navSub;
        readonly TextBlock _tileUptime, _tileUptimeSub, _tileNext, _tileNextSub, _tileRestarts, _tileCrashes, _tileCrashesSub;
        readonly TextBlock _restartText, _hideIcon, _hideText;
        readonly Border _chip;
        readonly Button _watchBtn, _launchBtn, _restartBtn, _hideBtn;

        IntPtr _hwnd;
        bool _hotkeyOn, _pulsing, _noAnim;
        bool? _watchArmedShown;
        DateTime _restartConfirmUntil = DateTime.MinValue;

        public bool AllowClose;
        public bool HotkeyAllowed = true;
        public Window Window { get { return _w; } }

        public MainView(AppController app, Watchdog wd, DiscordNotifier discord,
                        ObservableCollection<LogEntry> log, ObservableCollection<LogEntry> recent)
        {
            _app = app;
            _wd = wd;
            _discord = discord;

            using (var s = typeof(MainView).Assembly.GetManifestResourceStream("GW2Monitor.MainWindow.xaml"))
                _w = (Window)XamlReader.Load(s);
            _w.Icon = MakeWindowIcon();

            _halo = E<Ellipse>("StatusHalo");
            _halo.RenderTransform = new ScaleTransform(1, 1);
            _dot = E<Ellipse>("StatusDot");
            _navDot = E<Ellipse>("NavDot");
            _statusTitle = E<TextBlock>("StatusTitle");
            _statusDetail = E<TextBlock>("StatusDetail");
            _chip = E<Border>("WatchChip");
            _chipText = E<TextBlock>("WatchChipText");
            _watchIcon = E<TextBlock>("WatchIcon");
            _watchText = E<TextBlock>("WatchText");
            _navStatus = E<TextBlock>("NavStatus");
            _navSub = E<TextBlock>("NavSub");
            _tileUptime = E<TextBlock>("TileUptime");
            _tileUptimeSub = E<TextBlock>("TileUptimeSub");
            _tileNext = E<TextBlock>("TileNext");
            _tileNextSub = E<TextBlock>("TileNextSub");
            _tileRestarts = E<TextBlock>("TileRestarts");
            _tileCrashes = E<TextBlock>("TileCrashes");
            _tileCrashesSub = E<TextBlock>("TileCrashesSub");
            _restartText = E<TextBlock>("RestartText");
            _hideIcon = E<TextBlock>("HideIcon");
            _hideText = E<TextBlock>("HideText");
            _watchBtn = E<Button>("WatchButton");
            _launchBtn = E<Button>("LaunchButton");
            _restartBtn = E<Button>("RestartButton");
            _hideBtn = E<Button>("HideButton");

            _saveTimer = new DispatcherTimer { Interval = TimeSpan.FromMilliseconds(400) };
            _saveTimer.Tick += (o, e) => FlushSave();
            Settings.Changed += () => { _saveTimer.Stop(); _saveTimer.Start(); RefreshEnables(); };

            WireNavigation();
            WireDashboard(recent);
            WireSettings();
            WireDiscord();
            WireLog(log, recent);
            RefreshEnables();

            _w.SourceInitialized += (o, e) => OnSourceInitialized();
            _w.Closing += (o, e) =>
            {
                if (AllowClose) return;
                e.Cancel = true; // Hide/Close must not run directly inside the Closing handler
                if (Settings.Current.CloseToTray) _w.Dispatcher.BeginInvoke(new Action(_app.HideToTray));
                else _w.Dispatcher.BeginInvoke(new Action(_app.Exit));
            };
        }

        T E<T>(string name) where T : class
        {
            var o = _w.FindName(name) as T;
            if (o == null) throw new InvalidOperationException("XAML element missing: " + name);
            return o;
        }

        Brush Res(string key) { return (Brush)_w.Resources[key]; }

        static Brush Frozen(byte r, byte g, byte b)
        {
            var br = new SolidColorBrush(Color.FromRgb(r, g, b));
            br.Freeze();
            return br;
        }

        // ================= Navigation =================

        void WireNavigation()
        {
            foreach (var p in Pages)
            {
                string page = p;
                E<RadioButton>("Nav" + page).Checked += (o, e) => ShowPage(page);
            }
        }

        void ShowPage(string page)
        {
            foreach (var p in Pages)
            {
                var el = E<FrameworkElement>("Page" + p);
                bool on = p == page;
                el.Visibility = on ? Visibility.Visible : Visibility.Collapsed;
                if (on && !_noAnim)
                    el.BeginAnimation(UIElement.OpacityProperty, new DoubleAnimation(0, 1, TimeSpan.FromMilliseconds(160)));
            }
        }

        // ================= Overview =================

        void WireDashboard(ObservableCollection<LogEntry> recent)
        {
            _watchBtn.Click += (o, e) => _wd.SetArmed(!_wd.Snapshot.Armed);
            _launchBtn.Click += (o, e) => _wd.LaunchGame();
            _hideBtn.Click += (o, e) => _wd.ToggleHidden();
            E<Button>("TrayButton").Click += (o, e) => _app.HideToTray();
            E<Button>("ShowLogButton").Click += (o, e) => E<RadioButton>("NavLog").IsChecked = true;

            // Restart needs a second click so nothing happens by accident.
            _restartBtn.Click += (o, e) =>
            {
                if (DateTime.Now < _restartConfirmUntil)
                {
                    _restartConfirmUntil = DateTime.MinValue;
                    _restartText.Text = "Restart game";
                    _wd.RestartGame();
                }
                else
                {
                    _restartConfirmUntil = DateTime.Now.AddSeconds(3);
                    _restartText.Text = "Sure? Click again";
                }
            };

            var list = E<ItemsControl>("RecentList");
            var empty = E<TextBlock>("RecentEmpty");
            list.ItemsSource = recent;
            recent.CollectionChanged += (o, e) => empty.Visibility = recent.Count == 0 ? Visibility.Visible : Visibility.Collapsed;
        }

        public void Refresh(Snapshot s)
        {
            var now = DateTime.Now;
            var cfg = Settings.Current;
            bool running = s.Pid != 0 && s.Phase == Phase.Running;
            bool hung = running && s.HungSince.HasValue && (now - s.HungSince.Value).TotalSeconds >= 5;

            string title, detail;
            Brush color;
            bool pulse;
            if (hung)
            {
                title = "Game not responding";
                detail = "Frozen for " + Fmt.Human(now - s.HungSince.Value) +
                         (s.Armed && cfg.FreezeDetection ? " · restart after " + Fmt.Seconds(cfg.FreezeSeconds) : "");
                color = Res("Bad");
                pulse = true;
            }
            else if (running)
            {
                title = "Game running";
                detail = "PID " + s.Pid + " · started " + s.GameStart.ToString("HH:mm") +
                         (s.Hidden ? " · window hidden" : "") + (s.LimitedAccess ? " · limited access" : "");
                color = Res("Good");
                pulse = s.Armed;
            }
            else if (s.Phase == Phase.Launching)
            {
                title = "Starting game …";
                detail = s.LaunchAttempt > 1 ? "Attempt " + s.LaunchAttempt + " of 3 · waiting for the game process" : "Waiting for the game process";
                color = Res("Info");
                pulse = true;
            }
            else if (s.Phase == Phase.Restarting)
            {
                title = "Restarting …";
                detail = "Reason: " + s.Reason;
                color = Res("Warn");
                pulse = true;
            }
            else if (s.Armed)
            {
                title = "Waiting for the game";
                detail = "It will be detected automatically as soon as it runs.";
                color = Res("Warn");
                pulse = false;
            }
            else
            {
                title = "Game not running";
                detail = "Start monitoring so crashes and freezes are handled automatically.";
                color = Res("Idle");
                pulse = false;
            }
            _statusTitle.Text = title;
            _statusDetail.Text = detail;
            SetPulse(pulse, color);

            _chipText.Text = s.Armed ? "MONITORED" : "NOT MONITORED";
            _chipText.Foreground = s.Armed ? Res("Good") : Res("Muted");
            _chip.Background = s.Armed ? _chipOn : _chipOff;

            if (_watchArmedShown != s.Armed)
            {
                _watchArmedShown = s.Armed;
                _watchBtn.Style = (Style)_w.Resources[s.Armed ? "BtnDanger" : "BtnPrimary"];
                _watchIcon.Text = s.Armed ? "" : "";
                _watchText.Text = s.Armed ? "Stop monitoring" : "Start monitoring";
            }

            // Tiles
            if (s.Pid != 0)
            {
                _tileUptime.Text = Fmt.Clock(now - s.GameStart);
                _tileUptimeSub.Text = "since " + s.GameStart.ToString("HH:mm");
            }
            else
            {
                _tileUptime.Text = "--:--:--";
                _tileUptimeSub.Text = "Game not active";
            }

            if (s.NextRestart.HasValue)
            {
                var left = s.NextRestart.Value - now;
                _tileNext.Text = left.TotalSeconds <= 0 ? "now" : Fmt.Clock(left);
                _tileNextSub.Text = "at " + s.NextRestart.Value.ToString("HH:mm") + " · every " + Fmt.Hours(cfg.TimedRestartHours);
            }
            else
            {
                _tileNext.Text = "–";
                _tileNextSub.Text = !cfg.TimedRestart ? "Scheduled restart off" : !s.Armed ? "Monitoring off" : "Game not active";
            }

            _tileRestarts.Text = s.Restarts.ToString();
            _tileCrashes.Text = (s.Crashes + s.Freezes).ToString();
            _tileCrashesSub.Text = s.Freezes > 0 ? s.Crashes + " crashes · " + s.Freezes + " freezes" : "since app start";
            _tileCrashes.Foreground = s.Crashes + s.Freezes > 0 ? Res("Bad") : Res("Text");

            // Actions
            _launchBtn.IsEnabled = s.Pid == 0 && s.Phase == Phase.Waiting;
            _restartBtn.IsEnabled = running;
            _hideBtn.IsEnabled = s.Pid != 0;
            _hideText.Text = s.Hidden ? "Show window" : "Hide window";
            _hideIcon.Text = s.Hidden ? "" : "";
            if (_restartConfirmUntil != DateTime.MinValue && now > _restartConfirmUntil)
            {
                _restartConfirmUntil = DateTime.MinValue;
                _restartText.Text = "Restart game";
            }

            // Sidebar
            _navDot.Fill = s.Armed ? (hung ? Res("Bad") : running ? Res("Good") : Res("Warn")) : Res("Idle");
            _navStatus.Text = s.Armed ? "Monitoring active" : "Monitoring off";
            _navSub.Text = s.Armed ? "for " + Fmt.Human(now - s.ArmedSince) : cfg.Hotkey ? "Hotkey: Ctrl+Alt+H" : "inactive";
        }

        void SetPulse(bool on, Brush color)
        {
            _halo.Fill = color;
            _dot.Fill = color;
            if (on == _pulsing) return;
            _pulsing = on;
            var st = (ScaleTransform)_halo.RenderTransform;
            if (on)
            {
                var dur = new Duration(TimeSpan.FromSeconds(1.8));
                var scale = new DoubleAnimation(0.4, 1.0, dur)
                {
                    RepeatBehavior = RepeatBehavior.Forever,
                    EasingFunction = new CubicEase { EasingMode = EasingMode.EaseOut },
                };
                var fade = new DoubleAnimation(0.55, 0.0, dur) { RepeatBehavior = RepeatBehavior.Forever };
                Timeline.SetDesiredFrameRate(scale, 30);
                Timeline.SetDesiredFrameRate(fade, 30);
                st.BeginAnimation(ScaleTransform.ScaleXProperty, scale);
                st.BeginAnimation(ScaleTransform.ScaleYProperty, scale);
                _halo.BeginAnimation(UIElement.OpacityProperty, fade);
            }
            else
            {
                st.BeginAnimation(ScaleTransform.ScaleXProperty, null);
                st.BeginAnimation(ScaleTransform.ScaleYProperty, null);
                _halo.BeginAnimation(UIElement.OpacityProperty, null);
                _halo.Opacity = 0.14;
            }
        }

        // ================= Settings =================

        void WireSettings()
        {
            BindText("GamePath", x => x.GamePath, (x, v) => x.GamePath = v, UpdatePathCheck);
            BindText("ProcessName", x => x.ProcessName, (x, v) => x.ProcessName = v);
            E<Button>("BrowseButton").Click += (o, e) => Browse();
            UpdatePathCheck();

            BindChoice("RestartPolicy", new double[] { 0, 1, 2 }, v => Watchdog.PolicyText((int)v),
                       x => x.RestartPolicy, (x, v) => x.RestartPolicy = (int)v);
            BindSwitch("TimedRestart", x => x.TimedRestart, (x, v) => x.TimedRestart = v);
            BindChoice("TimedHours", new[] { 0.5, 1, 2, 3, 4, 6, 8, 12, 24 }, v => "every " + Fmt.Hours(v),
                       x => x.TimedRestartHours, (x, v) => x.TimedRestartHours = v);
            BindSwitch("FreezeDetection", x => x.FreezeDetection, (x, v) => x.FreezeDetection = v);
            BindChoice("FreezeSeconds", new double[] { 30, 60, 90, 120, 180, 300 }, v => "after " + Fmt.Seconds(v),
                       x => x.FreezeSeconds, (x, v) => x.FreezeSeconds = (int)v);
            BindSwitch("StartHidden", x => x.StartHidden, (x, v) => x.StartHidden = v);
            BindSwitch("LaunchOnArm", x => x.LaunchOnArm, (x, v) => x.LaunchOnArm = v);
            BindSwitch("Hotkey", x => x.Hotkey, (x, v) => x.Hotkey = v, UpdateHotkey);

            BindSwitch("StartWithWindows", x => x.StartWithWindows, (x, v) => x.StartWithWindows = v, () => _app.ApplyAutostart());
            BindSwitch("ArmOnLaunch", x => x.ArmOnLaunch, (x, v) => x.ArmOnLaunch = v);
            BindSwitch("CloseToTray", x => x.CloseToTray, (x, v) => x.CloseToTray = v);

            BindChoice("PollSeconds", new[] { 0.5, 1, 2, 5 }, v => "every " + Fmt.Seconds(v),
                       x => x.PollSeconds, (x, v) => x.PollSeconds = v);
            BindChoice("Cooldown", new double[] { 3, 5, 10, 20, 30, 60 }, v => Fmt.Seconds(v),
                       x => x.RestartCooldownSeconds, (x, v) => x.RestartCooldownSeconds = (int)v);
            BindChoice("MaxRestarts", new double[] { 3, 5, 10, 20, 0 }, v => v == 0 ? "Unlimited" : v + " per hour",
                       x => x.MaxRestartsPerHour, (x, v) => x.MaxRestartsPerHour = (int)v);
            E<Button>("OpenConfigButton").Click += (o, e) => RevealInExplorer(Settings.FilePath);
        }

        void RefreshEnables()
        {
            var s = Settings.Current;
            E<ComboBox>("TimedHours").IsEnabled = s.TimedRestart;
            E<ComboBox>("FreezeSeconds").IsEnabled = s.FreezeDetection;
            E<ComboBox>("HeartbeatHours").IsEnabled = s.NotifyHeartbeat;
        }

        void Browse()
        {
            var dlg = new OpenFileDialog
            {
                Title = "Select the game EXE",
                Filter = "Programs (*.exe)|*.exe|All files (*.*)|*.*",
            };
            try
            {
                string dir = System.IO.Path.GetDirectoryName(Settings.Current.GamePath);
                if (!string.IsNullOrEmpty(dir) && Directory.Exists(dir)) dlg.InitialDirectory = dir;
            }
            catch { }
            if (dlg.ShowDialog(_w) == true)
            {
                E<TextBox>("GamePath").Text = dlg.FileName;
                E<TextBox>("ProcessName").Text = System.IO.Path.GetFileName(dlg.FileName);
            }
        }

        void UpdatePathCheck()
        {
            var tb = E<TextBlock>("PathCheck");
            string p = Settings.Current.GamePath.Trim().Trim('"');
            if (p.Length == 0) SetHint(tb, "No game path set", "Warn");
            else if (p.Contains("://")) SetHint(tb, "Link – opened through Windows (e.g. Steam)", "Info");
            else if (File.Exists(p)) SetHint(tb, "✓  File found", "Good");
            else SetHint(tb, "✕  File not found", "Bad");
        }

        void SetHint(TextBlock tb, string text, string brush)
        {
            tb.Text = text;
            tb.Foreground = Res(brush);
        }

        // ================= Discord =================

        void WireDiscord()
        {
            BindText("WebhookUrl", x => x.WebhookUrl, (x, v) => x.WebhookUrl = v, UpdateWebhookHint);
            BindText("UserId", x => x.DiscordUserId, (x, v) => x.DiscordUserId = v);
            BindText("InstanceName", x => x.InstanceName, (x, v) => x.InstanceName = v);
            BindSwitch("PingOnlyOnProblems", x => x.PingOnlyOnProblems, (x, v) => x.PingOnlyOnProblems = v);
            BindSwitch("NotifyGameClosed", x => x.NotifyGameClosed, (x, v) => x.NotifyGameClosed = v);
            BindSwitch("NotifyFreeze", x => x.NotifyFreeze, (x, v) => x.NotifyFreeze = v);
            BindSwitch("NotifyRestart", x => x.NotifyRestart, (x, v) => x.NotifyRestart = v);
            BindSwitch("NotifyGameStarted", x => x.NotifyGameStarted, (x, v) => x.NotifyGameStarted = v);
            BindSwitch("NotifyWatchdog", x => x.NotifyWatchdog, (x, v) => x.NotifyWatchdog = v);
            BindSwitch("NotifyHideShow", x => x.NotifyHideShow, (x, v) => x.NotifyHideShow = v);
            BindSwitch("NotifyHeartbeat", x => x.NotifyHeartbeat, (x, v) => x.NotifyHeartbeat = v);
            BindChoice("HeartbeatHours", new double[] { 1, 2, 3, 6, 12, 24 }, v => "every " + Fmt.Hours(v),
                       x => x.HeartbeatHours, (x, v) => x.HeartbeatHours = v);
            E<Button>("TestButton").Click += (o, e) => SendTest();
            UpdateWebhookHint();
        }

        void UpdateWebhookHint()
        {
            var tb = E<TextBlock>("WebhookHint");
            string u = Settings.Current.WebhookUrl;
            if (u.Length == 0) SetHint(tb, "Without a URL, no notifications are sent.", "Muted");
            else if (WebhookRx.IsMatch(u)) SetHint(tb, "✓  Valid Discord webhook URL", "Good");
            else SetHint(tb, "This doesn't look like a Discord webhook URL.", "Warn");
        }

        void SendTest()
        {
            var result = E<TextBlock>("TestResult");
            var btn = E<Button>("TestButton");
            var cfg = Settings.Current;
            if (cfg.WebhookUrl.Length == 0) { SetHint(result, "Enter a webhook URL first.", "Warn"); return; }

            btn.IsEnabled = false;
            SetHint(result, "Sending …", "Muted");
            var snap = _wd.Snapshot;
            var embed = new Embed("🧪 Test message", Embed.Blurple, "The webhook works – notifications will show up here.", true)
                .Field("Game", snap.Pid != 0 ? "Running (PID " + snap.Pid + ")" : "Not running")
                .Field("Monitoring", snap.Armed ? "active" : "off");
            _discord.Send(cfg, embed, (ok, msg) => _w.Dispatcher.BeginInvoke(new Action(() =>
            {
                btn.IsEnabled = true;
                SetHint(result, ok ? "✓  Delivered – check your Discord channel" : "✕  " + msg, ok ? "Good" : "Bad");
            })));
        }

        // ================= Log =================

        void WireLog(ObservableCollection<LogEntry> log, ObservableCollection<LogEntry> recent)
        {
            E<ListBox>("LogList").ItemsSource = log;
            E<Button>("ClearLogButton").Click += (o, e) => { log.Clear(); recent.Clear(); };
            E<Button>("OpenLogButton").Click += (o, e) => RevealInExplorer(FileLog.FilePath);
        }

        static void RevealInExplorer(string file)
        {
            try
            {
                if (File.Exists(file)) Process.Start("explorer.exe", "/select,\"" + file + "\"");
                else Process.Start("explorer.exe", "\"" + System.IO.Path.GetDirectoryName(file) + "\"");
            }
            catch { }
        }

        // ================= Bindings =================

        void BindSwitch(string name, Func<Settings, bool> get, Action<Settings, bool> set, Action after = null)
        {
            var cb = E<CheckBox>(name);
            cb.IsChecked = get(Settings.Current);
            RoutedEventHandler h = (o, e) =>
            {
                bool v = cb.IsChecked == true;
                Settings.Mutate(x => set(x, v));
                if (after != null) after();
            };
            cb.Checked += h;
            cb.Unchecked += h;
        }

        void BindChoice(string name, double[] values, Func<double, string> label, Func<Settings, double> get, Action<Settings, double> set)
        {
            var cb = E<ComboBox>(name);
            var list = values.ToList();
            double cur = get(Settings.Current);
            int idx = list.FindIndex(v => Math.Abs(v - cur) < 1e-9);
            if (idx < 0) { list.Add(cur); idx = list.Count - 1; } // keep a custom value from the file
            foreach (var v in list) cb.Items.Add(label(v));
            cb.SelectedIndex = idx;
            cb.SelectionChanged += (o, e) =>
            {
                if (cb.SelectedIndex < 0) return;
                double v = list[cb.SelectedIndex];
                Settings.Mutate(x => set(x, v));
            };
        }

        void BindText(string name, Func<Settings, string> get, Action<Settings, string> set, Action after = null)
        {
            var tb = E<TextBox>(name);
            tb.Text = get(Settings.Current);
            tb.TextChanged += (o, e) =>
            {
                string v = tb.Text.Trim();
                Settings.Mutate(x => set(x, v));
                if (after != null) after();
            };
        }

        public void FlushSave()
        {
            _saveTimer.Stop();
            Settings.Current.Save();
        }

        // ================= Window, hotkey =================

        void OnSourceInitialized()
        {
            _hwnd = new WindowInteropHelper(_w).Handle;

            // Dark title bar (Win10/11); on Win11 it matches the background color exactly.
            int on = 1;
            if (Native.DwmSetWindowAttribute(_hwnd, 20, ref on, 4) != 0) Native.DwmSetWindowAttribute(_hwnd, 19, ref on, 4);
            int caption = 0x00140F0E, text = 0x00F5EEEC, border = 0x00312320; // COLORREF = 0x00BBGGRR
            Native.DwmSetWindowAttribute(_hwnd, 35, ref caption, 4);
            Native.DwmSetWindowAttribute(_hwnd, 36, ref text, 4);
            Native.DwmSetWindowAttribute(_hwnd, 34, ref border, 4);

            HwndSource.FromHwnd(_hwnd).AddHook(WndProc);
            UpdateHotkey();
        }

        IntPtr WndProc(IntPtr hwnd, int msg, IntPtr w, IntPtr l, ref bool handled)
        {
            if (msg == Native.WM_HOTKEY && w.ToInt32() == HotkeyId)
            {
                _wd.ToggleHidden();
                handled = true;
            }
            return IntPtr.Zero;
        }

        void UpdateHotkey()
        {
            if (_hwnd == IntPtr.Zero) return;
            bool want = Settings.Current.Hotkey && HotkeyAllowed;
            if (want == _hotkeyOn) return;
            if (want)
            {
                _hotkeyOn = Native.RegisterHotKey(_hwnd, HotkeyId, Native.MOD_CONTROL | Native.MOD_ALT | Native.MOD_NOREPEAT, 0x48 /* H */);
                if (!_hotkeyOn) _app.Log(Level.Warning, "Hotkey Ctrl+Alt+H is already used by another program");
            }
            else
            {
                Native.UnregisterHotKey(_hwnd, HotkeyId);
                _hotkeyOn = false;
            }
        }

        static ImageSource MakeWindowIcon()
        {
            using (var bmp = IconArt.Draw(64))
            using (var ms = new MemoryStream())
            {
                bmp.Save(ms, System.Drawing.Imaging.ImageFormat.Png);
                ms.Position = 0;
                return BitmapFrame.Create(ms, BitmapCreateOptions.None, BitmapCacheOption.OnLoad);
            }
        }

        /// <summary>Dev helper: renders every page to PNG (GW2Monitor.exe --render folder).</summary>
        public void RenderPages(string dir)
        {
            _noAnim = true;
            Directory.CreateDirectory(dir);
            foreach (var p in Pages)
            {
                E<RadioButton>("Nav" + p).IsChecked = true;
                ShowPage(p);
                E<FrameworkElement>("Page" + p).Opacity = 1;
                _w.UpdateLayout();
                var visual = (FrameworkElement)VisualTreeHelper.GetChild(_w, 0);
                int width = (int)Math.Ceiling(visual.ActualWidth), height = (int)Math.Ceiling(visual.ActualHeight);
                var rtb = new RenderTargetBitmap(width, height, 96, 96, PixelFormats.Pbgra32);
                rtb.Render(visual);
                var enc = new PngBitmapEncoder();
                enc.Frames.Add(BitmapFrame.Create(rtb));
                using (var f = File.Create(System.IO.Path.Combine(dir, p + ".png"))) enc.Save(f);
            }
            E<RadioButton>("NavDashboard").IsChecked = true;
            _noAnim = false;
        }
    }
}
