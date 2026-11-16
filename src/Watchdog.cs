using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Threading;

namespace GW2Monitor
{
    public enum Phase { Waiting, Launching, Running, Restarting }

    /// <summary>Immutable state for the UI (published by the watchdog thread).</summary>
    public sealed class Snapshot
    {
        public bool Armed;
        public DateTime ArmedSince;
        public Phase Phase;
        public int Pid;
        public DateTime GameStart;
        public bool Hidden;
        public DateTime? HungSince;
        public DateTime? NextRestart;
        public int Restarts, Crashes, Freezes;
        public string Reason = "";
        public int LaunchAttempt;
        public bool LimitedAccess;
    }

    /// <summary>
    /// Monitors the game on its own thread. All state belongs to that thread;
    /// the UI only posts commands (Post) and reads snapshots.
    ///
    /// Instead of scanning every process each second, once the game is found the watchdog
    /// waits directly on its process handle: crashes are detected instantly, including the exit code.
    /// </summary>
    public sealed class Watchdog
    {
        const double StableSeconds = 4;     // a process must live this long before it is adopted
        const double AnnounceSeconds = 15;  // only then does the game count as started (ignores launcher hand-offs)
        const double HungLogSeconds = 10;
        const int MaxLaunchAttempts = 3;
        const int GracefulCloseMs = 20000;

        enum CloseResult { Clean, Killed, Failed }
        sealed class Found { public int Pid; public DateTime? Start; }

        public event Action<Level, string> Log;
        public event Action<string, string> Alert;

        readonly DiscordNotifier _discord;
        readonly Thread _thread;
        readonly AutoResetEvent _wake = new AutoResetEvent(false);
        readonly ManualResetEvent _quit = new ManualResetEvent(false);
        readonly ConcurrentQueue<Action> _commands = new ConcurrentQueue<Action>();
        volatile Snapshot _snap = new Snapshot();

        // ---- state (watchdog thread only) ----
        Settings _cfg = Settings.Current;
        bool _armed;
        DateTime _armedSince, _nextHeartbeat;
        Phase _phase = Phase.Waiting;
        int _pid;
        ProcessWaitHandle _proc;
        DateTime _gameStart;
        bool _announced;
        bool _hidden, _autoHideLogged;
        readonly Dictionary<IntPtr, int> _hiddenWindows = new Dictionary<IntPtr, int>();
        DateTime? _hungSince;
        bool _hungLogged, _hungHandled;
        int _candidatePid;
        DateTime _candidateSeen;
        DateTime? _launchAt;
        DateTime _launchDeadline;
        int _launchAttempt;
        string _restartReason;
        int _restarts, _crashes, _freezes;
        readonly List<DateTime> _autoRestarts = new List<DateTime>();

        public Watchdog(DiscordNotifier discord)
        {
            _discord = discord;
            _thread = new Thread(Run) { IsBackground = true, Name = "Watchdog" };
            _thread.Start();
        }

        public Snapshot Snapshot { get { return _snap; } }

        // ================= Commands (thread-safe) =================

        public void SetArmed(bool on) { Post(() => DoSetArmed(on)); }
        public void ToggleHidden() { Post(() => DoSetHidden(!_hidden, true)); }
        public void LaunchGame() { Post(DoManualLaunch); }

        public void RestartGame()
        {
            Post(() =>
            {
                if (_pid != 0) DoRestart("Manual", false);
                else Emit(Level.Warning, "Game is not running – nothing to restart");
            });
        }

        public void Shutdown()
        {
            _quit.Set();
            _thread.Join(5000);
        }

        void Post(Action a)
        {
            _commands.Enqueue(a);
            _wake.Set();
        }

        // ================= Main loop =================

        void Run()
        {
            while (!_quit.WaitOne(0))
            {
                _cfg = Settings.Current;
                try
                {
                    Action cmd;
                    while (!_quit.WaitOne(0) && _commands.TryDequeue(out cmd)) cmd();
                    if (!_quit.WaitOne(0)) Step();
                }
                catch (Exception ex)
                {
                    Emit(Level.Error, "Internal error: " + ex.Message);
                    FileLog.Write(Level.Error, ex.ToString());
                }
                Publish();

                var handles = _proc != null
                    ? new WaitHandle[] { _wake, _quit, _proc }
                    : new WaitHandle[] { _wake, _quit };
                try { WaitHandle.WaitAny(handles, NextWaitMs()); }
                catch (ObjectDisposedException) { }
            }

            // Never leave an invisible game behind when exiting.
            try { RestoreWindows(false); } catch { }
            Detach();
        }

        void Step()
        {
            var now = DateTime.Now;

            if (_pid != 0)
            {
                uint code;
                bool known;
                if (HasExited(out code, out known)) OnExit(code, known);
                else RunningTick(now);
            }

            if (_pid == 0)
            {
                Detect(now);
                if (_pid == 0 && _phase == Phase.Launching && now >= _launchDeadline) OnLaunchTimeout();
            }

            Heartbeat(now);
        }

        int NextWaitMs()
        {
            int poll = (int)(_cfg.PollSeconds * 1000);
            if (_pid != 0)
                return _hidden && (DateTime.Now - _gameStart).TotalSeconds < 120 ? Math.Min(poll, 250) : poll;
            if (_candidatePid != 0 || _phase == Phase.Launching) return Math.Min(poll, 500);
            return poll;
        }

        // ================= Detection =================

        void Detect(DateTime now)
        {
            var found = FindGame(_cfg);
            if (found == null) { _candidatePid = 0; return; }

            if (found.Pid != _candidatePid) { _candidatePid = found.Pid; _candidateSeen = now; }
            if (_armed && _cfg.StartHidden && HideWindowsOf(found.Pid) > 0 && !_autoHideLogged) // don't even let it flash up
            {
                _autoHideLogged = true;
                Emit(Level.Action, "Game window hidden automatically");
            }

            DateTime start = found.Start ?? _candidateSeen;
            if ((now - start).TotalSeconds >= StableSeconds || (now - _candidateSeen).TotalSeconds >= StableSeconds)
                Attach(found.Pid, start);
        }

        static Found FindGame(Settings cfg)
        {
            string name = (cfg.ProcessName ?? "").Trim();
            if (name.EndsWith(".exe", StringComparison.OrdinalIgnoreCase)) name = name.Substring(0, name.Length - 4);
            if (name.Length == 0) return null;

            Process[] procs;
            try { procs = Process.GetProcessesByName(name); }
            catch { return null; }

            try
            {
                string want = NormalizePath(cfg.GamePath);
                Found best = null;
                bool bestMatch = false;
                foreach (var p in procs)
                {
                    int pid;
                    try { pid = p.Id; } catch { continue; }
                    var start = Native.StartTime(pid);
                    bool match = want != null && want == NormalizePath(Native.ImagePath(pid));
                    bool better = best == null
                        || (match && !bestMatch)
                        || (match == bestMatch && (start ?? DateTime.MinValue) > (best.Start ?? DateTime.MinValue));
                    if (better) { best = new Found { Pid = pid, Start = start }; bestMatch = match; }
                }
                return best;
            }
            finally
            {
                foreach (var p in procs) p.Dispose();
            }
        }

        static string NormalizePath(string p)
        {
            if (string.IsNullOrWhiteSpace(p)) return null;
            p = p.Trim().Trim('"');
            if (p.Contains("://")) return null;
            try { return Path.GetFullPath(p).ToLowerInvariant(); }
            catch { return p.ToLowerInvariant(); }
        }

        void Attach(int pid, DateTime start)
        {
            IntPtr h = Native.OpenProcess(Native.SYNCHRONIZE | Native.PROCESS_QUERY_LIMITED_INFORMATION | Native.PROCESS_TERMINATE, false, pid);
            if (h == IntPtr.Zero) h = Native.OpenProcess(Native.SYNCHRONIZE | Native.PROCESS_QUERY_LIMITED_INFORMATION, false, pid);
            _proc = h != IntPtr.Zero ? new ProcessWaitHandle(h) : null;

            _pid = pid;
            _gameStart = start;
            _candidatePid = 0;
            _announced = false;
            _hungSince = null;
            _hungLogged = _hungHandled = false;
            _hidden = _armed && _cfg.StartHidden;
            _phase = Phase.Running;

            Emit(Level.Info, "Game process found (PID " + pid + ")");
            if (_proc == null)
                Emit(Level.Warning, "No full access to the game (running as administrator?) – exit codes can't be read.");
        }

        void Detach()
        {
            if (_proc != null) { _proc.Dispose(); _proc = null; }
            _pid = 0;
            _announced = false;
            _hungSince = null;
            _hungLogged = _hungHandled = false;
            _hiddenWindows.Clear();
            _autoHideLogged = false;
        }

        bool HasExited(out uint code, out bool known)
        {
            code = 0;
            known = false;
            if (_proc != null)
            {
                if (!_proc.WaitOne(0)) return false;
                known = Native.GetExitCodeProcess(_proc.Raw, out code);
                return true;
            }
            return !PidAlive(_pid);
        }

        static bool PidAlive(int pid)
        {
            try { using (var p = Process.GetProcessById(pid)) return !p.HasExited; }
            catch (ArgumentException) { return false; }
            catch { return true; } // no access -> still running
        }

        // ================= Running game =================

        void RunningTick(DateTime now)
        {
            _phase = Phase.Running;

            if (_hidden && HideWindowsOf(_pid) > 0 && !_autoHideLogged)
            {
                _autoHideLogged = true;
                Emit(Level.Action, "Game window hidden automatically");
            }

            if (!_announced && (now - _gameStart).TotalSeconds >= AnnounceSeconds) Announce(now);

            // --- Freeze detection ---
            if (IsHung(_pid))
            {
                if (_hungSince == null) _hungSince = now;
                var hung = now - _hungSince.Value;
                if (!_hungLogged && hung.TotalSeconds >= HungLogSeconds)
                {
                    _hungLogged = true;
                    Emit(Level.Warning, "Game is not responding …");
                }
                if (_armed && _cfg.FreezeDetection && !_hungHandled && hung.TotalSeconds >= _cfg.FreezeSeconds)
                {
                    _hungHandled = true;
                    _freezes++;
                    bool allowed = RestartAllowed(now);
                    string action = allowed ? "Restart (forced)" : "None – restart limit reached";
                    Emit(Level.Error, "Game frozen for " + Fmt.Human(hung) + (allowed ? " – restarting" : " – " + LimitText()));
                    RaiseAlert("Game not responding", allowed ? "Restarting automatically." : "Restart limit reached.");
                    Notify(c => c.NotifyFreeze, new Embed("🧊 Game not responding", Embed.Red, "The game has frozen.", true)
                        .Field("Frozen for", Fmt.Human(hung))
                        .Field("Uptime", Fmt.Human(now - _gameStart))
                        .Field("Action", action));
                    if (allowed)
                    {
                        _autoRestarts.Add(now);
                        DoRestart("Freeze", true);
                        return;
                    }
                }
            }
            else if (_hungSince != null)
            {
                if (_hungLogged) Emit(Level.Success, "Game is responding again (after " + Fmt.Human(now - _hungSince.Value) + ")");
                _hungSince = null;
                _hungLogged = _hungHandled = false;
            }

            // --- Scheduled restart ---
            if (_armed && _cfg.TimedRestart && _hungSince == null && now >= NextTimedRestart())
                DoRestart("Scheduled", false);
        }

        DateTime NextTimedRestart()
        {
            var due = _gameStart.AddHours(_cfg.TimedRestartHours);
            var earliest = _armedSince.AddSeconds(30); // don't restart right after enabling monitoring
            return due < earliest ? earliest : due;
        }

        void Announce(DateTime now)
        {
            _announced = true;
            bool launchedByUs = _launchAt.HasValue;
            if (_restartReason != null)
            {
                Emit(Level.Success, "Restart complete (" + _restartReason + ")");
                Notify(c => c.NotifyRestart, new Embed("🔄 Restart complete", Embed.Green)
                    .Field("Reason", _restartReason)
                    .Field("PID", _pid.ToString())
                    .Field("Total restarts", _restarts.ToString()));
                _restartReason = null;
            }
            else
            {
                bool fresh = launchedByUs || (now - _gameStart).TotalMinutes < 2;
                Emit(Level.Success, fresh ? "Game started" : "Running game detected");
                Notify(c => c.NotifyGameStarted, new Embed(fresh ? "✅ Game started" : "✅ Game detected", Embed.Green,
                        fresh ? "" : "The game was already running and is now being monitored.")
                    .Field("PID", _pid.ToString())
                    .Field("Window", _hidden ? "hidden" : "visible"));
            }
            _launchAt = null;
            _launchAttempt = 0;
        }

        void OnExit(uint code, bool known)
        {
            var now = DateTime.Now;
            var uptime = now - _gameStart;
            bool announced = _announced;
            int pid = _pid;
            Detach();

            if (!announced)
            {
                // Very short-lived process: usually a hand-off to the EA app / Steam, which relaunches the game.
                Emit(Level.Info, "Game process " + pid + " exited after " + Fmt.Human(uptime) + " – probably a launcher hand-off, waiting …");
                _phase = _launchAt.HasValue ? Phase.Launching : Phase.Waiting;
                return;
            }

            _phase = Phase.Waiting;
            bool crash = !known || code != 0;
            string codeText = known ? Fmt.ExitCode(code) : "unknown";
            if (crash)
            {
                _crashes++;
                Emit(Level.Error, "Game crashed after " + Fmt.Human(uptime) + " (exit code " + codeText + ")");
            }
            else
            {
                Emit(Level.Warning, "Game was closed after " + Fmt.Human(uptime));
            }

            if (!_armed) return;

            bool wanted = _cfg.RestartPolicy == 2 || (_cfg.RestartPolicy == 1 && crash);
            bool allowed = wanted && RestartAllowed(now);
            string action = !wanted ? "No restart (setting)" : allowed ? "Restarting" : "None – restart limit reached";

            if (crash) RaiseAlert("Game crashed", action);
            Notify(c => c.NotifyGameClosed, crash
                ? new Embed("💥 Game crashed", Embed.Red, "", true)
                    .Field("Uptime", Fmt.Human(uptime)).Field("Exit code", codeText).Field("Action", action)
                : new Embed("⏹️ Game closed", Embed.Orange)
                    .Field("Uptime", Fmt.Human(uptime)).Field("Action", action));

            if (wanted && !allowed) Emit(Level.Error, LimitText());
            if (allowed)
            {
                _autoRestarts.Add(now);
                DoRestart(crash ? "Crash" : "Game closed", false);
            }
        }

        bool IsHung(int pid)
        {
            foreach (var h in Native.TopLevelWindows(pid))
                if ((Native.IsWindowVisible(h) || _hiddenWindows.ContainsKey(h)) && Native.IsHungAppWindow(h))
                    return true;
            return false;
        }

        bool RestartAllowed(DateTime now)
        {
            _autoRestarts.RemoveAll(t => (now - t).TotalHours >= 1);
            return _cfg.MaxRestartsPerHour <= 0 || _autoRestarts.Count < _cfg.MaxRestartsPerHour;
        }

        string LimitText()
        {
            return "Restart limit reached (" + _autoRestarts.Count + " automatic restarts in the last hour)";
        }

        // ================= Restart & launch =================

        void DoRestart(string reason, bool kill)
        {
            if (_phase == Phase.Restarting) return;
            var now = DateTime.Now;
            _phase = Phase.Restarting;
            _restartReason = reason;
            _restarts++;
            Emit(Level.Action, "Restart: " + reason);

            var embed = new Embed("🔄 Restarting game", Embed.Yellow).Field("Reason", reason);
            if (_pid != 0) embed.Field("Uptime", Fmt.Human(now - _gameStart));
            Notify(c => c.NotifyRestart, embed);
            Publish();

            if (_pid != 0)
            {
                var result = CloseGame(kill);
                if (_quit.WaitOne(0)) return;
                if (result == CloseResult.Failed)
                {
                    Emit(Level.Error, "Game could not be closed – restart aborted");
                    _phase = Phase.Running;
                    _restartReason = null;
                    return;
                }
                Emit(result == CloseResult.Clean ? Level.Info : Level.Warning,
                     result == CloseResult.Clean ? "Game closed cleanly" : "Game was force-closed");
                Detach();
            }

            if (_quit.WaitOne(_cfg.RestartCooldownSeconds * 1000)) return;
            _launchAttempt = 0;
            StartLaunch();
        }

        CloseResult CloseGame(bool kill)
        {
            if (!kill)
            {
                int posted = 0;
                foreach (var h in Native.TopLevelWindows(_pid))
                {
                    if (Native.IsWindowVisible(h) || _hiddenWindows.ContainsKey(h) || Native.GetWindowTextLength(h) > 0)
                    {
                        Native.PostMessage(h, Native.WM_CLOSE, IntPtr.Zero, IntPtr.Zero);
                        posted++;
                    }
                }
                if (posted > 0 && WaitForExit(GracefulCloseMs)) return CloseResult.Clean;
                if (_quit.WaitOne(0)) return CloseResult.Failed;
            }

            if (!(_proc != null && Native.TerminateProcess(_proc.Raw, 1)))
            {
                try { using (var p = Process.GetProcessById(_pid)) p.Kill(); } catch { }
            }
            return WaitForExit(8000) ? CloseResult.Killed : CloseResult.Failed;
        }

        bool WaitForExit(int ms)
        {
            if (_proc != null) return WaitHandle.WaitAny(new WaitHandle[] { _proc, _quit }, ms) == 0;
            var end = DateTime.Now.AddMilliseconds(ms);
            while (DateTime.Now < end)
            {
                if (!PidAlive(_pid)) return true;
                if (_quit.WaitOne(250)) return false;
            }
            return !PidAlive(_pid);
        }

        void DoManualLaunch()
        {
            if (_pid != 0 || FindGame(_cfg) != null) { Emit(Level.Warning, "Game is already running"); return; }
            if (_phase != Phase.Waiting) { Emit(Level.Warning, "Game is already starting"); return; }
            _restartReason = null;
            _launchAttempt = 0;
            StartLaunch();
        }

        bool StartLaunch()
        {
            string path = (_cfg.GamePath ?? "").Trim().Trim('"');
            _launchAttempt++;
            try
            {
                if (path.Length == 0) throw new InvalidOperationException("No game path set");
                bool isLink = path.Contains("://");
                if (!isLink && !File.Exists(path)) throw new FileNotFoundException("File not found: " + path);
                var psi = new ProcessStartInfo(path) { UseShellExecute = true };
                if (!isLink) psi.WorkingDirectory = Path.GetDirectoryName(path);
                using (Process.Start(psi)) { }
            }
            catch (Exception ex)
            {
                Emit(Level.Error, "Game launch failed: " + ex.Message);
                FailLaunch(ex.Message);
                return false;
            }

            _launchAt = DateTime.Now;
            _launchDeadline = _launchAt.Value.AddSeconds(_cfg.LaunchTimeoutSeconds);
            _phase = Phase.Launching;
            Emit(Level.Action, _launchAttempt > 1
                ? "Starting game (attempt " + _launchAttempt + "/" + MaxLaunchAttempts + ") …"
                : "Starting game …");
            return true;
        }

        void OnLaunchTimeout()
        {
            if (_armed && _launchAttempt < MaxLaunchAttempts)
            {
                Emit(Level.Warning, "Game didn't start within " + Fmt.Human(TimeSpan.FromSeconds(_cfg.LaunchTimeoutSeconds)) + " – retrying");
                StartLaunch();
                return;
            }
            Emit(Level.Error, "Game could not be started");
            FailLaunch("The game did not start after " + _launchAttempt + " attempt(s).");
        }

        void FailLaunch(string why)
        {
            string reason = _restartReason;
            _phase = Phase.Waiting;
            _launchAt = null;
            _launchAttempt = 0;
            _restartReason = null;
            RaiseAlert("Game launch failed", why);
            Notify(c => c.NotifyRestart || c.NotifyGameClosed, new Embed("❌ Game launch failed", Embed.Red, why, true)
                .Field("Trigger", reason ?? "Manual launch"));
        }

        // ================= Monitoring on/off, windows =================

        void DoSetArmed(bool on)
        {
            if (on == _armed) return;
            var now = DateTime.Now;
            if (on)
            {
                _armed = true;
                _armedSince = now;
                _nextHeartbeat = now.AddHours(_cfg.HeartbeatHours);
                Emit(Level.Success, "Monitoring started");
                Notify(c => c.NotifyWatchdog, new Embed("🟢 Monitoring started", Embed.Green)
                    .Field("Game", _pid != 0 ? "Running for " + Fmt.Human(now - _gameStart) : "Not running")
                    .Field("Restart on exit", PolicyText(_cfg.RestartPolicy))
                    .Field("Scheduled restart", _cfg.TimedRestart ? "every " + Fmt.Hours(_cfg.TimedRestartHours) : "off")
                    .Field("Freeze detection", _cfg.FreezeDetection ? "after " + Fmt.Seconds(_cfg.FreezeSeconds) : "off"));

                if (_pid != 0 && _cfg.StartHidden && !_hidden) DoSetHidden(true, false);
                if (_pid == 0 && _phase == Phase.Waiting && _cfg.LaunchOnArm && FindGame(_cfg) == null)
                {
                    _restartReason = null;
                    _launchAttempt = 0;
                    StartLaunch();
                }
            }
            else
            {
                Notify(c => c.NotifyWatchdog, new Embed("⚪ Monitoring stopped", Embed.Grey)
                    .Field("Monitored for", Fmt.Human(now - _armedSince))
                    .Field("Restarts", _restarts.ToString())
                    .Field("Crashes", (_crashes + _freezes).ToString()));
                _armed = false;
                Emit(Level.Info, "Monitoring stopped");
            }
        }

        void DoSetHidden(bool on, bool notify)
        {
            if (_pid == 0) { Emit(Level.Warning, "Game is not running – no window to " + (on ? "hide" : "show")); return; }
            if (on == _hidden) return;
            _hidden = on;
            if (on)
            {
                int n = HideWindowsOf(_pid);
                _autoHideLogged = true;
                Emit(Level.Action, n > 0 ? "Game window hidden" : "Game window will be hidden as soon as it appears");
            }
            else
            {
                RestoreWindows(true);
                Emit(Level.Action, "Game window visible again");
            }
            if (notify)
                Notify(c => c.NotifyHideShow, new Embed(on ? "🙈 Game window hidden" : "👁️ Game window shown", Embed.Cyan));
        }

        int HideWindowsOf(int pid)
        {
            int n = 0;
            foreach (var h in Native.TopLevelWindows(pid))
            {
                if (!Native.IsWindowVisible(h)) continue;
                Native.ShowWindowAsync(h, Native.SW_HIDE);
                _hiddenWindows[h] = pid;
                n++;
            }
            return n;
        }

        void RestoreWindows(bool focus)
        {
            IntPtr first = IntPtr.Zero;
            foreach (var kv in _hiddenWindows)
            {
                if (!Native.IsWindow(kv.Key) || Native.WindowPid(kv.Key) != kv.Value) continue;
                Native.ShowWindowAsync(kv.Key, Native.SW_SHOW);
                if (first == IntPtr.Zero) first = kv.Key;
            }
            _hiddenWindows.Clear();
            if (focus && first != IntPtr.Zero) Native.SetForegroundWindow(first);
        }

        // ================= Status report, notifications =================

        void Heartbeat(DateTime now)
        {
            if (!_armed || !_cfg.NotifyHeartbeat || now < _nextHeartbeat) return;
            _nextHeartbeat = now.AddHours(_cfg.HeartbeatHours);
            Notify(c => true, new Embed("💓 Status report", Embed.Blurple)
                .Field("Game", _pid != 0 ? "Running for " + Fmt.Human(now - _gameStart) : "Not running")
                .Field("Monitored for", Fmt.Human(now - _armedSince))
                .Field("Window", _pid != 0 ? (_hidden ? "hidden" : "visible") : "–")
                .Field("Restarts", _restarts.ToString())
                .Field("Crashes", _crashes.ToString())
                .Field("Freezes", _freezes.ToString()));
        }

        void Notify(Func<Settings, bool> enabled, Embed e)
        {
            var cfg = _cfg;
            if (!_armed || !enabled(cfg) || string.IsNullOrWhiteSpace(cfg.WebhookUrl)) return;
            _discord.Send(cfg, e);
        }

        public static string PolicyText(int p)
        {
            return p == 0 ? "Never" : p == 1 ? "Only on crash" : "Always";
        }

        void Publish()
        {
            bool running = _pid != 0 && _phase == Phase.Running;
            _snap = new Snapshot
            {
                Armed = _armed,
                ArmedSince = _armedSince,
                Phase = _phase,
                Pid = _pid,
                GameStart = _gameStart,
                Hidden = _pid != 0 && _hidden,
                HungSince = _hungSince,
                NextRestart = _armed && _cfg.TimedRestart && running ? NextTimedRestart() : (DateTime?)null,
                Restarts = _restarts,
                Crashes = _crashes,
                Freezes = _freezes,
                Reason = _restartReason ?? "",
                LaunchAttempt = _launchAttempt,
                LimitedAccess = _pid != 0 && _proc == null,
            };
        }

        void Emit(Level l, string m)
        {
            var h = Log;
            if (h != null) h(l, m);
        }

        void RaiseAlert(string title, string text)
        {
            var h = Alert;
            if (h != null) h(title, text);
        }
    }
}
