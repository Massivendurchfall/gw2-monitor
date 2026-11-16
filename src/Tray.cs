using System;
using System.Drawing;
using WinForms = System.Windows.Forms;

namespace GW2Monitor
{
    /// <summary>Tray icon with status color and a dark context menu.</summary>
    sealed class Tray : IDisposable
    {
        public enum State { Off, Ok, Busy, Problem }

        readonly WinForms.NotifyIcon _icon;
        readonly WinForms.ToolStripMenuItem _watch, _hide, _restart;
        readonly Func<Snapshot> _snapshot;
        Icon _current;
        State? _state;

        public Tray(Func<Snapshot> snapshot, Action open, Action toggleWatch, Action toggleHide, Action restart, Action exit)
        {
            _snapshot = snapshot;

            var menu = new WinForms.ContextMenuStrip
            {
                Renderer = new WinForms.ToolStripProfessionalRenderer(new DarkColors()) { RoundedEdges = false },
                ShowImageMargin = false,
                BackColor = DarkColors.Bg,
                ForeColor = DarkColors.Fg,
                Font = new Font("Segoe UI", 9.5f),
                Padding = new WinForms.Padding(2, 4, 2, 4),
            };
            var openItem = Item("Open GW2 Monitor", open);
            openItem.Font = new Font(menu.Font, FontStyle.Bold);
            _watch = Item("Start monitoring", toggleWatch);
            _hide = Item("Hide game window", toggleHide);
            _restart = Item("Restart game", restart);
            menu.Items.Add(openItem);
            menu.Items.Add(new WinForms.ToolStripSeparator());
            menu.Items.Add(_watch);
            menu.Items.Add(_hide);
            menu.Items.Add(_restart);
            menu.Items.Add(new WinForms.ToolStripSeparator());
            menu.Items.Add(Item("Exit", exit));
            menu.Opening += (s, e) => UpdateMenu();

            _icon = new WinForms.NotifyIcon { ContextMenuStrip = menu, Text = "GW2 Monitor", Visible = true };
            _icon.MouseClick += (s, e) => { if (e.Button == WinForms.MouseButtons.Left) open(); };
            SetState(State.Off);
        }

        static WinForms.ToolStripMenuItem Item(string text, Action action)
        {
            var item = new WinForms.ToolStripMenuItem(text) { ForeColor = DarkColors.Fg, Padding = new WinForms.Padding(6, 3, 6, 3) };
            item.Click += (s, e) => action();
            return item;
        }

        void UpdateMenu()
        {
            var s = _snapshot();
            _watch.Text = s.Armed ? "Stop monitoring" : "Start monitoring";
            _hide.Text = s.Hidden ? "Show game window" : "Hide game window";
            _hide.Enabled = s.Pid != 0;
            _restart.Enabled = s.Pid != 0 && s.Phase == Phase.Running;
        }

        public void Update(State state, string tooltip)
        {
            SetState(state);
            if (tooltip.Length > 63) tooltip = tooltip.Substring(0, 62) + "…";
            if (_icon.Text != tooltip) _icon.Text = tooltip;
        }

        void SetState(State state)
        {
            if (_state == state) return;
            _state = state;
            Color badge = state == State.Ok ? Color.FromArgb(52, 211, 153)
                        : state == State.Busy ? Color.FromArgb(251, 191, 36)
                        : state == State.Problem ? Color.FromArgb(248, 113, 113)
                        : Color.FromArgb(107, 112, 133);
            int size = Math.Max(16, WinForms.SystemInformation.SmallIconSize.Width);
            using (var bmp = IconArt.Draw(size, badge))
            {
                IntPtr h = bmp.GetHicon();
                var next = Icon.FromHandle(h);
                var old = _current;
                _icon.Icon = next;
                _current = next;
                if (old != null) { Native.DestroyIcon(old.Handle); old.Dispose(); }
            }
        }

        public void Balloon(string title, string text, bool error)
        {
            _icon.ShowBalloonTip(5000, title, text, error ? WinForms.ToolTipIcon.Error : WinForms.ToolTipIcon.Info);
        }

        public void Dispose()
        {
            _icon.Visible = false;
            _icon.Dispose();
            if (_current != null) { Native.DestroyIcon(_current.Handle); _current.Dispose(); }
        }

        sealed class DarkColors : WinForms.ProfessionalColorTable
        {
            public static readonly Color Bg = Color.FromArgb(28, 30, 40);
            public static readonly Color Fg = Color.FromArgb(236, 238, 245);
            static readonly Color Hi = Color.FromArgb(46, 49, 66);
            static readonly Color Line = Color.FromArgb(54, 58, 77);

            public override Color ToolStripDropDownBackground { get { return Bg; } }
            public override Color ImageMarginGradientBegin { get { return Bg; } }
            public override Color ImageMarginGradientMiddle { get { return Bg; } }
            public override Color ImageMarginGradientEnd { get { return Bg; } }
            public override Color MenuBorder { get { return Line; } }
            public override Color MenuItemBorder { get { return Hi; } }
            public override Color MenuItemSelected { get { return Hi; } }
            public override Color MenuItemSelectedGradientBegin { get { return Hi; } }
            public override Color MenuItemSelectedGradientEnd { get { return Hi; } }
            public override Color SeparatorDark { get { return Line; } }
            public override Color SeparatorLight { get { return Bg; } }
        }
    }
}
