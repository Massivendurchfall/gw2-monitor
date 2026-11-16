using System;
using System.Drawing;
using System.Drawing.Drawing2D;
using System.Drawing.Imaging;

namespace GW2Monitor
{
    /// <summary>Draws the logo (gradient tile with a pulse line), optionally with a status dot for the tray.</summary>
    public static class IconArt
    {
        public static readonly Color Violet = Color.FromArgb(124, 92, 255);
        public static readonly Color Cyan = Color.FromArgb(34, 211, 238);
        public static readonly Color Dark = Color.FromArgb(14, 15, 20);

        public static Bitmap Draw(int size, Color? badge = null)
        {
            var bmp = new Bitmap(size, size, PixelFormat.Format32bppArgb);
            using (var g = Graphics.FromImage(bmp))
            {
                g.SmoothingMode = SmoothingMode.AntiAlias;
                g.PixelOffsetMode = PixelOffsetMode.HighQuality;
                g.Clear(Color.Transparent);

                float s = size;
                var rect = new RectangleF(s * 0.03f, s * 0.03f, s * 0.94f, s * 0.94f);
                using (var path = Rounded(rect, s * 0.26f))
                using (var brush = new LinearGradientBrush(rect, Violet, Cyan, LinearGradientMode.ForwardDiagonal))
                    g.FillPath(brush, path);

                PointF[] pts =
                {
                    P(s, 0.17f, 0.54f), P(s, 0.35f, 0.54f), P(s, 0.45f, 0.29f),
                    P(s, 0.57f, 0.75f), P(s, 0.66f, 0.47f), P(s, 0.83f, 0.47f),
                };
                using (var pen = new Pen(Color.White, Math.Max(1.6f, s * 0.095f)))
                {
                    pen.LineJoin = LineJoin.Round;
                    pen.StartCap = LineCap.Round;
                    pen.EndCap = LineCap.Round;
                    g.DrawLines(pen, pts);
                }

                if (badge.HasValue)
                {
                    float d = s * 0.46f;
                    var outer = new RectangleF(s - d, s - d, d, d);
                    using (var b = new SolidBrush(Dark)) g.FillEllipse(b, outer);
                    float inset = Math.Max(1.5f, s * 0.07f);
                    var inner = RectangleF.Inflate(outer, -inset, -inset);
                    using (var b = new SolidBrush(badge.Value)) g.FillEllipse(b, inner);
                }
            }
            return bmp;
        }

        static PointF P(float s, float x, float y) { return new PointF(s * x, s * y); }

        static GraphicsPath Rounded(RectangleF r, float radius)
        {
            float d = radius * 2;
            var p = new GraphicsPath();
            p.AddArc(r.X, r.Y, d, d, 180, 90);
            p.AddArc(r.Right - d, r.Y, d, d, 270, 90);
            p.AddArc(r.Right - d, r.Bottom - d, d, d, 0, 90);
            p.AddArc(r.X, r.Bottom - d, d, d, 90, 90);
            p.CloseFigure();
            return p;
        }
    }
}
