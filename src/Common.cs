using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Text;
using System.Windows.Media;

namespace GW2Monitor
{
    public enum Level { Info, Success, Warning, Error, Action }

    /// <summary>One log entry (bound directly to the UI).</summary>
    public sealed class LogEntry
    {
        static readonly Dictionary<Level, Brush> Colors = new Dictionary<Level, Brush>
        {
            { Level.Info,    Frozen(0x6B, 0x70, 0x85) },
            { Level.Success, Frozen(0x34, 0xD3, 0x99) },
            { Level.Warning, Frozen(0xFB, 0xBF, 0x24) },
            { Level.Error,   Frozen(0xF8, 0x71, 0x71) },
            { Level.Action,  Frozen(0x8B, 0x6F, 0xFF) },
        };

        static Brush Frozen(byte r, byte g, byte b)
        {
            var br = new SolidColorBrush(Color.FromRgb(r, g, b));
            br.Freeze();
            return br;
        }

        public LogEntry(Level level, string message)
        {
            Level = level;
            Message = message;
            Time = DateTime.Now.ToString("HH:mm:ss");
            Brush = Colors[level];
        }

        public Level Level { get; private set; }
        public string Message { get; private set; }
        public string Time { get; private set; }
        public Brush Brush { get; private set; }
    }

    /// <summary>Log file next to the EXE (rotated at 2 MB).</summary>
    static class FileLog
    {
        static readonly object Gate = new object();
        public static string FilePath { get; private set; }

        public static void Init(string dir)
        {
            FilePath = Path.Combine(dir, "GW2Monitor.log");
            try
            {
                var fi = new FileInfo(FilePath);
                if (fi.Exists && fi.Length > 2000000)
                {
                    File.Copy(FilePath, FilePath + ".old", true);
                    File.Delete(FilePath);
                }
            }
            catch { }
        }

        public static void Write(Level level, string message)
        {
            if (FilePath == null) return;
            lock (Gate)
            {
                try
                {
                    File.AppendAllText(FilePath,
                        string.Format("{0:yyyy-MM-dd HH:mm:ss}  {1,-7}  {2}\r\n", DateTime.Now, level.ToString().ToUpperInvariant(), message),
                        Encoding.UTF8);
                }
                catch { }
            }
        }
    }

    static class Fmt
    {
        static readonly CultureInfo Inv = CultureInfo.InvariantCulture;

        /// <summary>00:00:00 (hours keep counting past 24).</summary>
        public static string Clock(TimeSpan t)
        {
            if (t < TimeSpan.Zero) t = TimeSpan.Zero;
            return string.Format("{0:00}:{1:00}:{2:00}", (int)t.TotalHours, t.Minutes, t.Seconds);
        }

        /// <summary>Readable duration: "12 s", "5 min 3 s", "2 h 14 min", "1 d 3 h".</summary>
        public static string Human(TimeSpan t)
        {
            if (t < TimeSpan.Zero) t = TimeSpan.Zero;
            if (t.TotalSeconds < 60) return (int)t.TotalSeconds + " s";
            if (t.TotalMinutes < 60) return (int)t.TotalMinutes + " min " + t.Seconds + " s";
            if (t.TotalHours < 24) return (int)t.TotalHours + " h " + t.Minutes + " min";
            return (int)t.TotalDays + " d " + t.Hours + " h";
        }

        public static string Hours(double h)
        {
            if (h < 1) return (h * 60).ToString("0", Inv) + " min";
            return h.ToString("0.#", Inv) + " h";
        }

        public static string Seconds(double s)
        {
            if (s < 1) return s.ToString("0.##", Inv) + " s";
            if (s < 120) return s.ToString("0.#", Inv) + " s";
            return (s / 60).ToString("0.#", Inv) + " min";
        }

        public static string ExitCode(uint code)
        {
            string hex = code > 0xFFFF ? "0x" + code.ToString("X8") : code.ToString();
            string name;
            switch (code)
            {
                case 0: name = "normal"; break;
                case 1: name = "terminated"; break;
                case 0xC0000005: name = "access violation"; break;
                case 0xC0000409: name = "stack buffer overrun / fail-fast"; break;
                case 0xC00000FD: name = "stack overflow"; break;
                case 0xC0000374: name = "heap corruption"; break;
                case 0xC0000142: name = "DLL init failed"; break;
                case 0xC000013A: name = "aborted"; break;
                case 0x887A0005: name = "GPU device removed"; break;
                case 0x887A0006: name = "GPU hung"; break;
                default: name = null; break;
            }
            return name == null ? hex : hex + " (" + name + ")";
        }
    }
}
