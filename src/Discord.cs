using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using System.Net;
using System.Net.Http;
using System.Text;
using System.Threading;
using System.Web.Script.Serialization;

namespace GW2Monitor
{
    /// <summary>One Discord message (sent as an embed).</summary>
    public sealed class Embed
    {
        public const int Green = 0x57F287, Red = 0xED4245, Yellow = 0xFEE75C, Blurple = 0x5865F2,
                         Cyan = 0x22D3EE, Grey = 0x95A5A6, Orange = 0xF0A030;

        public string Title = "";
        public string Description = "";
        public int Color = Blurple;
        /// <summary>Important event (crash, freeze, error) – pings even with "Ping only on problems".</summary>
        public bool Critical;
        public readonly List<KeyValuePair<string, string>> Fields = new List<KeyValuePair<string, string>>();

        public Embed(string title, int color, string description = "", bool critical = false)
        {
            Title = title; Color = color; Description = description; Critical = critical;
        }

        public Embed Field(string name, string value)
        {
            Fields.Add(new KeyValuePair<string, string>(name, value));
            return this;
        }
    }

    /// <summary>
    /// Sends webhooks through a queue on its own thread: order is preserved,
    /// rate limits (429) are respected and network errors are retried.
    /// </summary>
    public sealed class DiscordNotifier
    {
        sealed class Job { public string Url; public string Json; public Action<bool, string> Done; }

        static readonly HttpClient Http;
        readonly BlockingCollection<Job> _queue = new BlockingCollection<Job>(64);
        int _sent;

        public event Action<Level, string> Log;
        public int Sent { get { return _sent; } }
        public string LastStatus { get; private set; }

        static DiscordNotifier()
        {
            // Discord requires TLS 1.2+
            ServicePointManager.SecurityProtocol |= SecurityProtocolType.Tls12 | (SecurityProtocolType)12288 /* Tls13 */;
            Http = new HttpClient { Timeout = TimeSpan.FromSeconds(15) };
            Http.DefaultRequestHeaders.UserAgent.ParseAdd("GW2Monitor/2.0");
        }

        public DiscordNotifier()
        {
            LastStatus = "Nothing sent yet";
            new Thread(Worker) { IsBackground = true, Name = "Discord" }.Start();
        }

        public void Send(Settings s, Embed e, Action<bool, string> done = null)
        {
            string url = (s.WebhookUrl ?? "").Trim();
            if (url.Length == 0)
            {
                if (done != null) done(false, "No webhook URL set");
                return;
            }
            var job = new Job { Url = url, Json = BuildPayload(s, e), Done = done };
            if (!_queue.TryAdd(job))
            {
                Emit(Level.Warning, "Discord: queue full – message dropped");
                if (done != null) done(false, "Queue full");
            }
        }

        static string BuildPayload(Settings s, Embed e)
        {
            string uid = new string((s.DiscordUserId ?? "").Where(char.IsDigit).ToArray());
            bool ping = uid.Length >= 15 && (e.Critical || !s.PingOnlyOnProblems);
            string footer = "GW2 Monitor" + (string.IsNullOrWhiteSpace(s.InstanceName) ? "" : " · " + s.InstanceName.Trim());

            var embed = new Dictionary<string, object>
            {
                { "title", e.Title },
                { "color", e.Color },
                { "timestamp", DateTime.UtcNow.ToString("yyyy-MM-ddTHH:mm:ss.fffZ") },
                { "footer", new Dictionary<string, object> { { "text", footer } } },
            };
            if (!string.IsNullOrEmpty(e.Description)) embed["description"] = e.Description;
            if (e.Fields.Count > 0)
            {
                embed["fields"] = e.Fields.Select(f => new Dictionary<string, object>
                {
                    { "name", f.Key },
                    { "value", string.IsNullOrEmpty(f.Value) ? "–" : f.Value },
                    { "inline", true },
                }).ToList();
            }

            var payload = new Dictionary<string, object> { { "embeds", new object[] { embed } } };
            if (ping)
            {
                payload["content"] = "<@" + uid + ">";
                payload["allowed_mentions"] = new Dictionary<string, object> { { "users", new[] { uid } } };
            }
            else
            {
                payload["allowed_mentions"] = new Dictionary<string, object> { { "parse", new string[0] } };
            }
            return new JavaScriptSerializer().Serialize(payload);
        }

        void Worker()
        {
            foreach (var job in _queue.GetConsumingEnumerable())
            {
                bool ok = false;
                string status = "";
                for (int attempt = 1; attempt <= 4 && !ok; attempt++)
                {
                    try
                    {
                        using (var content = new StringContent(job.Json, Encoding.UTF8, "application/json"))
                        using (var resp = Http.PostAsync(job.Url, content).GetAwaiter().GetResult())
                        {
                            int code = (int)resp.StatusCode;
                            if (code >= 200 && code < 300) { ok = true; status = "Delivered"; break; }

                            string body = resp.Content.ReadAsStringAsync().GetAwaiter().GetResult();
                            if (code == 429)
                            {
                                status = "Rate limited by Discord";
                                Thread.Sleep(RetryAfterMs(body));
                                continue;
                            }
                            if (code >= 500)
                            {
                                status = "HTTP " + code + " – Discord server error";
                                Thread.Sleep(attempt * 2000);
                                continue;
                            }
                            status = code == 404 ? "HTTP 404 – webhook doesn't exist (check the URL)"
                                   : code == 401 || code == 403 ? "HTTP " + code + " – access denied"
                                   : code == 400 ? "HTTP 400 – Discord rejected the message"
                                   : "HTTP " + code;
                            break; // client error: retrying won't help
                        }
                    }
                    catch (Exception ex)
                    {
                        var inner = ex.InnerException ?? ex;
                        status = ex is System.Threading.Tasks.TaskCanceledException || inner is System.Threading.Tasks.TaskCanceledException
                            ? "Timed out"
                            : "No connection (" + (inner.InnerException ?? inner).Message + ")";
                        Thread.Sleep(attempt * 2000);
                    }
                }

                if (ok) Interlocked.Increment(ref _sent);
                else Emit(Level.Warning, "Discord: " + status);
                LastStatus = status;
                if (job.Done != null)
                {
                    try { job.Done(ok, status); } catch { }
                }
            }
        }

        static int RetryAfterMs(string body)
        {
            try
            {
                var d = new JavaScriptSerializer().DeserializeObject(body) as Dictionary<string, object>;
                object ra;
                if (d != null && d.TryGetValue("retry_after", out ra))
                    return (int)(Math.Max(0.5, Math.Min(30, Convert.ToDouble(ra))) * 1000);
            }
            catch { }
            return 2000;
        }

        void Emit(Level l, string m)
        {
            var h = Log;
            if (h != null) h(l, m);
        }
    }
}
