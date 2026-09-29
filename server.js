import http from "node:http";
import fs from "node:fs/promises";
import path from "node:path";
import crypto from "node:crypto";
import { WebSocketServer, WebSocket } from "ws";

/*
 * NAUTICA LOAD BALANCER — HOSTLESS.CLOUD PORT
 * --------------------------------------------
 * This is a runtime port of the Cloudflare Worker LB.
 *
 * Preserved:
 *   - backend list + admin editing
 *   - counter/time/random backend ordering
 *   - backend dead/failure cache
 *   - retry/failover
 *   - /sub dashboard
 *   - /admin panel
 *   - login/session/rate limiting
 *   - proxy-list cache
 *   - normal HTTP forwarding
 *   - WebSocket forwarding
 *
 * Changed only:
 *   Cloudflare Worker runtime -> Node.js HTTP + ws
 *   Cloudflare KV -> local JSON config file
 *   CF fetch cache -> in-memory cache
 *   Worker WebSocket pass-through -> explicit ws bridge
 */

const PORT = Number(process.env.PORT || 8080);
// Hostless container filesystem: use an explicit writable temp directory by default.
// If Hostless provides a persistent writable mount, set DATA_DIR to that path.
const DATA_DIR = process.env.DATA_DIR || "/tmp/nautica-lb-data";
const CONFIG_FILE = process.env.CONFIG_FILE || path.join(DATA_DIR, "config.json");

const WORKER_URLS = [
  "cf.bebas11.workers.dev",
  "cf.bebas9.workers.dev",
  "avaritia.elvinrakus.workers.dev",
  "urv-worker-cf.renaldisch.workers.dev",
  "cf.buatvpn.workers.dev",
  "cf.kebal1.workers.dev",
  "cf.osianne23.workers.dev",
  "wibu.wibucf6.workers.dev",
  "cf.yeyay736.workers.dev",
  "cf.andremith59.workers.dev",
  "fajar.masfajar0004.workers.dev",
  "cf.evintokes.workers.dev",
  "rizaxyz.uddyalsh4.workers.dev",
  "rizaxy.allieisozk96.workers.dev"
];

const PROXY_BANK_URL =
  process.env.PROXY_BANK_URL ||
  "https://raw.githubusercontent.com/papapapapdelesia/Emilia/refs/heads/main/Data/Country-ALIVE.txt";

const DONATE_LINK = process.env.DONATE_LINK || "";
const PROXY_PER_PAGE = 20;
const PORTS = [443, 80];
const PROTOCOLS = ["trojan", "vless", "ss"];

const DEFAULT_ADMIN_PASSWORD =
  process.env.DEFAULT_ADMIN_PASSWORD || "admin123";

const MEMORY_CACHE_TTL_MS = 5 * 60_000;
const CONFIG_CACHE_TTL_MS = 30_000;
const BACKEND_DEAD_TTL_MS = 60_000;
const BACKEND_FAILURE_THRESHOLD = 2;
const REQUEST_TIMEOUT_MS = 10_000;
const HEALTH_TIMEOUT_MS = 5_000;

const LOGIN_MAX_ATTEMPTS = 5;
const LOGIN_WINDOW_MS = 15 * 60_000;
const LOGIN_BLOCK_MS = 15 * 60_000;
const SESSION_TTL_SEC = 8 * 60 * 60;

let proxyMemory = { list: [], ts: 0 };
let configMemory = { value: null, ts: 0 };
let configLoaded = false;
let rrCounter = 0;

const backendState = new Map();
const loginAttempts = new Map();

function normalizeHost(value) {
  let s = String(value || "").trim().toLowerCase();
  s = s.replace(/^https?:\/\//, "").split("/")[0].split(":")[0];
  return /^[a-z0-9.-]+$/.test(s) ? s : "";
}

function normalizeBackendList(list) {
  if (!Array.isArray(list)) return [];
  const out = [];
  const seen = new Set();
  for (const raw of list) {
    const host = normalizeHost(raw);
    if (!host || seen.has(host)) continue;
    seen.add(host);
    out.push(host);
  }
  return out.slice(0, 100);
}

function validPort(p) {
  const n = Number(p);
  return Number.isInteger(n) && n >= 1 && n <= 65535;
}

function validIP(ip) {
  const s = String(ip || "").trim();
  if (/^\d{1,3}(\.\d{1,3}){3}$/.test(s)) {
    return s.split(".").every(x => Number(x) <= 255);
  }
  return /^[0-9a-fA-F:]+$/.test(s) && s.includes(":");
}

function escapeHTML(v) {
  return String(v ?? "").replace(/[&<>"']/g, c => ({
    "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;"
  }[c]));
}

function getFlagEmoji(iso) {
  iso = String(iso || "XX").trim().toUpperCase();
  if (!/^[A-Z]{2}$/.test(iso) || iso === "XX") return "🌐";
  return String.fromCodePoint(...iso.split("").map(c => 127397 + c.charCodeAt(0)));
}

function minifyHTML(s) {
  return s.replace(/<!--[\s\S]*?-->/g, "").replace(/>\s+</g, "><").trim();
}

function shuffle(a) {
  const x = [...a];
  for (let i = x.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [x[i], x[j]] = [x[j], x[i]];
  }
  return x;
}

function getOrderedBackends(backends, mode = "counter") {
  const list = [...backends];
  if (list.length < 2) return list;
  if (mode === "random") return shuffle(list);
  if (mode === "time") {
    const start = Math.floor(Date.now() / 10_000) % list.length;
    return [...list.slice(start), ...list.slice(0, start)];
  }
  const start = rrCounter++ % list.length;
  if (rrCounter > Number.MAX_SAFE_INTEGER - 1000) rrCounter = 0;
  return [...list.slice(start), ...list.slice(0, start)];
}

function getBackendInfo(host) {
  let s = backendState.get(host);
  if (!s) {
    s = { failures: 0, deadUntil: 0, lastOk: 0, lastFail: 0, latency: null };
    backendState.set(host, s);
  }
  return s;
}

function isBackendDead(host) {
  const s = getBackendInfo(host);
  if (s.deadUntil && Date.now() >= s.deadUntil) {
    s.deadUntil = 0;
    s.failures = 0;
  }
  return s.deadUntil > Date.now();
}

function markBackendFailure(host) {
  const s = getBackendInfo(host);
  s.failures++;
  s.lastFail = Date.now();
  if (s.failures >= BACKEND_FAILURE_THRESHOLD) {
    s.deadUntil = Date.now() + BACKEND_DEAD_TTL_MS;
  }
}

function markBackendOK(host, latency = null) {
  const s = getBackendInfo(host);
  s.failures = 0;
  s.deadUntil = 0;
  s.lastOk = Date.now();
  if (Number.isFinite(latency)) s.latency = latency;
}

function backendStats(host) {
  const s = getBackendInfo(host);
  return {
    host,
    alive: !isBackendDead(host),
    failures: s.failures,
    deadUntil: s.deadUntil || 0,
    lastOk: s.lastOk || 0,
    lastFail: s.lastFail || 0,
    latency: s.latency
  };
}

async function sha256(text) {
  return crypto.createHash("sha256").update(String(text)).digest("hex");
}

function constantTimeEqual(a, b) {
  a = String(a || "");
  b = String(b || "");
  if (a.length !== b.length) return false;
  return crypto.timingSafeEqual(Buffer.from(a), Buffer.from(b));
}

function b64urlEncode(s) {
  return Buffer.from(String(s)).toString("base64url");
}

function b64urlDecode(s) {
  try { return Buffer.from(String(s), "base64url").toString(); }
  catch { return ""; }
}

function hmacSHA256(secret, text) {
  return crypto.createHmac("sha256", String(secret)).update(String(text)).digest("hex");
}

function getClientIP(req) {
  return String(
    req.headers["x-real-ip"] ||
    String(req.headers["x-forwarded-for"] || "").split(",")[0].trim() ||
    req.socket.remoteAddress ||
    "unknown"
  );
}

function parseCookies(req) {
  const out = {};
  for (const part of String(req.headers.cookie || "").split(";")) {
    const i = part.indexOf("=");
    if (i < 0) continue;
    out[part.slice(0, i).trim()] = part.slice(i + 1).trim();
  }
  return out;
}

async function ensureDataDir() {
  try {
    await fs.mkdir(DATA_DIR, { recursive: true });
  } catch (err) {
    console.error(`[Nautica LB] Tidak dapat membuat DATA_DIR=${DATA_DIR}:`, err);
    throw new Error(`DATA_DIR tidak dapat ditulis: ${DATA_DIR} (${err.code || err.message})`);
  }
}

async function readConfig(force = false) {
  const now = Date.now();
  if (!force && configMemory.value && now - configMemory.ts < CONFIG_CACHE_TTL_MS) {
    return configMemory.value;
  }

  if (!configLoaded) {
    try {
      const raw = await fs.readFile(CONFIG_FILE, "utf8");
      const cfg = JSON.parse(raw);
      configMemory = { value: cfg && typeof cfg === "object" ? cfg : {}, ts: now };
    } catch {
      configMemory = { value: { backends: WORKER_URLS, mode: "counter" }, ts: now };
    }
    configLoaded = true;
  } else if (force) {
    try {
      const raw = await fs.readFile(CONFIG_FILE, "utf8");
      const cfg = JSON.parse(raw);
      configMemory = { value: cfg && typeof cfg === "object" ? cfg : {}, ts: now };
    } catch {}
  }

  return configMemory.value || { backends: WORKER_URLS, mode: "counter" };
}

async function writeConfig(patch) {
  await ensureDataDir();
  const current = await readConfig(true);
  const merged = { ...current, ...patch };

  if (patch.backends !== undefined) {
    merged.backends = normalizeBackendList(patch.backends);
    if (!merged.backends.length) throw new Error("Backend tidak boleh kosong.");
  }
  if (!["counter", "time", "random"].includes(merged.mode)) merged.mode = "counter";

  const tmp = `${CONFIG_FILE}.tmp`;
  await fs.writeFile(tmp, JSON.stringify(merged, null, 2), "utf8");
  await fs.rename(tmp, CONFIG_FILE);
  configMemory = { value: merged, ts: Date.now() };
  return merged;
}

async function getBackends() {
  const cfg = await readConfig();
  const list = normalizeBackendList(cfg.backends);
  return list.length ? list : WORKER_URLS;
}

async function getAdminPasswordHash() {
  const cfg = await readConfig();
  if (cfg.passwordHash) return String(cfg.passwordHash);
  return sha256(DEFAULT_ADMIN_PASSWORD);
}

function loginCheck(ip) {
  const now = Date.now();
  const r = loginAttempts.get(ip);
  if (!r) return { ok: true };
  if (r.blockedUntil > now) {
    return { ok: false, retryAfter: Math.ceil((r.blockedUntil - now) / 1000) };
  }
  if (now - r.first > LOGIN_WINDOW_MS) loginAttempts.delete(ip);
  return { ok: true };
}

function loginFail(ip) {
  const now = Date.now();
  let r = loginAttempts.get(ip);
  if (!r || now - r.first > LOGIN_WINDOW_MS) {
    r = { count: 0, first: now, blockedUntil: 0 };
  }
  r.count++;
  if (r.count >= LOGIN_MAX_ATTEMPTS) {
    r.blockedUntil = now + LOGIN_BLOCK_MS;
    r.count = 0;
    r.first = now;
  }
  loginAttempts.set(ip, r);
}

function loginSuccess(ip) {
  loginAttempts.delete(ip);
}

function createSession(ip) {
  const secret = String(
    process.env.SESSION_SECRET ||
    process.env.ADMIN_SESSION_SECRET ||
    process.env.ADMIN_SECRET ||
    DEFAULT_ADMIN_PASSWORD
  );
  const payload = `${Date.now() + SESSION_TTL_SEC * 1000}.${ip}`;
  const sig = hmacSHA256(secret, payload);
  return `${b64urlEncode(payload)}.${sig}`;
}

function verifySession(req) {
  const cookie = parseCookies(req).nautica_admin;
  if (!cookie) return false;
  const dot = cookie.lastIndexOf(".");
  if (dot < 1) return false;

  const payload = b64urlDecode(cookie.slice(0, dot));
  const sig = cookie.slice(dot + 1);
  const [exp, ip] = payload.split(".");
  if (!exp || !ip || Number(exp) < Date.now()) return false;
  if (ip !== getClientIP(req)) return false;

  const secret = String(
    process.env.SESSION_SECRET ||
    process.env.ADMIN_SESSION_SECRET ||
    process.env.ADMIN_SECRET ||
    DEFAULT_ADMIN_PASSWORD
  );
  const expected = hmacSHA256(secret, payload);
  return constantTimeEqual(sig, expected);
}

async function fetchWithTimeout(url, init = {}, timeoutMs = 10_000) {
  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), timeoutMs);
  try {
    return await fetch(url, { ...init, signal: controller.signal });
  } finally {
    clearTimeout(timer);
  }
}

async function fetchProxyListUpstream() {
  try {
    const res = await fetchWithTimeout(PROXY_BANK_URL, {
      headers: { "user-agent": "NauticaLB-Hostless/1.0" }
    }, 15_000);
    if (!res.ok) return null;

    const text = await res.text();
    const list = [];
    for (const line of text.split(/\r?\n/)) {
      const parts = line.split(",");
      const proxyIP = String(parts[0] || "").trim();
      const proxyPort = String(parts[1] || "").trim();
      const country = String(parts[2] || "XX").trim().toUpperCase();
      const org = String(parts.slice(3).join(",") || "Unknown Org").trim();

      if (!proxyIP || !validIP(proxyIP) || !validPort(proxyPort)) continue;
      list.push({
        proxyIP,
        proxyPort,
        country: /^[A-Z]{2}$/.test(country) ? country : "XX",
        org: org.slice(0, 120) || "Unknown Org"
      });
    }
    return list;
  } catch (e) {
    console.error("fetchProxyListUpstream:", e.message);
    return null;
  }
}

async function getProxyList() {
  const now = Date.now();
  if (proxyMemory.list.length && now - proxyMemory.ts < MEMORY_CACHE_TTL_MS) {
    return proxyMemory.list;
  }

  const fresh = await fetchProxyListUpstream();
  if (fresh?.length) {
    proxyMemory = { list: fresh, ts: now };
    return fresh;
  }
  return proxyMemory.list;
}

function buildSubscription(host, proxyList, page = 0) {
  page = Math.max(0, Number(page) || 0);
  const totalPages = Math.max(1, Math.ceil(proxyList.length / PROXY_PER_PAGE));
  if (page >= totalPages) page = totalPages - 1;

  const start = page * PROXY_PER_PAGE;
  const uuid = crypto.randomUUID();
  const groups = [];

  for (let i = start; i < Math.min(start + PROXY_PER_PAGE, proxyList.length); i++) {
    const p = proxyList[i];
    const configs = [];
    const routePath = `/${p.proxyIP}-${p.proxyPort}`;

    for (const port of PORTS) {
      for (const protocol of PROTOCOLS) {
        const uri = new URL(`${protocol}://${host}`);
        uri.port = String(port);
        uri.searchParams.set("type", "ws");
        uri.searchParams.set("host", host);
        uri.searchParams.set("path", routePath);
        uri.searchParams.set("security", port === 443 ? "tls" : "none");
        uri.searchParams.set("encryption", "none");
        uri.searchParams.set("sni", port === 80 && protocol === "vless" ? "" : host);

        if (protocol === "ss") {
          uri.username = Buffer.from(`none:${uuid}`).toString("base64");
          uri.searchParams.set(
            "plugin",
            `v2ray-plugin${port === 80 ? "" : ";tls"};mux=0;mode=websocket;path=${routePath};host=${host}`
          );
        } else {
          uri.username = uuid;
        }
        uri.hash = `${i + 1} ${getFlagEmoji(p.country)} ${p.org} WS ${port === 443 ? "TLS" : "NTLS"} [LB]`;
        configs.push(uri.toString());
      }
    }
    groups.push({ proxy: p, urls: configs });
  }

  const cards = groups.map((g, idx) => {
    const p = g.proxy;
    const buttons = g.urls.map((u, i) =>
      `<button class="protocol-btn" data-copy="${escapeHTML(u)}">${PROTOCOLS[i % 3].toUpperCase()} ${PORTS[Math.floor(i / 3)]}</button>`
    ).join("");
    return `<article class="proxy-card">
      <div class="card-top"><div class="country-id"><div class="flag">${getFlagEmoji(p.country)}</div>
      <div><small>${escapeHTML(p.country)}</small><strong>${escapeHTML(p.proxyIP)}</strong></div></div>
      <span class="health">READY</span></div>
      <div class="org">${escapeHTML(p.org)}</div>
      <div class="endpoint"><span>${escapeHTML(p.proxyIP)}</span><b>:${escapeHTML(p.proxyPort)}</b></div>
      <div class="protocol-label">COPY CONFIG</div>
      <div class="protocol-grid">${buttons}</div>
    </article>`;
  }).join("");

  const prev = page > 0
    ? `<a class="dock-btn" href="/sub/${page - 1}">Prev</a>`
    : `<button class="dock-btn" disabled>Prev</button>`;
  const next = page < totalPages - 1
    ? `<a class="dock-btn" href="/sub/${page + 1}">Next</a>`
    : `<button class="dock-btn" disabled>Next</button>`;

  return minifyHTML(`<!doctype html><html lang="id"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Nautica LB</title>
<style>
:root{--bg:#090a0f;--panel:rgba(23,19,31,.88);--text:#f1eff6;--muted:#8b8798;--line:rgba(220,214,235,.12);--cyan:#00f0ff;--green:#45f5a1}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--text);font-family:system-ui,sans-serif}
a,button{font:inherit}.app{min-height:100vh;padding:20px 20px 105px}.wrap{max-width:1440px;margin:auto}
.glass{background:var(--panel);border:1px solid var(--line);border-radius:10px;box-shadow:0 20px 60px rgba(0,0,0,.25)}
.top{padding:16px;display:flex;justify-content:space-between;gap:15px;align-items:center}.brand{display:flex;gap:12px;align-items:center}
.mark{width:42px;height:42px;display:grid;place-items:center;color:var(--cyan);border:1px solid rgba(0,240,255,.3);border-radius:7px}
.brand h1{font-size:15px;margin:0}.brand h1 span{color:var(--cyan)}.brand p{margin:5px 0 0;color:var(--muted);font-size:9px}
.chips{display:flex;gap:7px;flex-wrap:wrap}.chip{padding:8px 10px;border:1px solid var(--line);border-radius:5px;color:var(--muted);font-size:9px}
.heading{padding:28px 3px 17px}.heading p{color:var(--cyan);font-size:9px;letter-spacing:.15em}.heading h2{margin:0;font-size:28px}
.grid{display:grid;grid-template-columns:repeat(4,minmax(0,1fr));gap:14px}.proxy-card{padding:15px}.card-top{display:flex;justify-content:space-between;gap:8px}
.country-id{display:flex;align-items:center;gap:9px}.flag{font-size:25px}.country-id small{display:block;color:var(--muted);font-size:8px}
.country-id strong{display:block;margin-top:3px;font-size:12px}.health{padding:6px 8px;border-radius:4px;font-size:8px;color:var(--green);border:1px solid rgba(69,245,161,.25);background:rgba(69,245,161,.05)}
.org{min-height:38px;margin:14px 0;color:#c8c5ce;font-size:12px;overflow-wrap:anywhere}
.endpoint{display:flex;justify-content:space-between;gap:8px;padding:10px;border:1px solid rgba(255,255,255,.06);border-radius:5px;background:rgba(9,10,15,.6);font-size:9px}
.endpoint span{overflow:hidden;text-overflow:ellipsis;color:var(--muted)}.endpoint b{color:var(--cyan)}
.protocol-label{margin:13px 0 7px;color:#595563;font-size:8px;letter-spacing:.13em}.protocol-grid{display:grid;grid-template-columns:repeat(2,1fr);gap:7px}
.protocol-btn,.dock-btn{min-height:34px;padding:7px 8px;border:1px solid rgba(0,240,255,.2);border-radius:5px;background:rgba(0,240,255,.05);color:#8deaf0;cursor:pointer}
.protocol-btn:hover,.dock-btn:hover{transform:translateY(-1px);background:rgba(0,240,255,.1)}
.dock{position:fixed;z-index:20;left:50%;bottom:18px;transform:translateX(-50%);display:flex;gap:7px;padding:7px;background:rgba(13,13,20,.92);border:1px solid var(--line);border-radius:8px}
.dock-btn{text-decoration:none;color:var(--muted);font-size:9px}.dock-btn:disabled{opacity:.35}
@media(max-width:1180px){.grid{grid-template-columns:repeat(3,1fr)}}@media(max-width:900px){.grid{grid-template-columns:repeat(2,1fr)}}@media(max-width:680px){.app{padding:12px 12px 100px}.grid{grid-template-columns:1fr}.top{flex-direction:column;align-items:flex-start}.dock{max-width:calc(100% - 24px);overflow:auto}}
</style></head><body><main class="app"><div class="wrap">
<section class="top glass"><div class="brand"><div class="mark">NL</div><div><h1>Nautica <span>LB</span></h1><p>PROXY COMMAND CENTER</p></div></div>
<div class="chips"><span class="chip">TOTAL ${proxyList.length}</span><span class="chip">PAGE ${page + 1}/${totalPages}</span><span class="chip">HOST ${escapeHTML(host)}</span></div></section>
<section class="heading"><p>SUBSCRIPTION</p><h2>Proxy Pool</h2></section>
<section class="grid">${cards || '<div class="glass" style="padding:20px">Proxy list kosong.</div>'}</section>
</div></main><nav class="dock">${prev}${next}<button class="dock-btn" id="copyAll">COPY PAGE</button>
${DONATE_LINK ? `<a class="dock-btn" href="${escapeHTML(DONATE_LINK)}" target="_blank" rel="noreferrer">DONATE</a>` : ""}</nav>
<script>
const toast=t=>alert(t);
document.querySelectorAll('[data-copy]').forEach(b=>b.addEventListener('click',async()=>{try{await navigator.clipboard.writeText(b.dataset.copy);toast('Config copied')}catch{toast('Clipboard blocked')}}));
document.getElementById('copyAll')?.addEventListener('click',async()=>{const a=[...document.querySelectorAll('[data-copy]')].map(x=>x.dataset.copy).join('\\n');try{await navigator.clipboard.writeText(a);toast('All configs copied')}catch{toast('Clipboard blocked')}});
</script></body></html>`);
}

function sanitizeForwardHeaders(headers) {
  const skip = new Set([
    "host","connection","upgrade","content-length",
    "cf-connecting-ip","cf-ray","cf-visitor","cf-worker",
    "x-forwarded-host","x-forwarded-proto"
  ]);
  const out = {};
  for (const [k, v] of Object.entries(headers)) {
    if (!skip.has(k.toLowerCase())) out[k] = v;
  }
  return out;
}

async function readRequestBody(req) {
  const chunks = [];
  for await (const chunk of req) chunks.push(Buffer.from(chunk));
  return Buffer.concat(chunks);
}

async function forwardHTTP(req, res) {
  const backends = await getBackends();
  if (!backends.length) return sendText(res, 503, "No backend configured");

  const cfg = await readConfig();
  const mode = ["counter","time","random"].includes(cfg.mode) ? cfg.mode : "counter";
  const ordered = getOrderedBackends(backends, mode);
  const candidates = ordered.filter(h => !isBackendDead(h));
  const usable = candidates.length ? candidates : ordered;

  const incoming = new URL(req.url, `https://${req.headers.host || "localhost"}`);
  const body = req.method === "GET" || req.method === "HEAD" ? undefined : await readRequestBody(req);
  let lastError = null;

  for (const host of usable) {
    try {
      const target = new URL(incoming.toString());
      target.protocol = "https:";
      target.hostname = host;
      const headers = sanitizeForwardHeaders(req.headers);
      headers["x-forwarded-host"] = req.headers.host || "";
      headers["x-nautica-lb"] = "1";

      const started = Date.now();
      const upstream = await fetchWithTimeout(target.toString(), {
        method: req.method,
        headers,
        body,
        redirect: "manual"
      }, REQUEST_TIMEOUT_MS);

      const latency = Date.now() - started;
      if (upstream.status >= 500 || upstream.status === 429) {
        markBackendFailure(host);
        lastError = new Error(`${host}: HTTP ${upstream.status}`);
        continue;
      }

      markBackendOK(host, latency);
      const buf = Buffer.from(await upstream.arrayBuffer());
      const outHeaders = {};
      for (const [k,v] of upstream.headers) {
        if (!["connection","transfer-encoding"].includes(k.toLowerCase())) outHeaders[k] = v;
      }
      outHeaders["x-nautica-backend"] = host;
      outHeaders["x-nautica-latency"] = String(latency);
      res.writeHead(upstream.status, outHeaders);
      return res.end(buf);
    } catch (e) {
      markBackendFailure(host);
      lastError = e;
    }
  }

  console.error("All HTTP backends failed:", lastError?.message || lastError);
  return sendJSON(res, 503, { ok:false, error:"All backends unavailable", backends:usable.length });
}

function websocketHeaders(req, host) {
  const headers = {};
  for (const [k, v] of Object.entries(req.headers)) {
    const key = k.toLowerCase();
    if (["host","connection","upgrade","sec-websocket-key","sec-websocket-version","sec-websocket-extensions","content-length"].includes(key)) continue;
    headers[k] = v;
  }
  headers["x-forwarded-host"] = req.headers.host || "";
  headers["x-nautica-lb"] = "1";
  return headers;
}

async function proxyWebSocket(req, clientSocket, head) {
  const backends = await getBackends();
  if (!backends.length) return clientSocket.destroy();

  const cfg = await readConfig();
  const mode = ["counter","time","random"].includes(cfg.mode) ? cfg.mode : "counter";
  const ordered = getOrderedBackends(backends, mode);
  const candidates = ordered.filter(h => !isBackendDead(h));
  const usable = candidates.length ? candidates : ordered;

  const incoming = new URL(req.url, `https://${req.headers.host || "localhost"}`);

  for (const host of usable) {
    const target = new URL(incoming.toString());
    target.protocol = "wss:";
    target.hostname = host;

    const protocols = req.headers["sec-websocket-protocol"];
    const opts = {
      headers: websocketHeaders(req, host),
      perMessageDeflate: false,
      handshakeTimeout: REQUEST_TIMEOUT_MS
    };
    if (protocols) {
      opts.protocol = String(protocols).split(",")[0].trim();
    }

    const started = Date.now();
    const backend = new WebSocket(target.toString(), opts);

    let settled = false;
    const fail = () => {
      if (settled) return;
      settled = true;
      try { backend.terminate(); } catch {}
      markBackendFailure(host);
    };

    await new Promise(resolve => {
      const timer = setTimeout(() => { fail(); resolve(); }, REQUEST_TIMEOUT_MS);

      backend.once("open", () => {
        clearTimeout(timer);
        settled = true;
        markBackendOK(host, Date.now() - started);

        const wss = new WebSocketServer({ noServer: true });
        wss.handleUpgrade(req, clientSocket, head, client => {
          backend.on("message", (data, isBinary) => {
            if (client.readyState === WebSocket.OPEN) client.send(data, { binary: isBinary });
          });

          backend.on("close", (code, reason) => {
            if (client.readyState === WebSocket.OPEN) {
              // 1006 may be emitted by ws for an abnormal close, but it
              // MUST NOT be sent in a WebSocket close frame.
              const n = Number(code);
              const validCloseCode =
                Number.isInteger(n) &&
                ((n >= 1000 && n <= 1003) || (n >= 1007 && n <= 1014) || (n >= 3000 && n <= 4999));
              try {
                if (validCloseCode) client.close(n, reason);
                else client.terminate();
              } catch {
                try { client.terminate(); } catch {}
              }
            }
            try { wss.close(); } catch {}
          });

          backend.on("error", () => {
            if (client.readyState === WebSocket.OPEN) client.close(1011, "backend error");
          });

          client.on("message", (data, isBinary) => {
            if (backend.readyState === WebSocket.OPEN) backend.send(data, { binary: isBinary });
          });

          client.on("close", () => {
            try {
              if (backend.readyState === WebSocket.OPEN) backend.close(1000, "client closed");
              else if (backend.readyState === WebSocket.CONNECTING) backend.terminate();
            } catch {
              try { backend.terminate(); } catch {}
            }
            try { wss.close(); } catch {}
          });

          client.on("error", () => {
            try {
              if (backend.readyState === WebSocket.OPEN) backend.close(1011, "client error");
              else backend.terminate();
            } catch {
              try { backend.terminate(); } catch {}
            }
            try { wss.close(); } catch {}
          });
        });
        resolve(true);
      });

      backend.once("error", () => { clearTimeout(timer); fail(); resolve(false); });
    });

    if (settled && backend.readyState === WebSocket.OPEN) return;
  }

  try {
    clientSocket.write("HTTP/1.1 503 Service Unavailable\\r\\nConnection: close\\r\\nContent-Length: 19\\r\\n\\r\\nAll backends failed");
  } catch {}
  clientSocket.destroy();
}

async function checkBackend(host) {
  const started = Date.now();
  try {
    const r = await fetchWithTimeout(`https://${host}/`, {
      headers: { "user-agent": "NauticaLB-Health/1.0" }
    }, HEALTH_TIMEOUT_MS);
    const latency = Date.now() - started;
    if (r.status >= 500) {
      markBackendFailure(host);
      return { ...backendStats(host), ok:false, status:r.status, latency };
    }
    markBackendOK(host, latency);
    return { ...backendStats(host), ok:true, status:r.status, latency };
  } catch (e) {
    markBackendFailure(host);
    return { ...backendStats(host), ok:false, status:0, latency:Date.now()-started, error:e.message };
  }
}

function sendJSON(res, status, data, extra = {}) {
  const body = JSON.stringify(data);
  res.writeHead(status, {
    "content-type": "application/json; charset=utf-8",
    "cache-control": "no-store",
    ...extra
  });
  res.end(body);
}

function sendText(res, status, text) {
  res.writeHead(status, { "content-type": "text/plain; charset=utf-8", "cache-control": "no-store" });
  res.end(text);
}

function adminPage() {
  return `<!doctype html><html lang="id"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Nautica LB Admin</title>
<style>
*{box-sizing:border-box}body{margin:0;background:#090a0f;color:#eee;font-family:system-ui,sans-serif}
main{max-width:900px;margin:30px auto;padding:16px}.card{padding:20px;margin-bottom:14px;border:1px solid #292633;border-radius:10px;background:#121019}
h1{margin-top:0;color:#00f0ff}input,textarea,select,button{width:100%;padding:11px;border-radius:6px;border:1px solid #332f3d;background:#0b0b10;color:#eee;margin:5px 0 10px}
textarea{min-height:180px;font-family:monospace}.row{display:grid;grid-template-columns:1fr 1fr;gap:10px}.btn{cursor:pointer;background:#071d20;border-color:#00f0ff;color:#8deaf0}
.backend{padding:9px;border-bottom:1px solid #24212b;font:12px monospace;display:flex;justify-content:space-between;gap:10px}.ok{color:#45f5a1}.bad{color:#ff5678}
@media(max-width:650px){.row{grid-template-columns:1fr}}
</style></head><body><main>
<div class="card" id="login"><h1>Nautica LB</h1><p>Admin panel</p>
<input id="password" type="password" placeholder="Password"><button class="btn" id="loginBtn">LOGIN</button>
<p>Default password: admin123 — segera ganti.</p></div>
<div id="panel" style="display:none">
<div class="card"><h1>Backend Control</h1><p>Satu hostname per baris.</p>
<textarea id="backends"></textarea><div class="row">
<select id="mode"><option value="counter">Round Robin / Counter</option><option value="time">Time Rotation</option><option value="random">Random</option></select>
<button class="btn" id="save">SAVE CONFIG</button></div></div>
<div class="card"><h2>Ganti Password</h2>
<input id="newpass" type="password" placeholder="Password baru (min. 10 karakter)">
<button class="btn" id="changePass">CHANGE PASSWORD</button></div>
<div class="card"><h2>Backend Health</h2><button class="btn" id="health">CHECK ALL</button><div id="results"></div></div>
<div class="card"><button class="btn" id="logout">LOGOUT</button></div>
</div>
<script>
const $=id=>document.getElementById(id);
async function api(url,opt){const r=await fetch(url,opt);let d={};try{d=await r.json()}catch{}if(!r.ok)throw new Error(d.error||'Request failed');return d}
async function load(){const d=await api('/admin/api/config');$('backends').value=(d.backends||[]).join('\\n');$('mode').value=d.mode||'counter';$('login').style.display='none';$('panel').style.display='block'}
$('loginBtn').onclick=async()=>{try{await api('/admin/api/login',{method:'POST',headers:{'content-type':'application/json'},body:JSON.stringify({password:$('password').value})});await load()}catch(e){alert(e.message)}};
$('save').onclick=async()=>{try{const d=await api('/admin/api/config',{method:'PUT',headers:{'content-type':'application/json'},body:JSON.stringify({backends:$('backends').value.split(/\\r?\\n/).map(x=>x.trim()).filter(Boolean),mode:$('mode').value})});$('backends').value=d.backends.join('\\n');alert('Saved')}catch(e){alert(e.message)}};
$('changePass').onclick=async()=>{try{await api('/admin/api/password',{method:'POST',headers:{'content-type':'application/json'},body:JSON.stringify({password:$('newpass').value})});$('newpass').value='';alert('Password changed')}catch(e){alert(e.message)}};
$('health').onclick=async()=>{try{const d=await api('/admin/api/health');$('results').innerHTML=d.results.map(x=>'<div class="backend"><span>'+x.host+'</span><span class="'+(x.ok?'ok':'bad')+'">'+(x.ok?'OK '+x.status+' '+x.latency+'ms':'FAIL '+(x.error||x.status))+'</span></div>').join('')}catch(e){alert(e.message)}};
$('logout').onclick=async()=>{await fetch('/admin/api/logout',{method:'POST'});location.reload()};
load().catch(()=>{});
</script></main></body></html>`;
}

async function handleAdmin(req, res, url) {
  if (url.pathname === "/admin/api/login" && req.method === "POST") {
    const ip = getClientIP(req);
    const lim = loginCheck(ip);
    if (!lim.ok) return sendJSON(res, 429, { error:"Too many attempts", retryAfter:lim.retryAfter });

    let body = {};
    try { body = JSON.parse((await readRequestBody(req)).toString() || "{}"); } catch {}
    const expected = await getAdminPasswordHash();
    const suppliedHash = await sha256(String(body.password || ""));

    if (!constantTimeEqual(suppliedHash, expected)) {
      loginFail(ip);
      return sendJSON(res, 401, { error:"Invalid password" });
    }

    loginSuccess(ip);
    const token = createSession(ip);
    return sendJSON(res, 200, { ok:true }, {
      "set-cookie": `nautica_admin=${token}; Max-Age=${SESSION_TTL_SEC}; Path=/admin; HttpOnly; Secure; SameSite=Strict`
    });
  }

  if (url.pathname === "/admin/api/logout" && req.method === "POST") {
    return sendJSON(res, 200, { ok:true }, {
      "set-cookie": "nautica_admin=; Max-Age=0; Path=/admin; HttpOnly; Secure; SameSite=Strict"
    });
  }

  if (!verifySession(req)) return sendJSON(res, 401, { error:"Unauthorized" });

  if (url.pathname === "/admin/api/config" && req.method === "GET") {
    const cfg = await readConfig(true);
    const backends = normalizeBackendList(cfg.backends).length ? normalizeBackendList(cfg.backends) : WORKER_URLS;
    return sendJSON(res, 200, {
      backends,
      mode:["counter","time","random"].includes(cfg.mode) ? cfg.mode : "counter"
    });
  }

  if (url.pathname === "/admin/api/config" && req.method === "PUT") {
    let body;
    try { body = JSON.parse((await readRequestBody(req)).toString() || "{}"); }
    catch { return sendJSON(res, 400, { error:"Invalid JSON" }); }

    try {
      const merged = await writeConfig({ backends:body.backends, mode:body.mode });
      return sendJSON(res, 200, {
        ok:true,
        backends:normalizeBackendList(merged.backends),
        mode:merged.mode
      });
    } catch (e) {
      return sendJSON(res, 400, { error:e.message });
    }
  }

  if (url.pathname === "/admin/api/password" && req.method === "POST") {
    let body = {};
    try { body = JSON.parse((await readRequestBody(req)).toString() || "{}"); } catch {}
    const password = String(body.password || "");
    if (password.length < 10 || password.length > 200) {
      return sendJSON(res, 400, { error:"Password harus 10-200 karakter." });
    }
    const hash = await sha256(password);
    await writeConfig({ passwordHash:hash });
    const token = createSession(getClientIP(req));
    return sendJSON(res, 200, { ok:true }, {
      "set-cookie": `nautica_admin=${token}; Max-Age=${SESSION_TTL_SEC}; Path=/admin; HttpOnly; Secure; SameSite=Strict`
    });
  }

  if (url.pathname === "/admin/api/health" && req.method === "GET") {
    const hosts = await getBackends();
    return sendJSON(res, 200, { results: await Promise.all(hosts.map(checkBackend)) });
  }

  return sendJSON(res, 404, { error:"Not found" });
}

async function handleHTTP(req, res) {
  const url = new URL(req.url, `https://${req.headers.host || "localhost"}`);

  if (url.pathname === "/health") {
    const backends = await getBackends();
    return sendJSON(res, 200, {
      ok:true,
      service:"Nautica LB",
      runtime:"Hostless.cloud / Node.js",
      backends:backends.length,
      alive:backends.filter(h => !isBackendDead(h)).length,
      time:new Date().toISOString()
    });
  }

  if (url.pathname.startsWith("/admin/api/")) return handleAdmin(req, res, url);
  if (url.pathname === "/admin" || url.pathname === "/admin/") {
    return res.end(adminPage());
  }

  if (url.pathname === "/sub" || url.pathname.startsWith("/sub/")) {
    const pagePart = url.pathname.split("/")[2] || "0";
    const page = /^\d+$/.test(pagePart) ? Number(pagePart) : 0;
    const list = await getProxyList();
    const host = String(req.headers.host || "").split(":")[0];
    const result = buildSubscription(host, list, page);
    res.writeHead(200, {
      "content-type":"text/html; charset=utf-8",
      "cache-control":"public, max-age=120"
    });
    return res.end(result);
  }

  if (url.pathname === "/") {
    return res.end(`<!doctype html><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Nautica LB</title><body style="background:#090a0f;color:#eee;font:16px system-ui;padding:40px"><h1 style="color:#00f0ff">Nautica LB</h1><p>Load balancer is online.</p><p><a href="/sub" style="color:#8deaf0">/sub</a> · <a href="/admin" style="color:#8deaf0">/admin</a> · <a href="/health" style="color:#8deaf0">/health</a></p></body>`);
  }

  return forwardHTTP(req, res);
}

await ensureDataDir();
await readConfig();

const server = http.createServer((req, res) => {
  handleHTTP(req, res).catch(e => {
    console.error("HTTP:", e);
    if (!res.headersSent) sendJSON(res, 500, { ok:false, error:"Internal server error" });
    else res.destroy();
  });
});

server.on("upgrade", (req, socket, head) => {
  proxyWebSocket(req, socket, head).catch(e => {
    console.error("WebSocket:", e);
    try { socket.destroy(); } catch {}
  });
});

server.listen(PORT, "0.0.0.0", () => {
  console.log(`[Nautica LB Hostless] listening on 0.0.0.0:${PORT}`);
  console.log(`[Nautica LB Hostless] backends: ${WORKER_URLS.length}`);
});
