# -*- coding: utf-8 -*-
"""
EVE Canary — der Kanarienvogel im Bergwerk. Liest die lokalen EVE-Logs (EULA-konform, reine
Textdateien, jede Client-Sprache) und zeigt Mining, Schaden, ISK, Effizienz,
Spielzeit und Sicherheits-Alarme (Spieler-Angriff, Asteroid leer) live +
historisch im Browser. Alles lokal, SQLite-Historie, Backups.

Start:  python eve_dashboard.py   ->  http://localhost:8765
"""
import json
import os
import re
import shutil
import sqlite3
import sys
import threading
import time
import urllib.request

VERSION = "1.1.0"
UPDATE_FILES = ["eve_dashboard.py", "ore_types.json", "npc_names.json",
                "mining_tools.json", "README_INSTALL.md"]
from collections import deque
from datetime import datetime, timezone, timedelta
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

APP_DIR = Path(__file__).parent
DB_PATH = APP_DIR / "dashboard.db"
CONFIG_PATH = APP_DIR / "config.json"
BACKUP_DIR = APP_DIR / "backups"


def load_json(name, default):
    p = APP_DIR / name
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        return default


ORE_TYPES = load_json("ore_types.json", {})
NPC_NAMES = set(load_json("npc_names.json", []))
MINING_TOOLS = sorted(load_json("mining_tools.json", []), key=len, reverse=True)

REGIONS = {"10000002": "Jita", "10000043": "Amarr", "10000030": "Rens",
           "10000032": "Dodixie", "10000042": "Hek"}
PRICE_REFRESH = 900
PORT_DEFAULT = 8765

TS_RE = re.compile(r"^\[ (\d{4})\.(\d{2})\.(\d{2}) (\d{2}):(\d{2}):(\d{2}) \] \((\w+)\) (.*)$")
HINT_RE = re.compile(r'hint="([^"]+)"')
STRIP_RE = re.compile(r"<[^>]+>")
NUM_RE = re.compile(r"([\d][\d.,   ]*)")
CHAR_FILE_RE = re.compile(r"^\d{8}_\d{6}_(\d+)\.txt$")
CHAT_LINE_RE = re.compile(r"^\[ [\d. :]+ \] ([^>]+?) > (.*)$")
OUT_COLOR = "0xff00ffff"
IN_COLOR = "0xffcc0000"
# Sprachabhängige Signale (DE/EN) — für weitere Sprachen hier ergänzen
CARGO_FULL_TEXTS = ["Frachtraum des Schiffs ist voll", "cargo hold is full",
                    "cargohold is full"]
DRONE_UNLOAD_TEXTS = ["Bergbaudrohnen müssen ihre aktuellen Erzladungen verladen",
                      "mining drones must unload"]
UNDOCK_TEXTS = ["Abdocken", "Undocking"]      # (None)-Zeile beim Abdocken
TRADE_TEXTS = ["Handel mit", "Trade with"]    # Handel abgeschlossen -> Laderaum unklar


def num(s):
    return int(re.sub(r"[.,   ]", "", s) or 0)


def parse_line(raw):
    """Gamelog-Zeile -> Event-Dict oder None. Nur sprachunabhängige Signale."""
    m = TS_RE.match(raw.strip())
    if not m:
        return None
    y, mo, d, h, mi, s, tag, body = m.groups()
    ts = datetime(int(y), int(mo), int(d), int(h), int(mi), int(s),
                  tzinfo=timezone.utc).timestamp()
    day = f"{y}-{mo}-{d}"
    base = {"ts": ts, "day": day}
    if tag == "mining":
        hint = HINT_RE.search(body)
        n = NUM_RE.search(STRIP_RE.sub("", body))
        if hint and n:
            return {**base, "kind": "ore", "key": hint.group(1), "value": num(n.group(1))}
    elif tag == "combat":
        low = body.lower()
        direction = "dmg_out" if OUT_COLOR in low else ("dmg_in" if IN_COLOR in low else None)
        if direction:
            n = NUM_RE.search(STRIP_RE.sub("", body))
            hints = HINT_RE.findall(body)
            if n:
                ev = {**base, "kind": direction,
                      "key": hints[0] if hints else "?", "value": num(n.group(1))}
                if direction == "dmg_out" and len(hints) > 1:
                    ev["weapon"] = hints[1]
                return ev
    elif tag == "bounty":
        n = NUM_RE.search(STRIP_RE.sub("", body))
        if n:
            return {**base, "kind": "bounty", "key": "", "value": num(n.group(1))}
    elif tag == "notify":
        text = STRIP_RE.sub("", body).strip()
        hints = HINT_RE.findall(body)
        comp = next((h for h in hints if h.startswith("Compressed")), None)
        if comp:
            n = NUM_RE.search(text)
            if n:
                raw_ore = next((h for h in hints if not h.startswith("Compressed")), None)
                return {**base, "kind": "compressed", "key": comp,
                        "raw": raw_ore, "value": num(n.group(1))}
        if any(t in text for t in TRADE_TEXTS):
            return {**base, "kind": "hold_reset", "key": "trade", "value": 1}
        for tool in MINING_TOOLS:
            # Modulnamen sind nie lokalisiert: "Strip Miner I* schaltet ab, …"
            if text.startswith(tool):
                return {**base, "kind": "depleted", "key": tool, "value": 1}
        if hints == ["Asteroid"]:
            # Modul versucht Zyklus auf zerstörtem/ungültigem Ziel — Asteroid weg
            return {**base, "kind": "depleted", "key": "Ziel verloren", "value": 1}
        if (len(hints) == 1 and hints[0] in ORE_TYPES
                and not hints[0].startswith("Compressed")
                and not any(ch.isdigit() for ch in text)):
            # "Drohnen greifen <Erz> an" (ohne Zahlen — Distanz-Fehler haben immer km-Angaben):
            # Mining-Drohnen wurden neu angesetzt -> Drohnen-Warnung aufheben
            return {**base, "kind": "drone_engage", "key": hints[0], "value": 1}
        if any(t in text for t in CARGO_FULL_TEXTS):
            return {**base, "kind": "cargo", "key": "", "value": 1}
        if any(t in text for t in DRONE_UNLOAD_TEXTS):
            return {**base, "kind": "drone_idle", "key": "", "value": 1}
        return None
    elif tag == "None":
        text = STRIP_RE.sub("", body)
        if any(t in text for t in UNDOCK_TEXTS):
            return {**base, "kind": "hold_reset", "key": "dock", "value": 1}
        return None
    return None


def read_char_name(file):
    try:
        with open(file, encoding="utf-8-sig", errors="replace") as f:
            for _ in range(6):
                line = f.readline()
                if ":" in line and "---" not in line:
                    return line.split(":", 1)[1].strip()
    except OSError:
        pass
    return file.stem


def find_log_dir():
    for d in [Path.home() / "Documents", Path.home() / "OneDrive" / "Documents",
              Path.home() / "OneDrive" / "Dokumente", Path.home() / "Dokumente"]:
        p = d / "EVE" / "logs" / "Gamelogs"
        if p.exists():
            return p
    return None


def load_config():
    cfg = {"port": PORT_DEFAULT, "region": "10000002", "log_dir": None,
           "mode": "all", "install_ts": time.time(),
           "goal": None, "watchlist": [], "idle_warn": 240,
           "update_url": "https://raw.githubusercontent.com/Eve-Online-Askend/eve-canary/main"}
    if CONFIG_PATH.exists():
        try:
            cfg.update(json.loads(CONFIG_PATH.read_text(encoding="utf-8")))
        except Exception:
            pass
    if not cfg.get("log_dir"):
        d = find_log_dir()
        cfg["log_dir"] = str(d) if d else ""
    save_config(cfg)
    return cfg


def save_config(cfg=None):
    CONFIG_PATH.write_text(json.dumps(cfg or CONFIG, indent=1, ensure_ascii=False),
                           encoding="utf-8")


CONFIG = load_config()

# ---------------------------------------------------------------- Datenbank
DB_LOCK = threading.Lock()
DB = sqlite3.connect(DB_PATH, check_same_thread=False)
DB.executescript("""
CREATE TABLE IF NOT EXISTS meta(key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE IF NOT EXISTS files(name TEXT PRIMARY KEY, char_id TEXT, char_name TEXT,
    offset INTEGER DEFAULT 0, skipped INTEGER DEFAULT 0,
    first_ts REAL, last_ts REAL);
CREATE TABLE IF NOT EXISTS daily(day TEXT, char_id TEXT, char_name TEXT, kind TEXT,
    key TEXT, value REAL, PRIMARY KEY(day, char_id, kind, key));
CREATE TABLE IF NOT EXISTS baseline_offsets(day TEXT, char_id TEXT, kind TEXT,
    key TEXT, value REAL, PRIMARY KEY(day, char_id, kind, key));
""")
DB.commit()


def meta_get(key, default=None):
    r = DB.execute("SELECT value FROM meta WHERE key=?", (key,)).fetchone()
    return r[0] if r else default


def db_add(day, char_id, char_name, kind, key, value):
    DB.execute("""INSERT INTO daily VALUES(?,?,?,?,?,?)
                  ON CONFLICT(day,char_id,kind,key)
                  DO UPDATE SET value=value+excluded.value, char_name=excluded.char_name""",
               (day, char_id, char_name, kind, key, value))


def do_backup():
    BACKUP_DIR.mkdir(exist_ok=True)
    name = f"dashboard_{datetime.now().strftime('%Y%m%d_%H%M%S')}.db"
    with DB_LOCK:
        DB.commit()
        shutil.copy2(DB_PATH, BACKUP_DIR / name)
    for f in sorted(BACKUP_DIR.glob("dashboard_*.db"))[:-10]:
        f.unlink(missing_ok=True)
    return name


def do_reset_baseline():
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    with DB_LOCK:
        DB.execute("DELETE FROM baseline_offsets")
        DB.execute("""INSERT INTO baseline_offsets
                      SELECT day, char_id, kind, key, value FROM daily WHERE day=?""", (today,))
        DB.execute("INSERT OR REPLACE INTO meta VALUES('baseline_day',?)", (today,))
        DB.execute("INSERT OR REPLACE INTO meta VALUES('baseline_ts',?)", (str(time.time()),))
        DB.commit()


def clear_baseline():
    with DB_LOCK:
        DB.execute("DELETE FROM baseline_offsets")
        DB.execute("DELETE FROM meta WHERE key IN ('baseline_day','baseline_ts')")
        DB.commit()


# ---------------------------------------------------------------- Update
def fetch_url(url, timeout=15):
    with urllib.request.urlopen(url, timeout=timeout) as r:
        return r.read()


def check_update():
    base = (CONFIG.get("update_url") or "").rstrip("/")
    if not base.startswith("https://"):
        return {"ok": False, "error": "Keine Update-Quelle konfiguriert (Optionen -> update_url)."}
    try:
        info = json.loads(fetch_url(f"{base}/version.json").decode("utf-8"))
        latest = str(info.get("version", "?"))
        return {"ok": True, "current": VERSION, "latest": latest,
                "available": latest != VERSION,
                "files": info.get("files", UPDATE_FILES)}
    except Exception as e:
        return {"ok": False, "error": f"Update-Server nicht erreichbar: {e}"}


def do_update():
    chk = check_update()
    if not chk.get("ok"):
        return chk
    if not chk.get("available"):
        return {"ok": True, "updated": False, "message": "Bereits aktuell."}
    base = CONFIG["update_url"].rstrip("/")
    try:
        blobs = {}
        for name in chk["files"]:
            if name not in UPDATE_FILES:
                continue  # nur bekannte Dateien, keine fremden Pfade
            blobs[name] = fetch_url(f"{base}/{name}", timeout=30)
        if "eve_dashboard.py" in blobs:
            compile(blobs["eve_dashboard.py"].decode("utf-8"), "eve_dashboard.py", "exec")
        for name, data in blobs.items():
            target = APP_DIR / name
            if target.exists():
                shutil.copy2(target, APP_DIR / (name + ".bak"))
            target.write_bytes(data)
    except SyntaxError:
        return {"ok": False, "error": "Neue Version fehlerhaft — Update abgebrochen, nichts geändert."}
    except Exception as e:
        return {"ok": False, "error": f"Download fehlgeschlagen: {e}"}
    threading.Timer(1.0, lambda: os.execv(sys.executable,
                                          [sys.executable, str(APP_DIR / "eve_dashboard.py")])).start()
    return {"ok": True, "updated": True,
            "message": f"Update auf {chk['latest']} installiert — Neustart läuft, Seite lädt gleich neu."}


# ---------------------------------------------------------------- Alarme
class Alerts:
    def __init__(self):
        self.items = deque(maxlen=50)
        self.next_id = 1
        self.lock = threading.Lock()

    def push(self, kind, char, text):
        with self.lock:
            self.items.append({"id": self.next_id, "ts": time.time(),
                               "kind": kind, "char": char, "text": text})
            self.next_id += 1

    def list(self):
        with self.lock:
            return list(self.items)[-20:]


alerts = Alerts()


# ---------------------------------------------------------------- Live-Session
class CharSession:
    def __init__(self, char_id, name, file):
        self.char_id, self.name, self.file = char_id, name, file
        self.start = time.time()
        self.first_ts = None
        self.trips = 0  # Anzahl Station-Stopps (Abdocken) in dieser Session
        self.mining = {}
        self.compressed = {}
        self.hold_raw = {}    # Laderaum-Schaetzung: unkomprimiertes Erz
        self.hold_comp = {}   # Laderaum-Schaetzung: komprimiertes Erz
        self.weapons = {}
        self.depleted = 0
        self.tool_off = {}    # Werkzeug -> [Anzahl, letzter ts] — verfaellt nach 240s
        self.cargo_full = False
        self.cargo_ts = 0
        self.last_ore_ts = None   # fuer Stillstand-Erkennung
        self.idle_alerted = False
        self.low_since = None     # Raten-Waechter (Teilausfall-Erkennung)
        self.low_alerted = False
        self.gaps = deque(maxlen=40)  # letzte Abstaende zwischen Erz-Events (lernt Drohnen-Zyklen)
        self.dmg_out = self.dmg_in = self.bounty = 0
        self.targets = {}
        self.attackers = {}
        self.win_out = deque()
        self.win_in = deque()
        self.rate_min = deque(maxlen=180)  # [Minute, {Erz: m3}] — fuer Sparkline + Raten-Waechter

    def feed(self, ev, live):
        now = time.time()
        if self.first_ts is None or ev["ts"] < self.first_ts:
            self.first_ts = ev["ts"]
        k = ev["kind"]
        if k == "ore":
            self.cargo_full = False
            if self.last_ore_ts:
                gap = ev["ts"] - self.last_ore_ts
                if 0 < gap < 900:
                    self.gaps.append(gap)
            self.last_ore_ts = ev["ts"]
            self.idle_alerted = False
            self.mining[ev["key"]] = self.mining.get(ev["key"], 0) + ev["value"]
            self.hold_raw[ev["key"]] = self.hold_raw.get(ev["key"], 0) + ev["value"]
            vol = ORE_TYPES.get(ev["key"], {}).get("volume", 0.0)
            minute = int(ev["ts"] // 60) * 60
            if not self.rate_min or self.rate_min[-1][0] != minute:
                self.rate_min.append([minute, {}])
            mix = self.rate_min[-1][1]
            mix[ev["key"]] = mix.get(ev["key"], 0) + ev["value"] * vol
        elif k == "dmg_out":
            self.dmg_out += ev["value"]
            self.targets[ev["key"]] = self.targets.get(ev["key"], 0) + ev["value"]
            w = ev.get("weapon", "Schiff/Direkt")
            self.weapons[w] = self.weapons.get(w, 0) + ev["value"]
            if live:
                self.win_out.append((now, ev["value"]))
        elif k == "dmg_in":
            self.dmg_in += ev["value"]
            self.attackers[ev["key"]] = self.attackers.get(ev["key"], 0) + ev["value"]
            if live:
                self.win_in.append((now, ev["value"]))
        elif k == "bounty":
            self.bounty += ev["value"]
        elif k == "compressed":
            self.cargo_full = False  # Kompression schafft Platz
            self.compressed[ev["key"]] = self.compressed.get(ev["key"], 0) + ev["value"]
            self.hold_comp[ev["key"]] = self.hold_comp.get(ev["key"], 0) + ev["value"]
            raw_ore = ev.get("raw")
            if raw_ore:
                self.hold_raw[raw_ore] = max(0, self.hold_raw.get(raw_ore, 0) - ev["value"])
        elif k == "hold_reset":
            self.hold_raw = {}
            self.hold_comp = {}
            self.cargo_full = False  # angedockt/gehandelt -> Frachtraum-Warnung hinfaellig
            if ev["key"] == "dock":
                # Station-Stopp: Karte beginnt einen neuen Trip, sonst zeigen
                # ISK/Erz-Werte laengst abgeladene Ladung an. Historie (DB)
                # bleibt davon unberuehrt.
                self.trips += 1
                self.mining = {}
                self.compressed = {}
                self.weapons = {}
                self.targets = {}
                self.attackers = {}
                self.bounty = 0
                self.dmg_out = self.dmg_in = 0
                self.depleted = 0
                self.start = time.time()
                self.first_ts = ev["ts"]
        elif k == "depleted":
            self.depleted += 1
            e = self.tool_off.setdefault(ev["key"], [0, 0])
            if ev["ts"] - e[1] > 60:
                e[0] = 0  # alter Vorfall abgelaufen -> neu zaehlen
            e[0] += 1
            e[1] = ev["ts"]
        elif k == "cargo":
            self.cargo_full = True
            self.cargo_ts = ev["ts"]
        elif k == "drone_idle":
            e = self.tool_off.setdefault("Mining Drone", [0, 0])
            e[0] += 1
            e[1] = ev["ts"]
        elif k == "drone_engage":
            # Drohnen arbeiten wieder — Drohnen-Warnungen sofort aufheben
            for tool in list(self.tool_off):
                if "Drone" in tool:
                    del self.tool_off[tool]

    def tool_warns(self):
        """Aktive Modul-Warnungen (letzte 60s), mit Werkzeugname."""
        cutoff = time.time() - 60
        out = []
        for tool, (cnt, ts) in list(self.tool_off.items()):
            if ts < cutoff:
                del self.tool_off[tool]
            else:
                out.append({"tool": tool, "count": cnt, "drone": "Drone" in tool})
        return out

    def rate_status(self):
        """(Normalrate, aktuelle Rate) in m3/min — verglichen wird nur mit
        Minuten desselben dominanten Erzes (Moissanite ist langsamer als
        Veldspar und darf keinen Fehlalarm ausloesen)."""
        entries = list(self.rate_min)
        if len(entries) < 7:
            return None
        nowm = int(time.time() // 60) * 60
        last3 = {nowm - 60, nowm - 120, nowm - 180}
        totals = {m: sum(mix.values()) for m, mix in entries}
        doms = {m: max(mix, key=mix.get) for m, mix in entries if mix}
        cur = sum(totals.get(m, 0) for m in last3) / 3
        vols = {}
        for m, mix in entries:
            if m in last3:
                for o, v in mix.items():
                    vols[o] = vols.get(o, 0) + v
        if not vols:
            return None
        dom = max(vols, key=vols.get)
        hist = sorted(t for m, t in totals.items()
                      if m not in last3 and m != nowm and t > 0 and doms.get(m) == dom)
        if len(hist) < 5:
            return None
        return hist[len(hist) // 2], cur

    def idle_threshold(self, base):
        """Effektive Stillstand-Schwelle: 3x Median der Lieferabstaende,
        mindestens die konfigurierte Basis — passt sich Drohnen-Booten an."""
        if not self.gaps:
            return base
        med = sorted(self.gaps)[len(self.gaps) // 2]
        return max(base, 3 * med)

    def dps(self, win):
        cut = time.time() - 60
        while win and win[0][0] < cut:
            win.popleft()
        return round(sum(d for _, d in win) / 60, 1)


# ---------------------------------------------------------------- Ingest
class Ingest(threading.Thread):
    daemon = True

    def __init__(self):
        super().__init__()
        self.sessions = {}
        self.lock = threading.Lock()
        self.progress = {"done": 0, "total": 0}
        self.started_full = False

    def log_dir(self):
        return Path(CONFIG["log_dir"]) if CONFIG["log_dir"] else None

    def run(self):
        while True:
            try:
                self.tick()
                self.check_idle()
            except Exception:
                pass
            time.sleep(2)

    def check_idle(self):
        """Warnt, wenn ein aktiver Miner laenger als idle_warn kein Erz mehr liefert."""
        thr = int(CONFIG.get("idle_warn", 240) or 0)
        if thr <= 0 or not self.started_full:
            return
        now = time.time()
        with self.lock:
            for s in self.sessions.values():
                if s.last_ore_ts is None or s.idle_alerted:
                    continue
                idle = now - s.last_ore_ts
                eff = s.idle_threshold(thr)
                if eff < idle < 1800:
                    s.idle_alerted = True
                    alerts.push("idle", s.name,
                                f"{s.name}: Seit {round(idle / 60)} min kein Erz — Mining prüfen (Laser/Drohnen)!")
                # Raten-Waechter: Teilausfall (z.B. 1 von 2 Strip Minern aus)
                rs = s.rate_status()
                if rs:
                    base, cur = rs
                    if cur > 0 and cur < 0.55 * base:
                        if s.low_since is None:
                            s.low_since = now
                        elif now - s.low_since > 120 and not s.low_alerted:
                            s.low_alerted = True
                            alerts.push("rate", s.name,
                                        f"{s.name}: Abbaurate nur noch {round(100 * cur / base)}% "
                                        f"— vermutlich Modul oder Drohnen inaktiv!")
                    else:
                        s.low_since = None
                        if cur >= 0.75 * base:
                            s.low_alerted = False

    def tick(self):
        d = self.log_dir()
        if not d or not d.exists():
            return
        files = []
        for f in d.glob("*.txt"):
            m = CHAR_FILE_RE.match(f.name)
            if m:
                files.append((f, m.group(1)))
        newest = {}
        for f, cid in files:
            if cid not in newest or f.stat().st_mtime > newest[cid].stat().st_mtime:
                newest[cid] = f
        self.progress["total"] = len(files)
        done = 0
        for f, cid in sorted(files, key=lambda x: x[0].stat().st_mtime):
            row = DB.execute("SELECT offset, skipped, char_name, first_ts, last_ts "
                             "FROM files WHERE name=?", (f.name,)).fetchone()
            if row is None:
                skip = (CONFIG["mode"] == "fresh"
                        and f.stat().st_mtime < float(CONFIG["install_ts"])
                        and newest.get(cid) != f)
                name = read_char_name(f)
                with DB_LOCK:
                    DB.execute("INSERT OR REPLACE INTO files VALUES(?,?,?,?,?,NULL,NULL)",
                               (f.name, cid, name, f.stat().st_size if skip else 0, int(skip)))
                    DB.commit()
                row = (f.stat().st_size if skip else 0, int(skip), name, None, None)
            offset, skipped, cname, first_ts, last_ts = row
            if CONFIG["mode"] == "all" and skipped:
                with DB_LOCK:
                    DB.execute("UPDATE files SET offset=0, skipped=0 WHERE name=?", (f.name,))
                    DB.commit()
                offset, skipped = 0, 0
            live_file = newest.get(cid) == f
            sess = None
            if live_file and not skipped:
                with self.lock:
                    sess = self.sessions.get(cid)
                    if sess is None or sess.file != f:
                        sess = CharSession(cid, cname, f)
                        self.sessions[cid] = sess
                        if offset > 0:
                            # Session-Statistik für bereits eingelesenen Teil rekonstruieren
                            try:
                                with open(f, "rb") as fh0:
                                    head = fh0.read(offset)
                                for bline in head.split(b"\n"):
                                    ev = parse_line(bline.decode("utf-8", "replace").lstrip("﻿"))
                                    if ev:
                                        sess.feed(ev, live=False)
                            except OSError:
                                pass
            if skipped or f.stat().st_size <= offset:
                done += 1
                continue
            try:
                catch_up = not self.started_full
                batch = []
                with open(f, "rb") as fh:
                    fh.seek(offset)
                    data = fh.read()
                cut = data.rfind(b"\n")
                if cut < 0:
                    done += 1
                    continue
                new_offset = offset + cut + 1
                for bline in data[:cut + 1].split(b"\n"):
                    ev = parse_line(bline.decode("utf-8", "replace").lstrip("﻿"))
                    if ev:
                        batch.append(ev)
                        if sess:
                            sess.feed(ev, live=not catch_up)
                        if not catch_up:
                            self.live_alerts(ev, cname)
                with DB_LOCK:
                    for ev in batch:
                        if ev["kind"] in ("drone_engage", "hold_reset"):
                            continue  # reine Live-Signale, nicht historisieren
                        db_add(ev["day"], cid, cname, ev["kind"], ev["key"], ev["value"])
                        if ev["kind"] == "dmg_out" and "weapon" in ev:
                            db_add(ev["day"], cid, cname, "weapon", ev["weapon"], ev["value"])
                        if ev["kind"] == "dmg_in" and ev["key"] not in NPC_NAMES:
                            db_add(ev["day"], cid, cname, "pvp_in", ev["key"], ev["value"])
                    if batch:
                        ts = [ev["ts"] for ev in batch]
                        first_ts = min(first_ts or ts[0], *ts)
                        last_ts = max(last_ts or ts[0], *ts)
                        DB.execute("UPDATE files SET first_ts=?, last_ts=? WHERE name=?",
                                   (first_ts, last_ts, f.name))
                    DB.execute("UPDATE files SET offset=? WHERE name=?", (new_offset, f.name))
                    DB.commit()
            except OSError:
                pass
            done += 1
        self.progress["done"] = done
        self.started_full = True

    def live_alerts(self, ev, cname):
        if ev["kind"] == "depleted":
            if "Drone" in ev["key"]:
                alerts.push("drones", cname,
                            f"{cname}: Mining-Drohnen abgeschaltet ({ev['key']}) — Drohnen prüfen!")
            else:
                alerts.push("depleted", cname,
                            f"{cname}: Asteroid leer — {ev['key']} hat abgeschaltet")
        elif ev["kind"] == "cargo":
            alerts.push("cargo", cname, f"{cname}: Frachtraum voll — Mining gestoppt!")
        elif ev["kind"] == "drone_idle":
            alerts.push("drones", cname,
                        f"{cname}: Mining-Drohnen voll — Erz verladen, Drohnen prüfen!")
        elif ev["kind"] == "dmg_in" and ev["key"] not in NPC_NAMES:
            alerts.push("pvp", cname, f"SPIELER-ANGRIFF: {ev['key']} schießt auf {cname}!")


# ---------------------------------------------------------------- Local-Chat (System + Watchlist)
class ChatWatch(threading.Thread):
    daemon = True

    def __init__(self):
        super().__init__()
        self.systems = {}      # char_id -> System
        self.offsets = {}      # file -> offset
        self.started_full = False

    def chat_dir(self):
        if not CONFIG["log_dir"]:
            return None
        return Path(CONFIG["log_dir"]).parent / "Chatlogs"

    def run(self):
        while True:
            try:
                self.tick()
            except Exception:
                pass
            self.started_full = True
            time.sleep(3)

    def tick(self):
        d = self.chat_dir()
        if not d or not d.exists():
            return
        newest = {}
        for f in list(d.glob("Local_*.txt")) + list(d.glob("Lokal_*.txt")):
            m = re.search(r"_(\d+)\.txt$", f.name)
            if m:
                cid = m.group(1)
                if cid not in newest or f.stat().st_mtime > newest[cid].stat().st_mtime:
                    newest[cid] = f
        watch = {w.lower() for w in CONFIG.get("watchlist", [])}
        for cid, f in newest.items():
            off = self.offsets.get(f, 0)
            try:
                with open(f, "rb") as fh:
                    fh.seek(off)
                    data = fh.read()
                self.offsets[f] = off + len(data)
                for line in data.decode("utf-16-le", "replace").splitlines():
                    line = line.strip().lstrip("﻿").strip()
                    cm = CHAT_LINE_RE.match(line)
                    if not cm:
                        continue
                    sender, msg = cm.group(1).strip(), cm.group(2).strip()
                    if "EVE" in sender and ":" in msg:
                        self.systems[cid] = msg.rsplit(":", 1)[1].strip().rstrip("*")
                    elif (self.started_full and watch
                          and sender.lower() in watch):
                        alerts.push("watch", sender,
                                    f"Watchlist: {sender} ist im Local aktiv!")
            except OSError:
                pass


# ---------------------------------------------------------------- Preise
class Prices(threading.Thread):
    daemon = True

    def __init__(self):
        super().__init__()
        self.cache = {}
        self.fetched = {}

    def wanted_ids(self):
        ids = set()
        for (ore,) in DB.execute("SELECT DISTINCT key FROM daily WHERE kind IN ('ore','compressed')"):
            t = ORE_TYPES.get(ore)
            if t:
                ids.add(t["typeID"])
        return ids

    def get(self, region):
        return self.cache.setdefault(region, {})

    def run(self):
        while True:
            region = CONFIG["region"]
            ids = self.wanted_ids()
            if ids and time.time() - self.fetched.get(region, 0) > PRICE_REFRESH:
                try:
                    url = (f"https://market.fuzzwork.co.uk/aggregates/"
                           f"?region={region}&types={','.join(map(str, sorted(ids)))}")
                    with urllib.request.urlopen(url, timeout=15) as r:
                        data = json.load(r)
                    self.cache[region] = {int(k): float(v["buy"]["max"]) for k, v in data.items()}
                    self.fetched[region] = time.time()
                except Exception:
                    self.fetched[region] = time.time() - PRICE_REFRESH + 60
            time.sleep(3)


ingest = Ingest()
chatwatch = ChatWatch()
prices = Prices()


# ---------------------------------------------------------------- Abfragen
def ore_value(ore, units, pm):
    t = ORE_TYPES.get(ore, {})
    return units * pm.get(t.get("typeID"), 0.0), units * t.get("volume", 0.0)


def baseline_filter(rows):
    b_day = meta_get("baseline_day")
    if not b_day:
        return list(rows)
    offsets = {(d, c, k, key): v for d, c, k, key, v in DB.execute(
        "SELECT day,char_id,kind,key,value FROM baseline_offsets")}
    out = []
    for day, cid, cname, kind, key, value in rows:
        if day < b_day:
            continue
        if day == b_day:
            value -= offsets.get((day, cid, kind, key), 0)
            if value <= 0:
                continue
        out.append((day, cid, cname, kind, key, value))
    return out


def all_rows(days=None, kinds=None):
    q = "SELECT day,char_id,char_name,kind,key,value FROM daily WHERE 1=1"
    args = []
    if days:
        cutoff = datetime.now(timezone.utc).strftime("%Y-%m-%d")
        q += f" AND day > date('{cutoff}', '-{int(days)} day')"
    if kinds:
        q += f" AND kind IN ({','.join('?' * len(kinds))})"
        args += list(kinds)
    return baseline_filter(DB.execute(q, args).fetchall())


def snapshot_live():
    pm = prices.get(CONFIG["region"])
    chars = []
    with ingest.lock:
        sessions = list(ingest.sessions.values())
    for s in sessions:
        ores, ore_isk, m3 = [], 0.0, 0.0
        for ore, units in sorted(s.mining.items(), key=lambda x: -x[1]):
            isk, vol = ore_value(ore, units, pm)
            ore_isk += isk
            m3 += vol
            ores.append({"ore": ore, "units": units, "m3": round(vol), "isk": round(isk)})
        ores.sort(key=lambda o: -o["isk"])
        comp = []
        for ctype, units in sorted(s.compressed.items(), key=lambda x: -x[1]):
            t = ORE_TYPES.get(ctype, {})
            comp.append({"type": ctype, "units": units,
                         "m3": round(units * t.get("volume", 0.0)),
                         "isk": round(units * pm.get(t.get("typeID"), 0.0))})
        comp.sort(key=lambda k: -k["isk"])
        hold_isk = hold_m3 = 0.0
        hold_types = hold_missing = 0
        for tname, units in list(s.hold_raw.items()) + list(s.hold_comp.items()):
            if units <= 0:
                continue
            hold_types += 1
            t = ORE_TYPES.get(tname, {})
            price = pm.get(t.get("typeID"))
            if price is None:
                hold_missing += 1
                price = 0.0
            hold_isk += units * price
            hold_m3 += units * t.get("volume", 0.0)
        if hold_types == 0 or hold_missing == 0:
            hold_prices = "ok"
        elif hold_missing == hold_types:
            hold_prices = "none"
        else:
            hold_prices = "partial"
        mins = max((time.time() - (s.first_ts or s.start)) / 60, 1)
        chars.append({
            "trips": s.trips,
            "compressed": comp, "tool_warns": s.tool_warns(),
            "rate_low": (lambda rs: round(100 * rs[1] / rs[0])
                         if rs and 0 < rs[1] < 0.55 * rs[0] else None)(s.rate_status()),
            "cargo_full": s.cargo_full and (time.time() - s.cargo_ts) < 300,
            "hold_isk": round(hold_isk), "hold_m3": round(hold_m3),
            "hold_prices": hold_prices,
            "mine_idle": round(time.time() - s.last_ore_ts) if s.last_ore_ts else None,
            "idle_thr": round(s.idle_threshold(int(CONFIG.get("idle_warn", 240) or 0))),
            "name": s.name, "session_min": round(mins),
            "system": chatwatch.systems.get(s.char_id, "?"),
            "ores": ores, "m3": round(m3), "ore_isk": round(ore_isk),
            "m3h": round(m3 / mins * 60), "bounty": s.bounty,
            "total_isk": round(ore_isk + s.bounty),
            "dmg_out": s.dmg_out, "dmg_in": s.dmg_in,
            "dps_out": s.dps(s.win_out), "dps_in": s.dps(s.win_in),
            "depleted": s.depleted,
            "weapons": sorted(s.weapons.items(), key=lambda x: -x[1])[:3],
            "top_targets": sorted(s.targets.items(), key=lambda x: -x[1])[:5],
            "top_attackers": sorted(s.attackers.items(), key=lambda x: -x[1])[:5],
            "spark": [round(sum(mix.values())) for _, mix in list(s.rate_min)[-60:]],
        })
    chars.sort(key=lambda c: c["name"])
    return chars


def query_month():
    pm = prices.get(CONFIG["region"])
    days = {}
    for day, cid, cname, kind, key, value in all_rows(days=30):
        d = days.setdefault(day, {"day": day, "chars": {}, "ore_isk": 0, "bounty": 0,
                                  "m3": 0, "dmg_out": 0, "dmg_in": 0, "depleted": 0})
        c = d["chars"].setdefault(cname, {"ore_isk": 0, "bounty": 0})
        if kind == "ore":
            isk, vol = ore_value(key, value, pm)
            d["ore_isk"] += isk
            d["m3"] += vol
            c["ore_isk"] += isk
        elif kind == "bounty":
            d["bounty"] += value
            c["bounty"] += value
        elif kind in ("dmg_out", "dmg_in", "depleted"):
            d[kind] += value
    out = sorted(days.values(), key=lambda d: d["day"])
    for d in out:
        d["ore_isk"] = round(d["ore_isk"])
        d["m3"] = round(d["m3"])
        d["depleted"] = round(d["depleted"])
        d["total"] = round(d["ore_isk"] + d["bounty"])
        d["chars"] = {k: {"ore_isk": round(v["ore_isk"]), "bounty": round(v["bounty"])}
                      for k, v in d["chars"].items()}
    return out


def query_total():
    pm = prices.get(CONFIG["region"])
    t = {"ore_isk": 0.0, "m3": 0.0, "bounty": 0, "dmg_out": 0, "dmg_in": 0,
         "units": 0, "days": set(), "ores": {}, "chars": {}, "depleted": 0}
    comp = {}
    day_isk = {}
    for day, cid, cname, kind, key, value in all_rows():
        t["days"].add(day)
        c = t["chars"].setdefault(cname, {"ore_isk": 0, "bounty": 0, "m3": 0})
        if kind == "ore":
            isk, vol = ore_value(key, value, pm)
            t["ore_isk"] += isk
            t["m3"] += vol
            t["units"] += value
            t["ores"][key] = t["ores"].get(key, 0) + value
            c["ore_isk"] += isk
            c["m3"] += vol
            day_isk[day] = day_isk.get(day, 0) + isk
        elif kind == "bounty":
            t["bounty"] += value
            c["bounty"] += value
            day_isk[day] = day_isk.get(day, 0) + value
        elif kind == "compressed":
            e = comp.setdefault(cname, {})
            e[key] = e.get(key, 0) + value
        elif kind in ("dmg_out", "dmg_in", "depleted"):
            t[kind] += value
    comp_list = []
    for cname, types in sorted(comp.items()):
        for ctype, units in sorted(types.items(), key=lambda x: -x[1]):
            tt = ORE_TYPES.get(ctype, {})
            comp_list.append({"char": cname, "type": ctype, "units": round(units),
                              "m3": round(units * tt.get("volume", 0.0)),
                              "isk": round(units * pm.get(tt.get("typeID"), 0.0))})
    best = max(day_isk.items(), key=lambda x: x[1]) if day_isk else ("—", 0)
    ores = []
    for ore, units in t["ores"].items():
        isk, vol = ore_value(ore, units, pm)
        ores.append({"ore": ore, "units": units, "m3": round(vol), "isk": round(isk)})
    ores.sort(key=lambda o: -o["isk"])
    ores = ores[:15]
    return {"ore_isk": round(t["ore_isk"]), "m3": round(t["m3"]), "bounty": t["bounty"],
            "total_isk": round(t["ore_isk"] + t["bounty"]), "units": t["units"],
            "days_active": len(t["days"]), "dmg_out": t["dmg_out"], "dmg_in": t["dmg_in"],
            "depleted": round(t["depleted"]),
            "best_day": {"day": best[0], "isk": round(best[1])}, "ores": ores,
            "compressed": comp_list,
            "chars": {k: {kk: round(vv) for kk, vv in v.items()} for k, v in t["chars"].items()}}


def compression_periods():
    """Kompressions-Bilanz je Zeitraum: gesamt + pro Charakter, nach Typ."""
    pm = prices.get(CONFIG["region"])
    today = datetime.now(timezone.utc).date()
    cuts = {"today": 0, "week": 6, "month": 29, "year": 364}
    rows = all_rows(kinds=["compressed"])

    def pack(d):
        types, U, M, I = [], 0, 0.0, 0.0
        for ctype, units in d.items():
            t = ORE_TYPES.get(ctype, {})
            isk = units * pm.get(t.get("typeID"), 0.0)
            m3 = units * t.get("volume", 0.0)
            U += units
            M += m3
            I += isk
            types.append({"type": ctype, "units": round(units), "m3": round(m3),
                          "isk": round(isk)})
        types.sort(key=lambda x: -x["isk"])
        return {"units": round(U), "m3": round(M), "isk": round(I), "types": types}

    out = {}
    for pkey, back in cuts.items():
        cutoff = (today - timedelta(days=back)).strftime("%Y-%m-%d")
        agg_t, agg_c = {}, {}
        for day, cid, cname, kind, key, value in rows:
            if day < cutoff:
                continue
            agg_t[key] = agg_t.get(key, 0) + value
            d = agg_c.setdefault(cname, {})
            d[key] = d.get(key, 0) + value
        out[pkey] = {"total": pack(agg_t),
                     "chars": {c: pack(d) for c, d in sorted(agg_c.items())}}
    return out


def query_analyse():
    pm = prices.get(CONFIG["region"])
    # Waffen
    weapons = {}
    for day, cid, cname, kind, key, value in all_rows(kinds=["weapon"]):
        weapons[key] = weapons.get(key, 0) + value
    # PvP-Vorfälle
    pvp = {}
    for day, cid, cname, kind, key, value in all_rows(kinds=["pvp_in"]):
        e = pvp.setdefault(key, {"dmg": 0, "days": set(), "char": cname})
        e["dmg"] += value
        e["days"].add(day)
    pvp_list = [{"attacker": k, "dmg": round(v["dmg"]), "char": v["char"],
                 "days": sorted(v["days"])} for k, v in
                sorted(pvp.items(), key=lambda x: -x[1]["dmg"])][:15]
    # Effizienz: ISK/m3 je geschürfter Erzart
    eff = []
    for day, cid, cname, kind, key, value in all_rows(kinds=["ore"]):
        eff.append((key, value))
    agg = {}
    for ore, units in eff:
        agg[ore] = agg.get(ore, 0) + units
    eff_list = []
    for ore, units in agg.items():
        t = ORE_TYPES.get(ore, {})
        price = pm.get(t.get("typeID"), 0.0)
        vol = t.get("volume", 0.0) or 1
        eff_list.append({"ore": ore, "units": units, "isk_per_m3": round(price / vol, 1),
                         "isk": round(units * price), "m3": round(units * vol)})
    eff_list.sort(key=lambda x: -x["isk_per_m3"])
    # Spielzeit pro Tag (aus Session-Dateien)
    b_ts = float(meta_get("baseline_ts") or 0)
    play = {}
    for name, cname, first_ts, last_ts in DB.execute(
            "SELECT name, char_name, first_ts, last_ts FROM files "
            "WHERE first_ts IS NOT NULL AND skipped=0"):
        if last_ts and last_ts > b_ts:
            day = datetime.fromtimestamp(max(first_ts, b_ts),
                                         timezone.utc).strftime("%Y-%m-%d")
            d = play.setdefault(day, {"day": day, "minutes": 0, "chars": {}})
            mins = (last_ts - max(first_ts, b_ts)) / 60
            d["minutes"] += mins
            d["chars"][cname] = d["chars"].get(cname, 0) + mins
    play_list = sorted(play.values(), key=lambda x: x["day"])
    for p in play_list:
        p["minutes"] = round(p["minutes"])
        p["chars"] = {k: round(v) for k, v in p["chars"].items()}
    # Ziel & Prognose
    goal = CONFIG.get("goal")
    goal_info = None
    total = query_total()
    month = query_month()
    if goal and goal.get("isk"):
        last7 = [d["total"] for d in month[-7:]]
        avg = sum(last7) / max(len(last7), 1)
        remaining = max(0, goal["isk"] - total["total_isk"])
        eta_days = round(remaining / avg, 1) if avg > 0 else None
        eta_date = ((datetime.now() + timedelta(days=eta_days)).strftime("%Y-%m-%d")
                    if eta_days is not None else None)
        goal_info = {"isk": goal["isk"], "deadline": goal.get("deadline"),
                     "current": total["total_isk"],
                     "pct": round(100 * total["total_isk"] / goal["isk"], 1),
                     "avg7": round(avg), "eta_days": eta_days, "eta_date": eta_date}
    return {"weapons": sorted(weapons.items(), key=lambda x: -x[1])[:10],
            "pvp": pvp_list, "efficiency": eff_list, "playtime": play_list,
            "goal": goal_info, "depleted_total": total["depleted"],
            "compression": compression_periods()}


def state_info():
    return {"region": CONFIG["region"], "regions": REGIONS, "mode": CONFIG["mode"],
            "baseline_day": meta_get("baseline_day"), "log_dir": CONFIG["log_dir"],
            "idle_warn": int(CONFIG.get("idle_warn", 240) or 0),
            "version": VERSION,
            "progress": ingest.progress, "prices_loaded": bool(prices.get(CONFIG["region"])),
            "watchlist": CONFIG.get("watchlist", []), "goal": CONFIG.get("goal"),
            "alerts": alerts.list()}


def export_csv():
    lines = ["day;char;kind;key;value"]
    for day, cid, cname, kind, key, value in all_rows():
        lines.append(f"{day};{cname};{kind};{key};{value}")
    return "\n".join(lines)


# ---------------------------------------------------------------- HTTP
class Handler(BaseHTTPRequestHandler):
    def _send(self, body, ctype="application/json", download=None):
        if isinstance(body, str):
            body = body.encode()
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        if download:
            self.send_header("Content-Disposition", f'attachment; filename="{download}"')
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        p = self.path.split("?")[0]
        if p == "/data":
            view = (self.path.split("view=")[1].split("&")[0]
                    if "view=" in self.path else "live")
            data = {"state": state_info()}
            if view == "live":
                data["chars"] = snapshot_live()
            elif view == "month":
                data["days"] = query_month()
            elif view == "analyse":
                data["analyse"] = query_analyse()
            else:
                data["total"] = query_total()
            self._send(json.dumps(data))
        elif p == "/export.csv":
            self._send(export_csv(), "text/csv; charset=utf-8", "eve_dashboard_export.csv")
        elif p == "/export.json":
            self._send(json.dumps({"month": query_month(), "total": query_total(),
                                   "analyse": query_analyse()}, indent=1),
                       "application/json", "eve_dashboard_export.json")
        else:
            self._send(PAGE, "text/html; charset=utf-8")

    def do_POST(self):
        length = int(self.headers.get("Content-Length", 0))
        try:
            body = json.loads(self.rfile.read(length) or b"{}")
        except Exception:
            body = {}
        action = body.get("action")
        if action == "region" and str(body.get("region")) in REGIONS:
            CONFIG["region"] = str(body["region"])
        elif action == "mode" and body.get("mode") in ("all", "fresh"):
            CONFIG["mode"] = body["mode"]
        elif action == "reset":
            do_reset_baseline()
        elif action == "clear_baseline":
            clear_baseline()
        elif action == "idle_warn":
            CONFIG["idle_warn"] = max(0, int(body.get("seconds") or 0))
        elif action == "watchlist":
            CONFIG["watchlist"] = [str(n).strip() for n in body.get("names", []) if str(n).strip()][:50]
        elif action == "goal":
            isk = body.get("isk")
            CONFIG["goal"] = ({"isk": int(isk), "deadline": str(body.get("deadline") or "")}
                              if isk else None)
        elif action == "backup":
            name = do_backup()
            self._send(json.dumps({"ok": True, "file": name}))
            return
        elif action == "check_update":
            self._send(json.dumps(check_update()))
            return
        elif action == "do_update":
            self._send(json.dumps(do_update()))
            return
        save_config()
        self._send(json.dumps({"ok": True, "state": state_info()}))

    def log_message(self, *a):
        pass


# ---------------------------------------------------------------- Frontend
PAGE = """<!DOCTYPE html><html lang="de"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>EVE Canary</title>
<link rel="icon" href="data:image/svg+xml,<svg xmlns=%22http://www.w3.org/2000/svg%22 viewBox=%220 0 100 100%22><text y=%22.9em%22 font-size=%2290%22>🐤</text></svg>">
<style>
:root{--bg:#0b0e14;--card:#121722;--inset:#0e1320;--line:#1e2636;--txt:#c9d4e3;
--dim:#5d6b80;--cyan:#35c8e8;--red:#e8564f;--green:#4fd47f;--gold:#e8c645;--white:#fff}
[data-theme=light]{--bg:#f2f4f8;--card:#ffffff;--inset:#eef1f6;--line:#d8dee9;
--txt:#2a3242;--dim:#7a8699;--cyan:#0e7ea3;--red:#c2372f;--green:#1e8f4d;--gold:#9a7a00;--white:#101828}
*{margin:0;box-sizing:border-box;font-family:'Segoe UI',system-ui,sans-serif}
body{background:var(--bg);color:var(--txt);padding:18px;transition:background .2s}
header{display:flex;align-items:center;gap:10px;flex-wrap:wrap;margin-bottom:10px}
h1{font-size:14px;font-weight:600;letter-spacing:2px;color:var(--dim)}
h1 b{color:var(--cyan)}
.pills{display:flex;gap:4px;margin-left:auto}
.pill{background:var(--card);border:1px solid var(--line);color:var(--dim);font-size:11px;
padding:4px 11px;border-radius:20px;cursor:pointer;user-select:none}
.pill.on{background:var(--cyan);color:var(--bg);border-color:var(--cyan)}
nav{display:flex;gap:2px;border-bottom:1px solid var(--line);margin-bottom:14px}
nav span{color:var(--dim);font-size:12px;padding:7px 16px;cursor:pointer;user-select:none}
nav span.on{color:var(--cyan);border-bottom:2px solid var(--cyan)}
#alerts{display:flex;flex-direction:column;gap:6px;margin-bottom:12px}
.alert{border-radius:8px;padding:8px 12px;font-size:12px;border:1px solid var(--line);background:var(--card)}
.alert.pvp{border-color:var(--red);color:var(--red);font-weight:600}
.alert.watch{border-color:var(--gold);color:var(--gold)}
.alert.depleted{border-color:var(--gold);color:var(--gold)}
.alert.idle{border-color:var(--gold);color:var(--gold);font-weight:600}
.alert.rate{border-color:var(--gold);color:var(--gold);font-weight:600}
.alert.drones{border-color:var(--red);color:var(--red);font-weight:600}
.alert.cargo{border-color:var(--red);color:var(--red);font-weight:600}
.cardwarn{border:1px solid var(--gold);color:var(--gold);border-radius:7px;
padding:7px 10px;font-size:12px;font-weight:600;margin-bottom:8px}
.cardwarn.drone{border-color:var(--red);color:var(--red)}
.warnbadge{color:var(--gold);font-weight:600}
.warnbadge.drone{color:var(--red)}
#grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(330px,1fr));gap:14px;align-items:start}
select.pill{appearance:none;-webkit-appearance:none;outline:none;background:var(--card);
border:1px solid var(--line);color:var(--dim);font-size:11px;padding:4px 11px;border-radius:20px;cursor:pointer}
.card{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:14px 16px}
.char{font-size:15px;font-weight:600;color:var(--white)}
.chead{display:flex;align-items:center;gap:8px;cursor:pointer;user-select:none}
.chead .mini{margin-left:auto;font-size:12px;color:var(--dim);white-space:nowrap}
.chead .arr{color:var(--dim);font-size:11px;transition:transform .15s}
.card.min .arr{transform:rotate(-90deg)}
.card.min .cbody{display:none}
.card.min{padding:10px 16px}
.sys{color:var(--cyan);font-weight:400;font-size:12px}
.sub{font-size:11px;color:var(--dim);margin-bottom:10px}
.stats{display:grid;grid-template-columns:repeat(3,1fr);gap:8px;margin-bottom:10px}
.stat{background:var(--inset);border-radius:7px;padding:8px 10px}
.stat .l{font-size:10px;text-transform:uppercase;letter-spacing:1px;color:var(--dim)}
.stat .v{font-size:16px;font-weight:600;margin-top:2px}
.isk{color:var(--gold)}.out{color:var(--cyan)}.in{color:var(--red)}.grn{color:var(--green)}
table{width:100%;border-collapse:collapse;font-size:12px;margin-top:6px}
td{padding:3px 0;border-top:1px solid var(--line)}
td.r{text-align:right;color:var(--dim)}
.sect{font-size:10px;text-transform:uppercase;letter-spacing:1px;color:var(--dim);margin-top:10px}
.bar{height:4px;border-radius:2px;background:var(--cyan);opacity:.7}
.spark{display:flex;align-items:flex-end;gap:1px;height:30px;margin-top:8px}
.spark div{flex:1;background:var(--cyan);opacity:.75;border-radius:1px 1px 0 0;min-height:1px}
.chart{display:flex;align-items:flex-end;gap:3px;height:120px;margin-top:12px}
.chart .col{flex:1;display:flex;flex-direction:column;justify-content:flex-end}
.chart .seg1{background:var(--cyan);border-radius:2px 2px 0 0}
.chart .seg2{background:var(--green)}
.legend{display:flex;gap:14px;font-size:11px;color:var(--dim);margin-top:6px}
.dot{display:inline-block;width:8px;height:8px;border-radius:2px;margin-right:4px;vertical-align:-1px}
.progress{background:var(--inset);border-radius:8px;height:16px;overflow:hidden;margin:8px 0}
.progress div{background:var(--gold);height:100%;transition:width .5s}
#empty{color:var(--dim);font-size:13px;margin-top:30px}
dialog{background:var(--card);color:var(--txt);border:1px solid var(--line);border-radius:12px;
padding:20px 22px;max-width:460px;width:94%}
dialog::backdrop{background:rgba(0,0,0,.55)}
dialog h2{font-size:14px;margin-bottom:12px;color:var(--white)}
dialog label{display:block;font-size:13px;margin:8px 0;cursor:pointer}
dialog .hint{font-size:11px;color:var(--dim);margin:2px 0 10px 0}
dialog input[type=text],dialog input[type=number],dialog input[type=date],dialog textarea{
background:var(--inset);border:1px solid var(--line);color:var(--txt);border-radius:6px;
padding:6px 8px;font-size:12px;width:100%}
.btn{background:var(--inset);border:1px solid var(--line);color:var(--txt);font-size:12px;
padding:7px 14px;border-radius:8px;cursor:pointer;margin:4px 6px 0 0}
.btn.warn{color:var(--red);border-color:var(--red)}
.note{font-size:11px;color:var(--dim);margin-top:10px}
</style></head><body>
<header>
 <h1>🐤 EVE <b>CANARY</b></h1>
 <select class="pill" id="charFilter" title="Charakter-Filter"><option value="">Alle Charaktere</option></select>
 <span class="pill" id="collapseAll">Alle einklappen</span>
 <div class="pills" id="regions"></div>
 <span class="pill" id="ovToggle" title="Always-on-top Mini-Overlay (Chrome/Edge)">◱ Overlay</span>
 <span class="pill" id="theme" title="Dark/Light">◐</span>
 <span class="pill" id="gear">⚙ Optionen</span>
</header>
<nav>
 <span data-v="live" class="on">Live</span>
 <span data-v="month">30 Tage</span>
 <span data-v="total">Gesamt</span>
 <span data-v="analyse">Analyse</span>
</nav>
<div id="alerts"></div>
<div id="grid"></div>
<div id="empty" hidden></div>

<dialog id="opts">
 <h2>Optionen</h2>
 <div class="sect">Datenbasis</div>
 <label><input type="radio" name="mode" value="all"> Alle vorhandenen Logs auswerten</label>
 <label><input type="radio" name="mode" value="fresh"> Nur ab Installation zählen</label>
 <div class="sect">Zähler</div>
 <button class="btn warn" id="reset">Auswertung ab jetzt neu lesen</button>
 <button class="btn" id="unreset">Baseline aufheben</button>
 <div class="hint" id="baseinfo"></div>
 <div class="sect">Ziel</div>
 <div style="display:flex;gap:6px">
  <input type="number" id="goalIsk" placeholder="ISK-Ziel, z.B. 1000000000">
  <input type="date" id="goalDate">
 </div>
 <button class="btn" id="saveGoal">Ziel speichern</button>
 <button class="btn" id="clearGoal">Ziel löschen</button>
 <div class="sect">Watchlist (Local-Chat, ein Name pro Zeile)</div>
 <textarea id="watchlist" rows="3" placeholder="Bekannte Ganker..."></textarea>
 <button class="btn" id="saveWatch">Watchlist speichern</button>
 <div class="sect">Mining-Stillstand-Warnung</div>
 <div style="display:flex;gap:6px;align-items:center">
  <input type="number" id="idleWarn" min="0" step="30" style="width:110px"> <span class="hint" style="margin:0">Sekunden ohne Erz bis zur Warnung (0 = aus)</span>
 </div>
 <button class="btn" id="saveIdle">Speichern</button>
 <div class="sect">Mini-Overlay</div>
 <button class="btn" id="ovBtn">Mini-Overlay öffnen/schließen</button>
 <div class="hint">Schwebendes Always-on-top-Fenster mit Status aller Charaktere und Alarmen —
 bleibt über dem EVE-Client (Fenstermodus/randlos). Benötigt Chrome oder Edge.
 Browser-seitig kann es nur per Klick geöffnet werden, nicht automatisch beim Start.</div>
 <div class="sect">Alarme</div>
 <label><input type="checkbox" id="sndPvp" checked> Sound bei Spieler-Angriff</label>
 <label><input type="checkbox" id="sndDep" checked> Sound bei leerem Asteroiden</label>
 <label><input type="checkbox" id="sndWatch" checked> Sound bei Watchlist-Treffer</label>
 <button class="btn" id="notifPerm">Desktop-Benachrichtigungen erlauben</button>
 <div class="sect">Version &amp; Update</div>
 <div class="hint" id="verinfo"></div>
 <button class="btn" id="checkUpd">Nach Update suchen</button>
 <button class="btn" id="doUpd" hidden>Update installieren</button>
 <div class="hint" id="updstatus"></div>
 <div class="sect">Daten</div>
 <button class="btn" id="backup">Backup erstellen</button>
 <a class="btn" href="/export.csv" style="text-decoration:none">Export CSV</a>
 <a class="btn" href="/export.json" style="text-decoration:none">Export JSON</a>
 <div class="note" id="loginfo"></div>
 <div style="text-align:right;margin-top:12px"><button class="btn" id="close">Schließen</button></div>
</dialog>

<script>
const $=s=>document.querySelector(s);
const fmt=n=>Math.round(n).toLocaleString();
const fmtM=n=>n>=1e9?(n/1e9).toFixed(2)+' Mrd':n>=1e6?(n/1e6).toFixed(1)+' M':fmt(n);
let view='live', state=null, lastAlertId=Number(localStorage.getItem('lastAlertId')||0);

const savedTheme=localStorage.getItem('theme');
if(savedTheme)document.documentElement.dataset.theme=savedTheme;
else if(matchMedia('(prefers-color-scheme: light)').matches)document.documentElement.dataset.theme='light';
$('#theme').onclick=()=>{const t=document.documentElement.dataset.theme==='light'?'dark':'light';
 document.documentElement.dataset.theme=t;localStorage.setItem('theme',t);};

document.querySelectorAll('nav span').forEach(el=>el.onclick=()=>{
 document.querySelectorAll('nav span').forEach(x=>x.classList.remove('on'));
 el.classList.add('on');view=el.dataset.v;tick();});

['sndPvp','sndDep','sndWatch'].forEach(id=>{
 const el=$('#'+id);
 el.checked=localStorage.getItem(id)!=='0';
 el.onchange=()=>localStorage.setItem(id,el.checked?'1':'0');});

$('#gear').onclick=()=>{syncOpts();$('#opts').showModal();};
$('#close').onclick=()=>$('#opts').close();
$('#reset').onclick=async()=>{if(confirm('Auswertung ab jetzt neu starten? Alte Daten bleiben gespeichert, werden aber ausgeblendet.')){await post({action:'reset'});tick();syncOpts();}};
$('#unreset').onclick=async()=>{await post({action:'clear_baseline'});tick();syncOpts();};
$('#backup').onclick=async()=>{const r=await post({action:'backup'});alert('Backup: '+r.file);};
$('#saveGoal').onclick=async()=>{await post({action:'goal',isk:Number($('#goalIsk').value)||null,deadline:$('#goalDate').value});syncOpts();};
$('#clearGoal').onclick=async()=>{await post({action:'goal',isk:null});$('#goalIsk').value='';syncOpts();};
$('#saveWatch').onclick=async()=>{await post({action:'watchlist',names:$('#watchlist').value.split('\\n')});};
$('#notifPerm').onclick=()=>Notification.requestPermission();
$('#saveIdle').onclick=async()=>{await post({action:'idle_warn',seconds:Number($('#idleWarn').value)||0});syncOpts();};
$('#checkUpd').onclick=async()=>{
 $('#updstatus').textContent='Prüfe …';$('#doUpd').hidden=true;
 const r=await post({action:'check_update'});
 if(!r.ok){$('#updstatus').textContent=r.error;return;}
 if(r.available){$('#updstatus').textContent='Neue Version verfügbar: '+r.latest+' (installiert: '+r.current+')';$('#doUpd').hidden=false;}
 else $('#updstatus').textContent='Du hast die aktuellste Version ('+r.current+').';
};
$('#doUpd').onclick=async()=>{
 $('#updstatus').textContent='Lade Update …';
 const r=await post({action:'do_update'});
 $('#updstatus').textContent=r.ok?(r.message||''):r.error;
 if(r.ok&&r.updated)setTimeout(()=>location.reload(),4000);
};
document.querySelectorAll('#opts input[name=mode]').forEach(r=>r.onchange=()=>post({action:'mode',mode:r.value}));

async function post(b){return (await fetch('/',{method:'POST',body:JSON.stringify(b)})).json();}

function syncOpts(){
 if(!state)return;
 document.querySelectorAll('#opts input[name=mode]').forEach(r=>r.checked=r.value===state.mode);
 $('#baseinfo').textContent=state.baseline_day?('Aktive Baseline: zählt seit '+state.baseline_day+' (UTC).'):'Keine Baseline aktiv.';
 $('#loginfo').textContent='Log-Ordner: '+(state.log_dir||'nicht gefunden!')+' · Dateien: '+state.progress.done+'/'+state.progress.total;
 $('#watchlist').value=(state.watchlist||[]).join('\\n');
 $('#idleWarn').value=state.idle_warn??240;
 $('#verinfo').textContent='Installiert: EVE Canary v'+(state.version||'?');
 if(state.goal){$('#goalIsk').value=state.goal.isk;$('#goalDate').value=state.goal.deadline||'';}
}

function beep(freq,times,dur){
 try{
  const ctx=beep.ctx||(beep.ctx=new (window.AudioContext||window.webkitAudioContext)());
  for(let i=0;i<times;i++){
   const o=ctx.createOscillator(),g=ctx.createGain();
   o.frequency.value=freq;o.connect(g);g.connect(ctx.destination);
   const t=ctx.currentTime+i*(dur+0.08);
   g.gain.setValueAtTime(0.15,t);g.gain.exponentialRampToValueAtTime(0.001,t+dur);
   o.start(t);o.stop(t+dur);}
 }catch(e){}}

function handleAlerts(){
 const list=state.alerts||[];
 const now=Date.now()/1000;
 $('#alerts').innerHTML=list.filter(a=>now-a.ts<300).slice(-4).reverse().map(a=>{
  const t=new Date(a.ts*1000).toLocaleTimeString();
  return `<div class="alert ${a.kind}">[${t}] ${a.text}</div>`}).join('');
 for(const a of list){
  if(a.id<=lastAlertId)continue;
  if(a.kind==='pvp'){
   if($('#sndPvp').checked)beep(880,3,0.18);
   if(Notification.permission==='granted')new Notification('EVE: SPIELER-ANGRIFF!',{body:a.text});
  }else if(a.kind==='depleted'&&$('#sndDep').checked)beep(520,1,0.12);
  else if(a.kind==='drones'){
   if($('#sndDep').checked)beep(590,2,0.15);
   if(Notification.permission==='granted')new Notification('EVE: Drohnen prüfen!',{body:a.text});
  }
  else if(a.kind==='cargo'){
   if($('#sndDep').checked)beep(700,3,0.18);
   if(Notification.permission==='granted')new Notification('EVE: Frachtraum voll!',{body:a.text});
  }
  else if(a.kind==='idle'){
   if($('#sndDep').checked)beep(470,2,0.2);
   if(Notification.permission==='granted')new Notification('EVE: Mining steht!',{body:a.text});
  }
  else if(a.kind==='rate'){
   if($('#sndDep').checked)beep(505,2,0.18);
   if(Notification.permission==='granted')new Notification('EVE: Abbaurate gefallen!',{body:a.text});
  }
  else if(a.kind==='watch'){
   if($('#sndWatch').checked)beep(660,2,0.15);
   if(Notification.permission==='granted')new Notification('EVE: Watchlist',{body:a.text});
  }
  lastAlertId=a.id;
 }
 localStorage.setItem('lastAlertId',lastAlertId);
}

function regionPills(){
 $('#regions').innerHTML=Object.entries(state.regions).map(([id,n])=>
  `<span class="pill ${id===state.region?'on':''}" data-r="${id}">${n}</span>`).join('');
 document.querySelectorAll('#regions .pill').forEach(p=>p.onclick=async()=>{
  await post({action:'region',region:p.dataset.r});tick();});
}

let collapsed=new Set(JSON.parse(localStorage.getItem('collapsed')||'[]'));
function toggleChar(name){
 if(collapsed.has(name))collapsed.delete(name);else collapsed.add(name);
 localStorage.setItem('collapsed',JSON.stringify([...collapsed]));
 if(lastChars)renderLive(lastChars);
}
let lastChars=null;
$('#charFilter').value=localStorage.getItem('charFilter')||'';
$('#charFilter').onchange=()=>{
 localStorage.setItem('charFilter',$('#charFilter').value);
 if(lastChars)renderLive(lastChars);};
$('#collapseAll').onclick=()=>{
 const names=(lastChars||[]).map(c=>c.name);
 if(names.length&&names.every(n=>collapsed.has(n)))names.forEach(n=>collapsed.delete(n));
 else names.forEach(n=>collapsed.add(n));
 localStorage.setItem('collapsed',JSON.stringify([...collapsed]));
 if(lastChars)renderLive(lastChars);};
function syncCharFilter(chars){
 const sel=$('#charFilter');
 const names=chars.map(c=>c.name);
 const want='Alle Charaktere|'+names.join('|');
 if(sel.dataset.opts!==want){
  const cur=sel.value;
  sel.innerHTML='<option value="">Alle Charaktere</option>'+
   names.map(n=>`<option value="${n}">${n}</option>`).join('');
  sel.value=names.includes(cur)?cur:'';
  sel.dataset.opts=want;
 }
 const all=names.length&&names.every(n=>collapsed.has(n));
 $('#collapseAll').textContent=all?'Alle aufklappen':'Alle einklappen';
}
function renderLive(chars){
 lastChars=chars;
 syncCharFilter(chars);
 const f=localStorage.getItem('charFilter')||'';
 if(f&&chars.some(c=>c.name===f))chars=chars.filter(c=>c.name===f);
 if(!chars.length){$('#empty').hidden=false;
  $('#empty').textContent='Warte auf Gamelog-Daten … (EVE-Client an? Im Client „Spielprotokoll speichern" aktivieren.)';
  $('#grid').innerHTML='';return;}
 $('#empty').hidden=true;
 $('#grid').innerHTML=chars.map(c=>{
  const maxOre=Math.max(1,...c.ores.map(o=>o.isk));
  const maxS=Math.max(1,...c.spark);
  const min=collapsed.has(c.name);
  return `<div class="card ${min?'min':''}">
   <div class="chead" data-c="${c.name}">
    <span class="arr">▼</span>
    <span class="char">${c.name} <span class="sys">· ${c.system}</span></span>
    <span class="mini">${c.cargo_full?'<span class="warnbadge drone">⚠ Frachtraum voll!</span> · ':''}${(c.tool_warns||[]).map(w=>'<span class="warnbadge'+(w.drone?' drone':'')+'">⚠ '+w.tool+(w.count>1?' ×'+w.count:'')+'</span> · ').join('')}${c.rate_low?'<span class="warnbadge">⚠ Rate '+c.rate_low+'%</span> · ':''}${mineIdle(c,state)?'<span class="warnbadge">⚠ Kein Erz seit '+Math.round(c.mine_idle/60)+' min</span> · ':''}${fmtM(c.total_isk)} ISK · ${fmt(c.m3h)} m³/h${c.dps_in>0?' · <span class=\"in\">⚠ '+c.dps_in+' DPS rein</span>':''}</span>
   </div>
   <div class="cbody">
   ${c.cargo_full?`<div class="cardwarn drone">⚠ Frachtraum voll — Erz verladen oder komprimieren!</div>`:''}
   ${(c.tool_warns||[]).map(w=>w.drone
     ?`<div class="cardwarn drone">⚠ ${w.tool}${w.count>1?' ×'+w.count:''} abgeschaltet — Drohnen prüfen!</div>`
     :`<div class="cardwarn">⚠ ${w.tool}${w.count>1?' ×'+w.count:''} abgeschaltet — Ziel prüfen</div>`).join('')}
   ${c.rate_low?`<div class="cardwarn">⚠ Abbaurate nur ${c.rate_low}% des Normalwerts — vermutlich Modul oder Drohnen inaktiv</div>`:''}
   ${mineIdle(c,state)?`<div class="cardwarn">⚠ Seit ${Math.round(c.mine_idle/60)} min kein Erz — Mining prüfen (Laser/Drohnen)</div>`:''}
   <div class="sub">${c.trips>0?'Trip '+(c.trips+1)+' · seit Abdocken':'Session'} ${c.session_min} min · ${c.depleted} Asteroiden leergebaggert · Preise: ${state.regions[state.region]}</div>
   <div class="stats">
    <div class="stat"><div class="l">${c.trips>0?'ISK Trip':'ISK Session'}</div><div class="v isk">${fmtM(c.total_isk)}</div></div>
    <div class="stat"><div class="l">Erz (${fmt(c.m3)} m³)</div><div class="v isk">${fmtM(c.ore_isk)}</div></div>
    <div class="stat"><div class="l">m³/h</div><div class="v out">${fmt(c.m3h)}</div></div>
    <div class="stat"><div class="l">Laderaum ≈ ${fmt(c.hold_m3)} m³ · ${state.regions[state.region]}</div><div class="v isk">${
      c.hold_prices==='none'
       ?'<span style="color:var(--dim);font-size:12px;font-weight:400">keine Preisdaten</span>'
       :'~'+fmtM(c.hold_isk)+(c.hold_prices==='partial'?' <span style="color:var(--dim)" title="Für einzelne Erztypen fehlen Preisdaten">±</span>':'')
    }</div></div>
    <div class="stat"><div class="l">Bounties</div><div class="v grn">${fmtM(c.bounty)}</div></div>
    <div class="stat"><div class="l">Schaden raus/rein</div><div class="v"><span class="out">${fmtM(c.dmg_out)}</span> / <span class="in">${fmtM(c.dmg_in)}</span></div></div>
    <div class="stat"><div class="l">DPS raus/rein</div><div class="v"><span class="out">${c.dps_out}</span> / <span class="in">${c.dps_in}</span></div></div>
   </div>
   ${c.spark.length>1?`<div class="spark">${c.spark.map(v=>`<div style="height:${Math.max(3,100*v/maxS)}%"></div>`).join('')}</div><div class="sub">Mining m³/min</div>`:''}
   ${c.ores.length?`<div class="sect">Mining</div><table>`+c.ores.map(o=>
     `<tr><td>${o.ore}<div class="bar" style="width:${100*o.isk/maxOre}%"></div></td>
      <td class="r">${fmt(o.units)} Stk</td><td class="r isk">${fmtM(o.isk)}</td></tr>`).join('')+`</table>`:''}
   ${c.compressed.length?`<div class="sect">Komprimiert (Session)</div><table>`+c.compressed.map(k=>
     `<tr><td>${k.type}</td><td class="r">${fmt(k.units)} Stk</td><td class="r">${fmt(k.m3)} m³</td><td class="r isk">${fmtM(k.isk)}</td></tr>`).join('')+`</table>`:''}
   ${c.weapons.length?`<div class="sect">Waffen</div><table>`+c.weapons.map(w=>
     `<tr><td>${w[0]}</td><td class="r">${fmt(w[1])} dmg</td></tr>`).join('')+`</table>`:''}
   ${c.top_targets.length?`<div class="sect">Top-Ziele</div><table>`+c.top_targets.map(t=>
     `<tr><td>${t[0]}</td><td class="r">${fmt(t[1])}</td></tr>`).join('')+`</table>`:''}
   ${c.top_attackers.length?`<div class="sect">Top-Angreifer</div><table>`+c.top_attackers.map(t=>
     `<tr><td>${t[0]}</td><td class="r">${fmt(t[1])}</td></tr>`).join('')+`</table>`:''}
   </div>
  </div>`}).join('');
 document.querySelectorAll('.chead').forEach(h=>h.onclick=()=>toggleChar(h.dataset.c));
}

function renderMonth(days){
 $('#empty').hidden=days.length>0;
 if(!days.length){$('#empty').textContent='Noch keine historischen Daten.';$('#grid').innerHTML='';return;}
 const max=Math.max(1,...days.map(d=>d.total));
 const sum=days.reduce((a,d)=>a+d.total,0), sumM3=days.reduce((a,d)=>a+d.m3,0);
 $('#grid').innerHTML=`<div class="card" style="grid-column:1/-1">
   <div class="char">Letzte 30 Tage</div>
   <div class="sub">${fmtM(sum)} ISK · ${fmt(sumM3)} m³ · Bewertung: aktuelle ${state.regions[state.region]}-Preise</div>
   <div class="chart">${days.map(d=>{
     const h1=110*d.ore_isk/max, h2=110*d.bounty/max;
     return `<div class="col" title="${d.day}: ${fmtM(d.total)} ISK">
       <div class="seg2" style="height:${h2}px"></div><div class="seg1" style="height:${h1}px"></div></div>`;}).join('')}</div>
   <div class="legend"><span><span class="dot" style="background:var(--cyan)"></span>Erz</span>
   <span><span class="dot" style="background:var(--green)"></span>Bounties</span></div>
   <table>${days.slice().reverse().map(d=>
    `<tr><td>${d.day}</td><td class="r">${fmt(d.m3)} m³</td><td class="r">${fmt(d.depleted)} Asteroiden</td><td class="r out">${fmtM(d.dmg_out)} dmg</td><td class="r isk">${fmtM(d.total)} ISK</td></tr>`).join('')}</table>
  </div>`;
}

function renderTotal(t){
 $('#empty').hidden=true;
 const maxOre=Math.max(1,...t.ores.map(o=>o.isk));
 $('#grid').innerHTML=`<div class="card">
   <div class="char">Gesamt${state.baseline_day?' (seit '+state.baseline_day+')':''}</div>
   <div class="sub">${t.days_active} aktive Tage · ${fmt(t.depleted)} Asteroiden leergebaggert</div>
   <div class="stats">
    <div class="stat"><div class="l">ISK gesamt</div><div class="v isk">${fmtM(t.total_isk)}</div></div>
    <div class="stat"><div class="l">Erz-Wert</div><div class="v isk">${fmtM(t.ore_isk)}</div></div>
    <div class="stat"><div class="l">Bounties</div><div class="v grn">${fmtM(t.bounty)}</div></div>
    <div class="stat"><div class="l">Erz gesamt</div><div class="v">${fmt(t.m3)} m³</div></div>
    <div class="stat"><div class="l">Bester Tag</div><div class="v isk">${fmtM(t.best_day.isk)}</div></div>
    <div class="stat"><div class="l">Schaden raus/rein</div><div class="v"><span class="out">${fmtM(t.dmg_out)}</span> / <span class="in">${fmtM(t.dmg_in)}</span></div></div>
   </div>
   <div class="sub">Bester Tag: ${t.best_day.day}</div>
  </div>
  <div class="card"><div class="char">Erz-Bilanz (nach Wert)</div><table>${t.ores.map(o=>
   `<tr><td>${o.ore}<div class="bar" style="width:${100*o.isk/maxOre}%"></div></td>
    <td class="r">${fmt(o.units)}</td><td class="r">${fmt(o.m3)} m³</td><td class="r isk">${fmtM(o.isk)}</td></tr>`).join('')}</table></div>
  <div class="card"><div class="char">Pro Charakter</div><table>${Object.entries(t.chars).map(([n,c])=>
   `<tr><td>${n}</td><td class="r">${fmt(c.m3)} m³</td><td class="r grn">${fmtM(c.bounty)}</td><td class="r isk">${fmtM(c.ore_isk+c.bounty)}</td></tr>`).join('')}</table></div>
  <div class="card"><div class="char">Komprimiert pro Charakter</div>
   <div class="sub">Alles, was über die Schiffs-Kompression gelaufen ist</div>
   <table>${t.compressed.length?t.compressed.map(k=>
   `<tr><td>${k.char}</td><td>${k.type}</td><td class="r">${fmt(k.units)} Stk</td><td class="r">${fmt(k.m3)} m³</td><td class="r isk">${fmtM(k.isk)}</td></tr>`).join(''):'<tr><td>Noch nichts komprimiert</td></tr>'}</table></div>`;
}

let compPeriod=localStorage.getItem('compPeriod')||'today';
let lastAnalyse=null;
const PERIODS={today:'Heute',week:'7 Tage',month:'30 Tage',year:'12 Monate'};
let compOpen=new Set(JSON.parse(localStorage.getItem('compOpen')||'[]'));
function toggleComp(key){
 if(compOpen.has(key))compOpen.delete(key);else compOpen.add(key);
 localStorage.setItem('compOpen',JSON.stringify([...compOpen]));
 if(lastAnalyse)renderAnalyse(lastAnalyse);
}
function compCard(comp){
 const p=comp[compPeriod]||{total:{units:0,m3:0,isk:0,types:[]},chars:{}};
 const pills=Object.entries(PERIODS).map(([k,l])=>
  `<span class="pill ${k===compPeriod?'on':''}" data-p="${k}">${l}</span>`).join('');
 const tbl=rows=>rows.map(k=>
  `<tr><td>${k.type}</td><td class="r">${fmt(k.units)} Stk</td><td class="r">${fmt(k.m3)} m³</td><td class="r isk">${fmtM(k.isk)}</td></tr>`).join('');
 const row=(key,label,d)=>{
  const open=compOpen.has(key);
  return `<div class="chead" data-cc="${key}" style="padding:6px 0;border-top:1px solid var(--line)">
    <span class="arr" style="${open?'':'transform:rotate(-90deg)'}">▼</span>
    <span style="font-size:13px;font-weight:600;color:var(--white)">${label}</span>
    <span class="mini">${fmt(d.units)} Stk · ${fmt(d.m3)} m³ · <span class="isk">${fmtM(d.isk)} ISK</span></span>
   </div>${open?`<table style="margin:0 0 8px 18px">${tbl(d.types)}</table>`:''}`;
 };
 return `<div class="card" style="grid-column:1/-1"><div class="chead" style="cursor:default">
   <span class="char">Kompression</span><span class="mini" style="display:flex;gap:4px">${pills}</span></div>
  <div class="sub">${PERIODS[compPeriod]} gesamt: ${fmt(p.total.units)} Stk · ${fmt(p.total.m3)} m³ · <span class="isk">${fmtM(p.total.isk)} ISK</span></div>
  ${p.total.types.length?row('__total__','Gesamt nach Typ',p.total):'<div class="sub">Keine Kompression im Zeitraum.</div>'}
  ${Object.entries(p.chars).map(([n,c])=>row(n,n,c)).join('')}
 </div>`;
}
function renderAnalyse(a){
 lastAnalyse=a;
 $('#empty').hidden=true;
 let goalHtml='';
 if(a.goal){
  goalHtml=`<div class="card" style="grid-column:1/-1"><div class="char">Ziel: ${fmtM(a.goal.isk)} ISK${a.goal.deadline?' bis '+a.goal.deadline:''}</div>
   <div class="progress"><div style="width:${Math.min(100,a.goal.pct)}%"></div></div>
   <div class="sub">${fmtM(a.goal.current)} / ${fmtM(a.goal.isk)} (${a.goal.pct}%) · Ø letzte 7 Tage: ${fmtM(a.goal.avg7)}/Tag
   ${a.goal.eta_date?' · bei aktueller Rate erreicht am <b>'+a.goal.eta_date+'</b>':''}</div></div>`;
 }else{
  goalHtml=`<div class="card" style="grid-column:1/-1"><div class="sub">Kein Ziel gesetzt — unter ⚙ Optionen kannst du ein ISK-Ziel mit Prognose anlegen.</div></div>`;
 }
 const maxP=Math.max(1,...a.playtime.map(p=>p.minutes));
 $('#grid').innerHTML=goalHtml+compCard(a.compression||{})+
  `<div class="card"><div class="char">Erz-Effizienz (ISK/m³)</div>
   <div class="sub">Was lohnt sich am meisten pro Laderaum?</div><table>${a.efficiency.map(e=>
   `<tr><td>${e.ore}</td><td class="r">${e.isk_per_m3} ISK/m³</td><td class="r">${fmt(e.m3)} m³</td><td class="r isk">${fmtM(e.isk)}</td></tr>`).join('')}</table></div>
  <div class="card"><div class="char">Waffen-Bilanz</div><table>${a.weapons.length?a.weapons.map(w=>
   `<tr><td>${w[0]}</td><td class="r out">${fmt(w[1])} dmg</td></tr>`).join(''):'<tr><td class="r">Noch keine Kampfdaten</td></tr>'}</table></div>
  <div class="card"><div class="char">Spielzeit</div><table>${a.playtime.slice(-14).reverse().map(p=>
   `<tr><td>${p.day}<div class="bar" style="width:${100*p.minutes/maxP}%"></div></td>
    <td class="r">${Math.floor(p.minutes/60)}h ${p.minutes%60}m</td></tr>`).join('')}</table></div>
  <div class="card"><div class="char">Sicherheit</div>
   <div class="sub">Spieler-Angriffe (gesamt)</div><table>${a.pvp.length?a.pvp.map(p=>
   `<tr><td class="in">${p.attacker}</td><td class="r">auf ${p.char}</td><td class="r">${fmt(p.dmg)} dmg</td><td class="r">${p.days[p.days.length-1]}</td></tr>`).join(''):'<tr><td>Keine Spieler-Angriffe erkannt ✓</td></tr>'}</table></div>`;
 document.querySelectorAll('[data-p]').forEach(el=>el.onclick=()=>{
  compPeriod=el.dataset.p;localStorage.setItem('compPeriod',compPeriod);
  if(lastAnalyse)renderAnalyse(lastAnalyse);});
 document.querySelectorAll('[data-cc]').forEach(el=>el.onclick=()=>toggleComp(el.dataset.cc));
}

let pipWin=null;
const OV_CSS=`*{margin:0;box-sizing:border-box;font-family:'Segoe UI',system-ui,sans-serif}
body{background:#0b0e14;padding:8px;overflow-y:auto}
.hd{display:flex;justify-content:space-between;align-items:center;font-size:9px;
letter-spacing:1.5px;color:#5d6b80;margin-bottom:6px}
.hd b{color:#35c8e8}
.row{display:flex;align-items:center;gap:8px;background:#121722;border:1px solid #1e2636;
border-radius:8px;padding:6px 10px;margin-bottom:5px}
.dot{width:9px;height:9px;border-radius:50%;flex:none}
.ok{background:#4fd47f}.warn{background:#e8c645}
.bad{background:#e8564f;animation:p .9s infinite}
@keyframes p{50%{opacity:.25}}
.nm{font-weight:600;color:#fff;font-size:12px;line-height:1.2}
.sys{color:#35c8e8;font-size:9px;font-weight:400}
.st{font-size:9px;color:#e8c645}
.st.bad{color:#e8564f;background:none;animation:none}
.val{margin-left:auto;text-align:right;font-size:11px;color:#e8c645;font-weight:600;line-height:1.25}
.val small{display:block;font-size:9px;color:#5d6b80;font-weight:400}
.al{font-size:10px;border-radius:6px;padding:4px 8px;margin-top:4px;border:1px solid #1e2636;color:#5d6b80;background:#121722}
.al.pvp,.al.cargo,.al.drones{color:#e8564f;border-color:#e8564f;font-weight:600}
.al.depleted,.al.watch{color:#e8c645;border-color:#e8c645}
body.alarm{outline:3px solid #e8564f;outline-offset:-3px}`;

async function toggleOverlay(){
 if(pipWin){pipWin.close();pipWin=null;return;}
 if(!('documentPictureInPicture' in window)){
  alert('Das Mini-Overlay benötigt Chrome oder Edge (Document Picture-in-Picture).');return;}
 try{
  pipWin=await documentPictureInPicture.requestWindow({width:330,height:240});
 }catch(e){return;}
 const d=pipWin.document;
 const st=d.createElement('style');st.textContent=OV_CSS;d.head.appendChild(st);
 d.title='EVE Canary';
 d.body.innerHTML='<div id="ov"><div class="hd"><span>🐤 <b>CANARY</b></span></div></div>';
 pipWin.addEventListener('pagehide',()=>{pipWin=null;});
 overlayTick();
}
function mineIdle(c,st){
 return c.mine_idle&&st.idle_warn>0&&c.mine_idle>(c.idle_thr||st.idle_warn)&&c.mine_idle<1800;
}
function ovStatus(c,st){
 if(c.dps_in>0)return['bad','UNTER BESCHUSS'];
 if(c.cargo_full)return['bad','FRACHTRAUM VOLL'];
 const tw=c.tool_warns||[];
 const dr=tw.find(w=>w.drone);
 if(dr)return['bad','DROHNEN PRÜFEN ('+dr.tool+')'];
 if(tw.length)return['warn',tw[0].tool.toUpperCase()+(tw[0].count>1?' ×'+tw[0].count:'')+' AUS'];
 if(c.rate_low)return['warn','ABBAURATE '+c.rate_low+'%'];
 if(mineIdle(c,st))return['warn','KEIN ERZ SEIT '+Math.round(c.mine_idle/60)+' MIN'];
 return['ok',''];
}
async function overlayTick(){
 if(!pipWin)return;
 try{
  const d=await (await fetch('/data?view=live')).json();
  const doc=pipWin.document, now=Date.now()/1000;
  const alerts=(d.state.alerts||[]).filter(a=>now-a.ts<180).slice(-3).reverse();
  const hot=alerts.some(a=>(a.kind==='pvp'||a.kind==='cargo'||a.kind==='drones')&&now-a.ts<45);
  doc.body.classList.toggle('alarm',hot);
  doc.getElementById('ov').innerHTML=
   `<div class="hd"><span>🐤 <b>CANARY</b></span><span>${new Date().toLocaleTimeString()}</span></div>`+
   d.chars.map(c=>{const [cls,txt]=ovStatus(c,d.state);
    return `<div class="row"><span class="dot ${cls}"></span>
     <span><div class="nm">${c.name} <span class="sys">· ${c.system}</span></div>
     ${txt?`<div class="st ${cls==='bad'?'bad':''}">${txt}</div>`:''}</span>
     <span class="val">${fmtM(c.total_isk)}<small>${fmt(c.m3h)} m³/h</small></span></div>`;}).join('')+
   alerts.map(a=>`<div class="al ${a.kind}">[${new Date(a.ts*1000).toLocaleTimeString()}] ${a.text}</div>`).join('');
 }catch(e){}
}
setInterval(overlayTick,2000);
$('#ovToggle').onclick=toggleOverlay;
$('#ovBtn').onclick=toggleOverlay;

async function tick(){
 try{
  const d=await (await fetch('/data?view='+view)).json();
  state=d.state;regionPills();handleAlerts();
  if(view==='live')renderLive(d.chars);
  else if(view==='month')renderMonth(d.days);
  else if(view==='analyse')renderAnalyse(d.analyse);
  else renderTotal(d.total);
 }catch(e){}
}
tick();setInterval(tick,2000);
</script></body></html>"""


if __name__ == "__main__":
    if not CONFIG["log_dir"]:
        print("WARNUNG: EVE-Gamelog-Ordner nicht gefunden — Pfad in config.json eintragen.")
    if DB_PATH.exists():
        try:
            do_backup()
        except Exception:
            pass
    ingest.start()
    chatwatch.start()
    prices.start()
    port = int(CONFIG.get("port", PORT_DEFAULT))
    print(f"EVE Canary läuft:  http://localhost:{port}")
    ThreadingHTTPServer(("127.0.0.1", port), Handler).serve_forever()
