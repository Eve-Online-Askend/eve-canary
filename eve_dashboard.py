# -*- coding: utf-8 -*-
"""
EVE Canary — der Kanarienvogel im Bergwerk. Liest die lokalen EVE-Logs (EULA-konform, reine
Textdateien, jede Client-Sprache) und zeigt Mining, Schaden, ISK, Effizienz,
Spielzeit und Sicherheits-Alarme (Spieler-Angriff, Asteroid leer) live +
historisch im Browser. Alles lokal, SQLite-Historie, Backups.

Start:  python eve_dashboard.py   ->  http://localhost:8765
"""
import base64
import email.utils
import hashlib
import json
import os
import re
import shutil
import sqlite3
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request

VERSION = "1.6.9"
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
SESSION_MAX_AGE = 3 * 3600  # Log länger unverändert -> Session gilt als beendet, keine Live-Karte
# Schweres Wasser pro Sekunde Kernlaufzeit (ESI-Dogma: Medium/Large Industrial Core,
# T1 = 100/min, T2 = 200/min — gilt für Porpoise und Orca gleichermassen)
HW_RATE = {"t1": 100 / 60.0, "t2": 200 / 60.0}
HW_CORE_GAP = 300  # laengere Kompressions-Pause -> Kern gilt als aus (Verbrauch pausiert)

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
           "goal": None, "watchlist": [], "idle_warn": 240, "heavy_water": {},
           "clip_watch": False,
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


CONFIG_LOCK = threading.RLock()


def save_config(cfg=None):
    # Atomar und thread-sicher: mehrere Threads (hw_tick, Esi.poll, do_POST …)
    # schreiben sonst gleichzeitig und hinterlassen kaputtes JSON.
    with CONFIG_LOCK:
        data = json.dumps(cfg or CONFIG, indent=1, ensure_ascii=False)
        tmp = CONFIG_PATH.with_suffix(".tmp")
        tmp.write_text(data, encoding="utf-8")
        os.replace(tmp, CONFIG_PATH)


CONFIG = load_config()

# ---------------------------------------------------------------- Datenbank
DB_LOCK = threading.Lock()
DB = sqlite3.connect(DB_PATH, check_same_thread=False)
# WAL + kurzer Busy-Timeout: Leser sehen stets den letzten committeten Stand,
# statt halbe Schreibtransaktionen anderer Threads (Dirty Reads).
try:
    DB.execute("PRAGMA journal_mode=WAL")
    DB.execute("PRAGMA busy_timeout=4000")
except sqlite3.OperationalError:
    pass
DB.executescript("""
CREATE TABLE IF NOT EXISTS meta(key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE IF NOT EXISTS files(name TEXT PRIMARY KEY, char_id TEXT, char_name TEXT,
    offset INTEGER DEFAULT 0, skipped INTEGER DEFAULT 0,
    first_ts REAL, last_ts REAL);
CREATE TABLE IF NOT EXISTS daily(day TEXT, char_id TEXT, char_name TEXT, kind TEXT,
    key TEXT, value REAL, PRIMARY KEY(day, char_id, kind, key));
CREATE TABLE IF NOT EXISTS baseline_offsets(day TEXT, char_id TEXT, kind TEXT,
    key TEXT, value REAL, PRIMARY KEY(day, char_id, kind, key));
CREATE TABLE IF NOT EXISTS threat(name TEXT PRIMARY KEY COLLATE NOCASE,
    data TEXT, ts REAL);
CREATE TABLE IF NOT EXISTS journal(id INTEGER, char TEXT, ts REAL,
    ref_type TEXT, amount REAL, party TEXT, PRIMARY KEY(id, char));
""")
DB.commit()
try:  # v1.5.1: System-Kontext je Journal-Eintrag (filtert Belt-Bounties aus der Missions-Statistik)
    DB.execute("ALTER TABLE journal ADD COLUMN ctx INTEGER")
    DB.commit()
except sqlite3.OperationalError:
    pass


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


def autostart_path():
    return (Path(os.environ.get("APPDATA", "")) / "Microsoft" / "Windows"
            / "Start Menu" / "Programs" / "Startup" / "EVE-Canary-Autostart.vbs")


def set_autostart(on):
    """Startet Canary beim Windows-Login still im Hintergrund (VBS, kein Konsolenfenster)."""
    p = autostart_path()
    if not on:
        try:
            p.unlink()
        except FileNotFoundError:
            pass
        return
    exe = Path(sys.executable)
    pyw = exe.with_name("pythonw.exe")
    runner = pyw if pyw.exists() else exe
    script = APP_DIR / "eve_dashboard.py"
    # --no-browser: beim Windows-Login still starten, ohne Browser-Tab aufzupoppen
    p.write_text('CreateObject("WScript.Shell").Run '
                 f'"""{runner}"" ""{script}"" --no-browser", 0\n', encoding="utf-8")


UPDATE_INFO = {"ts": 0, "available": False, "latest": None}


def refresh_update_info():
    """Alle 6 Stunden still nach einer neuen Version schauen (für den Kopfleisten-Badge)."""
    if time.time() - UPDATE_INFO["ts"] < 6 * 3600:
        return
    UPDATE_INFO["ts"] = time.time()
    chk = check_update()
    if chk.get("ok"):
        UPDATE_INFO["available"] = bool(chk.get("available"))
        UPDATE_INFO["latest"] = chk.get("latest")


def _ver(v):
    """Versionsstring in vergleichbares Tupel, '1.5.2' -> (1, 5, 2).
    Pro Segment nur den fuehrenden Zahlteil (so bleibt '1.6.0-rc1' vergleichbar)."""
    out = []
    for seg in str(v).split("."):
        m = re.match(r"\d+", seg)
        out.append(int(m.group()) if m else 0)
    return tuple(out)


def check_update():
    base = (CONFIG.get("update_url") or "").rstrip("/")
    if not base.startswith("https://"):
        return {"ok": False, "error": "Keine Update-Quelle konfiguriert (Optionen -> update_url)."}
    try:
        info = json.loads(fetch_url(f"{base}/version.json").decode("utf-8"))
        latest = str(info.get("version", "?"))
        return {"ok": True, "current": VERSION, "latest": latest,
                "available": _ver(latest) > _ver(VERSION),
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
    except SyntaxError:
        return {"ok": False, "error": "Die neue Version war fehlerhaft. Update abgebrochen, es wurde nichts geändert."}
    except Exception as e:
        return {"ok": False, "error": f"Download fehlgeschlagen: {e}"}
    # Atomar anwenden: erst alle Dateien komplett als .new schreiben, dann per
    # os.replace einzeln tauschen. Bricht das Tauschen ab (z.B. Virenscanner-Lock),
    # werden bereits getauschte Dateien aus dem .bak zurückgerollt -> keine Mischversion.
    written = []
    try:
        for name, data in blobs.items():
            (APP_DIR / (name + ".new")).write_bytes(data)
        for name in blobs:
            target = APP_DIR / name
            if target.exists():
                shutil.copy2(target, APP_DIR / (name + ".bak"))
            os.replace(APP_DIR / (name + ".new"), target)
            written.append(name)
    except Exception as e:
        for name in written:  # Rollback der schon getauschten Dateien
            bak = APP_DIR / (name + ".bak")
            if bak.exists():
                try:
                    shutil.copy2(bak, APP_DIR / name)
                except OSError:
                    pass
        for name in blobs:  # verwaiste .new aufräumen
            try:
                (APP_DIR / (name + ".new")).unlink()
            except OSError:
                pass
        return {"ok": False, "error": f"Update konnte nicht angewendet werden ({e}). "
                "Vorheriger Stand wurde wiederhergestellt."}
    def _restart():
        import subprocess
        kwargs = {"cwd": str(APP_DIR), "stdout": subprocess.DEVNULL,
                  "stderr": subprocess.DEVNULL}
        if os.name == "nt":
            # DETACHED_PROCESS | CREATE_NEW_PROCESS_GROUP: ueberlebt das
            # Schliessen des alten Konsolenfensters; Popen quotet Pfade
            # mit Leerzeichen korrekt (os.execv tut das unter Windows nicht!)
            kwargs["creationflags"] = 0x00000008 | 0x00000200
        subprocess.Popen([sys.executable, str(APP_DIR / "eve_dashboard.py")], **kwargs)
        os._exit(0)

    threading.Timer(1.0, _restart).start()
    return {"ok": True, "updated": True,
            "message": f"Update auf {chk['latest']} installiert. Neustart läuft, die Seite lädt gleich neu."}


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

    def resolve(self, kinds, char, min_age=0):
        """Alarme eines Chars entfernen, deren Ursache behoben ist
        (z.B. Erz fliesst wieder -> Frachtraum/Asteroid/Stillstand hinfaellig).
        min_age: Alarme juenger als X Sekunden bleiben stehen, damit die
        Warnung nicht verschwindet, bevor man sie gesehen hat."""
        cutoff = time.time() - min_age
        with self.lock:
            kept = [a for a in self.items
                    if a["char"] != char or a["kind"] not in kinds
                    or a["ts"] > cutoff]
            if len(kept) != len(self.items):
                self.items = deque(kept, maxlen=self.items.maxlen)

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
        self.lasers_off = {}  # Laser -> {"since": ts, "before": m3/min} — bleibt bis Erholung/Dock/Klick
        self.core_timeline = []  # (ts, kumulative Kern-Sekunden) je Kompressions-Event
        self.cargo_full = False
        self.cargo_ts = 0
        self.last_ore_ts = None   # fuer Stillstand-Erkennung
        self.idle_alerted = False
        self.low_since = None     # Raten-Waechter (Teilausfall-Erkennung)
        self.low_alerted = False
        self.gaps = deque(maxlen=40)  # letzte Abstaende zwischen Erz-Events (lernt Drohnen-Zyklen)
        # Drohnen-Erkennung: Mining-Drohnen liefern mehrere kleine Erz-Portionen
        # dicht beieinander (ein Zyklus = alle Drohnen fast gleichzeitig). Bleiben
        # diese Bursts aus, waehrend der Laser weiterlaeuft, sind die Drohnen idle.
        self.ore_ts = deque(maxlen=12)   # letzte Erz-Lieferzeitpunkte (Burst-Fenster)
        self.drone_last = None           # ts des letzten erkannten Drohnen-Bursts
        self.drone_gaps = deque(maxlen=15)  # Abstaende zwischen Drohnen-Bursts
        self.drone_alerted = False
        self.ore_hist = deque(maxlen=400)  # alle Erz-ts (fuer Laser/Drohnen-Strom-Analyse)
        self.laser_alerted = False
        self.dmg_out = self.dmg_in = self.bounty = 0
        self.kills = 0  # NPC-Abschuesse (eine Bounty-Zeile = ein Kill)
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
            # Drohnen-Burst: >=4 Erz-Lieferungen innerhalb von 8s. Ein Schiff hat
            # hoechstens 3 Strip Miner, also sind 4+ dicht aufeinanderfolgende
            # Lieferungen zwangslaeufig Mining-Drohnen (kein Fehlalarm bei Lasern).
            self.ore_ts.append(ev["ts"])
            self.ore_hist.append(ev["ts"])
            recent = [t for t in self.ore_ts if ev["ts"] - t <= 8]
            if len(recent) >= 4:
                # Neuer Zyklus nur, wenn >15s seit letztem Burst (sonst zaehlen die
                # 5 Drohnen EINES Zyklus als 5 Bursts -> falsche Mini-Gaps).
                if self.drone_last is None or ev["ts"] - self.drone_last > 15:
                    if self.drone_last and ev["ts"] - self.drone_last < 900:
                        self.drone_gaps.append(ev["ts"] - self.drone_last)
                self.drone_last = ev["ts"]
                self.drone_alerted = False   # Drohnen liefern wieder
            self.mining[ev["key"]] = self.mining.get(ev["key"], 0) + ev["value"]
            self.hold_raw[ev["key"]] = self.hold_raw.get(ev["key"], 0) + ev["value"]
            vol = ORE_TYPES.get(ev["key"], {}).get("volume", 0.0)
            minute = int(ev["ts"] // 60) * 60
            if not self.rate_min or self.rate_min[-1][0] != minute:
                if self.rate_min and self.lasers_off:
                    # Abgeschlossene Minute auswerten: Rate wieder auf Normal-
                    # niveau -> abgeschalteter Laser wurde offenbar neu gezielt
                    pm, pmix = self.rate_min[-1]
                    ptotal = sum(pmix.values())
                    for tool, info in list(self.lasers_off.items()):
                        if (info["before"] and pm > info["since"]
                                and ptotal >= 0.85 * info["before"]):
                            del self.lasers_off[tool]
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
            self.kills += 1
        elif k == "compressed":
            self.cargo_full = False  # Kompression schafft Platz
            # Kern-Laufzeit aus Kompressions-Kadenz: Luecken > HW_CORE_GAP
            # zaehlen nicht (Kern war vermutlich aus / angedockt)
            tl = self.core_timeline
            cum = tl[-1][1] if tl else 0.0
            if tl:
                gap = ev["ts"] - tl[-1][0]
                if 0 < gap < HW_CORE_GAP:
                    cum += gap
            tl.append((ev["ts"], cum))
            if len(tl) > 6000:
                del tl[:1000]
            self.compressed[ev["key"]] = self.compressed.get(ev["key"], 0) + ev["value"]
            self.hold_comp[ev["key"]] = self.hold_comp.get(ev["key"], 0) + ev["value"]
            raw_ore = ev.get("raw")
            if raw_ore:
                self.hold_raw[raw_ore] = max(0, self.hold_raw.get(raw_ore, 0) - ev["value"])
        elif k == "hold_reset":
            self.hold_raw = {}
            self.hold_comp = {}
            self.cargo_full = False  # angedockt/gehandelt -> Frachtraum-Warnung hinfaellig
            self.lasers_off = {}     # an der Station sind alle Module ohnehin aus
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
                self.kills = 0
                self.dmg_out = self.dmg_in = 0
                self.depleted = 0
                self.start = time.time()
                self.first_ts = ev["ts"]
        elif k == "depleted":
            self.depleted += 1
            if "Drone" not in ev["key"]:
                # Dauerstatus "Laser aus": Normalrate vor dem Ausfall merken
                # (Median der letzten vollen Minuten), damit die Erholung
                # erkannt werden kann, sobald die Rate wieder stimmt.
                completed = [t for t in (sum(mix.values())
                                         for _, mix in list(self.rate_min)[:-1]) if t > 0]
                tail = sorted(completed[-6:])
                before = tail[len(tail) // 2] if len(tail) >= 3 else None
                self.lasers_off[ev["key"]] = {"since": ev["ts"], "before": before}
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

    def core_active_since(self, t0):
        """Sekunden mit laufendem Industriekern seit t0 (aus Kompressions-Kadenz)."""
        tl = self.core_timeline
        if not tl or tl[-1][0] <= t0:
            return 0.0
        base = 0.0
        for ts, cum in reversed(tl):
            if ts <= t0:
                base = cum
                break
        return tl[-1][1] - base

    def core_on(self):
        return bool(self.core_timeline) and time.time() - self.core_timeline[-1][0] < HW_CORE_GAP

    def idle_threshold(self, base):
        """Effektive Stillstand-Schwelle: 3x Median der Lieferabstaende,
        mindestens die konfigurierte Basis — passt sich Drohnen-Booten an."""
        if not self.gaps:
            return base
        med = sorted(self.gaps)[len(self.gaps) // 2]
        return max(base, 3 * med)

    def drones_idle(self, now=None):
        """True, wenn Mining-Drohnen liefen, jetzt aber keine Bursts mehr kommen,
        obwohl weiter Erz eintrifft (Laser laeuft, Drohnen stehen). Braucht ein
        gelerntes Zyklus-Muster (>=4 Bursts), sonst kein Urteil."""
        if self.drone_last is None or len(self.drone_gaps) < 4:
            return False
        now = now or time.time()
        if self.last_ore_ts is None or now - self.last_ore_ts > 180:
            return False   # gar kein Erz mehr -> Stillstand-Warnung greift, nicht drohnenspezifisch
        # Schwelle an die SCHWANKUNG der Abstaende anpassen: Drohnen fliegen je
        # nach Asteroiden-Distanz unterschiedlich lange (Rueckweg!), der Abstand
        # schwankt stark. 90%-Perzentil + 30s Puffer sitzt knapp ueber dem
        # normalen Maximal-Abstand -> kein Fehlalarm beim langen Rueckflug,
        # trotzdem schnelle Meldung bei gleichmaessigen Drohnen.
        g = sorted(self.drone_gaps)
        p90 = g[min(len(g) - 1, int(len(g) * 0.9))]
        return max(90, p90 + 30) < now - self.drone_last < 1800

    def laser_stalled(self, now=None):
        """True, wenn der Strip-Miner-/Laser-Strom abreisst, waehrend Drohnen
        weiterliefern (Laser manuell aus oder haengt). Dichte-Analyse: isolierte
        Lieferungen = Laser, dichte 4er-Cluster = Drohnen. Braucht ein gelerntes
        Laser-Muster; Erschoepfungs-Faelle deckt bereits lasers_off ab."""
        if self.lasers_off:
            return False   # Erschoepfung ist bereits erkannt -> keine Doppelmeldung
        now = now or time.time()
        ts = list(self.ore_hist)
        if len(ts) < 12:
            return False
        laser, drone = [], []
        for i, t in enumerate(ts):
            near = sum(1 for u in ts if abs(u - t) <= 6)
            (drone if near >= 4 else laser).append(t)
        if len(laser) < 5 or not drone:
            return False   # kein klares Laser-Muster oder gar keine Drohnen als Referenz
        # Drohnen muessen noch aktiv sein (sonst ist es Gesamt-Stillstand -> mine_idle)
        if now - drone[-1] > 180:
            return False
        gaps = sorted(b - a for a, b in zip(laser, laser[1:]) if 0 < b - a < 400)
        if len(gaps) < 4:
            return False
        # 25%-Perzentil als Takt: Laser-Lieferungen, die zufaellig mit einem
        # Drohnen-Burst zusammenfallen, werden als Drohne fehlklassifiziert und
        # blaehen den Median auf — das Perzentil bleibt beim echten Takt.
        p25 = gaps[len(gaps) // 4]
        return max(75, p25 * 3) < now - laser[-1] < 1800

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
        self.filecache = {}  # name -> (size, mtime) fertig verarbeiteter Dateien
        self.live_files = []  # [(Pfad, cid)] der neuesten Datei je Char
        self.last_scan = 0.0  # Zeitpunkt des letzten Voll-Scans des Log-Ordners

    def log_dir(self):
        return Path(CONFIG["log_dir"]) if CONFIG["log_dir"] else None

    def run(self):
        while True:
            try:
                self.tick()
                self.check_idle()
                self.hw_tick()
                refresh_update_info()
            except Exception:
                pass
            time.sleep(2)

    def hw_tick(self):
        """Schweres-Wasser-Buchhaltung: Verbrauch seit letztem Checkpoint abziehen,
        Stand in der Config sichern (uebersteht Neustarts), bei <30 min warnen."""
        with CONFIG_LOCK:
            hw = dict(CONFIG.get("heavy_water") or {})  # Kopie: do_POST/sync_ship mutieren parallel
        if not hw:
            return
        now = time.time()
        changed = False
        with self.lock:
            by_name = {s.name: s for s in self.sessions.values()}
        for char, e in hw.items():
            if now - e.get("ck", 0) < 60:
                continue
            e["ck"] = now
            s = by_name.get(char)
            if s is None:
                continue
            rate = HW_RATE.get(e.get("core"), HW_RATE["t1"])
            active = s.core_active_since(e.get("ts", now))
            if active > 0:
                e["units"] = max(0.0, e["units"] - active * rate)
                e["ts"] = now
                changed = True
            if (s.core_on() and not e.get("warned")
                    and e["units"] < rate * 1800):
                e["warned"] = True
                changed = True
                mins = int(e["units"] / rate / 60)
                alerts.push("hw", char,
                            f"{char}: Heavy Water fast leer, reicht noch etwa {mins} Minuten!")
        if changed:
            save_config()

    def check_idle(self):
        """Warnt, wenn ein aktiver Miner laenger als idle_warn kein Erz mehr liefert."""
        if not self.started_full:
            return
        thr = int(CONFIG.get("idle_warn", 240) or 0)
        now = time.time()
        # Drohnen- und Strip-Miner-Stillstand erscheinen NUR als Info in der
        # Charakter-Karte (Felder drones_idle/laser_stalled), nicht im Alarm-Banner.
        with self.lock:
            for s in self.sessions.values():
                if thr <= 0:
                    continue
                if s.last_ore_ts is None or s.idle_alerted:
                    continue
                idle = now - s.last_ore_ts
                eff = s.idle_threshold(thr)
                if eff < idle < 1800:
                    s.idle_alerted = True
                    alerts.push("idle", s.name,
                                f"{s.name}: Seit {round(idle / 60)} Minuten kein Erz. Laser und Drohnen prüfen!")
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
                                        f"{s.name}: Abbaurate nur noch {round(100 * cur / base)}%. "
                                        f"Vermutlich ist ein Modul oder eine Drohne aus!")
                    else:
                        s.low_since = None
                        if cur >= 0.75 * base:
                            s.low_alerted = False

    def tick(self):
        d = self.log_dir()
        if not d or not d.exists():
            return
        # Voll-Scan des Ordners nur alle 15s (neue Dateien entstehen nur beim
        # EVE-Login). Dazwischen werden nur die Live-Dateien der Chars geprüft:
        # bei Jahren an Logs spart das den Grossteil der Dauerlast.
        full = time.time() - self.last_scan >= 15 or not self.live_files
        if full:
            self.last_scan = time.time()
            files = []
            for f in d.glob("*.txt"):
                m = CHAR_FILE_RE.match(f.name)
                if m:
                    try:
                        files.append((f, m.group(1), f.stat()))
                    except OSError:
                        continue
            newest = {}
            for f, cid, st in files:
                if cid not in newest or st.st_mtime > newest[cid][1]:
                    newest[cid] = (f, st.st_mtime)
            newest = {cid: f for cid, (f, _) in newest.items()}
            self.live_files = [(f, cid) for cid, f in newest.items()]
            self.progress["total"] = len(files)
        else:
            files = []
            for f, cid in self.live_files:
                try:
                    files.append((f, cid, f.stat()))
                except OSError:
                    self.last_scan = 0  # Datei weg? Beim nächsten Tick voll scannen
                    return
            newest = {cid: f for f, cid in self.live_files}
        done = 0
        for f, cid, st in sorted(files, key=lambda x: x[2].st_mtime):
            # Fertig gelesene Alt-Dateien ohne Datenbank-Zugriff überspringen.
            # Bei Jahren an Logs (zigtausend Dateien) macht das den Takt erst bezahlbar.
            if (self.filecache.get(f.name) == (st.st_size, st.st_mtime)
                    and newest.get(cid) != f):
                done += 1
                if full:
                    self.progress["done"] = done
                continue
            row = DB.execute("SELECT offset, skipped, char_name, first_ts, last_ts "
                             "FROM files WHERE name=?", (f.name,)).fetchone()
            if row is None:
                skip = (CONFIG["mode"] == "fresh"
                        and st.st_mtime < float(CONFIG["install_ts"])
                        and newest.get(cid) != f)
                name = read_char_name(f)
                with DB_LOCK:
                    DB.execute("INSERT OR REPLACE INTO files VALUES(?,?,?,?,?,NULL,NULL)",
                               (f.name, cid, name, st.st_size if skip else 0, int(skip)))
                    DB.commit()
                row = (st.st_size if skip else 0, int(skip), name, None, None)
            offset, skipped, cname, first_ts, last_ts = row
            if CONFIG["mode"] == "all" and skipped:
                with DB_LOCK:
                    DB.execute("UPDATE files SET offset=0, skipped=0 WHERE name=?", (f.name,))
                    DB.commit()
                offset, skipped = 0, 0
            live_file = newest.get(cid) == f
            sess = None
            if live_file and not skipped:
                fresh = time.time() - st.st_mtime <= SESSION_MAX_AGE
                with self.lock:
                    sess = self.sessions.get(cid)
                    if not fresh:
                        # Log seit Stunden unverändert (z.B. Session von gestern):
                        # keine Live-Karte aufbauen bzw. verwaiste entfernen.
                        # Kommen wieder Einträge, wird die Session beim nächsten
                        # Tick vollständig aus dem Dateikopf rekonstruiert.
                        self.sessions.pop(cid, None)
                        sess = None
                    elif sess is None or sess.file != f:
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
            if skipped or st.st_size <= offset:
                if newest.get(cid) != f:
                    self.filecache[f.name] = (st.st_size, st.st_mtime)
                done += 1
                if full:
                    self.progress["done"] = done
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
                now = time.time()
                # Session-Mutation unter self.lock, damit snapshot_live (HTTP-Thread)
                # nicht mitten in der Iteration von mining/rate_min/win_out crasht.
                with self.lock:
                    for bline in data[:cut + 1].split(b"\n"):
                        ev = parse_line(bline.decode("utf-8", "replace").lstrip("﻿"))
                        if ev:
                            batch.append(ev)
                            if sess:
                                sess.feed(ev, live=not catch_up)
                            # Live-Alarme nur für wirklich frische Ereignisse (< 10 min).
                            # Schaltet man später auf "alle Logs", werden sonst Jahre an
                            # historischen PvP-Treffern als Alarm + zKill-Abfrage ausgelöst.
                            if not catch_up and now - ev["ts"] < 600:
                                self.live_alerts(ev, cname)
                                if ev["kind"] == "ore":
                                    self.learn_mine_system(cid)
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
            # Fortschritt live mitschreiben: beim Erst-Einlesen grosser Bestaende
            # (Jahre an Logs) soll die Anzeige nicht minutenlang auf 0 stehen
            if full:
                self.progress["done"] = done
        if full:
            self.progress["done"] = done
            self.started_full = True

    def learn_mine_system(self, cid):
        """Merkt sich Systeme, in denen aktiv gemint wird. Bounties aus diesen
        Systemen zählen nicht als Missions-Einkommen (Belt-Ratten-Filter)."""
        sysname = chatwatch.systems.get(cid)
        if not sysname or sysname == "?":
            return
        ms = CONFIG.setdefault("mine_systems", {})
        if sysname not in ms:
            ms[sysname] = 0  # System-ID löst der ESI-Thread nach
            save_config()

    def live_alerts(self, ev, cname):
        # Entwarnung: Gegensignal im Log macht alte Alarme sofort hinfaellig
        if ev["kind"] == "ore":
            alerts.resolve(("cargo", "idle", "rate"), cname)
            # Asteroid-leer erst nach 60s Anzeige loeschen: der zweite Laser
            # liefert evtl. weiter Erz, obwohl der erste noch neu gezielt
            # werden muss — die Warnung soll sichtbar bleiben.
            alerts.resolve(("depleted",), cname, min_age=60)
        elif ev["kind"] == "compressed":
            alerts.resolve(("cargo",), cname)
        elif ev["kind"] == "hold_reset":
            alerts.resolve(("cargo", "depleted", "idle"), cname)
        elif ev["kind"] == "drone_engage":
            alerts.resolve(("drones",), cname)
        # Drohnen-/Modul-Status (depleted, drone_idle) landet NICHT im oberen
        # Alarm-Banner — nur als Info in der jeweiligen Charakter-Karte (tool_warns).
        # Grund: 5 Drohnen erzeugten 5 fast identische Banner-Eintraege, und beim
        # Zurückfliegen der Drohnen ist ein kurzer Lieferstopp kein echtes Problem.
        if ev["kind"] == "cargo":
            alerts.push("cargo", cname, f"{cname}: Frachtraum voll, Mining gestoppt!")
        elif ev["kind"] == "dmg_in" and ev["key"] not in NPC_NAMES:
            alerts.push("pvp", cname, f"SPIELER-ANGRIFF: {ev['key']} schießt auf {cname}!")
            # Täterprofil sofort nachladen — Ergebnis kommt als eigener Intel-Alarm
            threat.request([ev["key"]], prio=True, alert="yellow")


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
                # UTF-16 = 2 Byte je Zeichen. Erwischt read() einen noch nicht
                # fertig geschriebenen Block mit ungerader Länge, nur die geraden
                # Bytes konsumieren; das letzte Byte bleibt für den nächsten Tick.
                usable = len(data) & ~1
                self.offsets[f] = off + usable
                for line in data[:usable].decode("utf-16-le", "replace").splitlines():
                    line = line.strip().lstrip("﻿").strip()
                    cm = CHAT_LINE_RE.match(line)
                    if not cm:
                        continue
                    sender, msg = cm.group(1).strip(), cm.group(2).strip()
                    if "EVE" in sender and ":" in msg:
                        self.systems[cid] = msg.rsplit(":", 1)[1].strip().rstrip("*")
                    elif self.started_full:
                        if watch and sender.lower() in watch:
                            alerts.push("watch", sender,
                                        f"Watchlist: {sender} ist im Local aktiv!")
                        # Jeden Local-Sprecher still einstufen; Alarm nur bei Rot
                        threat.request([sender], alert="red")
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
                comp = ORE_TYPES.get("Compressed " + ore)
                if comp:  # Bewertung läuft über den Preis der komprimierten Variante
                    ids.add(comp["typeID"])
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


# ---------------------------------------------------------------- ESI (offizielles EVE-SSO, PKCE)
SSO_AUTH = "https://login.eveonline.com/v2/oauth/authorize"
SSO_TOKEN = "https://login.eveonline.com/v2/oauth/token"
ESI_BASE = "https://esi.evetech.net/latest"
ESI_SCOPES = ("esi-assets.read_assets.v1 esi-location.read_ship_type.v1 "
              "esi-wallet.read_character_wallet.v1")
ESI_UA = f"EVE-Canary/{VERSION} (https://github.com/Eve-Online-Askend/eve-canary)"
HW_TYPE_ID = 16272  # Heavy Water
# Wallet-Journal-Typen fuer die Missions-Statistik
JOURNAL_TYPES = {"agent_mission_reward", "agent_mission_time_bonus_reward",
                 "bounty_prizes", "bounty_prize"}
CORE_TYPES = {62590: "t1", 62591: "t2",   # Medium Industrial Core I/II (Porpoise)
              58945: "t1", 58950: "t2"}   # Large Industrial Core I/II (Orca)


class Esi(threading.Thread):
    """EVE-SSO-Login (PKCE, ohne Client-Secret) + periodischer Abgleich:
    Schweres Wasser im aktuellen Schiff, Kern-Typ aus der Fitting, Wallet."""
    daemon = True

    def __init__(self):
        super().__init__()
        self.pending = {}     # state -> code_verifier laufender Logins
        self.status = {}      # char -> Klartext-Status fuer die Optionen-Seite
        self.type_cache = {}  # type_id -> Name (Schiffstypen, öffentlicher Endpunkt)
        self.party_names = {} # id -> Name (Agenten aus dem Wallet-Journal)

    def cfg(self):
        return CONFIG.setdefault("esi", {"client_id": "", "chars": {}})

    def redirect_uri(self):
        return f"http://localhost:{CONFIG.get('port', PORT_DEFAULT)}/sso/callback"

    def login_url(self):
        if not self.cfg().get("client_id"):
            return None
        verifier = base64.urlsafe_b64encode(os.urandom(32)).rstrip(b"=").decode()
        challenge = base64.urlsafe_b64encode(
            hashlib.sha256(verifier.encode()).digest()).rstrip(b"=").decode()
        state = base64.urlsafe_b64encode(os.urandom(12)).rstrip(b"=").decode()
        self.pending[state] = verifier
        return SSO_AUTH + "?" + urllib.parse.urlencode({
            "response_type": "code", "redirect_uri": self.redirect_uri(),
            "client_id": self.cfg()["client_id"], "scope": ESI_SCOPES,
            "code_challenge": challenge, "code_challenge_method": "S256",
            "state": state})

    def _token_request(self, data):
        req = urllib.request.Request(
            SSO_TOKEN, data=urllib.parse.urlencode(data).encode(),
            headers={"Content-Type": "application/x-www-form-urlencoded",
                     "User-Agent": ESI_UA})
        with urllib.request.urlopen(req, timeout=20) as r:
            return json.loads(r.read())

    def callback(self, code, state):
        """Auth-Code gegen Tokens tauschen. Liefert None bei Erfolg, sonst Fehlertext."""
        verifier = self.pending.pop(state, None)
        if not verifier:
            return "Die Login-Anfrage ist abgelaufen. Bitte starte den Login noch einmal."
        try:
            tok = self._token_request({
                "grant_type": "authorization_code", "code": code,
                "client_id": self.cfg()["client_id"], "code_verifier": verifier})
            pay = tok["access_token"].split(".")[1]
            pay = json.loads(base64.urlsafe_b64decode(pay + "==="))
            name = pay["name"]
            self.cfg()["chars"][name] = {
                "char_id": int(pay["sub"].split(":")[-1]),
                "refresh": tok["refresh_token"], "access": tok["access_token"],
                "exp": time.time() + tok.get("expires_in", 1199) - 60,
                "assets_next": 0}
            save_config()
            self.status[name] = "verbunden"
            return None
        except Exception as e:
            return f"Token-Tausch fehlgeschlagen: {e}"

    def _access(self, c):
        if time.time() >= c.get("exp", 0) or not c.get("access"):
            tok = self._token_request({
                "grant_type": "refresh_token", "refresh_token": c["refresh"],
                "client_id": self.cfg()["client_id"]})
            c["refresh"] = tok.get("refresh_token", c["refresh"])
            c["access"] = tok["access_token"]
            c["exp"] = time.time() + tok.get("expires_in", 1199) - 60
            # Rotiertes Refresh-Token SOFORT sichern: CCP invalidiert das alte,
            # ein späterer Fehler im selben poll dürfte es sonst nie speichern.
            save_config()
        return c["access"]

    def _get(self, c, path, params=None):
        url = ESI_BASE + path + ("?" + urllib.parse.urlencode(params) if params else "")
        req = urllib.request.Request(url, headers={
            "Authorization": "Bearer " + self._access(c), "User-Agent": ESI_UA})
        with urllib.request.urlopen(req, timeout=30) as r:
            return json.loads(r.read()), r.headers

    def type_name(self, tid):
        n = self.type_cache.get(tid)
        if n:
            return n
        try:
            req = urllib.request.Request(f"{ESI_BASE}/universe/types/{tid}/",
                                         headers={"User-Agent": ESI_UA})
            with urllib.request.urlopen(req, timeout=15) as r:
                n = json.loads(r.read()).get("name")
        except Exception:
            return None
        if n:
            self.type_cache[tid] = n
        return n

    def sync_ship(self, name, c):
        """Heavy Water + Kern-Typ aus dem aktuellen Schiff uebernehmen."""
        ship, _ = self._get(c, f"/characters/{c['char_id']}/ship/")
        items, page = [], 1
        while True:
            data, hdr = self._get(c, f"/characters/{c['char_id']}/assets/",
                                  {"page": page})
            items += data
            if page >= int(hdr.get("X-Pages") or 1):
                break
            page += 1
        # Asset-Cache: erst nach Ablauf erneut fragen (ESI cached bis zu 1h)
        try:
            exp = email.utils.parsedate_to_datetime(hdr["Expires"]).timestamp()
        except Exception:
            exp = time.time() + 3600
        c["assets_next"] = exp + 10
        in_ship = [i for i in items if i.get("location_id") == ship["ship_item_id"]]
        units = sum(i["quantity"] for i in in_ship if i["type_id"] == HW_TYPE_ID)
        core = next((CORE_TYPES[i["type_id"]] for i in in_ship
                     if i["type_id"] in CORE_TYPES), None)
        with CONFIG_LOCK:
            hw = CONFIG.setdefault("heavy_water", {})
            prev = hw.get(name) or {}
            if core is None and units == 0:
                # Schiff ohne Industriekern (Barge, Hauler, ...) -> keine Anzeige
                if prev.get("esi"):
                    hw.pop(name, None)
            else:
                hw[name] = {"units": float(units), "fill": max(float(units), prev.get("fill") or 0),
                            "core": core or prev.get("core", "t1"),
                            "ts": time.time(), "ck": 0, "esi": True,
                            "warned": bool(prev.get("warned")) and units <= prev.get("units", 0)}

    def sync_journal(self, name, c):
        """Wallet-Journal einlesen: Missions-Belohnungen, Boni, Bounty-Ticks.
        Lokale Historie waechst unbegrenzt (ESI liefert nur ~30 Tage rueckwirkend)."""
        data, hdr = self._get(c, f"/characters/{c['char_id']}/wallet/journal/")
        pages = int(hdr.get("X-Pages") or 1)
        page = 2
        while page <= pages:  # aktive Tage/lange Offline-Zeit füllen mehrere Seiten
            more, _ = self._get(c, f"/characters/{c['char_id']}/wallet/journal/",
                                {"page": page})
            data += more
            page += 1
        try:
            exp = email.utils.parsedate_to_datetime(hdr["Expires"]).timestamp()
        except Exception:
            exp = time.time() + 3600
        c["journal_next"] = exp + 10
        keep = [e for e in data if e.get("ref_type") in JOURNAL_TYPES
                and (e.get("amount") or 0) > 0]
        ids = {e.get("first_party_id") for e in keep
               if str(e.get("ref_type", "")).startswith("agent_")}
        ids -= set(self.party_names)
        try:
            self.party_names.update(self._names(list(ids)))
        except Exception:
            pass
        with DB_LOCK:
            for e in keep:
                ts = datetime.fromisoformat(
                    e["date"].replace("Z", "+00:00")).timestamp()
                ctx = (e.get("context_id")
                       if e.get("context_id_type") == "system_id" else None)
                DB.execute("INSERT OR IGNORE INTO journal VALUES(?,?,?,?,?,?,?)",
                           (e["id"], name, ts, e["ref_type"], e["amount"],
                            self.party_names.get(e.get("first_party_id"), ""), ctx))
            DB.commit()

    def resolve_mine_systems(self):
        """System-Namen aus dem Belt-Bounty-Filter zu IDs auflösen (öffentlich)."""
        ms = CONFIG.get("mine_systems") or {}
        names = [n for n, i in ms.items() if not i]
        if not names:
            return False
        req = urllib.request.Request(
            ESI_BASE + "/universe/ids/", data=json.dumps(names).encode(),
            headers={"Content-Type": "application/json", "User-Agent": ESI_UA})
        with urllib.request.urlopen(req, timeout=20) as r:
            data = json.loads(r.read())
        for s in data.get("systems", []):
            ms[s["name"]] = s["id"]
        return bool(data.get("systems"))

    def poll(self):
        changed = False
        try:
            changed = self.resolve_mine_systems() or changed
        except Exception:
            pass
        for name, c in list(self.cfg().get("chars", {}).items()):
            try:
                bal, _ = self._get(c, f"/characters/{c['char_id']}/wallet/")
                c["wallet"] = bal
                if time.time() >= c.get("journal_next", 0):
                    self.sync_journal(name, c)
                ship, _ = self._get(c, f"/characters/{c['char_id']}/ship/")
                new_ship = ship["ship_type_id"] != c.get("ship_type_id")
                c["ship_type_id"] = ship["ship_type_id"]
                c["ship"] = self.type_name(ship["ship_type_id"]) or c.get("ship") or "?"
                if new_ship:
                    c["assets_next"] = 0  # Schiffswechsel -> Laderaum sofort neu abgleichen
                if time.time() >= c.get("assets_next", 0):
                    self.sync_ship(name, c)
                self.status[name] = "verbunden"
                changed = True
            except urllib.error.HTTPError as e:
                self.status[name] = f"HTTP-Fehler {e.code}" + (
                    ". Login abgelaufen? Bitte neu verbinden." if e.code in (400, 401) else "")
            except Exception as e:
                self.status[name] = f"Fehler: {str(e)[:80]}"
        if changed:
            save_config()

    def run(self):
        time.sleep(6)
        while True:
            try:
                self.poll()
            except Exception:
                pass
            time.sleep(120)


# ---------------------------------------------------------------- Bedrohungs-Ampel (öffentliche APIs)
# Opfer-Schiffsgruppen, die auf Miner-/Hauler-Ganks hindeuten
MINER_GROUPS = {463, 543,        # Mining Barge, Exhumer
                941, 883,        # Industrial Command Ship (Orca/Porpoise), Capital Industrial (Rorqual)
                28, 380, 1202,   # Hauler, Deep Space Transport, Blockade Runner
                513, 902}        # Freighter, Jump Freighter
THREAT_TTL = 12 * 3600           # Cache-Lebensdauer eines Profils


class ThreatIntel(threading.Thread):
    """Bedrohungs-Einstufung von Piloten über öffentliche APIs (ESI + zKillboard).
    Kein Login nötig. Ergebnisse landen im SQLite-Cache (Tabelle threat)."""
    daemon = True

    def __init__(self):
        super().__init__()
        self.queue = []          # [Name, ...] FIFO
        self.queued = set()      # lower(Name) zum Dedupen
        self.alert_on = {}       # lower(Name) -> Mindest-Stufe fuer Alarm ("red"/"yellow")
        self.lock = threading.Lock()
        self.wake = threading.Event()

    # ---------- oeffentliche Schnittstelle
    def request(self, names, prio=False, alert=None):
        """Namen zur Pruefung einreihen (nur unbekannte/abgelaufene). Liefert Cache-Treffer.
        alert: "yellow" = ab Gelb alarmieren (Angreifer), "red" = nur bei Rot (Sprecher)."""
        results, missing = {}, []
        for n in names:
            n = n.strip()
            if not n or len(n) > 37:
                continue
            hit = self.cached(n)
            if hit is not None:
                results[n] = hit
            else:
                missing.append(n)
        with self.lock:
            for n in missing:
                k = n.lower()
                if alert:
                    self.alert_on[k] = alert
                if k not in self.queued:
                    self.queued.add(k)
                    if prio:
                        self.queue.insert(0, n)
                    else:
                        self.queue.append(n)
        if missing:
            self.wake.set()
        return results

    def cached(self, name):
        row = DB.execute("SELECT data, ts FROM threat WHERE name=?", (name,)).fetchone()
        if row and time.time() - row[1] < THREAT_TTL:
            return json.loads(row[0])
        return None

    def pending(self):
        with self.lock:
            return len(self.queue)

    # ---------- Verarbeitung
    def _http(self, url, timeout=20):
        req = urllib.request.Request(url, headers={
            "User-Agent": ESI_UA, "Accept-Encoding": "gzip"})
        with urllib.request.urlopen(req, timeout=timeout) as r:
            raw = r.read()
            if r.headers.get("Content-Encoding") == "gzip":
                import gzip
                raw = gzip.decompress(raw)
            return json.loads(raw)

    def _post_ids(self, names):
        """ESI: Namen -> Charakter-IDs (exakte Treffer, oeffentlich)."""
        req = urllib.request.Request(
            ESI_BASE + "/universe/ids/", data=json.dumps(names).encode(),
            headers={"Content-Type": "application/json", "User-Agent": ESI_UA})
        with urllib.request.urlopen(req, timeout=20) as r:
            data = json.loads(r.read())
        return {c["name"]: c["id"] for c in data.get("characters", [])}

    def _names(self, ids):
        """ESI: IDs -> Namen (Corp/Allianz, oeffentlich)."""
        ids = [i for i in ids if i]
        if not ids:
            return {}
        req = urllib.request.Request(
            ESI_BASE + "/universe/names/", data=json.dumps(ids).encode(),
            headers={"Content-Type": "application/json", "User-Agent": ESI_UA})
        with urllib.request.urlopen(req, timeout=20) as r:
            return {e["id"]: e["name"] for e in json.loads(r.read())}

    @staticmethod
    def _classify(age_days, sec, recent_kills, miner_kills, total_kills, danger):
        if (miner_kills >= 3 and recent_kills >= 1) or sec <= -2.0 \
                or (age_days is not None and age_days < 60 and recent_kills >= 1):
            return "red"
        if recent_kills >= 3 or danger >= 60 or miner_kills >= 3:
            return "yellow"
        if recent_kills >= 1 or total_kills >= 10:
            return "yellow" if danger >= 30 else "green"
        return "green"

    def _store(self, name, data):
        with DB_LOCK:
            DB.execute("INSERT OR REPLACE INTO threat VALUES(?,?,?)",
                       (name, json.dumps(data), time.time()))
            DB.commit()
        k = name.lower()
        with self.lock:
            min_lvl = self.alert_on.pop(k, None)
        lvl = data.get("level")
        if min_lvl and (lvl == "red" or (lvl == "yellow" and min_lvl == "yellow")):
            lbl = "GANKER-VERDACHT" if lvl == "red" else "PvP-aktiv"
            alerts.push("intel", name,
                        f"⚠ {lbl}: {name} ({data.get('corp') or '?'}), "
                        f"{data.get('recent_kills', 0)} Kills in 60 Tagen, "
                        f"{data.get('miner_kills', 0)} Miner-Kills gesamt")

    def _profile(self, name, cid):
        pub = self._http(f"{ESI_BASE}/characters/{cid}/")
        age = None
        try:
            born = datetime.fromisoformat(pub["birthday"].replace("Z", "+00:00"))
            age = int((datetime.now(timezone.utc) - born).days)
        except Exception:
            pass
        z = self._http(f"https://zkillboard.com/api/stats/characterID/{cid}/") or {}
        months = z.get("months") or {}
        now = datetime.now(timezone.utc)
        keys = {(now.year, now.month)}
        for back in (1, 2):
            y, m = now.year, now.month - back
            while m < 1:
                m += 12
                y -= 1
            keys.add((y, m))
        recent = sum((v or {}).get("shipsDestroyed", 0) for k, v in months.items()
                     if (int(str(k)[:4]), int(str(k)[4:])) in keys)
        miner = sum((g or {}).get("shipsDestroyed", 0)
                    for gid, g in (z.get("groups") or {}).items()
                    if int(gid) in MINER_GROUPS)
        info = z.get("info") or {}
        nm = self._names([pub.get("corporation_id"), pub.get("alliance_id")])
        sec = float(info.get("secStatus") or 0.0)
        total = int(z.get("shipsDestroyed") or 0)
        danger = int(z.get("dangerRatio") or 0)
        return {
            "id": cid, "age_days": age, "sec": round(sec, 1),
            "corp": nm.get(pub.get("corporation_id")),
            "alliance": nm.get(pub.get("alliance_id")),
            "kills": total, "losses": int(z.get("shipsLost") or 0),
            "recent_kills": recent, "miner_kills": miner,
            "danger": danger, "gang": int(z.get("gangRatio") or 0),
            "level": self._classify(age, sec, recent, miner, total, danger)}

    def run(self):
        while True:
            self.wake.wait()
            with self.lock:
                batch = self.queue[:20]
                del self.queue[:20]
                if not self.queue:
                    self.wake.clear()
            if not batch:
                continue
            try:
                ids = self._post_ids(batch)
            except Exception:
                ids = {}
            idmap = {n.lower(): (n, i) for n, i in ids.items()}
            for raw in batch:
                real, cid = idmap.get(raw.lower(), (raw, None))
                try:
                    if cid is None:
                        data = {"level": "unknown", "note": "kein Charakter mit diesem Namen"}
                    else:
                        data = self._profile(real, cid)
                except Exception as e:
                    data = {"level": "unknown", "note": f"Abfrage fehlgeschlagen: {str(e)[:60]}"}
                self._store(raw, data)
                with self.lock:
                    self.queued.discard(raw.lower())
                time.sleep(1.1)  # zKillboard-Etikette: nicht schneller als ~1 Request/s


NAME_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9' .-]{1,36}$")


class ClipWatch(threading.Thread):
    """Beobachtet die Windows-Zwischenablage (opt-in): Kopiert man im EVE-Local
    die Mitgliederliste (Strg+A, Strg+C), erkennt Canary die Namensliste und
    startet automatisch den Bedrohungs-Scan — ohne Alt-Tab. Der Inhalt bleibt
    lokal; nur als Pilotennamen erkannte Zeilen gehen zur Auflösung an ESI."""
    daemon = True

    def __init__(self):
        super().__init__()
        self.last = None
        self.names = []   # letzter automatisch erkannter Satz
        self.ts = 0

    @staticmethod
    def read_clipboard():
        import ctypes
        from ctypes import wintypes
        u32, k32 = ctypes.windll.user32, ctypes.windll.kernel32
        # 64-Bit-Handles: ohne explizite restypes stutzt ctypes auf 32 Bit!
        u32.GetClipboardData.restype = wintypes.HANDLE
        k32.GlobalLock.restype = ctypes.c_void_p
        k32.GlobalLock.argtypes = [wintypes.HANDLE]
        k32.GlobalUnlock.argtypes = [wintypes.HANDLE]
        if not u32.OpenClipboard(0):
            return None
        try:
            h = u32.GetClipboardData(13)  # CF_UNICODETEXT
            if not h:
                return None
            ptr = k32.GlobalLock(h)
            if not ptr:
                return None
            try:
                return ctypes.wstring_at(ptr)
            finally:
                k32.GlobalUnlock(h)
        finally:
            u32.CloseClipboard()

    def check(self):
        text = self.read_clipboard()
        if text is None or text == self.last or len(text) > 20000:
            self.last = text if text is not None and len(text) <= 20000 else self.last
            return
        self.last = text
        lines = [l.strip() for l in text.splitlines() if l.strip()]
        if not 2 <= len(lines) <= 300:
            return
        good = [l for l in lines if NAME_RE.match(l)]
        # nur reagieren, wenn der Inhalt klar wie eine Mitgliederliste aussieht
        if len(good) < 2 or len(good) / len(lines) < 0.8:
            return
        self.names = list(dict.fromkeys(good))[:200]
        self.ts = time.time()
        threat.request(self.names, alert="red")

    def run(self):
        while sys.platform == "win32":
            time.sleep(2)
            try:
                if CONFIG.get("clip_watch"):
                    self.check()
            except Exception:
                pass


ingest = Ingest()
chatwatch = ChatWatch()
prices = Prices()
esi = Esi()
threat = ThreatIntel()
clipwatch = ClipWatch()


# ---------------------------------------------------------------- Abfragen
def ore_value(ore, units, pm):
    """ISK und Volumen eines Erz-Postens. Bewertet wird zum Preis der
    komprimierten Variante (Komprimieren ist 1:1 in Stück), denn das ist der
    Wert, der beim Verkauf wirklich ankommt. Gibt es keine komprimierte
    Variante oder keinen Preis dafür, gilt der Rohpreis. Volumen immer vom Rohtyp."""
    t = ORE_TYPES.get(ore, {})
    comp = ORE_TYPES.get("Compressed " + ore)
    price = pm.get(comp["typeID"]) if comp else None
    if price is None:
        price = pm.get(t.get("typeID"), 0.0)
    return units * price, units * t.get("volume", 0.0)


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


def portrait_url(name):
    """Charakter-Portrait über den öffentlichen EVE-Bilderdienst. Die ID kommt
    vom ESI-Login oder aus dem Bedrohungs-Cache, sonst gibt es kein Bild."""
    c = (CONFIG.get("esi") or {}).get("chars", {}).get(name)
    cid = c.get("char_id") if c else None
    if not cid:
        hit = threat.cached(name)
        cid = hit.get("id") if hit else None
    return f"https://images.evetech.net/characters/{cid}/portrait?size=64" if cid else None


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
        hw_cfg = (CONFIG.get("heavy_water") or {}).get(s.name)
        hw = None
        if hw_cfg:
            rate = HW_RATE.get(hw_cfg.get("core"), HW_RATE["t1"])
            rem = max(0.0, hw_cfg["units"]
                      - s.core_active_since(hw_cfg.get("ts", 0)) * rate)
            on = s.core_on()
            hw = {"units": round(rem), "core": hw_cfg.get("core", "t1"), "on": on,
                  "fill": round(hw_cfg.get("fill") or 0), "esi": bool(hw_cfg.get("esi")),
                  "min_left": round(rem / rate / 60),
                  "eta": round(time.time() + rem / rate) if on else None}
        esi_char = (CONFIG.get("esi") or {}).get("chars", {}).get(s.name)
        chars.append({
            "heavy_water": hw,
            "portrait": portrait_url(s.name),
            "esi_linked": esi_char is not None,
            "ship": (esi_char or {}).get("ship"),
            "wallet": (esi_char or {}).get("wallet"),
            "trips": s.trips,
            "compressed": comp, "tool_warns": s.tool_warns(),
            "lasers_off": [{"tool": t, "since": int(i["since"])}
                           for t, i in sorted(s.lasers_off.items())],
            "rate_low": (lambda rs: round(100 * rs[1] / rs[0])
                         if rs and 0 < rs[1] < 0.55 * rs[0] else None)(s.rate_status()),
            "cargo_full": s.cargo_full and (time.time() - s.cargo_ts) < 300,
            "drones_idle": s.drones_idle(),
            "laser_stalled": s.laser_stalled(),
            "hold_isk": round(hold_isk), "hold_m3": round(hold_m3),
            "hold_prices": hold_prices,
            "mine_idle": round(time.time() - s.last_ore_ts) if s.last_ore_ts else None,
            "idle_thr": round(s.idle_threshold(int(CONFIG.get("idle_warn", 240) or 0))),
            "name": s.name, "session_min": round(mins),
            "system": chatwatch.systems.get(s.char_id, "?"),
            "ores": ores, "m3": round(m3), "ore_isk": round(ore_isk),
            "m3h": round(m3 / mins * 60), "bounty": s.bounty, "kills": s.kills,
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


CALC_CACHE = {}  # region -> {"ts": Zeit, "prices": {typeID: (buy, sell)}}
CALC_LOCK = threading.Lock()


def hub_prices(region, ids):
    """Buy/Sell-Preise für die angefragten Typen in einer Region, 15 min Cache."""
    with CALC_LOCK:
        e = CALC_CACHE.get(region)
        if e and time.time() - e["ts"] < PRICE_REFRESH and ids <= set(e["prices"]):
            return dict(e["prices"])
    url = (f"https://market.fuzzwork.co.uk/aggregates/?region={region}"
           f"&types={','.join(map(str, sorted(ids)))}")
    with urllib.request.urlopen(url, timeout=15) as r:
        data = json.load(r)
    fetched = {int(k): (float(v["buy"]["max"]), float(v["sell"]["min"]))
               for k, v in data.items()}
    with CALC_LOCK:
        merged = CALC_CACHE.get(region, {}).get("prices", {})
        merged.update(fetched)
        CALC_CACHE[region] = {"ts": time.time(), "prices": merged}
        return dict(merged)


def parse_calc_text(text):
    """Zeilen wie 'Compressed Veldspar<TAB>49.105' (Frachtraum-Kopie) oder
    'Compressed Scordite 42000' in (Typname, Menge) übersetzen."""
    names = sorted(ORE_TYPES, key=len, reverse=True)
    items, unknown = {}, []
    for raw in (text or "").splitlines():
        line = raw.strip()
        if not line:
            continue
        low = line.lower()
        match = next((n for n in names if low.startswith(n.lower())), None)
        if not match:
            unknown.append(line.split("\t")[0][:40])
            continue
        rest = line[len(match):].lstrip("*").split("\t")
        qty = 1
        for part in rest:
            m = NUM_RE.search(STRIP_RE.sub("", part))
            if m and num(m.group(1)) > 0:
                qty = num(m.group(1))
                break
        items[match] = items.get(match, 0) + qty
    return items, unknown


def calc_hubs(text):
    items, unknown = parse_calc_text(text)
    if not items:
        return {"ok": True, "items": [], "unknown": unknown}
    ids = {ORE_TYPES[n]["typeID"] for n in items}
    hubs, jita = {}, {}
    for rid, rname in REGIONS.items():
        try:
            pm = hub_prices(rid, ids)
        except Exception:
            hubs[rid] = {"name": rname, "error": True}
            continue
        if rid == "10000002":
            jita = pm
        hubs[rid] = {"name": rname,
                     "buy": round(sum(q * pm.get(ORE_TYPES[n]["typeID"], (0, 0))[0]
                                      for n, q in items.items())),
                     "sell": round(sum(q * pm.get(ORE_TYPES[n]["typeID"], (0, 0))[1]
                                       for n, q in items.items()))}
    rows = [{"name": n, "qty": q,
             "m3": round(q * ORE_TYPES[n].get("volume", 0)),
             "isk": round(q * jita.get(ORE_TYPES[n]["typeID"], (0, 0))[0])}
            for n, q in items.items()]
    rows.sort(key=lambda r: -r["isk"])
    return {"ok": True, "items": rows, "hubs": hubs, "unknown": unknown,
            "m3": round(sum(r["m3"] for r in rows))}


def query_summary():
    """Geminert-Wert heute, gestern und letzte 7 Tage (ISK und m3) für die Ertrags-Leiste."""
    pm = prices.get(CONFIG["region"])
    today = datetime.now(timezone.utc).date()
    isk, m3 = {}, {}
    # Nur Roherz zählen: das Komprimat ist dasselbe Material, sonst zählt es doppelt
    for day, cid, cname, kind, key, value in all_rows(days=8, kinds=("ore",)):
        i, v = ore_value(key, value, pm)
        isk[day] = isk.get(day, 0) + i
        m3[day] = m3.get(day, 0) + v
    t = today.strftime("%Y-%m-%d")
    y = (today - timedelta(days=1)).strftime("%Y-%m-%d")
    week = {(today - timedelta(days=n)).strftime("%Y-%m-%d") for n in range(7)}
    return {"today": round(isk.get(t, 0)), "yesterday": round(isk.get(y, 0)),
            "week": round(sum(v for d, v in isk.items() if d in week)),
            "m3_today": round(m3.get(t, 0)),
            "m3_week": round(sum(v for d, v in m3.items() if d in week))}


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
            "clip_watch": bool(CONFIG.get("clip_watch")),
            "autostart": autostart_path().exists(),
            "update": {"available": UPDATE_INFO["available"],
                       "latest": UPDATE_INFO["latest"]},
            "version": VERSION,
            "ingesting": not ingest.started_full,
            "progress": ingest.progress, "prices_loaded": bool(prices.get(CONFIG["region"])),
            "watchlist": CONFIG.get("watchlist", []), "goal": CONFIG.get("goal"),
            "esi": {"client_id": (CONFIG.get("esi") or {}).get("client_id", ""),
                    "cb": esi.redirect_uri(),
                    "chars": [{"name": n, "status": esi.status.get(n, "warte auf Abgleich …"),
                               "ship": c.get("ship"), "wallet": c.get("wallet")}
                              for n, c in (CONFIG.get("esi") or {}).get("chars", {}).items()]},
            "alerts": alerts.list()}


def query_missions():
    """Missions-Statistik aus dem Wallet-Journal: Tage, Quellen, Agenten, Chars.
    Bounties aus bekannten Mining-Systemen bleiben draussen (Belt-Ratten)."""
    mine_sys = CONFIG.get("mine_systems") or {}
    mine_ids = {i for i in mine_sys.values() if i}
    rows = DB.execute(
        "SELECT char, ts, ref_type, amount, party, ctx FROM journal").fetchall()
    days, agents, chars = {}, {}, {}
    for char, ts, ref, amount, party, ctx in rows:
        if ref in ("bounty_prizes", "bounty_prize") and ctx in mine_ids:
            continue
        day = datetime.fromtimestamp(ts, timezone.utc).strftime("%Y-%m-%d")
        d = days.setdefault(day, {"day": day, "missions": 0, "reward": 0,
                                  "bonus": 0, "bounty": 0, "total": 0})
        c = chars.setdefault(char, {"char": char, "missions": 0, "total": 0})
        d["total"] += amount
        c["total"] += amount
        if ref == "agent_mission_reward":
            d["missions"] += 1
            d["reward"] += amount
            c["missions"] += 1
            if party:
                a = agents.setdefault(party, {"agent": party, "missions": 0, "isk": 0})
                a["missions"] += 1
                a["isk"] += amount
        elif ref == "agent_mission_time_bonus_reward":
            d["bonus"] += amount
            if party:
                agents.setdefault(party, {"agent": party, "missions": 0, "isk": 0})["isk"] += amount
        else:
            d["bounty"] += amount
    day_list = sorted(days.values(), key=lambda d: d["day"], reverse=True)
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    return {
        "mine_systems": sorted(n for n, i in mine_sys.items() if i),
        "linked": bool((CONFIG.get("esi") or {}).get("chars")),
        "today": days.get(today) or {"day": today, "missions": 0, "reward": 0,
                                     "bonus": 0, "bounty": 0, "total": 0},
        "days": [{k: (round(v) if isinstance(v, float) else v) for k, v in d.items()}
                 for d in day_list[:30]],
        "agents": sorted(({**a, "isk": round(a["isk"])} for a in agents.values()),
                         key=lambda a: -a["isk"])[:10],
        "chars": sorted(({**c, "total": round(c["total"])} for c in chars.values()),
                        key=lambda c: -c["total"])}


def _csv_cell(s):
    """Formel-Injection neutralisieren: Excel/Calc fuehren Zellen aus, die mit
    = + - @ beginnen. Solche Namen (aus Logs) mit ' entschaerfen, ; quoten."""
    s = str(s)
    if s[:1] in ("=", "+", "-", "@"):
        s = "'" + s
    if ";" in s or '"' in s or "\n" in s:
        s = '"' + s.replace('"', '""') + '"'
    return s


def export_csv():
    lines = ["day;char;kind;key;value"]
    for day, cid, cname, kind, key, value in all_rows():
        lines.append(";".join(_csv_cell(x) for x in (day, cname, kind, key, value)))
    return "\n".join(lines)


# ---------------------------------------------------------------- HTTP
def _host_ok(headers):
    """Schuetzt vor DNS-Rebinding: nur localhost-Hosts duerfen zugreifen.
    Eine fremde Website, die per Rebinding auf 127.0.0.1 zeigt, sendet ihren
    eigenen (fremden) Host-Header und wird hier abgewiesen."""
    host = (headers.get("Host") or "").rsplit(":", 1)[0].strip("[]").lower()
    return host in ("localhost", "127.0.0.1", "::1", "")


def _origin_ok(headers):
    """Schuetzt vor CSRF: Ein Origin (bei fetch/CORS gesetzt) muss localhost sein.
    Gleiche-Ursprung-Requests der eigenen Seite senden localhost oder gar keinen."""
    origin = headers.get("Origin")
    if not origin:
        return True  # klassische Navigation/Formular ohne Origin -> ok, Host-Check greift
    try:
        h = urllib.parse.urlparse(origin).hostname or ""
    except ValueError:
        return False
    return h.lower() in ("localhost", "127.0.0.1", "::1")


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

    def _deny(self, code=403):
        self.send_response(code)
        self.send_header("Content-Length", "0")
        self.end_headers()

    def do_GET(self):
        if not _host_ok(self.headers):
            return self._deny()
        p = self.path.split("?")[0]
        if p == "/data":
            view = (self.path.split("view=")[1].split("&")[0]
                    if "view=" in self.path else "live")
            data = {"state": state_info()}
            if view == "live":
                data["chars"] = snapshot_live()
                data["summary"] = query_summary()
            elif view == "month":
                data["days"] = query_month()
            elif view == "analyse":
                data["analyse"] = query_analyse()
            elif view == "intel":
                data["intel_auto"] = {"ts": clipwatch.ts, "names": clipwatch.names}
            elif view == "missionen":
                data["missions"] = query_missions()
                data["chars"] = snapshot_live()
            elif view == "rechner":
                pass  # der Rechner holt seine Daten per calc-POST
            else:
                data["total"] = query_total()
            self._send(json.dumps(data))
        elif p == "/sso/callback":
            qs = urllib.parse.parse_qs(self.path.split("?", 1)[1] if "?" in self.path else "")
            err = esi.callback(qs.get("code", [""])[0], qs.get("state", [""])[0])
            ok = err is None
            self._send("<html><head><meta charset='utf-8'><title>EVE Canary</title></head>"
                       "<body style='font-family:sans-serif;background:#101418;color:#dfe7ef;"
                       "text-align:center;padding-top:90px'><div style='font-size:42px'>"
                       + ("🐤" if ok else "⚠️") + "</div><h2>"
                       + ("Charakter verbunden!" if ok else "Login fehlgeschlagen")
                       + "</h2><p>" + (err or "Du kannst dieses Fenster schließen. "
                       "Canary gleicht Laderaum und Wallet ab jetzt automatisch ab.")
                       + "</p></body></html>", "text/html; charset=utf-8")
        elif p == "/export.csv":
            self._send(export_csv(), "text/csv; charset=utf-8", "eve_dashboard_export.csv")
        elif p == "/export.json":
            self._send(json.dumps({"month": query_month(), "total": query_total(),
                                   "analyse": query_analyse()}, indent=1),
                       "application/json", "eve_dashboard_export.json")
        else:
            self._send(PAGE, "text/html; charset=utf-8")

    def do_POST(self):
        if not _host_ok(self.headers) or not _origin_ok(self.headers):
            return self._deny()
        length = int(self.headers.get("Content-Length", 0))
        try:
            body = json.loads(self.rfile.read(length) or b"{}")
        except Exception:
            body = {}
        action = body.get("action")
        if action == "region" and str(body.get("region")) in REGIONS:
            CONFIG["region"] = str(body["region"])
        elif action == "mode" and body.get("mode") in ("all", "fresh"):
            with ingest.lock:
                # filecache leeren, damit ein Wechsel fresh->all die geskippten
                # Alt-Logs wirklich nachimportiert (Cache-Check greift sonst davor).
                ingest.filecache.clear()
                ingest.last_scan = 0
            CONFIG["mode"] = body["mode"]
        elif action == "reset":
            do_reset_baseline()
        elif action == "clear_baseline":
            clear_baseline()
        elif action == "idle_warn":
            CONFIG["idle_warn"] = max(0, int(body.get("seconds") or 0))
        elif action == "autostart":
            set_autostart(bool(body.get("on")))
        elif action == "clip_watch":
            CONFIG["clip_watch"] = bool(body.get("on"))
        elif action == "calc":
            self._send(json.dumps(calc_hubs(body.get("text") or "")))
            return
        elif action == "threat_scan":
            names = [str(n).strip() for n in body.get("names", [])][:200]
            names = [n for n in names if n]
            results = threat.request(names, prio=True)
            self._send(json.dumps({"ok": True, "results": results,
                                   "pending": threat.pending()}))
            return
        elif action == "esi_client":
            esi.cfg()["client_id"] = str(body.get("client_id") or "").strip()
        elif action == "esi_login":
            url = esi.login_url()
            self._send(json.dumps({"ok": bool(url), "url": url,
                                   "error": None if url else "Zuerst Client-ID speichern."}))
            return
        elif action == "esi_forget":
            char = str(body.get("char") or "")
            with CONFIG_LOCK:
                esi.cfg().get("chars", {}).pop(char, None)
                esi.status.pop(char, None)
                hw_entry = (CONFIG.get("heavy_water") or {}).get(char)
                if hw_entry and hw_entry.get("esi"):
                    CONFIG["heavy_water"].pop(char, None)
        elif action == "heavy_water":
            char = str(body.get("char") or "")
            units = body.get("units")
            with CONFIG_LOCK:
                hw = CONFIG.setdefault("heavy_water", {})
                if char and units is None:
                    hw.pop(char, None)
                elif char:
                    hw[char] = {"units": max(0.0, float(units)),
                                "fill": max(0.0, float(units)),
                                "core": "t2" if body.get("core") == "t2" else "t1",
                                "ts": time.time(), "warned": False, "ck": 0}
        elif action == "laser_ok":
            with ingest.lock:
                for s in ingest.sessions.values():
                    if s.name == body.get("char"):
                        s.lasers_off.pop(body.get("tool"), None)
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
/* ---------- Photon-Skin: EVE-Fensterstil — Nebel, Transparenz+Blur, Titelleisten, Eck-Klammern */
html[data-skin=photon]{--bg:#0a0d0f;--card:rgba(13,17,19,.80);--inset:rgba(255,255,255,.04);
--line:rgba(130,150,158,.16);--txt:#c9d1d4;--dim:#7d888e;--cyan:#5fc1d4;--red:#c8443d;--green:#7db35c;
--gold:#d9a33c;--white:#eef1f2}
html[data-skin=photon] body,html[data-skin=photon] dialog,html[data-skin=photon] .btn,
html[data-skin=photon] input,html[data-skin=photon] textarea{font-family:'Bahnschrift','Segoe UI',system-ui,sans-serif}
/* Nebel + Sternenfeld (rein CSS, drei Stern-Ebenen als gekachelte Punkte) */
html[data-skin=photon] body{background:
 radial-gradient(1px 1px at 21% 33%,rgba(255,255,255,.5) 0,transparent 100%),
 radial-gradient(1px 1px at 67% 12%,rgba(255,255,255,.35) 0,transparent 100%),
 radial-gradient(1.5px 1.5px at 44% 76%,rgba(200,230,255,.4) 0,transparent 100%),
 radial-gradient(1px 1px at 86% 58%,rgba(255,255,255,.3) 0,transparent 100%),
 radial-gradient(1400px 900px at 78% -12%,rgba(52,102,84,.28),transparent 62%),
 radial-gradient(1100px 800px at 6% 108%,rgba(30,58,78,.30),transparent 58%),
 radial-gradient(700px 500px at 34% 42%,rgba(74,94,60,.10),transparent 60%),#0a0d0f;
 background-size:290px 290px,210px 210px,340px 340px,260px 260px,auto,auto,auto,auto;
 background-attachment:fixed}
/* Holo-Scanlines, extrem dezent */
html[data-skin=photon] body::after{content:"";position:fixed;inset:0;z-index:9999;pointer-events:none;
 background:repeating-linear-gradient(0deg,rgba(255,255,255,.012) 0 1px,transparent 1px 3px)}
/* Alles kantig */
html[data-skin=photon] .card,html[data-skin=photon] .stat,html[data-skin=photon] .alert,
html[data-skin=photon] .cardwarn,html[data-skin=photon] dialog,html[data-skin=photon] .btn,
html[data-skin=photon] input,html[data-skin=photon] textarea,html[data-skin=photon] select.pill,
html[data-skin=photon] .pill,html[data-skin=photon] .laserok,html[data-skin=photon] header{border-radius:0}
/* Karten = EVE-Fenster: transluzent, Blur, Eck-Klammern wie am Zielobjekt */
html[data-skin=photon] .card,html[data-skin=photon] header,html[data-skin=photon] dialog{
 background:var(--card);backdrop-filter:blur(9px);-webkit-backdrop-filter:blur(9px);
 border:1px solid var(--line);box-shadow:0 12px 30px rgba(0,0,0,.45)}
html[data-skin=photon] .card{position:relative;overflow:hidden}
html[data-skin=photon] .card::before,html[data-skin=photon] .card::after{
 content:"";position:absolute;width:11px;height:11px;pointer-events:none;opacity:.5}
html[data-skin=photon] .card::before{top:0;left:0;border-top:1px solid #dfe7ea;border-left:1px solid #dfe7ea}
html[data-skin=photon] .card::after{bottom:0;right:0;border-bottom:1px solid #dfe7ea;border-right:1px solid #dfe7ea}
/* Kartenkopf = Fenster-Titelleiste */
html[data-skin=photon] .chead{background:linear-gradient(180deg,rgba(255,255,255,.07),rgba(255,255,255,.02));
 margin:-14px -16px 10px -16px;padding:9px 14px;border-bottom:1px solid rgba(0,0,0,.55)}
html[data-skin=photon] .card.min .chead{margin:-10px -16px -10px -16px;border-bottom:none}
html[data-skin=photon] .char{color:var(--gold);font-weight:400;letter-spacing:.4px}
html[data-skin=photon] .sys{color:var(--txt);opacity:.7}
/* Kopfzeile als Leiste */
html[data-skin=photon] header{padding:8px 14px;margin-bottom:12px}
html[data-skin=photon] h1{letter-spacing:4px;font-weight:300}
html[data-skin=photon] h1 b{color:var(--gold);font-weight:400}
/* Navigation wie EVE-Tab-Leiste */
html[data-skin=photon] nav{border-bottom:1px solid var(--line);gap:0}
html[data-skin=photon] nav span{text-transform:uppercase;letter-spacing:1.4px;font-size:11px;
 border-right:1px solid rgba(130,150,158,.10);padding:8px 18px}
html[data-skin=photon] nav span:hover{background:rgba(95,193,212,.06);color:var(--txt)}
html[data-skin=photon] nav span.on{color:var(--white);background:rgba(255,255,255,.05);
 border-bottom:2px solid var(--gold)}
/* Typo-Details */
html[data-skin=photon] .sect{text-transform:uppercase;letter-spacing:1.4px;font-size:10px}
html[data-skin=photon] th{text-transform:uppercase;font-size:10px;letter-spacing:1px;font-weight:400}
html[data-skin=photon] .stat .l{text-transform:uppercase;letter-spacing:.6px;font-size:9.5px}
html[data-skin=photon] .stat .v{font-weight:300;letter-spacing:.3px}
/* Zeilen-Hover wie Overview-Selektion */
html[data-skin=photon] .pf{border-radius:1px;border:1px solid var(--line)}
html[data-skin=photon] tr:hover td{background:rgba(95,193,212,.07)}
html[data-skin=photon] td{border-top-color:rgba(130,150,158,.10)}
/* Bedienelemente */
html[data-skin=photon] .btn{text-transform:uppercase;letter-spacing:.8px;font-size:11px;
 background:rgba(255,255,255,.04)}
html[data-skin=photon] .btn:hover{border-color:var(--cyan);color:var(--white);
 box-shadow:inset 0 0 10px rgba(95,193,212,.12),0 0 8px rgba(95,193,212,.18)}
html[data-skin=photon] .pill{background:rgba(255,255,255,.03)}
html[data-skin=photon] .pill.on{background:rgba(95,193,212,.12);color:var(--cyan);border-color:var(--cyan)}
html[data-skin=photon] .stat{border:1px solid rgba(130,150,158,.10);background:rgba(255,255,255,.03);
 transition:border-color .12s,box-shadow .12s}
/* Hover wie ein EVE-Inventar-Slot: Teal-Rahmen mit Eck-Klammern und Glimmen */
html[data-skin=photon] .stat:hover{border-color:rgba(95,193,212,.55);
 box-shadow:0 0 10px rgba(95,193,212,.25),inset 0 0 14px rgba(95,193,212,.06);
 background-image:
  linear-gradient(var(--cyan),var(--cyan)),linear-gradient(var(--cyan),var(--cyan)),
  linear-gradient(var(--cyan),var(--cyan)),linear-gradient(var(--cyan),var(--cyan)),
  linear-gradient(var(--cyan),var(--cyan)),linear-gradient(var(--cyan),var(--cyan)),
  linear-gradient(var(--cyan),var(--cyan)),linear-gradient(var(--cyan),var(--cyan));
 background-repeat:no-repeat;
 background-size:9px 2px,2px 9px,9px 2px,2px 9px,9px 2px,2px 9px,9px 2px,2px 9px;
 background-position:top left,top left,top right,top right,bottom left,bottom left,bottom right,bottom right}
html[data-skin=photon] .alert{border-left-width:3px;backdrop-filter:blur(9px)}
html[data-skin=photon] dialog::backdrop{background:rgba(2,4,5,.75);backdrop-filter:blur(3px)}
html[data-skin=photon] ::-webkit-scrollbar{width:9px;height:9px}
html[data-skin=photon] ::-webkit-scrollbar-thumb{background:#2b3236;border:2px solid #0b0e10}
html[data-skin=photon] ::-webkit-scrollbar-track{background:transparent}
*{margin:0;box-sizing:border-box;font-family:'Segoe UI',system-ui,sans-serif}
body{background:var(--bg);color:var(--txt);padding:18px;transition:background .2s}
html[data-fs="2"] body{zoom:1.15}
html[data-fs="3"] body{zoom:1.3}
header{display:flex;align-items:center;gap:10px;flex-wrap:wrap;margin-bottom:10px}
h1{font-size:14px;font-weight:600;letter-spacing:2px;color:var(--dim)}
h1 b{color:var(--cyan)}
.byline{font-size:10px;color:var(--dim);letter-spacing:1.6px;font-weight:400;text-transform:uppercase;opacity:.8}
/* ---------- Boot-Screen beim Erst-Einlesen */
#boot{position:fixed;inset:0;z-index:2000;background:var(--bg);display:flex;
 align-items:center;justify-content:center;opacity:1;transition:opacity .8s}
/* hidden-Attribut MUSS gewinnen: sonst überdeckt der Boot-Screen beim
   Schnellstart (DB schon gefüllt) dauerhaft das fertige Dashboard. */
#boot[hidden]{display:none}
#boot.fade{opacity:0;pointer-events:none}
.bootbox{text-align:center;width:min(440px,84vw)}
.bootbird{font-size:64px;animation:bootpulse 1.6s ease-in-out infinite}
@keyframes bootpulse{0%,100%{transform:scale(1)}50%{transform:scale(1.14)}}
.bootbox h2{letter-spacing:7px;font-weight:300;color:var(--txt);margin:12px 0 2px;font-size:22px}
.bootbox h2 b{color:var(--cyan);font-weight:600}
.bootby{color:var(--gold);font-size:11px;letter-spacing:2.5px;text-transform:uppercase;margin-bottom:26px}
.boottext{color:var(--dim);font-size:13px;margin-bottom:12px}
.bootbar{height:10px;border:1px solid var(--line);border-radius:6px;overflow:hidden;background:var(--card)}
#bootfill{height:100%;width:0%;background:linear-gradient(90deg,var(--cyan),var(--gold));
 transition:width .5s;box-shadow:0 0 12px rgba(53,200,232,.4)}
.bootnum{color:var(--txt);font-size:13px;margin-top:10px}
.boothint{color:var(--dim);font-size:11px;margin-top:18px;line-height:1.5}
html[data-skin=photon] .bootbar,html[data-skin=photon] #bootfill{border-radius:1px}
/* ---------- Optionen-Gruppen */
.optgroup{background:var(--inset);border:1px solid var(--line);border-radius:8px;
 padding:12px 14px;margin-bottom:10px}
.optgroup .sect{margin-top:0}
.btnrow{display:flex;gap:6px;flex-wrap:wrap;margin-top:8px}
html[data-skin=photon] .optgroup{border-radius:1px}
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
padding:7px 10px;font-size:12px;font-weight:600;margin-bottom:8px;overflow:hidden}
.cardwarn.drone{border-color:var(--red);color:var(--red)}
.warnbadge{color:var(--gold);font-weight:600}
.warnbadge.drone{color:var(--red)}
.pill.upd{border-color:var(--gold);color:var(--gold);animation:updpulse 2.4s ease-in-out infinite}
@keyframes updpulse{0%,100%{box-shadow:0 0 0 rgba(232,198,69,0)}50%{box-shadow:0 0 9px rgba(232,198,69,.45)}}
.laserok{float:right;border:1px solid var(--line);border-radius:20px;padding:1px 9px;
color:var(--dim);cursor:pointer;font-weight:400;margin-left:8px}
.laserok:hover{color:var(--fg);border-color:var(--fg)}
.hwset{cursor:pointer;opacity:.55}
.hwset:hover{opacity:1}
tr.lvl-red td{background:rgba(232,86,79,.10)}
tr.lvl-yellow td{background:rgba(228,179,76,.07)}
#intelTbl a{color:inherit}
#grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(420px,1fr));gap:14px;align-items:start}
@media (max-width:900px){#grid{grid-template-columns:1fr}}
#hero:not(:empty){margin-bottom:14px}
select.pill{appearance:none;-webkit-appearance:none;outline:none;background:var(--card);
border:1px solid var(--line);color:var(--dim);font-size:11px;padding:4px 11px;border-radius:20px;cursor:pointer}
.card{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:14px 16px}
.char{font-size:15px;font-weight:600;color:var(--white)}
.chead{display:flex;align-items:center;gap:8px;cursor:pointer;user-select:none;flex-wrap:wrap}
.chead .mini{margin-left:auto;font-size:12px;color:var(--dim);text-align:right;min-width:0}
.pf{width:26px;height:26px;border-radius:5px;flex:none;background:var(--inset)}
.pf-none{display:flex;align-items:center;justify-content:center;font-size:14px;
 border:1px dashed var(--dim);color:var(--dim);cursor:pointer;opacity:.7}
.pf-none:hover{opacity:1;border-color:var(--cyan);color:var(--cyan)}
.esinudge{border:1px solid var(--cyan);border-radius:7px;padding:8px 11px;margin:2px 0 10px 0;
 font-size:12px;color:var(--txt);background:rgba(53,200,232,.08)}
html[data-skin=photon] .esinudge{border-radius:1px}
#esiChars{font-size:13px;line-height:1.7;margin-bottom:8px}
#esiSetup{margin-top:8px}
#esiSetup>summary{cursor:pointer;font-size:12px;color:var(--dim);user-select:none;list-style:none}
#esiSetup>summary::-webkit-details-marker{display:none}
#esiSetup>summary::before{content:"▸ ";color:var(--cyan)}
#esiSetup[open]>summary::before{content:"▾ "}
#esiSetup>summary:hover{color:var(--txt)}
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
padding:20px 22px;max-width:620px;width:94%}
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
<div id="boot" hidden>
 <div class="bootbox">
  <div class="bootbird">🐤</div>
  <h2>EVE <b>CANARY</b></h2>
  <div class="bootby">by Askend</div>
  <div class="boottext">Logdateien werden gelesen und analysiert …</div>
  <div class="bootbar"><div id="bootfill"></div></div>
  <div class="bootnum" id="bootnum"></div>
  <div class="boothint">Das passiert nur beim ersten Start. Je nach Log-Bestand kann es ein paar Minuten dauern,
  danach öffnet sich das Dashboard von selbst.</div>
 </div>
</div>
<header>
 <h1>🐤 EVE <b>CANARY</b> <span class="byline">by Askend</span></h1>
 <select class="pill" id="charFilter" title="Charakter-Filter"><option value="">Alle Charaktere</option></select>
 <span class="pill" id="collapseAll">Alle einklappen</span>
 <div class="pills" id="regions"></div>
 <span class="pill upd" id="updBadge" hidden title="Neue Version verfügbar, Klick installiert sie"></span>
 <span class="pill" id="ovToggle" title="Always-on-top Mini-Overlay (Chrome/Edge)">◱ Overlay</span>
 <span class="pill" id="fontsize" title="Schriftgröße (3 Stufen)">A</span>
 <span class="pill" id="theme" title="Dark/Light">◐</span>
 <span class="pill" id="gear">⚙ Optionen</span>
</header>
<nav>
 <span data-v="live" class="on">Live</span>
 <span data-v="month">30 Tage</span>
 <span data-v="total">Gesamt</span>
 <span data-v="analyse">Analyse</span>
 <span data-v="intel">🚦 Intel</span>
 <span data-v="missionen">🎯 Missionen</span>
 <span data-v="rechner">🧮 Ore Calculator</span>
</nav>
<div id="alerts"></div>
<div id="hero"></div>
<div id="grid"></div>
<div id="empty" hidden></div>

<dialog id="opts">
 <h2>⚙ Optionen <span class="byline">EVE Canary by Askend</span></h2>

 <div class="optgroup">
  <div class="sect">🎨 Darstellung</div>
  <label><input type="radio" name="skin" value=""> Klassisch (das gewohnte Canary-Design)</label>
  <label><input type="radio" name="skin" value="photon"> Photon (angelehnt ans EVE-Interface: dunkel, kantig, Gold-Akzente)</label>
  <div class="btnrow"><button class="btn" id="ovBtn">◱ Mini-Overlay öffnen/schließen</button></div>
  <div class="hint">Das Overlay ist ein schwebendes Always-on-top-Fenster mit Status und Alarmen,
  bleibt über dem EVE-Client (Fenstermodus/randlos). Benötigt Chrome oder Edge, Start nur per Klick.</div>
 </div>

 <div class="optgroup">
  <div class="sect">🔔 Alarme &amp; Wachen</div>
  <label><input type="checkbox" id="sndPvp" checked> Sound bei Spieler-Angriff</label>
  <label><input type="checkbox" id="sndDep" checked> Sound bei leerem Asteroiden</label>
  <label><input type="checkbox" id="sndWatch" checked> Sound bei Watchlist-Treffer</label>
  <div style="display:flex;gap:6px;align-items:center;margin-top:8px">
   <input type="number" id="idleWarn" min="0" step="30" style="width:110px">
   <span class="hint" style="margin:0">Sekunden ohne Erz bis zur Stillstand-Warnung (0 = aus)</span>
   <button class="btn" id="saveIdle">Speichern</button>
  </div>
  <div class="sect" style="margin-top:12px">Watchlist (Local-Chat, ein Name pro Zeile)</div>
  <textarea id="watchlist" rows="3" placeholder="Bekannte Ganker..."></textarea>
  <div class="btnrow">
   <button class="btn" id="saveWatch">Watchlist speichern</button>
   <button class="btn" id="notifPerm">Desktop-Benachrichtigungen erlauben</button>
  </div>
 </div>

 <div class="optgroup">
  <div class="sect">🎯 Ziel &amp; Zähler</div>
  <div style="display:flex;gap:6px">
   <input type="number" id="goalIsk" placeholder="ISK-Ziel, z.B. 1000000000">
   <input type="date" id="goalDate">
  </div>
  <div class="btnrow">
   <button class="btn" id="saveGoal">Ziel speichern</button>
   <button class="btn" id="clearGoal">Ziel löschen</button>
   <button class="btn warn" id="reset">Auswertung ab jetzt neu lesen</button>
   <button class="btn" id="unreset">Baseline aufheben</button>
  </div>
  <div class="hint" id="baseinfo"></div>
 </div>

 <div class="optgroup">
  <div class="sect esi">🔑 EVE-Login (ESI): automatischer Abgleich</div>
  <div class="esinudge" id="esiNudge" hidden>✨ Noch kein Charakter verbunden. Mit dem EVE-Login zeigt Canary
   automatisch Portrait, aktuelles Schiff, Wallet-Stand und den Heavy-Water-Vorrat, ganz ohne manuelles Eintragen.</div>
  <div id="esiChars"></div>
  <div class="btnrow"><button class="btn" id="esiLogin">+ Charakter verbinden</button></div>
  <details id="esiSetup">
   <summary>Einrichtung &amp; Client-ID</summary>
   <div class="hint" style="margin-top:8px">Einmalig auf <a href="https://developers.eveonline.com" target="_blank" rel="noopener">developers.eveonline.com</a>
   eine Anwendung anlegen („Authentication &amp; API Access", Scopes: <b>esi-assets.read_assets.v1,
   esi-location.read_ship_type.v1, esi-wallet.read_character_wallet.v1</b>,
   Callback-URL: <b id="cbUrl"></b>), dann die Client-ID hier eintragen.</div>
   <input type="text" id="esiClient" placeholder="Client-ID deiner ESI-Anwendung">
   <div class="btnrow"><button class="btn" id="saveEsi">Client-ID speichern</button></div>
  </details>
 </div>

 <div class="optgroup">
  <div class="sect">🖥 System &amp; Daten</div>
  <label><input type="checkbox" id="autostart"> Canary beim Windows-Start automatisch mitstarten (still im Hintergrund, ohne Konsolenfenster)</label>
  <label style="margin-top:8px"><input type="radio" name="mode" value="all"> Alle vorhandenen Logs auswerten</label>
  <label><input type="radio" name="mode" value="fresh"> Nur ab Installation zählen</label>
  <div class="btnrow">
   <button class="btn" id="checkUpd">Nach Update suchen</button>
   <button class="btn" id="doUpd" hidden>Update installieren</button>
   <button class="btn" id="backup">Backup erstellen</button>
   <a class="btn" href="/export.csv" style="text-decoration:none">Export CSV</a>
   <a class="btn" href="/export.json" style="text-decoration:none">Export JSON</a>
  </div>
  <div class="hint" id="verinfo"></div>
  <div class="hint" id="updstatus"></div>
  <div class="note" id="loginfo"></div>
 </div>

 <div style="text-align:right"><button class="btn" id="close">Schließen</button></div>
</dialog>

<script>
const $=s=>document.querySelector(s);
const fmt=n=>Math.round(n).toLocaleString();
const fmtM=n=>n>=1e9?(n/1e9).toFixed(2)+' Mrd':n>=1e6?(n/1e6).toFixed(1)+' M':fmt(n);
// HTML-Escape: Spieler-/Corp-/Schiffsnamen aus Logs, ESI und zKillboard sind
// fremdbestimmt und dürfen nie ungefiltert in innerHTML landen (XSS).
const esc=s=>String(s==null?'':s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
function lsGet(key,fallback){try{const v=localStorage.getItem(key);return v==null?fallback:JSON.parse(v);}catch(e){return fallback;}}
const VIEWS=['live','month','total','analyse','intel','missionen','rechner'];
let view=location.pathname.replace(/^\\//,'')||'live', state=null, lastAlertId=Number(localStorage.getItem('lastAlertId')||0);
if(!VIEWS.includes(view))view='live';
window.addEventListener('popstate',()=>{
 view=location.pathname.replace(/^\\//,'')||'live';
 if(!VIEWS.includes(view))view='live';
 document.querySelectorAll('nav span').forEach(x=>x.classList.toggle('on',x.dataset.v===view));
 tick();
});

const savedTheme=localStorage.getItem('theme');
if(savedTheme)document.documentElement.dataset.theme=savedTheme;
else if(matchMedia('(prefers-color-scheme: light)').matches)document.documentElement.dataset.theme='light';
const savedSkin=localStorage.getItem('skin');
if(savedSkin)document.documentElement.dataset.skin=savedSkin;
$('#autostart').onchange=async()=>{const r=await post({action:'autostart',on:$('#autostart').checked});if(r.state)state=r.state;syncOpts();};
document.querySelectorAll('#opts input[name=skin]').forEach(r=>r.onchange=()=>{
 if(r.value)document.documentElement.dataset.skin=r.value;
 else delete document.documentElement.dataset.skin;
 localStorage.setItem('skin',r.value);
});
$('#theme').onclick=()=>{const t=document.documentElement.dataset.theme==='light'?'dark':'light';
 document.documentElement.dataset.theme=t;localStorage.setItem('theme',t);};

const FS_LABEL={1:'A',2:'A+',3:'A++'};
let fontsize=Number(localStorage.getItem('fontsize')||1);
function applyFs(){
 document.documentElement.dataset.fs=fontsize;
 $('#fontsize').textContent=FS_LABEL[fontsize];
}
applyFs();
$('#fontsize').onclick=()=>{fontsize=fontsize%3+1;localStorage.setItem('fontsize',fontsize);applyFs();};

document.querySelectorAll('nav span').forEach(el=>el.onclick=()=>{
 document.querySelectorAll('nav span').forEach(x=>x.classList.remove('on'));
 el.classList.add('on');view=el.dataset.v;
 history.pushState(null,'','/'+(view==='live'?'':view));tick();});
document.querySelectorAll('nav span').forEach(x=>x.classList.toggle('on',x.dataset.v===view));

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
$('#saveEsi').onclick=async()=>{const r=await post({action:'esi_client',client_id:$('#esiClient').value.trim()});if(r.state)state=r.state;syncOpts();};
$('#esiLogin').onclick=async()=>{
 const r=await post({action:'esi_login'});
 if(r.url){window.open(r.url,'_blank');return;}
 // Keine Client-ID hinterlegt: gezielt zur Einrichtung führen statt nur meckern
 $('#esiSetup').open=true;
 $('#esiClient').focus();
 $('#esiClient').scrollIntoView({block:'center'});
};
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
 document.querySelectorAll('#opts input[name=skin]').forEach(r=>r.checked=r.value===(document.documentElement.dataset.skin||''));
 $('#autostart').checked=!!state.autostart;
 $('#baseinfo').textContent=state.baseline_day?('Aktive Baseline: zählt seit '+state.baseline_day+' (UTC).'):'Keine Baseline aktiv.';
 $('#loginfo').textContent='Log-Ordner: '+(state.log_dir||'nicht gefunden!')+' · Dateien: '+state.progress.done+'/'+state.progress.total;
 $('#watchlist').value=(state.watchlist||[]).join('\\n');
 $('#idleWarn').value=state.idle_warn??240;
 $('#verinfo').textContent='Installiert: EVE Canary v'+(state.version||'?')+' · by Askend';
 if(state.goal){$('#goalIsk').value=state.goal.isk;$('#goalDate').value=state.goal.deadline||'';}
 if(state.esi){
  $('#cbUrl').textContent=state.esi.cb;
  if(document.activeElement!==$('#esiClient'))$('#esiClient').value=state.esi.client_id||'';
  const nchars=(state.esi.chars||[]).length;
  $('#esiNudge').hidden=nchars>0;
  // Anleitung nur aufklappen, solange noch nichts verbunden ist
  // Einrichtungstext bleibt standardmäßig eingeklappt (aufklappbar bei Bedarf,
  // oder automatisch beim Klick auf "Charakter verbinden" ohne Client-ID).
  $('#esiChars').innerHTML=(state.esi.chars||[]).map(c=>
   '👤 <b>'+esc(c.name)+'</b>: '+esc(c.status)+(c.ship?' · '+esc(c.ship):'')+(c.wallet!=null?' · Wallet: '+fmtM(c.wallet)+' ISK':'')+
   ' <span class="esiForget" data-char="'+esc(c.name)+'" style="cursor:pointer;text-decoration:underline">trennen</span>'
  ).join('<br>')||'';
  document.querySelectorAll('.esiForget').forEach(b=>b.onclick=async()=>{
   const r=await post({action:'esi_forget',char:b.dataset.char});if(r.state)state=r.state;syncOpts();});
 }
}

function beep(freq,times,dur){
 try{
  const ctx=beep.ctx||(beep.ctx=new (window.AudioContext||window.webkitAudioContext)());
  if(ctx.state==='suspended')ctx.resume();  // Autoplay-Sperre: erst nach User-Geste hörbar
  for(let i=0;i<times;i++){
   const o=ctx.createOscillator(),g=ctx.createGain();
   o.frequency.value=freq;o.connect(g);g.connect(ctx.destination);
   const t=ctx.currentTime+i*(dur+0.08);
   g.gain.setValueAtTime(0.15,t);g.gain.exponentialRampToValueAtTime(0.001,t+dur);
   o.start(t);o.stop(t+dur);}
 }catch(e){}}
// AudioContext bei der ersten Nutzer-Geste anlegen/aufwecken, damit spätere
// Alarme im Hintergrund-Tab wirklich tönen (Browser blockiert Autoplay sonst).
window.addEventListener('pointerdown',()=>{
 try{const ctx=beep.ctx||(beep.ctx=new (window.AudioContext||window.webkitAudioContext)());
  if(ctx.state==='suspended')ctx.resume();}catch(e){}
},{once:true});

function handleAlerts(){
 const list=state.alerts||[];
 const now=Date.now()/1000;
 $('#alerts').innerHTML=list.filter(a=>now-a.ts<300).slice(-4).reverse().map(a=>{
  const t=new Date(a.ts*1000).toLocaleTimeString();
  return `<div class="alert ${a.kind}">[${t}] ${esc(a.text)}</div>`}).join('');
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
  else if(a.kind==='intel'){
   if($('#sndWatch').checked)beep(770,3,0.16);
   if(Notification.permission==='granted')new Notification('EVE: Bedrohung erkannt!',{body:a.text});
  }
  else if(a.kind==='hw'){
   if($('#sndDep').checked)beep(430,2,0.2);
   if(Notification.permission==='granted')new Notification('EVE: Heavy Water fast leer!',{body:a.text});
  }
  lastAlertId=a.id;
 }
 localStorage.setItem('lastAlertId',lastAlertId);
}

let bootDone=false;
function bootScreen(){
 if(bootDone)return;
 const b=$('#boot'),p=(state&&state.progress)||{};
 if(state&&state.ingesting&&p.total>0&&p.done<p.total){
  b.hidden=false;
  const pct=Math.round(100*p.done/p.total);
  $('#bootfill').style.width=pct+'%';
  $('#bootnum').textContent=fmt(p.done)+' / '+fmt(p.total)+' Logdateien · '+pct+'%';
 }else if(!b.hidden){
  $('#bootfill').style.width='100%';
  $('#bootnum').textContent=fmt(p.total||0)+' Logdateien analysiert. Willkommen!';
  setTimeout(()=>b.classList.add('fade'),450);
  setTimeout(()=>{b.hidden=true;},1400);
  bootDone=true;
 }else bootDone=true;
}
function updateBadge(){
 const u=(state&&state.update)||{};
 const b=$('#updBadge');
 if(u.available&&u.latest){b.hidden=false;b.textContent='⬆ Update v'+u.latest;}
 else b.hidden=true;
}
$('#updBadge').onclick=async()=>{
 const v=(state&&state.update&&state.update.latest)||'?';
 if(!confirm('Update auf v'+v+' installieren? Canary startet danach automatisch neu.'))return;
 $('#updBadge').textContent='Update läuft …';
 const r=await post({action:'do_update'});
 if(r.ok&&r.updated)setTimeout(()=>location.reload(),4000);
 else{alert(r.error||r.message||'Update fehlgeschlagen.');updateBadge();}
};
function regionPills(){
 $('#regions').innerHTML=Object.entries(state.regions).map(([id,n])=>
  `<span class="pill ${id===state.region?'on':''}" data-r="${id}">${n}</span>`).join('');
 document.querySelectorAll('#regions .pill').forEach(p=>p.onclick=async()=>{
  await post({action:'region',region:p.dataset.r});tick();});
}

let collapsed=new Set(lsGet('collapsed',[]));
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
  // Auswahl aus localStorage wiederherstellen (beim ersten Render war value=''
  // gesetzt, bevor die Optionen existierten -> sonst Dropdown und Filter uneins).
  const cur=localStorage.getItem('charFilter')||'';
  sel.innerHTML='<option value="">Alle Charaktere</option>'+
   names.map(n=>`<option value="${esc(n)}">${esc(n)}</option>`).join('');
  sel.value=names.includes(cur)?cur:'';
  sel.dataset.opts=want;
 }
 const all=names.length&&names.every(n=>collapsed.has(n));
 $('#collapseAll').textContent=all?'Alle aufklappen':'Alle einklappen';
}
function heroTiles(label,today,yesterday,week,subToday,subWeek){
 const delta=yesterday>0?Math.round((today/yesterday-1)*100):null;
 const trend=delta==null?'':' · <span style="color:var(--'+(delta>=0?'green':'red')+')">'+(delta>=0?'▲':'▼')+' '+Math.abs(delta)+'% vs. gestern</span>';
 return `<div class="card" style="grid-column:1/-1">
  <div class="stats" style="grid-template-columns:repeat(3,1fr);margin:0">
   <div class="stat"><div class="l">${label}</div><div class="v isk" style="font-size:24px">${fmtM(today)}</div><div class="l">${subToday||''}${trend}</div></div>
   <div class="stat"><div class="l">Gestern</div><div class="v isk" style="font-size:24px">${fmtM(yesterday)}</div></div>
   <div class="stat"><div class="l">Letzte 7 Tage</div><div class="v isk" style="font-size:24px">${fmtM(week)}</div><div class="l">${subWeek||''}</div></div>
  </div></div>`;
}
function heroBar(s){
 if(!s)return '';
 return heroTiles('⛏ Geminert heute',s.today,s.yesterday,s.week,
  fmt(s.m3_today)+' m³',fmt(s.m3_week)+' m³ · Ø '+fmtM(s.week/7)+'/Tag');
}
function renderLive(chars,summary){
 lastChars=chars;
 syncCharFilter(chars);
 const f=localStorage.getItem('charFilter')||'';
 if(f&&chars.some(c=>c.name===f))chars=chars.filter(c=>c.name===f);
 $('#hero').innerHTML=heroBar(summary);
 if(!chars.length){$('#empty').hidden=false;
  $('#empty').textContent='Warte auf Gamelog-Daten … (EVE-Client an? Im Client „Spielprotokoll speichern" aktivieren.)';
  $('#grid').innerHTML='';return;}
 $('#empty').hidden=true;
 $('#grid').innerHTML=chars.map(c=>{
  const maxOre=Math.max(1,...c.ores.map(o=>o.isk));
  const maxS=Math.max(1,...c.spark);
  const min=collapsed.has(c.name);
  return `<div class="card ${min?'min':''}">
   <div class="chead" data-c="${esc(c.name)}">
    <span class="arr">▼</span>
    ${c.portrait?`<img class="pf" src="${c.portrait}" alt="">`
      :(!c.esi_linked?`<span class="pf pf-none" data-esihint="1" title="Noch nicht mit EVE-Login verbunden. Klick für Portrait, Schiff, Wallet und automatisches Heavy Water.">👤</span>`:'')}
    <span class="char">${esc(c.name)} <span class="sys">· ${esc(c.system)}${c.ship?' · '+esc(c.ship):''}</span></span>
    <span class="mini">${c.cargo_full?'<span class="warnbadge drone">⚠ Frachtraum voll!</span> · ':''}${(c.tool_warns||[]).map(w=>'<span class="warnbadge'+(w.drone?' drone':'')+'">⚠ '+w.tool+(w.count>1?' ×'+w.count:'')+'</span> · ').join('')}${(c.lasers_off||[]).map(w=>'<span class="warnbadge">⛔ '+w.tool+' aus</span> · ').join('')}${c.heavy_water&&c.heavy_water.on&&c.heavy_water.min_left<30?'<span class="warnbadge drone">⛽ HW ~'+c.heavy_water.min_left+' min</span> · ':''}${c.drones_idle?'<span class="warnbadge">🤖 Drohnen ohne Erz</span> · ':''}${c.laser_stalled?'<span class="warnbadge">⛏ Laser ohne Erz</span> · ':''}${c.rate_low?'<span class="warnbadge">⚠ Rate '+c.rate_low+'%</span> · ':''}${mineIdle(c,state)?'<span class="warnbadge">⚠ Kein Erz seit '+Math.round(c.mine_idle/60)+' min</span> · ':''}${fmtM(c.total_isk)} ISK · ${fmt(c.m3h)} m³/h${c.dps_in>0?' · <span class=\"in\">⚠ '+c.dps_in+' DPS rein</span>':''}</span>
   </div>
   <div class="cbody">
   ${c.cargo_full?`<div class="cardwarn drone">⚠ Frachtraum voll! Erz verladen oder komprimieren.</div>`:''}
   ${(c.tool_warns||[]).map(w=>w.drone
     ?`<div class="cardwarn drone">⚠ ${esc(w.tool)}${w.count>1?' ×'+w.count:''} abgeschaltet, Drohnen prüfen!</div>`
     :`<div class="cardwarn">⚠ ${esc(w.tool)}${w.count>1?' ×'+w.count:''} abgeschaltet, Ziel prüfen</div>`).join('')}
   ${(c.lasers_off||[]).map(w=>`<div class="cardwarn">⛔ ${esc(w.tool)} aus seit ${new Date(w.since*1000).toLocaleTimeString().slice(0,5)}. Neues Ziel erfassen! <span class="laserok" data-char="${esc(c.name)}" data-tool="${esc(w.tool)}">✓ erledigt</span></div>`).join('')}
   ${c.drones_idle?`<div class="cardwarn">🤖 Drohnen liefern gerade kein Erz (gestoppt, voll oder auf dem Rückweg).</div>`:''}
   ${c.laser_stalled?`<div class="cardwarn">⛏ Strip Miner liefert gerade kein Erz, während die Drohnen weiterlaufen.</div>`:''}
   ${c.rate_low?`<div class="cardwarn">⚠ Abbaurate nur noch ${c.rate_low}%. Vermutlich ist ein Modul oder eine Drohne aus.</div>`:''}
   ${mineIdle(c,state)?`<div class="cardwarn">⚠ Seit ${Math.round(c.mine_idle/60)} min kein Erz. Laser und Drohnen prüfen!</div>`:''}
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
    ${c.heavy_water||!c.esi_linked?`<div class="stat"><div class="l">Heavy Water${c.heavy_water?' · '+c.heavy_water.core.toUpperCase():''}${c.heavy_water&&c.heavy_water.esi?' · ESI':''} ${c.heavy_water&&c.heavy_water.esi?'':`<span class="hwset" data-char="${esc(c.name)}" data-core="${c.heavy_water?c.heavy_water.core:''}" data-fill="${c.heavy_water&&c.heavy_water.fill?c.heavy_water.fill:''}" title="Bestand im Laderaum setzen">⛽</span>`}</div><div class="v ${c.heavy_water&&c.heavy_water.on&&c.heavy_water.min_left<30?'in':''}">${c.heavy_water?fmt(c.heavy_water.units):'—'}</div><div class="l">${c.heavy_water?(c.heavy_water.on&&c.heavy_water.eta?'reicht bis ~'+new Date(c.heavy_water.eta*1000).toLocaleTimeString().slice(0,5)+' Uhr':'Kern inaktiv, Verbrauch pausiert'):'per ⛽ setzen'}</div></div>`:''}
    <div class="stat"><div class="l">Bounties</div><div class="v grn">${fmtM(c.bounty)}</div></div>
    ${c.wallet!=null?`<div class="stat"><div class="l">Wallet (ESI)</div><div class="v grn">${fmtM(c.wallet)}</div></div>`:''}
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
     `<tr><td>${esc(w[0])}</td><td class="r">${fmt(w[1])} dmg</td></tr>`).join('')+`</table>`:''}
   ${c.top_targets.length?`<div class="sect">Top-Ziele</div><table>`+c.top_targets.map(t=>
     `<tr><td>${esc(t[0])}</td><td class="r">${fmt(t[1])}</td></tr>`).join('')+`</table>`:''}
   ${c.top_attackers.length?`<div class="sect">Top-Angreifer</div><table>`+c.top_attackers.map(t=>
     `<tr><td>${esc(t[0])}</td><td class="r">${fmt(t[1])}</td></tr>`).join('')+`</table>`:''}
   </div>
  </div>`}).join('');
 document.querySelectorAll('.chead').forEach(h=>h.onclick=()=>toggleChar(h.dataset.c));
 document.querySelectorAll('[data-esihint]').forEach(el=>el.onclick=e=>{
  e.stopPropagation();syncOpts();$('#opts').showModal();
  const s=$('#opts .sect.esi');if(s)s.scrollIntoView({block:'center'});
 });
 document.querySelectorAll('.laserok').forEach(b=>b.onclick=async e=>{
  e.stopPropagation();
  await post({action:'laser_ok',char:b.dataset.char,tool:b.dataset.tool});
  tick();
 });
 document.querySelectorAll('.hwset').forEach(b=>b.onclick=async e=>{
  e.stopPropagation();
  const v=prompt('Heavy Water im Laderaum (Stück). Nach dem Nachfüllen einfach Enter drücken, 0 entfernt die Anzeige:',b.dataset.fill||'');
  if(v===null)return;
  if(v.trim()===''&&!b.dataset.fill)return;
  if(v.trim()==='0'){await post({action:'heavy_water',char:b.dataset.char});tick();return;}
  if(v.trim()===''){await post({action:'heavy_water',char:b.dataset.char,units:Number(b.dataset.fill),core:b.dataset.core||'t1'});tick();return;}
  const core=b.dataset.core||(confirm('Industrial Core II (T2, 200/min)?\\nOK = T2 · Abbrechen = T1 (100/min)')?'t2':'t1');
  await post({action:'heavy_water',char:b.dataset.char,units:Number(v.replace(/[^\\d]/g,''))||0,core});
  tick();
 });
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
   `<tr><td>${esc(n)}</td><td class="r">${fmt(c.m3)} m³</td><td class="r grn">${fmtM(c.bounty)}</td><td class="r isk">${fmtM(c.ore_isk+c.bounty)}</td></tr>`).join('')}</table></div>
  <div class="card"><div class="char">Komprimiert pro Charakter</div>
   <div class="sub">Alles, was über die Schiffs-Kompression gelaufen ist</div>
   <table>${t.compressed.length?t.compressed.map(k=>
   `<tr><td>${esc(k.char)}</td><td>${esc(k.type)}</td><td class="r">${fmt(k.units)} Stk</td><td class="r">${fmt(k.m3)} m³</td><td class="r isk">${fmtM(k.isk)}</td></tr>`).join(''):'<tr><td>Noch nichts komprimiert</td></tr>'}</table></div>`;
}

let compPeriod=localStorage.getItem('compPeriod')||'today';
let lastAnalyse=null;
const PERIODS={today:'Heute',week:'7 Tage',month:'30 Tage',year:'12 Monate'};
let compOpen=new Set(lsGet('compOpen',[]));
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
  goalHtml=`<div class="card" style="grid-column:1/-1"><div class="sub">Kein Ziel gesetzt. Unter ⚙ Optionen kannst du ein ISK-Ziel mit Prognose anlegen.</div></div>`;
 }
 const maxP=Math.max(1,...a.playtime.map(p=>p.minutes));
 $('#grid').innerHTML=goalHtml+compCard(a.compression||{})+
  `<div class="card"><div class="char">Erz-Effizienz (ISK/m³)</div>
   <div class="sub">Was lohnt sich am meisten pro Laderaum?</div><table>${a.efficiency.map(e=>
   `<tr><td>${e.ore}</td><td class="r">${e.isk_per_m3} ISK/m³</td><td class="r">${fmt(e.m3)} m³</td><td class="r isk">${fmtM(e.isk)}</td></tr>`).join('')}</table></div>
  <div class="card"><div class="char">Waffen-Bilanz</div><table>${a.weapons.length?a.weapons.map(w=>
   `<tr><td>${esc(w[0])}</td><td class="r out">${fmt(w[1])} dmg</td></tr>`).join(''):'<tr><td class="r">Noch keine Kampfdaten</td></tr>'}</table></div>
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
 const lo=c.lasers_off||[];
 if(lo.length)return['warn',lo[0].tool.toUpperCase()+' AUS'];
 if(c.drones_idle)return['warn','DROHNEN OHNE ERZ'];
 if(c.laser_stalled)return['warn','LASER OHNE ERZ'];
 if(c.heavy_water&&c.heavy_water.on&&c.heavy_water.min_left<30)return['warn','HEAVY WATER ~'+c.heavy_water.min_left+' MIN'];
 if(c.rate_low)return['warn','ABBAURATE '+c.rate_low+'%'];
 if(mineIdle(c,st))return['warn','KEIN ERZ SEIT '+Math.round(c.mine_idle/60)+' MIN'];
 return['ok',''];
}
async function overlayTick(){
 if(!pipWin)return;
 try{
  const d=await (await fetch('/data?view=live')).json();
  const doc=pipWin.document, now=Date.now()/1000;
  doc.body.style.zoom={1:'1',2:'1.15',3:'1.3'}[fontsize]||'1';
  const alerts=(d.state.alerts||[]).filter(a=>now-a.ts<180).slice(-3).reverse();
  const hot=alerts.some(a=>(a.kind==='pvp'||a.kind==='cargo'||a.kind==='drones')&&now-a.ts<45);
  doc.body.classList.toggle('alarm',hot);
  doc.getElementById('ov').innerHTML=
   `<div class="hd"><span>🐤 <b>CANARY</b></span><span>${new Date().toLocaleTimeString()}</span></div>`+
   d.chars.map(c=>{const [cls,txt]=ovStatus(c,d.state);
    return `<div class="row"><span class="dot ${cls}"></span>
     <span><div class="nm">${esc(c.name)} <span class="sys">· ${esc(c.system)}</span></div>
     ${txt?`<div class="st ${cls==='bad'?'bad':''}">${txt}</div>`:''}</span>
     <span class="val">${fmtM(c.total_isk)}<small>${fmt(c.m3h)} m³/h</small></span></div>`;}).join('')+
   alerts.map(a=>`<div class="al ${a.kind}">[${new Date(a.ts*1000).toLocaleTimeString()}] ${esc(a.text)}</div>`).join('');
 }catch(e){}
}
setInterval(overlayTick,2000);
$('#ovToggle').onclick=toggleOverlay;
$('#ovBtn').onclick=toggleOverlay;

let intelNames=lsGet('intelNames',[]),intelSettled=false;
let intelBusy=false,intelAutoTs=Number(localStorage.getItem('intelAutoTs')||0);
function renderIntel(auto){
 if(!document.getElementById('intelBox')){
  $('#grid').innerHTML=`<div class="card" id="intelBox" style="grid-column:1/-1">
   <b>🚦 Bedrohungs-Ampel (Local-Scan)</b>
   <div style="font-size:12px;color:var(--dim);margin:6px 0">Im EVE-Local-Fenster in die Mitgliederliste klicken, dann <b>Strg+A</b> und <b>Strg+C</b>. Mit Auto-Scan reicht das schon, Canary erkennt die kopierte Liste von selbst.
   Alternativ hier einfügen und auf Scannen klicken. Quellen: zKillboard und ESI (öffentlich, ohne Login). Etwa ein Pilot pro Sekunde, Ergebnisse bleiben 12 Stunden gespeichert.</div>
   <label style="font-size:12px;display:block;margin:6px 0"><input type="checkbox" id="clipWatch"> <b>Auto-Scan:</b> Zwischenablage überwachen. Strg+A/C im Local genügt, bei 🔴 gibt es Alarm auch ohne offenen Intel-Tab. <span style="color:var(--dim)">(Der Inhalt bleibt lokal, nur erkannte Pilotennamen werden bei ESI und zKillboard nachgeschlagen.)</span></label>
   <textarea id="intelIn" rows="5" style="width:100%" placeholder="Piloten-Namen einfügen …"></textarea>
   <div style="margin:8px 0"><button class="btn" id="intelGo">Scannen</button> <span id="intelStat" style="font-size:12px;color:var(--dim)"></span></div>
   <div id="intelTbl" style="overflow-x:auto"></div></div>`;
  $('#intelGo').onclick=()=>{
   intelNames=[...new Set($('#intelIn').value.split(/\\n/).map(s=>s.trim()).filter(s=>s&&!s.startsWith('[')))].slice(0,200);
   localStorage.setItem('intelNames',JSON.stringify(intelNames));
   intelSettled=false;
   $('#intelTbl').innerHTML='';
   intelPoll();
  };
  $('#clipWatch').checked=!!(state&&state.clip_watch);
  $('#clipWatch').onchange=()=>post({action:'clip_watch',on:$('#clipWatch').checked});
  if(intelNames.length)$('#intelIn').value=intelNames.join('\\n');
 }
 if(auto&&auto.ts>intelAutoTs&&auto.names&&auto.names.length&&document.activeElement!==$('#intelIn')){
  // nicht überschreiben, während der Nutzer gerade im Feld tippt
  intelAutoTs=auto.ts;localStorage.setItem('intelAutoTs',intelAutoTs);
  intelNames=auto.names;
  localStorage.setItem('intelNames',JSON.stringify(intelNames));
  intelSettled=false;
  $('#intelIn').value=intelNames.join('\\n');
  $('#intelTbl').innerHTML='';
 }
 intelPoll();
}
async function intelPoll(){
 if(!intelNames.length||intelBusy||view!=='intel'||intelSettled)return;
 intelBusy=true;
 try{
  const r=await post({action:'threat_scan',names:intelNames});
  const res=r.results||{};
  // Fertig (nichts mehr offen)? Dann nicht mehr alle 2s neu abfragen/rendern,
  // sonst geht Textselektion und Link-Hover in der Tabelle laufend verloren.
  intelSettled=!r.pending;
  const order={red:0,yellow:1,unknown:2,green:3};
  const ICON={red:'🔴',yellow:'🟡',green:'🟢',unknown:'⚪'};
  const rows=intelNames.map(n=>[n,res[n]]).sort((a,b)=>{
   const ra=a[1]?(order[a[1].level]??2):4,rb=b[1]?(order[b[1].level]??2):4;
   return ra-rb||a[0].localeCompare(b[0]);});
  const cnt={red:0,yellow:0,green:0,unknown:0};
  rows.forEach(([n,d])=>{if(d&&cnt[d.level]!=null)cnt[d.level]++;});
  $('#intelStat').textContent=(r.pending?'prüfe … noch '+r.pending+' offen · ':'')+
   cnt.red+' rot · '+cnt.yellow+' gelb · '+cnt.green+' grün · '+cnt.unknown+' unbekannt';
  $('#intelTbl').innerHTML=`<table><tr><th></th><th>Pilot</th><th>Alter</th><th>Corp · Allianz</th>
   <th class="r">Kills 60d</th><th class="r">Miner-Kills</th><th class="r">Kills/Verluste</th>
   <th class="r">Danger</th><th class="r">Sec</th></tr>`+
   rows.map(([n,d])=>{
    if(!d)return '<tr><td>⏳</td><td>'+esc(n)+'</td><td colspan="7" style="color:var(--dim)">wird geprüft …</td></tr>';
    if(d.level==='unknown')return '<tr><td>⚪</td><td>'+esc(n)+'</td><td colspan="7" style="color:var(--dim)">'+esc(d.note||'')+'</td></tr>';
    const corp=esc((d.corp||'?')+(d.alliance?' · '+d.alliance:''));
    const age=d.age_days!=null?(d.age_days<365?d.age_days+' T':(d.age_days/365).toFixed(1)+' J'):'?';
    return `<tr class="lvl-${d.level}"><td>${ICON[d.level]}</td>
     <td><a href="https://zkillboard.com/character/${encodeURIComponent(d.id)}/" target="_blank" rel="noopener">${esc(n)}</a></td>
     <td>${age}</td><td>${corp}</td><td class="r">${d.recent_kills}</td>
     <td class="r${d.miner_kills>=3?' in':''}">${d.miner_kills}</td>
     <td class="r">${d.kills}/${d.losses}</td><td class="r">${d.danger}%</td>
     <td class="r">${d.sec}</td></tr>`;}).join('')+'</table>';
 }catch(e){}
 intelBusy=false;
}
function renderMissions(d){
 const m=d.missions||{},t=m.today||{};
 const live=(d.chars||[]).filter(c=>c.bounty>0||c.kills>0);
 const byDay={};(m.days||[]).forEach(x=>byDay[x.day]=x);
 const iso=n=>new Date(Date.now()-n*864e5).toISOString().slice(0,10);
 const y=byDay[iso(1)]||{};
 let wIsk=0,wMis=0;
 for(let n=0;n<7;n++){const x=byDay[iso(n)];if(x){wIsk+=x.total;wMis+=x.missions;}}
 $('#hero').innerHTML=heroTiles('🎯 Verdient heute',t.total||0,y.total||0,wIsk,
  (t.missions||0)+' Missionen',wMis+' Missionen · Ø '+fmtM(wIsk/7)+'/Tag');
 $('#grid').innerHTML=`
 <div class="card" style="grid-column:1/-1">
  <b>Heute im Detail (EVE-Zeit)</b>
  <div class="stats" style="margin-top:10px">
   <div class="stat"><div class="l">Missionen erledigt</div><div class="v out">${t.missions||0}</div></div>
   <div class="stat"><div class="l">Belohnungen</div><div class="v isk">${fmtM(t.reward||0)}</div></div>
   <div class="stat"><div class="l">Zeitboni</div><div class="v isk">${fmtM(t.bonus||0)}</div></div>
   <div class="stat"><div class="l">Bounties</div><div class="v grn">${fmtM(t.bounty||0)}</div></div>
  </div>
  ${(m.mine_systems&&m.mine_systems.length)?`<div class="sub" style="margin-top:8px">Bounties aus deinen Mining-Systemen (${m.mine_systems.join(', ')}) zählen hier nicht mit, das sind Belt-Ratten.</div>`:''}
  ${m.linked?'':'<div class="cardwarn" style="margin-top:10px">⚠ Kein EVE-Login verbunden. Belohnungen und Boni kommen aus dem Wallet-Journal (ESI), einzurichten unter ⚙ Optionen.</div>'}
  ${live.length?'<div class="sect">Live-Session (aus den Gamelogs)</div>'+live.map(c=>
   `<div class="sub">⚔ <b>${esc(c.name)}</b>${c.ship?' · '+esc(c.ship):''} · ${c.kills} Kills · ${fmtM(c.bounty)} Bounties · DPS ${c.dps_out} raus / ${c.dps_in} rein · Session ${c.session_min} min</div>`).join(''):''}
 </div>
 <div class="card" style="grid-column:1/-1">
  <div class="sect">Letzte 30 Tage</div>
  ${(m.days&&m.days.length)?`<div style="overflow-x:auto"><table>
   <tr><th>Tag</th><th class="r">Missionen</th><th class="r">Belohnung</th><th class="r">Zeitbonus</th><th class="r">Bounties</th><th class="r">Gesamt</th></tr>`+
   m.days.map(x=>`<tr><td>${x.day}</td><td class="r">${x.missions}</td><td class="r isk">${fmtM(x.reward)}</td><td class="r isk">${fmtM(x.bonus)}</td><td class="r grn">${fmtM(x.bounty)}</td><td class="r isk"><b>${fmtM(x.total)}</b></td></tr>`).join('')+
   '</table></div>':'<div class="sub">Noch keine Journal-Daten. Nach dem ersten ESI-Abgleich (spätestens in einer Stunde) erscheinen hier die letzten 30 Tage.</div>'}
 </div>
 ${(m.agents&&m.agents.length)?`<div class="card">
  <div class="sect">Top-Agenten</div><table>
  <tr><th>Agent</th><th class="r">Missionen</th><th class="r">ISK</th></tr>`+
  m.agents.map(a=>`<tr><td>${esc(a.agent)}</td><td class="r">${a.missions}</td><td class="r isk">${fmtM(a.isk)}</td></tr>`).join('')+'</table></div>':''}
 ${(m.chars&&m.chars.length)?`<div class="card">
  <div class="sect">Nach Charakter (gesamt)</div><table>
  <tr><th>Charakter</th><th class="r">Missionen</th><th class="r">ISK</th></tr>`+
  m.chars.map(c=>`<tr><td>${c.char}</td><td class="r">${c.missions}</td><td class="r isk">${fmtM(c.total)}</td></tr>`).join('')+'</table></div>':''}`;
}
function renderRechner(){
 if(document.getElementById('calcBox'))return;
 $('#grid').innerHTML=`<div class="card" id="calcBox" style="grid-column:1/-1">
  <b>🧮 Ore Calculator</b>
  <div style="font-size:12px;color:var(--dim);margin:6px 0">Im Spiel den Frachtraum oder Container öffnen, alles markieren (Strg+A) und kopieren (Strg+C), dann hier einfügen.
  Einzelne Zeilen wie "Compressed Veldspar 50000" funktionieren genauso.</div>
  <textarea id="calcIn" rows="7" style="width:100%" placeholder="Compressed Veldspar	49.105&#10;Compressed Scordite	42.990"></textarea>
  <div style="margin:8px 0"><button class="btn" id="calcGo">Berechnen</button> <span id="calcStat" style="font-size:12px;color:var(--dim)"></span></div>
  <div id="calcOut" style="overflow-x:auto"></div></div>`;
 $('#calcGo').onclick=doCalc;
 const saved=localStorage.getItem('calcText');
 if(saved)$('#calcIn').value=saved;
}
async function doCalc(){
 const text=$('#calcIn').value;
 localStorage.setItem('calcText',text);
 $('#calcStat').textContent='Hole Preise von allen Handelsplätzen …';
 let r;
 try{r=await post({action:'calc',text});}catch(e){r=null;}
 if(!$('#calcOut'))return;  // Nutzer hat die Ansicht während der Abfrage gewechselt
 if(!r){$('#calcStat').textContent='Preisabfrage fehlgeschlagen.';return;}
 $('#calcStat').textContent='';
 if(!r.items||!r.items.length){
  $('#calcOut').innerHTML='<div class="sub">Keine bekannten Erz-Typen erkannt.'+(r.unknown&&r.unknown.length?' Nicht zuzuordnen: '+esc(r.unknown.join(' · ')):'')+'</div>';
  return;}
 const hubs=Object.values(r.hubs||{}).filter(h=>!h.error);
 if(!hubs.length){$('#calcOut').innerHTML='<div class="sub">Keine Preisdaten von den Handelsplätzen erhalten. Bitte später erneut versuchen.</div>';return;}
 const bestBuy=Math.max(...hubs.map(h=>h.buy));
 $('#calcOut').innerHTML=
  `<div class="stats" style="grid-template-columns:repeat(${hubs.length},1fr)">`+
  hubs.map(h=>`<div class="stat"${h.buy===bestBuy?' style="border-color:var(--gold)"':''}>
   <div class="l">${esc(h.name)}${h.buy===bestBuy?' ★':''}</div>
   <div class="v isk" style="font-size:20px">${fmtM(h.buy)}</div>
   <div class="l">Sofortverkauf · mit Sell-Order: ${fmtM(h.sell)}</div></div>`).join('')+`</div>
  <div class="sub" style="margin-top:8px">${fmt(r.m3)} m³ gesamt · ★ = bester Sofortverkauf · Einzelwerte zu Jita-Buy-Preisen:</div>
  <table><tr><th>Typ</th><th class="r">Menge</th><th class="r">m³</th><th class="r">ISK (Jita)</th></tr>`+
  r.items.map(i=>`<tr><td>${esc(i.name)}</td><td class="r">${fmt(i.qty)}</td><td class="r">${fmt(i.m3)}</td><td class="r isk">${fmtM(i.isk)}</td></tr>`).join('')+'</table>'+
  (r.unknown&&r.unknown.length?`<div class="sub" style="margin-top:8px">Nicht erkannt: ${esc(r.unknown.join(' · '))}</div>`:'');
}
let tickBusy=false;
async function tick(){
 if(tickBusy)return;  // kein Request-Stau bei langsamem /data
 tickBusy=true;
 const reqView=view;  // View einfrieren: nach dem await zählt der Stand von JETZT
 try{
  const d=await (await fetch('/data?view='+reqView)).json();
  if(reqView!==view)return;  // Nutzer hat inzwischen gewechselt -> Antwort verwerfen
  state=d.state;regionPills();handleAlerts();updateBadge();bootScreen();
  if(view!=='live'&&view!=='month'&&view!=='total'&&view!=='analyse')$('#empty').hidden=true;
  if(view==='live')renderLive(d.chars,d.summary);
  else if(view==='missionen')renderMissions(d);
  else{
   $('#hero').innerHTML='';
   if(view==='month')renderMonth(d.days);
   else if(view==='analyse')renderAnalyse(d.analyse);
   else if(view==='intel')renderIntel(d.intel_auto);
   else if(view==='rechner')renderRechner();
   else renderTotal(d.total);
  }
 }catch(e){}
 finally{tickBusy=false;}
}
tick();setInterval(tick,2000);
</script></body></html>"""


if __name__ == "__main__":
    if not CONFIG["log_dir"]:
        print("WARNUNG: EVE-Gamelog-Ordner nicht gefunden. Bitte den Pfad in config.json eintragen.")
    if DB_PATH.exists():
        try:
            do_backup()
        except Exception:
            pass
    port = int(CONFIG.get("port", PORT_DEFAULT))

    class Server(ThreadingHTTPServer):
        # Windows: mit SO_REUSEADDR koennten mehrere Instanzen denselben Port
        # binden und sich gegenseitig die Anfragen wegschnappen. Deshalb aus.
        allow_reuse_address = False

    # Bis zu 12s auf den Port warten: nach einem Auto-Update startet der neue
    # Prozess evtl., bevor der alte den Socket (TIME_WAIT) freigegeben hat.
    srv = None
    for attempt in range(24):
        try:
            srv = Server(("127.0.0.1", port), Handler)
            break
        except OSError:
            time.sleep(0.5)
    if srv is None:
        print(f"EVE Canary läuft offenbar schon (Port {port} ist belegt).")
        print("Einfach das vorhandene Fenster nutzen: http://localhost:" + str(port))
        try:
            input("Enter zum Schließen ...")
        except EOFError:
            pass  # ohne Konsole (Autostart) einfach still beenden
        sys.exit(1)
    if DB_PATH.exists():
        try:
            do_backup()
        except Exception:
            pass
    ingest.start()
    chatwatch.start()
    prices.start()
    esi.start()
    threat.start()
    clipwatch.start()
    print(f"EVE Canary läuft:  http://localhost:{port}")
    if "--no-browser" not in sys.argv:
        # Browser erst jetzt öffnen, wo der Port sicher gebunden ist
        try:
            import webbrowser
            threading.Timer(0.5, lambda: webbrowser.open(f"http://localhost:{port}")).start()
        except Exception:
            pass
    srv.serve_forever()
