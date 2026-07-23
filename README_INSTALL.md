# EVE Canary 🐤: Installation

Der Kanarienvogel im Bergwerk: ein lokales Dashboard, das die EVE-Online-Logdateien auswertet: Mining, ISK,
Kompression, Schaden, Historie. Dazu Alarme bei Spieler-Angriffen, leeren
Asteroiden, vollem Frachtraum und Mining-Stillstand. Läuft komplett auf deinem
Rechner, keine Anmeldung, keine Accounts, EULA-konform (liest nur die
Text-Logs, die der EVE-Client selbst schreibt).

## Schnellinstallation (empfohlen)

Windows-Taste druecken, "PowerShell" tippen, oeffnen und diesen einen Befehl
einfuegen:

```
irm https://raw.githubusercontent.com/Eve-Online-Askend/eve-canary/main/install.ps1 | iex
```

Das war alles. Der Installer prueft Python (und installiert es notfalls
automatisch), laedt Canary nach `%LOCALAPPDATA%\EVE-Canary`, legt eine
Desktop-Verknuepfung "EVE Canary" an und startet das Dashboard. Updates kommen
danach wie gewohnt ueber den eingebauten Auto-Updater.

Wer lieber von Hand installiert, folgt den nächsten beiden Abschnitten.

## Linux (EVE über Steam/Proton oder Wine)

Ein Terminal öffnen und diesen Befehl einfügen:

```
curl -fsSL https://raw.githubusercontent.com/Eve-Online-Askend/eve-canary/main/install.sh | sh
```

Canary landet in `~/.local/share/eve-canary`, bekommt einen Startmenü-Eintrag
"EVE Canary" und startet danach direkt. Gebraucht wird nur Python 3, das bei den
meisten Distributionen ohnehin dabei ist.

Den Log-Ordner sucht Canary selbst. Unter Linux schreibt EVE nicht nach
`~/Dokumente`, sondern ins Wine-Präfix, bei Steam also zum Beispiel nach
`~/.steam/steam/steamapps/compatdata/8500/pfx/drive_c/users/steamuser/Documents/EVE/logs/Gamelogs`.
Durchsucht werden alle Steam-Bibliotheken (auch Flatpak, Snap und zweite
Festplatten) sowie `~/.wine` und die Lutris-Präfixe unter `~/Games`. Gibt es
mehrere Treffer, gewinnt der mit dem jüngsten Log. Wird nichts gefunden, den
Pfad einfach in den Optionen eintragen.

Zwei Unterschiede zu Windows: der automatische Local-Scan über die
Zwischenablage gibt es dort nicht (Namen von Hand in den Intel-Tab einfügen
funktioniert weiter), und der Autostart läuft über eine `.desktop`-Datei in
`~/.config/autostart`. Beide Schalter blendet Canary aus, wenn die Plattform sie
nicht kann.

## Wo liegt Canary und wie starte ich es wieder?

- Der Installer fragt nach dem Zielordner. Enter uebernimmt den Vorschlag
  `%LOCALAPPDATA%\EVE-Canary` (also `C:\Benutzer\DEINNAME\AppData\Local\EVE-Canary`),
  oder du tippst einen eigenen Pfad ein, zum Beispiel `D:\Spiele\EVE-Canary`.
- Nach einem Windows-Neustart einfach die **Desktop-Verknuepfung "EVE Canary"**
  doppelklicken, oder Windows-Taste druecken, "EVE Canary" tippen, Enter.
- Bequemer: In den Canary-Optionen (Zahnrad) unter **System** den Haken
  **"beim Windows-Start automatisch mitstarten"** setzen. Dann laeuft Canary
  nach jedem Neustart still im Hintergrund und ist sofort unter
  http://localhost:8765 erreichbar.

## Deinstallieren

Im Canary-Ordner liegt **uninstall.ps1**. Rechtsklick darauf -> "Mit PowerShell
ausfuehren", oder in einer PowerShell:

```
powershell -ExecutionPolicy Bypass -File uninstall.ps1
```

Das beendet Canary, entfernt den Autostart und beide Verknuepfungen und fragt,
ob der Ordner (inkl. Statistik und Einstellungen) geloescht werden soll. Mit
`-KeepData` bleiben Ordner und Daten erhalten und nur Autostart/Verknuepfungen
gehen weg. Von Hand sind es diese vier Stellen: der Installationsordner, die
Desktop- und Startmenue-Verknuepfung "EVE Canary" und die Datei
`EVE-Canary-Autostart.vbs` im Autostart-Ordner (`shell:startup`).

## Voraussetzungen

1. **Windows** mit EVE Online
2. **Python 3** (kostenlos): https://www.python.org/downloads/
   - Beim Installieren unbedingt **"Add Python to PATH"** anhaken!
   - Keine weiteren Pakete nötig, das Dashboard nutzt nur die Standardbibliothek.
3. Im EVE-Client muss das **Spielprotokoll** aktiviert sein (ist Standard):
   Esc-Menü → Einstellungen → dort „Spielprotokoll speichern" / „Log game to file"
   aktivieren. Für die System-Anzeige zusätzlich „Chat protokollieren".

## Installation

1. Diesen Ordner irgendwohin entpacken/kopieren (z. B. `C:\EVE-Dashboard`)
2. Doppelklick auf **`start_dashboard.bat`**
3. Der Browser öffnet sich automatisch mit http://localhost:8765
4. Fertig. Beim ersten Start werden alle vorhandenen Logs eingelesen.

Der Gamelog-Ordner (`Dokumente\EVE\logs\Gamelogs`) wird automatisch gefunden,
auch bei OneDrive-Dokumenten. Falls nicht: Pfad in `config.json` unter
`"log_dir"` eintragen (die Datei entsteht nach dem ersten Start).

## Erste Schritte

- **⚙ Optionen**: Datenbasis wählen (alle alten Logs auswerten oder erst ab
  jetzt zählen), ISK-Ziel setzen, Watchlist pflegen, Backup erstellen.
- **Einmal in die Seite klicken** nach dem Öffnen, erst danach darf der
  Browser Warntöne abspielen.
- **◱ Overlay**: schwebendes Always-on-top-Fenster über dem EVE-Client
  (benötigt Chrome oder Edge; EVE im Fenster-/randlosen Modus).
- **Desktop-Benachrichtigungen** in den Optionen erlauben, wenn gewünscht.

## 🚦 Bedrohungs-Ampel (Intel-Tab)

Stuft Piloten aus dem Local automatisch ein, über öffentliche APIs (zKillboard
+ ESI), ganz ohne Login: 🔴 Ganker-Verdacht (Miner-Kills, Outlaw-Sec-Status,
junger Char mit frischen Kills) · 🟡 PvP-aktiv · 🟢 unauffällig.

- **Local-Scan:** Im EVE-Local in die Mitgliederliste klicken → Strg+A →
  Strg+C → im Intel-Tab einfügen → Scannen.
- **Auto-Scan (empfohlen):** Checkbox im Intel-Tab aktivieren. Dann genügt
  Strg+A/C im Spiel, Canary erkennt die kopierte Liste selbst und alarmiert
  bei 🔴 sogar, wenn das Dashboard im Hintergrund liegt. (Die Zwischenablage
  wird nur lokal gelesen; nur erkannte Pilotennamen werden nachgeschlagen.)
- Zusätzlich automatisch: Wer dich angreift oder im Local schreibt, wird im
  Hintergrund eingestuft. Angreifer melden sich ab 🟡, Sprecher nur bei 🔴.
- Ergebnisse werden 12 h zwischengespeichert (Tabelle `threat` in der lokalen DB).

## EVE-Login (ESI): optional, für Automatik-Features

Mit dem offiziellen EVE-Login liest Canary zusätzlich (nur lesend!): aktuelles
Schiff, Heavy Water im Laderaum inkl. Kern-Typ (für die „reicht bis…"-Anzeige
bei Orca/Porpoise), den Wallet-Stand, Portrait und Missions-Einnahmen. Ohne ESI
funktioniert alles andere ganz normal; Heavy Water lässt sich dann per ⛽ manuell setzen.

**Kein Setup nötig.** In den Optionen unter „EVE-Account verbinden" auf
**„🔑 Mit EVE-Account verbinden"** klicken, im EVE-Login den Charakter wählen,
fertig. Für weitere Charaktere (auch andere Accounts) einfach wiederholen; auf
der Login-Seite ggf. „Switch accounts" nutzen.

Sicherheit: offizieller CCP-OAuth-Login (PKCE). Canary sieht nie dein Passwort,
bekommt nur Lese-Rechte, die Zugangs-Tokens bleiben lokal in `config.json`.
Zugriff jederzeit widerrufbar unter
https://community.eveonline.com/support/third-party-applications/

Fortgeschritten: Wer lieber seine eigene ESI-App nutzt, trägt deren Client-ID
in den Optionen unter „Eigene ESI-App verwenden" ein (Callback
`http://localhost:8765/sso/callback`).

## Wenn etwas nicht läuft: Diagnose

Canary meldet Probleme mit einem kurzen Code, zum Beispiel `CN-LOG-02`. Der Code
steht im Konsolenfenster und unten in den ⚙ Optionen unter „System & Daten".

**So schickst du den Fehler weiter:** ⚙ Optionen öffnen, auf
**„🩺 Diagnose kopieren"** klicken, der Bericht liegt dann in der
Zwischenablage. Einfach in den Canary-Kanal im Discord einfügen. Der Bericht
enthält Version, Betriebssystem, Log-Ordner, Zählerstände und die letzten
Fehler, aber keine Charakternamen und keine Zugangsdaten.

| Code | Bedeutung |
|---|---|
| `CN-LOG-01` | Kein Log-Ordner eingestellt |
| `CN-LOG-02` | Log-Ordner existiert nicht |
| `CN-LOG-03` | Ordner gefunden, aber keine Gamelogs darin (meist der falsche Unterordner) |
| `CN-LOG-04` | Logdatei nicht lesbar, fehlende Rechte |
| `CN-LOG-05` | Fehler beim Einlesen der Logs |
| `CN-CHAT-01` | Chatlogs nicht lesbar, die Systemanzeige fällt dann aus |
| `CN-DB-01` | Datenbankfehler |
| `CN-NET-01` | Marktpreise nicht abrufbar, meist nur die Internetverbindung |
| `CN-ESI-01` | ESI-Abfrage fehlgeschlagen, Token evtl. abgelaufen |
| `CN-INTEL-01` | Bedrohungs-Abfrage fehlgeschlagen |
| `CN-CLIP-01` | Zwischenablage nicht lesbar |
| `CN-UPD-01` | Update fehlgeschlagen |
| `CN-CFG-01` | Einstellungen nicht speicherbar, Ordner schreibgeschützt oder Platte voll |
| `CN-SRV-01` | Interner Fehler, bitte melden |

Die drei häufigsten sind harmlos: `CN-NET-01` heißt meistens nur, dass gerade
kein Internet da war, `CN-ESI-01` verschwindet nach einem neuen EVE-Login, und
`CN-LOG-03` bedeutet fast immer, dass der Pfad auf `logs` statt auf
`logs/Gamelogs` zeigt.

## Hinweise

- Marktpreise kommen von market.fuzzwork.co.uk (öffentlich, kein Login).
  Ohne Internet läuft alles weiter, nur ohne ISK-Bewertung.
- Alle Daten bleiben lokal in `dashboard.db`. Backup = Ordner kopieren,
  zusätzlich landen automatische Backups in `backups\`.
- Client-Sprache: Deutsch und Englisch komplett; andere Sprachen funktionieren
  bei Mining/Kampf/Kompression ebenfalls (sprachunabhängige Erkennung), nur
  einzelne Warnungen (Frachtraum voll, Drohnen verladen) brauchen Textmuster,
  erweiterbar in `eve_dashboard.py` (`CARGO_FULL_TEXTS` / `DRONE_UNLOAD_TEXTS`).
- Beenden: das schwarze Konsolenfenster schließen.
