# EVE Canary 🐤 — Installation

Der Kanarienvogel im Bergwerk: ein lokales Dashboard, das die EVE-Online-Logdateien auswertet: Mining, ISK,
Kompression, Schaden, Historie — plus Alarme bei Spieler-Angriffen, leeren
Asteroiden, vollem Frachtraum und Mining-Stillstand. Läuft komplett auf deinem
Rechner, keine Anmeldung, keine Accounts, EULA-konform (liest nur die
Text-Logs, die der EVE-Client selbst schreibt).

## Voraussetzungen

1. **Windows** mit EVE Online
2. **Python 3** (kostenlos): https://www.python.org/downloads/
   - Beim Installieren unbedingt **"Add Python to PATH"** anhaken!
   - Keine weiteren Pakete nötig — das Dashboard nutzt nur die Standardbibliothek.
3. Im EVE-Client muss das **Spielprotokoll** aktiviert sein (ist Standard):
   Esc-Menü → Einstellungen → dort „Spielprotokoll speichern" / „Log game to file"
   aktivieren. Für die System-Anzeige zusätzlich „Chat protokollieren".

## Installation

1. Diesen Ordner irgendwohin entpacken/kopieren (z. B. `C:\EVE-Dashboard`)
2. Doppelklick auf **`start_dashboard.bat`**
3. Der Browser öffnet sich automatisch mit http://localhost:8765
4. Fertig — beim ersten Start werden alle vorhandenen Logs eingelesen.

Der Gamelog-Ordner (`Dokumente\EVE\logs\Gamelogs`) wird automatisch gefunden,
auch bei OneDrive-Dokumenten. Falls nicht: Pfad in `config.json` unter
`"log_dir"` eintragen (die Datei entsteht nach dem ersten Start).

## Erste Schritte

- **⚙ Optionen**: Datenbasis wählen (alle alten Logs auswerten oder erst ab
  jetzt zählen), ISK-Ziel setzen, Watchlist pflegen, Backup erstellen.
- **Einmal in die Seite klicken** nach dem Öffnen — erst danach darf der
  Browser Warntöne abspielen.
- **◱ Overlay**: schwebendes Always-on-top-Fenster über dem EVE-Client
  (benötigt Chrome oder Edge; EVE im Fenster-/randlosen Modus).
- **Desktop-Benachrichtigungen** in den Optionen erlauben, wenn gewünscht.

## EVE-Login (ESI) — optional, für Automatik-Features

Mit dem offiziellen EVE-Login liest Canary zusätzlich (nur lesend!): aktuelles
Schiff, Heavy Water im Laderaum inkl. Kern-Typ (für die „reicht bis…"-Anzeige
bei Orca/Porpoise) und den Wallet-Stand. Ohne ESI funktioniert alles andere
ganz normal; Heavy Water lässt sich dann per ⛽ manuell setzen.

Einrichtung (einmalig, ~5 Minuten — jeder Nutzer braucht seine **eigene** Client-ID):

1. Auf https://developers.eveonline.com mit dem EVE-Account einloggen
   (Developer-Lizenz beim ersten Mal akzeptieren).
2. „Manage Applications" → „Create New Application":
   - Connection Type: **Authentication & API Access**
   - Permissions (Scopes): `esi-assets.read_assets.v1`,
     `esi-location.read_ship_type.v1`, `esi-wallet.read_character_wallet.v1`
   - Callback URL: **http://localhost:8765/sso/callback**
3. Die angezeigte **Client ID** kopieren → Canary → ⚙ Optionen →
   „EVE-Login (ESI)" → einfügen → speichern.
4. „+ Charakter verbinden" → EVE-Login → Charakter wählen → fertig.
   Für weitere Charaktere wiederholen (auch andere Accounts: auf der
   Login-Seite „Switch accounts" oder die URL im Inkognito-Fenster öffnen).

Sicherheit: offizieller CCP-OAuth-Login (PKCE) — Canary sieht nie das Passwort,
bekommt nur Lese-Rechte, Tokens bleiben lokal in `config.json`. Zugriff jederzeit
widerrufbar unter https://community.eveonline.com/support/third-party-applications/

## Hinweise

- Marktpreise kommen von market.fuzzwork.co.uk (öffentlich, kein Login).
  Ohne Internet läuft alles weiter — nur ohne ISK-Bewertung.
- Alle Daten bleiben lokal in `dashboard.db`. Backup = Ordner kopieren,
  zusätzlich landen automatische Backups in `backups\`.
- Client-Sprache: Deutsch und Englisch komplett; andere Sprachen funktionieren
  bei Mining/Kampf/Kompression ebenfalls (sprachunabhängige Erkennung), nur
  einzelne Warnungen (Frachtraum voll, Drohnen verladen) brauchen Textmuster —
  erweiterbar in `eve_dashboard.py` (`CARGO_FULL_TEXTS` / `DRONE_UNLOAD_TEXTS`).
- Beenden: das schwarze Konsolenfenster schließen.
