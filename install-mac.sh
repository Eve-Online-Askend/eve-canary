#!/usr/bin/env sh
# EVE Canary Installer fuer macOS (Gegenstueck zu install.sh/install.ps1).
# Aufruf:  curl -fsSL <repo>/install-mac.sh | sh
set -eu

REPO="${CANARY_REPO:-https://raw.githubusercontent.com/Eve-Online-Askend/eve-canary/main}"
DIR="${CANARY_DIR:-$HOME/Library/Application Support/EVE-Canary}"

echo ""
echo "  EVE Canary wird installiert"
echo ""

PY=""
for c in python3 python; do
  if command -v "$c" >/dev/null 2>&1 && "$c" -c 'import sys; sys.exit(0 if sys.version_info[0]==3 else 1)' 2>/dev/null; then
    PY="$c"
    break
  fi
done
if [ -z "$PY" ]; then
  echo "  Python 3 wurde nicht gefunden."
  echo "  Am schnellsten geht es mit den Kommandozeilen-Tools von Apple:"
  echo "    xcode-select --install"
  echo "  Alternativ: https://www.python.org/downloads/macos/ oder mit Homebrew:"
  echo "    brew install python3"
  echo "  Danach diesen Befehl noch einmal ausfuehren."
  exit 1
fi
echo "  Python gefunden ($PY)"

if command -v curl >/dev/null 2>&1; then
  DL='curl -fsSL -o'
elif command -v wget >/dev/null 2>&1; then
  DL='wget -q -O'
else
  echo "  Weder curl noch wget gefunden. Bitte eines davon installieren."
  exit 1
fi

FILES="eve_dashboard.py ore_types.json mining_tools.json mission_sigs.json market_types.json README_INSTALL.md start_dashboard.sh"

# Erst vollstaendig in einen Temp-Ordner laden, dann ans Ziel verschieben, damit
# ein abgebrochener Download keine halbe Installation hinterlaesst.
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT INT TERM

# Bevorzugt vom GitHub-Release laden: nur dort zaehlt GitHub die Downloads.
# Klappt das nicht, geht es ueber raw weiter, die Installation haengt nicht daran.
RELBASE=""
if $DL "$TMP/version.json" "$REPO/version.json" 2>/dev/null; then
  SLUG=$(sed -n 's/.*"repo"[^"]*"\([^"]*\)".*/\1/p' "$TMP/version.json")
  TAG=$(sed -n 's/.*"tag"[^"]*"\([^"]*\)".*/\1/p' "$TMP/version.json")
  [ -n "$SLUG" ] && [ -n "$TAG" ] && RELBASE="https://github.com/$SLUG/releases/download/$TAG"
  rm -f "$TMP/version.json"
fi

for f in $FILES; do
  got=""
  if [ -n "$RELBASE" ] && $DL "$TMP/$f" "$RELBASE/$f" 2>/dev/null && [ -s "$TMP/$f" ]; then
    got=1
  elif $DL "$TMP/$f" "$REPO/$f" && [ -s "$TMP/$f" ]; then
    got=1
  fi
  if [ -z "$got" ]; then
    echo ""
    echo "  Download fehlgeschlagen bei: $f"
    echo "  Es wurde nichts installiert. Bitte Internetverbindung pruefen."
    exit 1
  fi
  echo "  geladen: $f"
done

mkdir -p "$DIR"
for f in $FILES; do
  mv -f "$TMP/$f" "$DIR/$f"
done
chmod +x "$DIR/start_dashboard.sh"

# Doppelklick-Start: ein .command-Skript auf dem Schreibtisch, das Finder direkt
# im Terminal ausfuehrt (Spotlight findet es genauso wie einen Programmnamen).
LAUNCHER="$HOME/Desktop/EVE Canary.command"
cat > "$LAUNCHER" <<EOF
#!/usr/bin/env sh
cd "$DIR"
exec ./start_dashboard.sh
EOF
chmod +x "$LAUNCHER"

echo ""
echo "  Fertig. Canary liegt in: $DIR"
echo "  Start ueber \"EVE Canary\" auf dem Schreibtisch (per Doppelklick oder"
echo "  Spotlight, cmd+leertaste, Namen tippen) oder:"
echo "    \"$DIR/start_dashboard.sh\""
echo ""
echo "  Den Gamelog-Ordner (Dokumente/EVE/logs/Gamelogs) findet Canary von"
echo "  selbst. Wird nichts gefunden, den Pfad einfach in den Optionen eintragen."
echo ""

cd "$DIR"
exec ./start_dashboard.sh
