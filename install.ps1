# EVE Canary Schnellinstallation
# Ein Befehl in PowerShell genuegt:
#   irm https://raw.githubusercontent.com/Eve-Online-Askend/eve-canary/main/install.ps1 | iex
param(
    [string]$Dir = "",
    [string]$Repo = "https://raw.githubusercontent.com/Eve-Online-Askend/eve-canary/main",
    [switch]$NoStart,
    [switch]$NoShortcut
)
$ErrorActionPreference = "Stop"

Write-Host ""
Write-Host "  ================================" -ForegroundColor DarkCyan
Write-Host "   EVE Canary wird installiert" -ForegroundColor Cyan
Write-Host "  ================================" -ForegroundColor DarkCyan
Write-Host ""

# Installationsordner per Windows-Dialog waehlen
$default = "$env:LOCALAPPDATA\EVE-Canary"
if (-not $Dir) {
    Write-Host "  Es oeffnet sich ein Fenster zur Ordner-Auswahl ..."
    try {
        Add-Type -AssemblyName System.Windows.Forms
        $dlg = New-Object System.Windows.Forms.FolderBrowserDialog
        $dlg.Description = "Wohin soll EVE Canary installiert werden? Canary legt dort einen Unterordner 'EVE-Canary' an. Abbrechen nimmt den Standardordner."
        $dlg.SelectedPath = $env:LOCALAPPDATA
        $dlg.ShowNewFolderButton = $true
        $owner = New-Object System.Windows.Forms.Form
        $owner.TopMost = $true
        $result = $dlg.ShowDialog($owner)
        $owner.Dispose()
        if ($result -eq [System.Windows.Forms.DialogResult]::OK -and $dlg.SelectedPath) {
            if ((Split-Path $dlg.SelectedPath -Leaf) -ieq "EVE-Canary") {
                $Dir = $dlg.SelectedPath
            } else {
                $Dir = Join-Path $dlg.SelectedPath "EVE-Canary"
            }
        } else {
            Write-Host "  Keine Auswahl getroffen, es bleibt beim Standardordner."
            $Dir = $default
        }
    } catch {
        # Kein Fenster moeglich (z.B. Fernsitzung): Eingabe per Tastatur, sonst Standard
        try { $inp = Read-Host "  Ordner [$default]" } catch { $inp = "" }
        if ($inp) {
            $Dir = [Environment]::ExpandEnvironmentVariables($inp.Trim().Trim('"'))
        } else {
            $Dir = $default
        }
    }
}
Write-Host "  Installationsordner: $Dir"
Write-Host ""

function Find-Python {
    foreach ($cmd in "python", "py") {
        try {
            $v = & $cmd --version 2>$null
            if ("$v" -match "Python 3") { return $cmd }
        } catch {}
    }
    return $null
}

$py = Find-Python
if (-not $py) {
    Write-Host "  Python 3 fehlt, Installation laeuft ueber winget (einmalig) ..."
    try {
        winget install -e --id Python.Python.3.12 --accept-package-agreements --accept-source-agreements | Out-Null
    } catch {}
    $env:Path = [Environment]::GetEnvironmentVariable("Path", "User") + ";" +
                [Environment]::GetEnvironmentVariable("Path", "Machine")
    $py = Find-Python
}
if (-not $py) {
    Write-Host ""
    Write-Host "  Python konnte nicht automatisch installiert werden." -ForegroundColor Yellow
    Write-Host "  Bitte von https://www.python.org/downloads/ installieren," -ForegroundColor Yellow
    Write-Host "  beim Setup den Haken bei 'Add Python to PATH' setzen" -ForegroundColor Yellow
    Write-Host "  und diesen Befehl danach noch einmal ausfuehren." -ForegroundColor Yellow
    return
}
Write-Host "  Python gefunden ($py)"

New-Item -ItemType Directory -Force -Path $Dir | Out-Null
$files = "eve_dashboard.py", "ore_types.json", "npc_names.json",
         "mining_tools.json", "README_INSTALL.md", "start_dashboard.bat"
foreach ($f in $files) {
    Invoke-WebRequest -Uri "$Repo/$f" -OutFile (Join-Path $Dir $f) -UseBasicParsing
    Write-Host "  geladen: $f"
}

if (-not $NoShortcut) {
    $ws = New-Object -ComObject WScript.Shell
    foreach ($folder in "Desktop", "Programs") {
        $lnk = $ws.CreateShortcut((Join-Path $ws.SpecialFolders.Item($folder) "EVE Canary.lnk"))
        $lnk.TargetPath = Join-Path $Dir "start_dashboard.bat"
        $lnk.WorkingDirectory = $Dir
        $lnk.IconLocation = "$env:SystemRoot\System32\shell32.dll,13"
        $lnk.Save()
    }
    Write-Host "  Verknuepfungen angelegt: Desktop und Startmenue"
}

Write-Host ""
Write-Host "  Fertig! Canary liegt jetzt in $Dir" -ForegroundColor Green
if (-not $NoStart) {
    Write-Host "  Das Dashboard startet, der Browser oeffnet sich gleich ..."
    Start-Process -FilePath (Join-Path $Dir "start_dashboard.bat") -WorkingDirectory $Dir
}
