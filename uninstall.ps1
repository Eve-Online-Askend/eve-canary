# EVE Canary Deinstallation
# Entfernt Autostart, Verknuepfungen und optional den Programmordner.
# Ausfuehren aus dem Canary-Ordner:  powershell -ExecutionPolicy Bypass -File uninstall.ps1
param([switch]$KeepData)
$ErrorActionPreference = "SilentlyContinue"

Write-Host ""
Write-Host "  EVE Canary wird entfernt ..." -ForegroundColor Cyan

# 1) Laufende Instanz beenden (Prozess mit eve_dashboard.py)
Get-CimInstance Win32_Process -Filter "Name='python.exe' OR Name='pythonw.exe'" |
    Where-Object { $_.CommandLine -match 'eve_dashboard\.py' } |
    ForEach-Object { Stop-Process -Id $_.ProcessId -Force }

# 2) Autostart-VBS entfernen
$vbs = Join-Path $env:APPDATA "Microsoft\Windows\Start Menu\Programs\Startup\EVE-Canary-Autostart.vbs"
if (Test-Path $vbs) { Remove-Item $vbs -Force; Write-Host "  Autostart entfernt" }

# 3) Verknuepfungen (Desktop + Startmenue)
$ws = New-Object -ComObject WScript.Shell
foreach ($folder in "Desktop", "Programs") {
    $lnk = Join-Path $ws.SpecialFolders.Item($folder) "EVE Canary.lnk"
    if (Test-Path $lnk) { Remove-Item $lnk -Force; Write-Host "  Verknuepfung entfernt: $folder" }
}

# 4) Programmordner (dieser Ordner)
$dir = Split-Path -Parent $MyInvocation.MyCommand.Path
if ($KeepData) {
    Write-Host "  Deine Daten (dashboard.db, config.json) bleiben in $dir erhalten." -ForegroundColor Yellow
    Write-Host "  Ordner NICHT geloescht. Fertig." -ForegroundColor Green
} else {
    Write-Host ""
    Write-Host "  Loescht jetzt den kompletten Ordner inkl. Statistik und Einstellungen:" -ForegroundColor Yellow
    Write-Host "  $dir"
    $a = Read-Host "  Wirklich loeschen? (j/N)"
    if ($a -eq "j" -or $a -eq "J") {
        Set-Location $env:TEMP
        Remove-Item -Recurse -Force $dir
        Write-Host "  Alles entfernt. Danke fuer's Fliegen mit Canary!" -ForegroundColor Green
    } else {
        Write-Host "  Ordner behalten. Autostart und Verknuepfungen sind entfernt." -ForegroundColor Green
    }
}
