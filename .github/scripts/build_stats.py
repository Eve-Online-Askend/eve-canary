# -*- coding: utf-8 -*-
"""
Rechnet stats.json neu aus, fuer den CI-Cronjob (.github/workflows/stats.yml).

Portiert dieselbe Rechnung wie stats_build() in eve-live-dashboard/release.py,
nur ohne die lokale Zwei-Repo-Struktur und ohne git-credential-Zugriff: hier
kommt der Token vom Workflow (GITHUB_TOKEN), das Schreiben und Pushen macht
der Workflow selbst per git.
"""
import json
import os
import re
import time
import urllib.error
import urllib.request
from pathlib import Path

REPO_SLUG = "Eve-Online-Askend/eve-canary"
REPO = Path(__file__).resolve().parents[2]


def api(url, token=None):
    head = {"Accept": "application/vnd.github+json", "User-Agent": "canary-stats-ci"}
    if token:
        head["Authorization"] = "Bearer " + token
    req = urllib.request.Request(url, headers=head)
    with urllib.request.urlopen(req, timeout=60) as r:
        raw = r.read()
        return json.loads(raw) if raw else {}


def ping_release(token, tag):
    try:
        return api(f"https://api.github.com/repos/{REPO_SLUG}/releases/tags/{tag}", token)
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return None
        raise


def ping_assets(rel, token=None):
    if not rel:
        return {}
    out, page = {}, 1
    while True:
        got = api(f"https://api.github.com/repos/{REPO_SLUG}/releases/"
                  f"{rel['id']}/assets?per_page=100&page={page}", token)
        for a in got:
            out[a["name"]] = a
        if len(got) < 100:
            return out
        page += 1


def stats_build(token=None):
    rels, seite = [], 1
    while seite <= 4:
        teil = api(f"https://api.github.com/repos/{REPO_SLUG}/releases"
                   f"?per_page=100&page={seite}", token)
        rels += teil
        if len(teil) < 100:
            break
        seite += 1
    vers = [r for r in rels if re.match(r"^v\d", r.get("tag_name", ""))]

    def summe(rel, datei):
        return sum(a["download_count"] for a in rel.get("assets", [])
                   if a["name"] == datei)

    win = sum(summe(r, "start_dashboard.bat") for r in vers)
    lin = sum(summe(r, "start_dashboard.sh") for r in vers)
    zeilen = [{"v": r["tag_name"].lstrip("v"), "d": summe(r, "eve_dashboard.py"),
               "t": r["published_at"]} for r in vers]
    mit = [z for z in zeilen if z["d"] > 0]
    neuste = max(zeilen, key=lambda z: z["t"]) if zeilen else None

    aktiv = {"monat": {}, "tag": {}}
    for tag, ziel in ((f"stats-{time.strftime('%Y', time.gmtime())}", "monat"),
                      (time.strftime("stats-%Y-%m", time.gmtime()), "tag"),
                      (time.strftime("stats-%Y-%m",
                                     time.gmtime(time.time() - 31 * 86400)), "tag")):
        try:
            for name, a in ping_assets(ping_release(token, tag), token).items():
                if a["download_count"]:
                    aktiv[ziel][name[len("ping-"):-len(".json")]] = a["download_count"]
        except urllib.error.HTTPError:
            pass

    return {
        "stand": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "installs": {"win": win, "lin": lin},
        "downloads": {
            "total": sum(z["d"] for z in zeilen),
            "versionen": len(mit),
            "latest": {"v": neuste["v"], "d": neuste["d"]} if neuste else None,
            "top": sorted(mit, key=lambda z: -z["d"])[:5]},
        "aktiv": aktiv}


if __name__ == "__main__":
    token = os.environ.get("GITHUB_TOKEN")
    daten = stats_build(token)
    (REPO / "stats.json").write_text(
        json.dumps(daten, ensure_ascii=False, indent=1), encoding="utf-8")
    print(f"stats.json geschrieben: {daten['installs']['win']} Windows + "
          f"{daten['installs']['lin']} Linux, {daten['downloads']['total']} Downloads, "
          f"aktiv {daten['aktiv']['monat']}")
