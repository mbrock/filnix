#!/usr/bin/env python3
"""history.py SITE REPO: the documents' history, from git, on the built site.

The Nix build cannot see .git, so the site's workflow runs this on the
built copy (.github/workflows/pages.yml, with the full history checked
out). It reads `git log` of docs/, nanofil/docs/ and pages/ once,
following renames, and

- writes SITE/history.json: per document, when it was written and last
  changed, its edits, the Amp threads and the authors behind them;
- puts a line of dates and activity under each document's title;
- fills the home page's <div data-history="recent"> with the documents
  written or changed most recently.

A commit that touches more than SWEEP documents (a restyle, a rename of
many, a new kind of link) is maintenance: it does not count as an edit
or make a document look recently changed. "Now" is HEAD's commit time,
so a rebuild of one commit gives the same site.
"""
import collections
import datetime as dt
import html
import json
import os
import re
import subprocess
import sys

SWEEP = 15
ROOTS = ["docs", "nanofil/docs", "pages"]
GITHUB = "https://github.com/mbrock/filnix"
DOC = re.compile(r"^(docs|nanofil/docs)/(archive/)?[^/]+\.(md|txt)$|^pages/[^/]+/index\.html$")


def git(repo, *args):
    return subprocess.run(["git", "-C", repo, *args], check=True, capture_output=True, text=True).stdout


def commits(repo):
    """Each commit touching ROOTS, newest first, with its changes."""
    out = git(repo, "log", "-M", "--name-status", "--format=@@%H%x09%aI%x09%an%x09"
              "%(trailers:key=Amp-Thread-ID,valueonly,separator=%x2C)%x09%s", "--", *ROOTS)
    log, cur = [], None
    for line in out.splitlines():
        if line.startswith("@@"):
            h, when, who, threads, subject = line[2:].split("\t", 4)
            cur = {"sha": h, "when": when, "who": who, "subject": subject,
                   "threads": [t.rstrip("/").rsplit("/", 1)[-1] for t in threads.split(",") if t.strip()],
                   "changes": []}
            log.append(cur)
        elif line.strip() and cur is not None:
            parts = line.split("\t")
            cur["changes"].append((parts[0][0], parts[1:]))
    return log


def documents(repo):
    files = git(repo, "ls-files", "--", *ROOTS).splitlines()
    return [f for f in files if DOC.match(f)]


def history(repo):
    docs = documents(repo)
    alias = {d: d for d in docs}
    seen = collections.defaultdict(list)
    for c in commits(repo):
        touched = []
        for kind, paths in c["changes"]:
            if kind == "R":
                old, new = paths
                doc = alias.get(new)
                if doc:
                    alias[old] = doc
                    touched.append(doc)
            else:
                doc = alias.get(paths[0])
                if doc:
                    touched.append(doc)
        sweep = len(set(touched)) > SWEEP
        for doc in set(touched):
            seen[doc].append((c, sweep))
    return docs, seen


def when(iso):
    return dt.datetime.fromisoformat(iso).astimezone(dt.timezone.utc)


def summary(doc, entries, now):
    edits = [c for c, sweep in entries if not sweep]
    first = when(entries[-1][0]["when"])
    last = when((edits or [entries[0][0]])[0]["when"])
    authors = collections.Counter(c["who"] for c in edits)
    threads = {t for c in edits for t in c["threads"]}
    return {
        "path": doc,
        "created": first.isoformat(),
        "changed": last.isoformat(),
        "edits": len(edits),
        "week": sum(1 for c in edits if (now - when(c["when"])).days < 7),
        "month": sum(1 for c in edits if (now - when(c["when"])).days < 30),
        "threads": sorted(threads),
        "authors": dict(authors.most_common()),
        "commits": [{"sha": c["sha"][:10], "when": c["when"], "who": c["who"],
                     "threads": c["threads"], "subject": c["subject"]} for c in edits[:20]],
    }


def day(t, now):
    return t.strftime("%-d %b") if t.year == now.year else t.strftime("%-d %b %Y")


def line(s, now, archived):
    created, changed = when(s["created"]), when(s["changed"])
    bits = [f"Written {day(created, now)}"]
    if s["edits"] > 1 and changed.date() != created.date():
        bits.append(f"last changed {day(changed, now)}")
    n, t = s["edits"], len(s["threads"])
    bits.append(f"{n} edit{'s' if n != 1 else ''}" + (f" in {t} Amp thread{'s' if t != 1 else ''}" if t else ""))
    who = list(s["authors"])
    if who:
        bits.append("by " + " and ".join(who[:2]) + (" and others" if len(who) > 2 else ""))
    if not archived:
        if s["week"]:
            bits.append(f'<span class="busy">{s["week"]} this week</span>')
        elif s["month"]:
            bits.append(f'{s["month"]} in the last 30 days')
        elif (now - changed).days >= 45:
            bits.append(f"untouched for {(now - changed).days} days")
    bits.append(f'<a href="{GITHUB}/commits/main/{s["path"]}">history</a>')
    return '<p class="doc-history">' + " · ".join(bits) + "</p>"


def pages(site):
    """Each document's page in the built site, and its source path."""
    found = {}
    for src_dir, out_dir in (("docs", "docs"), ("nanofil/docs", "nanofil/docs")):
        for f in sorted(os.listdir(os.path.join(site, out_dir))):
            if not f.endswith(".html"):
                continue
            name = f[:-5]
            page = os.path.join(out_dir, f)
            text = open(os.path.join(site, page), encoding="utf-8").read()
            stub = re.search(r'http-equiv="refresh" content="0; url=\.\./([^"]+)"', text)
            if stub:
                page = "nanofil/" + stub.group(1)
            base = "README" if name == "index" else name
            for cand in (f"{src_dir}/{base}.md", f"{src_dir}/archive/{base}.md"):
                found[page] = (cand, out_dir)
                if os.path.exists(os.path.join(REPO, cand)):
                    break
    found["nanofil/index.html"] = ("nanofil/docs/README.md", "nanofil/docs")
    return found


def plain(h):
    """A heading's text: no tags, entities decoded, one line."""
    return " ".join(html.unescape(re.sub(r"<[^>]+>", "", h)).split())


TITLE = re.compile(r'(<h1 class="title">.*?</h1>|<h1[^>]*>.*?</h1>)', re.S)


def recent(index, titles, now, n=12):
    rows = sorted((s for s in index.values() if s["path"] in titles and "/archive/" not in s["path"]),
                  key=lambda s: s["changed"], reverse=True)[:n]
    items = []
    for s in rows:
        page, title = titles[s["path"]]
        fresh = (now - when(s["created"])).days < 7
        note = '<span class="new">new</span>' if fresh else (
            f'{s["week"]} edit{"s" if s["week"] != 1 else ""} this week' if s["week"] else "")
        items.append(
            f'<li><span class="when">{day(when(s["changed"]), now)}</span>'
            f'<span class="what"><a href="{page}">{html.escape(title)}</a>'
            + (f'<span class="note">{note}</span>' if note else "") + "</span></li>")
    return '<ul class="recent">' + "".join(items) + "</ul>"


def main(site, repo):
    global REPO
    REPO = repo
    now = when(git(repo, "log", "-1", "--format=%cI").strip())
    docs, seen = history(repo)
    index = {d: summary(d, seen[d], now) for d in docs if seen.get(d)}
    titles = {}
    dressed = 0
    for page, (src, _) in pages(site).items():
        s = index.get(src)
        path = os.path.join(site, page)
        if not s or not os.path.exists(path):
            continue
        text = open(path, encoding="utf-8").read()
        m = TITLE.search(text, text.find("</header>") + 1)
        if not m:
            continue
        titles[src] = (page, plain(m.group(1)))
        if "doc-history" in text:
            continue
        text = text[:m.end()] + "\n" + line(s, now, "/archive/" in src) + text[m.end():]
        os.chmod(path, 0o644)
        open(path, "w", encoding="utf-8").write(text)
        dressed += 1
    for d in docs:
        if d.startswith("pages/") and d in index:
            page = d[len("pages/"):]
            text = open(os.path.join(site, page), encoding="utf-8").read() if os.path.exists(os.path.join(site, page)) else ""
            m = re.compile(r"<h1[^>]*>(.*?)</h1>", re.S).search(text, text.find("</header>") + 1)
            if m and page != "index.html" and 'class="archived"' not in text:
                titles[d] = (page, plain(m.group(1)))
    home = os.path.join(site, "index.html")
    text = open(home, encoding="utf-8").read()
    text = re.sub(r'(<div data-history="recent">).*?(</div>)',
                  lambda m: m.group(1) + recent(index, titles, now) + m.group(2), text, count=1, flags=re.S)
    os.chmod(home, 0o644)
    open(home, "w", encoding="utf-8").write(text)
    with open(os.path.join(site, "history.json"), "w") as f:
        json.dump({"now": now.isoformat(), "head": git(repo, "rev-parse", "HEAD").strip(),
                   "sweep": SWEEP, "documents": index}, f, indent=1)
    print(f"history: {len(index)} documents, {dressed} pages dated", file=sys.stderr)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
