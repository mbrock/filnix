#!/usr/bin/env python3
"""chrome.py SITE SRC: give every page of the built site the same chrome.

The pages come from five renderers (pages/ by hand, pandoc's template,
dterm, dterm-rocq and dterm-nix, the playground). Each writes a header
band, but the site's band is the one written here, so the doors, the
site's name and the breadcrumb root change in one place without
re-rendering the cached Prolog and Rocq pages.

For each page it
- replaces <header class="library">...</header> with the site's band, the
  page's door selected (DOORS; door() picks it from the page's path);
- drops a leading "Wiki" crumb: a page's crumbs start at its section;
- adds a Contents menu to the status bar from the page's table of
  contents, for phones, where the side table is hidden;
- adds the site footer, with the links that leave the site;
- sets the blocks about a page (SITE/stream/about.tsv, from blocks.pl)
  in that page's margin, under its title;
- fills <span data-count="KEY"></span> with a count of the site's code
  pages (counts()), and fails if a key has none.
"""
import html
import os
import re
import sys

NAME = "Filnix"
# (id, label, path from the site's root)
# The site's name is the way home.
DOORS = [
    ("stream", "Stream", "stream/"),
    ("docs", "Docs", "docs/"),
    ("explainers", "Explainers", "explainers/"),
    ("nanofil", "nanofil", "nanofil/"),
    ("code", "Code", "code/"),
]
ELSEWHERE = [
    ("Campaigns", "https://nix.swa.sh/"),
    ("Source", "https://github.com/mbrock/filnix"),
]

HEADER = re.compile(r'<header class="library">.*?</header>', re.S)
CRUMBS = re.compile(r'(<nav class="crumbs"[^>]*>)(.*?)(</nav>)', re.S)
WIKI = re.compile(r'^\s*<a class="crumb" href="[^"]*">Wiki</a>\s*<span class="crumb-sep">›</span>\s*')
TOC = re.compile(r'<nav class="toc">.*?</nav>', re.S)
TOC_TITLE = re.compile(r'<div class="toc-title">.*?</div>', re.S)
STATUS_END = re.compile(r'(<div class="status">\s*<div class="page-frame status-frame">.*?</nav>)', re.S)


def door(rel, text):
    """The door a page belongs under, from its path in the site."""
    parts = rel.split("/")
    if rel == "index.html":
        return None
    if parts[0] == "stream":
        return "stream"
    if parts[0] == "docs":
        return "docs"
    if parts[0] in ("nix", "code"):
        return "code"
    if parts[0] == "explainers":
        return "explainers"
    if parts[0] == "nanofil":
        rest = parts[1:]
        if rest and rest[0] in ("rocq", "play", "workbench", "c"):
            return "code"
        if len(rest) == 1 and (rest[0].startswith("concept") or rest[0] == "src.html"):
            return "code"
        # A Prolog module's page: dterm's crumbs pass through src.
        if '<a class="crumb" href="src.html">src</a>' in text:
            return "code"
        return "nanofil"
    if len(parts) == 2 and parts[1] == "index.html":
        return "explainers"
    return None


def band(root, selected):
    doors = "".join(
        f'    <a class="door{" selected" if d == selected else ""}" href="{root}{path}">{label}</a>\n'
        for d, label, path in DOORS)
    return (
        '<header class="library"><div class="page-frame library-frame">\n'
        f'  <div class="library-heading"><h1><a href="{root}index.html">{NAME}</a></h1></div>\n'
        f'  <nav class="doors" aria-label="Sections">\n{doors}  </nav>\n'
        '</div></header>')


def footer(root):
    away = " · ".join(f'<a href="{href}">{label} ↗</a>' for label, href in ELSEWHERE)
    return (
        '<footer class="site-footer"><div class="page-frame">'
        f'<a href="{root}index.html">{NAME}</a> · {away}'
        '</div></footer>\n')


def section_menu(toc):
    """The page's table of contents as a menu in the status bar."""
    inner = TOC_TITLE.sub("", toc[len('<nav class="toc">'):-len("</nav>")])
    return (
        '<details class="section-menu"><summary>Contents</summary>'
        '<div class="section-menu-list" onclick="if(event.target.closest(\'a\'))'
        'this.parentNode.open=false">'
        f'{inner}</div></details>')


COUNT = re.compile(r'<span data-count="([a-z]+)"></span>')


def counts(site, src):
    """How many of each kind of drawn code the site has."""
    def pages(d, skip):
        return sum(1 for f in os.listdir(os.path.join(site, d))
                   if f.endswith(".html") and f not in skip)
    def files(d, ext):
        return sum(1 for f in os.listdir(os.path.join(src, d)) if f.endswith(ext))
    return {
        "nix": pages("nix", {"index.html", "options.html"}),
        "rocq": pages("nanofil/rocq", {"index.html"}),
        "prolog": files("nanofil/src", ".pl"),
        "concepts": files("nanofil/docs/concepts", ".md"),
    }


def fill(text, n):
    return COUNT.sub(lambda m: f'<span data-count="{m.group(1)}">{n[m.group(1)]:,}</span>', text)


def margins(site):
    """The blocks about each page: PAGE -> [(id, kind, created, title)]."""
    found = {}
    path = os.path.join(site, "stream", "about.tsv")
    if os.path.exists(path):
        for row in open(path, encoding="utf-8"):
            page, bid, kind, created, title = row.rstrip("\n").split("\t", 4)
            found.setdefault(page, []).append((bid, kind, created, title))
    return found


H1 = re.compile(r"<h1[^>]*>.*?</h1>", re.S)


def margin(rel, blocks):
    root = "../" * rel.count("/")
    items = "".join(
        f'<li><a href="{root}stream/{bid}.html">{html.escape(title)}</a>'
        f'<span>{kind} · {created[:10]}</span></li>'
        for bid, kind, created, title in sorted(blocks, key=lambda b: b[2], reverse=True)[:8])
    return (f'<aside class="about-blocks"><p>In the <a href="{root}stream/">stream</a>, '
            f'about this page</p><ul>{items}</ul></aside>')


def dress(rel, text, about=()):
    if 'http-equiv="refresh"' in text:
        return text
    root = "../" * rel.count("/")
    if HEADER.search(text):
        text = HEADER.sub(lambda _: band(root, door(rel, text)), text, count=1)
    text = CRUMBS.sub(lambda m: m.group(1) + WIKI.sub("", m.group(2)) + m.group(3), text, count=1)
    toc = TOC.search(text)
    if toc and "section-menu" not in text:
        text = STATUS_END.sub(lambda m: m.group(1) + section_menu(toc.group(0)), text, count=1)
    if about and "about-blocks" not in text:
        main = text.find("<main")
        m = H1.search(text, main if main >= 0 else 0)
        if m:
            text = text[:m.end()] + margin(rel, about) + text[m.end():]
    if "site-footer" not in text and "</body>" in text:
        text = text.replace("</body>", footer(root) + "</body>", 1)
    return text


def main(site, src):
    latest = os.path.join(site, "stream", "latest.html")
    stream = open(latest, encoding="utf-8").read() if os.path.exists(latest) else ""
    if stream:
        os.remove(latest)
    number = counts(site, src)
    about = margins(site)
    n = 0
    for dirpath, _, files in os.walk(site):
        for f in files:
            if not f.endswith(".html"):
                continue
            path = os.path.join(dirpath, f)
            rel = os.path.relpath(path, site)
            with open(path, encoding="utf-8") as fh:
                text = fh.read()
            new = fill(dress(rel, text, about.get(rel, ())), number)
            if rel == "index.html" and stream:
                new = re.sub(r'(<div data-stream="latest">).*?(</div>)',
                             lambda m: m.group(1) + stream + m.group(2), new, count=1, flags=re.S)
            if new != text:
                os.chmod(path, 0o644)
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(new)
                n += 1
    print(f"chrome: dressed {n} pages", file=sys.stderr)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
