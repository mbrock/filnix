# stamp.py OUT WEB: name each file the playground in OUT loads with a
# hash of its content (?v=HASH), so a browser holding a cached copy
# fetches a changed file at once and keeps an unchanged one. WEB holds
# dterm.js and dterm.css, which the site puts beside the playground.
# Files are stamped before the files that load them, so a change shows
# up in every URL on its way to index.html.
import hashlib
import pathlib
import sys

out, web = map(pathlib.Path, sys.argv[1:3])


def digest(*paths):
    h = hashlib.sha256()
    for p in paths:
        h.update(p.read_bytes())
    return h.hexdigest()[:12]


def stamp(name, pairs):
    f = out / name
    text = f.read_text()
    for old, new in pairs:
        if text.count(old) != 1:
            sys.exit(f"stamp.py: {name} should contain {old!r} once")
        text = text.replace(old, new)
    f.write_text(text)


swipl = digest(*sorted((out / "swipl").iterdir()))
stamp("worker.js", [
    ('"swipl/swipl-web.js"', f'"swipl/swipl-web.js?v={swipl}"'),
    ('"swipl/" + p', f'"swipl/" + p + "?v={swipl}"'),
    ('fetch("fs.json")', f'fetch("fs.json?v={digest(out / "fs.json")}")'),
])
stamp("play.js", [
    ('"./editor.js"', f'"./editor.js?v={digest(out / "editor.js")}"'),
    ('"./ir.js"', f'"./ir.js?v={digest(out / "ir.js")}"'),
    ('new Worker("worker.js")', f'new Worker("worker.js?v={digest(out / "worker.js")}")'),
])
stamp("index.html", [
    ('href="../dterm.css"', f'href="../dterm.css?v={digest(web / "dterm.css")}"'),
    ('href="play.css"', f'href="play.css?v={digest(out / "play.css")}"'),
    ('src="../dterm.js"', f'src="../dterm.js?v={digest(web / "dterm.js")}"'),
    ('src="play.js"', f'src="play.js?v={digest(out / "play.js")}"'),
])
