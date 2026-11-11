#!/usr/bin/env python3
"""Typeset a dterm page as a PDF with Typst.

    typeset.py PAGE.html -o OUT.pdf [--profile remarkable|a5|a4] [--typ OUT.typ]

PAGE.html is any page the Filnix wiki draws with dterm: a nanofil
document (nanofil/lambda-anf.html), a module (nanofil/ir.html), a Rocq
file (nanofil/rocq/...), a Nix file (nix/...). It must sit in the
wiki's layout, so its stylesheets and scripts load (the site build, or
pdf.sh's scratch copy).

Headless Chromium loads the page with print.css at the PDF's measure and
fonts, so dterm.js's printer chooses every term's line breaks for the
paper, as it does for a phone. extract.js then writes the laid-out page
as Typst: prose, lists, tables and headings for Typst to set and justify,
and every drawn block (clauses, Rocq, C, diagrams) as the lines the
printer set, glyph runs and bows at the positions it chose. Typst only
sets what it is given; no layout search runs inside it (README.md).

Chromium is driven over --remote-debugging-pipe, so nothing beyond the
standard library is needed besides `chromium` and `typst` on PATH (or
CHROMIUM and TYPST).
"""

import argparse
import fcntl
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
PT_PER_PX = 0.75

# Paper: width, height, margins (top, right, bottom, left) in mm, and the
# sizes of prose (in Equity; Source Serif 4 is set a little smaller) and of
# drawn terms in pt. The reMarkable 1 and 2 screen
# is 157.8 x 210.4 mm at 226 dpi; a page of exactly that shape fills it.
PROFILES = {
    "remarkable": dict(w=157.8, h=210.4, m=(13, 12, 15, 12), body=11.4, code=8.8, grey=True),
    "a5": dict(w=148, h=210, m=(16, 15, 18, 15), body=10.8, code=8.4, grey=False),
    "a4": dict(w=210, h=297, m=(25, 32, 28, 32), body=11.6, code=9.2, grey=False),
}
MM = 72 / 25.4


class Chrome:
    """A headless Chromium spoken to over a CDP pipe (fd 3 in, fd 4 out)."""

    def __init__(self, exe, fontconfig):
        self.to_r, self.to_w = os.pipe()
        self.from_r, self.from_w = os.pipe()
        self.profile = tempfile.mkdtemp(prefix="typeset-chrome-")
        env = dict(os.environ, FONTCONFIG_FILE=fontconfig)
        args = [exe, "--headless=new", "--remote-debugging-pipe", "--no-sandbox",
                "--disable-gpu", "--no-first-run", "--no-default-browser-check",
                "--allow-file-access-from-files", "--hide-scrollbars",
                "--font-render-hinting=none", f"--user-data-dir={self.profile}", "about:blank"]
        self.proc = subprocess.Popen(
            args, env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            pass_fds=(3, 4), preexec_fn=self._fds)
        os.close(self.to_r)
        os.close(self.from_w)
        self.buf = b""
        self.next_id = 0
        self.events = []

    def _fds(self):
        a = fcntl.fcntl(self.to_r, fcntl.F_DUPFD, 10)
        b = fcntl.fcntl(self.from_w, fcntl.F_DUPFD, 10)
        os.dup2(a, 3)
        os.dup2(b, 4)

    def _read(self):
        while b"\0" not in self.buf:
            chunk = os.read(self.from_r, 1 << 16)
            if not chunk:
                raise RuntimeError("chromium closed the pipe")
            self.buf += chunk
        msg, self.buf = self.buf.split(b"\0", 1)
        return json.loads(msg)

    def call(self, method, session=None, **params):
        self.next_id += 1
        msg = {"id": self.next_id, "method": method, "params": params}
        if session:
            msg["sessionId"] = session
        os.write(self.to_w, json.dumps(msg).encode() + b"\0")
        while True:
            m = self._read()
            if m.get("id") == self.next_id:
                if "error" in m:
                    raise RuntimeError(f"{method}: {m['error']}")
                return m["result"]
            self.events.append(m)

    def wait_event(self, method):
        for i, m in enumerate(self.events):
            if m.get("method") == method:
                return self.events.pop(i)
        while True:
            m = self._read()
            if m.get("method") == method:
                return m
            self.events.append(m)

    def close(self):
        try:
            self.call("Browser.close")
        except Exception:
            pass
        self.proc.wait(timeout=10)
        shutil.rmtree(self.profile, ignore_errors=True)


def equity(dirs):
    """Whether the licensed Equity family is among the font directories."""
    return any(p.name.startswith("Equity") for d in dirs for p in Path(d).rglob("*.otf"))


def font_dirs():
    dirs = [d for d in os.environ.get("TYPESET_FONTS", "").split(":") if d]
    if not dirs:
        sys.exit("typeset: set TYPESET_FONTS to the font directories (Public Sans, "
                 "Source Serif 4, DM Mono, and optionally Equity); typeset.nix does")
    return dirs


def fontconfig(dirs, tmp):
    conf = Path(tmp) / "fonts.conf"
    conf.write_text("<?xml version='1.0'?>\n<!DOCTYPE fontconfig SYSTEM 'fonts.dtd'>\n<fontconfig>\n"
                    + "".join(f"  <dir>{d}</dir>\n" for d in dirs)
                    + f"  <cachedir>{tmp}/fc-cache</cachedir>\n</fontconfig>\n")
    return str(conf)


def page_css(p):
    """The page's measure, in CSS px, for print.css."""
    text_w = (p["w"] - p["m"][1] - p["m"][3]) * MM
    return (f":root {{ --typeset-width: {text_w / PT_PER_PX:.3f}px;"
            f" --typeset-body: {p['body'] / PT_PER_PX:.3f}px;"
            f" --typeset-code: {p['code'] / PT_PER_PX:.3f}px; }}\n"), text_w


def prepare(page, css, tmp):
    """A copy of the page beside it, with print.css and without web fonts."""
    html = page.read_text()
    html = "\n".join(l for l in html.split("\n") if "fonts.googleapis" not in l and "fonts.gstatic" not in l)
    style = (f"<style>{css}</style>\n<link rel=\"stylesheet\" href=\"{(HERE / 'print.css').as_uri()}\">\n"
             f"<script src=\"{(HERE / 'extract.js').as_uri()}\"></script>\n")
    html = html.replace("</head>", style + "</head>", 1)
    fd, copy = tempfile.mkstemp(prefix=".typeset-", suffix=".html", dir=page.parent)
    with os.fdopen(fd, "w") as f:
        f.write(html)
    return Path(copy)


def extract(page, profile, base_url):
    p = PROFILES[profile]
    with tempfile.TemporaryDirectory(prefix="typeset-") as tmp:
        css, text_w = page_css(p)
        copy = prepare(page, css, tmp)
        chrome = Chrome(os.environ.get("CHROMIUM", "chromium"), fontconfig(font_dirs(), tmp))
        try:
            target = chrome.call("Target.createTarget", url="about:blank")["targetId"]
            s = chrome.call("Target.attachToTarget", targetId=target, flatten=True)["sessionId"]
            chrome.call("Emulation.setDeviceMetricsOverride", s, width=round(text_w / PT_PER_PX) + 1,
                        height=1200, deviceScaleFactor=2, mobile=False)
            chrome.call("Page.enable", s)
            chrome.call("Runtime.enable", s)
            chrome.call("Page.navigate", s, url=copy.as_uri())
            chrome.wait_event("Page.loadEventFired")
            text_h = (p["h"] - p["m"][0] - p["m"][2]) * MM
            opts = json.dumps({"base": base_url, "width": text_w / PT_PER_PX,
                               "maxHeight": 0.92 * text_h / PT_PER_PX})
            r = chrome.call("Runtime.evaluate", s, expression=f"dtermTypst({opts})",
                            awaitPromise=True, returnByValue=True, timeout=120000)
            if "exceptionDetails" in r:
                d = r["exceptionDetails"]
                raise RuntimeError(d.get("exception", {}).get("description") or d.get("text"))
            for e in chrome.events:
                if e.get("method") == "Runtime.consoleAPICalled":
                    a = e["params"]["args"]
                    print("console:", " ".join(str(x.get("value", x.get("description"))) for x in a), file=sys.stderr)
            return r["result"]["value"]
        finally:
            chrome.close()
            copy.unlink(missing_ok=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("page", type=Path)
    ap.add_argument("-o", "--output", type=Path)
    ap.add_argument("--profile", default="remarkable", choices=sorted(PROFILES))
    ap.add_argument("--typ", type=Path, help="also keep the Typst source here")
    ap.add_argument("--base", default="https://filnix.org/",
                    help="the wiki's URL, for links out of the PDF")
    ap.add_argument("--site", type=Path, help="the wiki's root directory (default: guessed)")
    a = ap.parse_args()
    page = a.page.resolve()
    site = (a.site or guess_site(page)).resolve()
    rel = page.relative_to(site).as_posix()
    p = PROFILES[a.profile]
    out = extract(page, a.profile, a.base.rstrip("/") + "/" + rel)
    if equity(font_dirs()):
        body, prose = p["body"], '("Equity OT A", "Source Serif 4")'
    else:
        body, prose = round(p["body"] * 0.92, 2), '("Source Serif 4",)'
    title = out["title"]
    source = rel.removesuffix(".html").replace("/", " · ")
    head = (f'#import "{(HERE / "dterm.typ").as_posix()}": *\n'
            f"#show: dterm-paper.with(\n"
            f"  title: {typst_str(title)},\n"
            f"  source: {typst_str(source)},\n"
            f"  url: {typst_str(a.base.rstrip('/') + '/' + rel)},\n"
            f"  paper: (width: {p['w']}mm, height: {p['h']}mm),\n"
            f"  margin: (top: {p['m'][0]}mm, right: {p['m'][1]}mm, bottom: {p['m'][2]}mm, left: {p['m'][3]}mm),\n"
            f"  body-size: {body}pt,\n"
            f"  prose-font: {prose},\n"
            f"  grey: {'true' if p['grey'] else 'false'},\n"
            f")\n\n")
    typ = head + out["typst"]
    output = a.output or page.with_suffix(".pdf")
    with tempfile.TemporaryDirectory(prefix="typeset-") as tmp:
        src = Path(a.typ) if a.typ else Path(tmp) / "page.typ"
        src.write_text(typ)
        cmd = [os.environ.get("TYPST", "typst"), "compile", "--root", "/", "--ignore-system-fonts"]
        for d in font_dirs():
            cmd += ["--font-path", d]
        cmd += [str(src), str(output)]
        r = subprocess.run(cmd)
        if r.returncode:
            sys.exit(r.returncode)
    print(output)


def typst_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", " ") + '"'


def guess_site(page):
    """The wiki root: the nearest ancestor with style.css."""
    for d in page.parents:
        if (d / "style.css").exists():
            return d
    return page.parent


if __name__ == "__main__":
    main()
