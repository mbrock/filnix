#!/usr/bin/env python3
"""Pin a complete site's resources, but not navigation, before publication."""
import argparse
from concurrent.futures import ProcessPoolExecutor
import html
from html.parser import HTMLParser
from itertools import repeat
from pathlib import Path
import re
from urllib.parse import urljoin, urlsplit, urlunsplit


class Page(HTMLParser):
    def __init__(self, source, path, sha):
        super().__init__(convert_charrefs=False)
        self.source = source
        self.url = "https://filnix.org/" + path
        self.prefix = f"/__releases/{sha}"
        self.lines = [0] + [match.end() for match in re.finditer("\n", source)]
        self.edits = []

    def handle_starttag(self, tag, attrs):
        updated = []
        for name, value in attrs:
            resource = name in ("src", "poster") or (
                name == "href" and (
                    tag == "link" and dict(attrs).get("rel") != "canonical"
                    or tag in ("a", "area") and "download" in dict(attrs)
                )
            )
            if resource and value and not value.startswith("#"):
                url = urlsplit(urljoin(self.url, value))
                if url.scheme == "https" and url.netloc == "filnix.org":
                    path = re.sub(r"^/__releases/[0-9a-f]{40}(?=/|$)", "", url.path)
                    value = urlunsplit(("", "", self.prefix + path, url.query, url.fragment))
            updated.append((name, value))
        if updated != attrs:
            # Only replace changed opening tags; scripts, styles, entities and
            # all other bytes stay untouched. HTMLParser handles quoted '>'.
            raw = self.get_starttag_text()
            text = "<" + tag + "".join(
                " " + name + ("" if value is None else '="' + html.escape(value, quote=True) + '"')
                for name, value in updated
            ) + ("/>" if raw.endswith("/>") else ">")
            line, column = self.getpos()
            start = self.lines[line - 1] + column
            self.edits.append((start, start + len(raw), text))

    handle_startendtag = handle_starttag

    def render(self):
        self.feed(self.source)
        parts, offset = [], 0
        for start, end, text in self.edits:
            parts.extend((self.source[offset:start], text))
            offset = end
        parts.append(self.source[offset:])
        return "".join(parts)


def prepare_page(path, root, sha):
    source = path.read_text()
    result = Page(source, path.relative_to(root).as_posix(), sha).render()
    if result != source:
        # Site artifacts originate in the read-only Nix store.
        path.chmod(path.stat().st_mode | 0o200)
        path.write_text(result)


def prepare(root, sha):
    if not re.fullmatch(r"[0-9a-f]{40}", sha):
        raise ValueError("Expected a full release commit SHA")
    # HTML parsing is CPU-bound; each worker owns a different file. Keep
    # resource pinning byte-identical without serializing hundreds of pages.
    with ProcessPoolExecutor(max_workers=4) as pool:
        list(pool.map(prepare_page, root.rglob("*.html"), repeat(root), repeat(sha)))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("site", type=Path)
    parser.add_argument("sha")
    args = parser.parse_args()
    prepare(args.site, args.sha)
