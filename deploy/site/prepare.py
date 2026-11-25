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


# Fast scanner: skip comments, <style> bodies, and all non-resource tags (such
# as hundreds of thousands of <span> elements) in C, then hand only candidate
# opening tags to HTMLParser for exact attribute and quoting handling.
CANDIDATE = re.compile(
    r"<!--.*?-->"
    r"|<style\b(?:\"[^\"]*\"|'[^']*'|[^\"'>])*>.*?</style>"
    r"|(<script\b(?:\"[^\"]*\"|'[^']*'|[^\"'>])*>).*?</script>"
    r"|(<(?:link|img|iframe|source|video|audio|embed|object|track|input|frame)\b(?:\"[^\"]*\"|'[^']*'|[^\"'>])*>)"
    r"|(<(?:a|area)\b(?:\"[^\"]*\"|'[^']*'|[^\"'>])*\bdownload\b(?:\"[^\"]*\"|'[^']*'|[^\"'>])*>)",
    re.IGNORECASE | re.DOTALL,
)


class TagRewriter(HTMLParser):
    def __init__(self, page_url, prefix):
        super().__init__(convert_charrefs=False)
        self.url = page_url
        self.prefix = prefix
        self.result = None

    def handle_starttag(self, tag, attrs):
        updated = []
        attr_map = dict(attrs)
        for name, value in attrs:
            resource = name in ("src", "poster") or (
                name == "href" and (
                    tag == "link" and attr_map.get("rel") != "canonical"
                    or tag in ("a", "area") and "download" in attr_map
                )
            )
            if resource and value and not value.startswith("#"):
                url = urlsplit(urljoin(self.url, value))
                if url.scheme == "https" and url.netloc == "filnix.org":
                    path = re.sub(r"^/__releases/[0-9a-f]{40}(?=/|$)", "", url.path)
                    value = urlunsplit(("", "", self.prefix + path, url.query, url.fragment))
            updated.append((name, value))
        if updated != attrs:
            raw = self.get_starttag_text()
            self.result = "<" + tag + "".join(
                " " + name + ("" if value is None else '="' + html.escape(value, quote=True) + '"')
                for name, value in updated
            ) + ("/>" if raw.endswith("/>") else ">")

    handle_startendtag = handle_starttag


def rewrite_html(source, path, sha):
    page_url = "https://filnix.org/" + path
    prefix = f"/__releases/{sha}"
    edits = []
    for match in CANDIDATE.finditer(source):
        group = 1 if match.group(1) else 2 if match.group(2) else 3 if match.group(3) else None
        if group is None:
            continue
        raw = match.group(group)
        parser = TagRewriter(page_url, prefix)
        parser.feed(raw)
        parser.close()
        if parser.result is not None:
            edits.append((match.start(group), match.end(group), parser.result))
    if not edits:
        return source
    parts, offset = [], 0
    for start, end, text in edits:
        parts.extend((source[offset:start], text))
        offset = end
    parts.append(source[offset:])
    return "".join(parts)


def prepare_page(path, root, sha):
    source = path.read_text()
    result = rewrite_html(source, path.relative_to(root).as_posix(), sha)
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
