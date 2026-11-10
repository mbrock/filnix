"""Published pages navigate canonically but load one immutable set of assets."""
from html.parser import HTMLParser
from pathlib import Path
import subprocess
import tempfile
import unittest


PREPARE = Path(__file__).resolve().parents[1] / "deploy/site/prepare.py"


class SitePrepare(unittest.TestCase):
    def test_publication_pins_resources_not_navigation_and_preserves_content(self):
        sha = "a" * 40
        prefix = f"/__releases/{sha}"
        source = '''<!doctype html>
<head><link rel="stylesheet" href="../../style.css?x=1&amp;y=2">
<link rel="canonical" href="https://filnix.org/nanofil/play/index.html"></head>
<body><a href="../guide.html#start">Guide</a><a href="#local">Local</a>
<a href="https://elsewhere.test/a.html">External</a><a href="mailto:a@b.test">Mail</a>
<a download href="/download.bin">Download</a>
<script type="module" src="play.js"></script>
<img title="quoted > and &amp;" src="/logo.png"/>
<img src="data:image/png;base64,AA==">
<iframe src="samples.html"></iframe>
<script>const untouched = '<a href="not-a-link.html">&thing;</a>';</script>
<pre>&lt;img src="example.png"&gt;</pre></body>'''
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "nanofil/play/index.html"
            path.parent.mkdir(parents=True)
            path.write_text(source)
            binary = root / "download.bin"
            binary.write_bytes(b"\x00\xff\x01")
            for release in (sha, sha, "b" * 40):
                subprocess.run(["python3", str(PREPARE), str(root), release], check=True)
                output = path.read_text()
                current = f"/__releases/{release}"
                tags = []
                class Tags(HTMLParser):
                    def handle_starttag(self, tag, attrs):
                        tags.append((tag, dict(attrs)))
                Tags().feed(output)
                self.assertIn(("link", {"rel": "stylesheet", "href": current + "/style.css?x=1&y=2"}), tags)
                self.assertIn(("link", {"rel": "canonical", "href": "https://filnix.org/nanofil/play/index.html"}), tags)
                self.assertIn(("a", {"href": "../guide.html#start"}), tags)
                self.assertIn(("a", {"href": "#local"}), tags)
                self.assertIn(("a", {"href": "https://elsewhere.test/a.html"}), tags)
                self.assertIn(("a", {"href": "mailto:a@b.test"}), tags)
                self.assertIn(("a", {"download": None, "href": current + "/download.bin"}), tags)
                self.assertIn(("script", {"type": "module", "src": current + "/nanofil/play/play.js"}), tags)
                self.assertIn(("img", {"title": "quoted > and &", "src": current + "/logo.png"}), tags)
                self.assertIn(("img", {"src": "data:image/png;base64,AA=="}), tags)
                self.assertIn(("iframe", {"src": current + "/nanofil/play/samples.html"}), tags)
                self.assertIn("<script>const untouched = '<a href=\"not-a-link.html\">&thing;</a>';</script>", output)
                self.assertIn('<pre>&lt;img src="example.png"&gt;</pre>', output)
                self.assertEqual(binary.read_bytes(), b"\x00\xff\x01")
                if release == sha:
                    self.assertNotIn(prefix + prefix, output)
