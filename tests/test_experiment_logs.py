"""Log cursor, attribution, bounded reading, and raw-evidence invariants."""

import json
from pathlib import Path
import tempfile
import unittest
from urllib.parse import urlencode

from experiment import nix
from experiment.controller import Controller
from experiment.logs import MAX_LINE, PAGE, build_log, decode, window
from experiment.model import connect, import_campaign
from experiment.web import application

A = "/nix/store/" + "a" * 32 + "-alpha.drv"
B = "/nix/store/" + "b" * 32 + "-beta.drv"


def record(text, activity=7):
    return (
        b"@nix "
        + json.dumps(
            dict(action="result", type=101, id=activity, fields=[text]),
            ensure_ascii=False,
        ).encode()
        + b"\n"
    )


class LogTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.state = Path(self.tmp.name)
        self.db = connect(self.state)
        self.cid = import_campaign(
            self.db,
            "logs",
            {"attrPaths": [["alpha"]]},
            "/source",
            "abc",
            nix.DEFAULT_POLICY,
            "test",
        )
        c = Controller(self.db, self.state)
        self.aid = c.intent(
            c.campaign(self.cid), "build", [A], output_paths=[], derivations=[]
        )
        self.path = self.state / "attempts" / self.aid / "stderr.log"
        for activity, drv in [(7, A), (8, B)]:
            self.db.execute(
                "INSERT INTO activities(attempt,activity,drv,kind) VALUES(?,?,?,'build')",
                (self.aid, str(activity), drv),
            )
        self.db.commit()

    def tearDown(self):
        self.db.close()
        self.tmp.cleanup()

    def capture(self, raw, indexed=None, finished=False):
        self.path.write_bytes(raw)
        self.db.execute(
            "UPDATE attempts SET offset=?,state=? WHERE id=?",
            (
                len(raw) if indexed is None else indexed,
                "finished" if finished else "running",
                self.aid,
            ),
        )
        self.db.commit()

    def read(self, **kwargs):
        return build_log(self.db, self.state, self.aid, **kwargs)

    def test_readable_scoped_output_and_ansi(self):
        self.capture(
            record("\x1b[31merror: α <script>bad</script>\x1b[0m")
            + record("other build", 8)
        )
        r = self.read(drv=A)
        self.assertEqual(len(r["entries"]), 1)
        self.assertEqual(r["entries"][0]["text"], "error: α <script>bad</script>")
        self.assertEqual(r["entries"][0]["kind"], "error")
        self.assertEqual(r["entries"][0]["drv"], A)
        self.assertEqual(len(self.read()["entries"]), 2)

    def test_complete_utf8_records_across_forward_pages(self):
        raw = b"".join(record(f"{i}: λ🐍 " + "x" * 600) for i in range(950))
        self.capture(raw)
        cursor, entries = 0, []
        while cursor < len(raw):
            r = self.read(direction="after", cursor=cursor)
            self.assertGreater(r["end"], cursor)
            self.assertLessEqual(r["end"] - cursor, PAGE + MAX_LINE)
            cursor = r["end"]
            entries += r["entries"]
        self.assertEqual(len(entries), 950)
        self.assertEqual(len({e["offset"] for e in entries}), 950)
        self.assertTrue(all("λ🐍" in e["text"] for e in entries))

    def test_tail_and_history_cover_every_record_without_overlap(self):
        self.capture(b"".join(record(f"line {i}: " + "x" * 1200) for i in range(900)))
        r = self.read()
        self.assertGreater(r["start"], 0)
        entries = r["entries"]
        self.assertTrue(entries[-1]["text"].startswith("line 899:"))
        while r["before"]:
            cursor = r["start"]
            r = self.read(direction="before", cursor=cursor)
            self.assertLess(r["start"], cursor)
            entries = r["entries"] + entries
        self.assertEqual(len(entries), 900)
        self.assertEqual(len({e["offset"] for e in entries}), 900)
        self.assertTrue(entries[0]["text"].startswith("line 0:"))

    def test_unindexed_activity_is_not_consumed(self):
        first = record("first")
        self.capture(first + record("not yet indexed", 9), indexed=len(first))
        r = self.read()
        self.assertEqual(r["end"], len(first))
        self.assertGreater(r["captured"], r["size"])

    def test_torn_live_line_waits_but_terminal_fragment_is_preserved(self):
        first, second = record("one"), record("two λ🐍")
        self.capture(first + second[:-4], indexed=len(first))
        r = self.read()
        self.assertEqual(r["end"], len(first))
        # The window reader also protects callers from a live incomplete line.
        _, end, raw, _ = window(
            self.path, self.path.stat().st_size, "after", len(first), False
        )
        self.assertEqual(end, len(first))
        self.assertEqual(raw, [])
        self.capture(first + second)
        self.assertEqual(
            self.read(direction="after", cursor=r["end"])["entries"][0]["text"],
            "two λ🐍",
        )
        self.capture(b"last diagnostic without newline", indexed=0, finished=True)
        self.assertEqual(
            self.read()["entries"][0]["text"], "last diagnostic without newline"
        )

    def test_oversized_record_has_bounded_progress_and_notice(self):
        self.capture(b"x" * (MAX_LINE * 2) + b"\n" + record("after huge line"))
        r = self.read(direction="after")
        self.assertTrue(r["skipped"])
        self.assertLessEqual(r["end"], MAX_LINE)
        r2 = self.read(direction="after", cursor=r["end"])
        self.assertGreater(r2["end"], r["end"])
        tail = self.read()
        self.assertEqual(tail["entries"][-1]["text"], "after huge line")

    def test_filtered_empty_window_advances_cursor(self):
        self.capture(record("only beta", 8))
        r = self.read(drv=A)
        self.assertEqual(r["entries"], [])
        self.assertEqual(r["end"], r["size"])

    def test_status_does_not_read_log_and_reset_is_explicit(self):
        self.capture(record("message"))
        r = self.read(direction="status", cursor=9000)
        self.assertTrue(r["reset"])
        self.assertEqual(r["entries"], [])
        self.assertEqual(len(r["sources"]), 2)

    def test_unknown_and_malformed_events_do_not_crash(self):
        for event in [
            [],
            {"action": "result", "fields": None},
            {"action": "result", "type": 101, "fields": [1]},
            {"action": "future", "type": 999},
        ]:
            decode(b"@nix " + json.dumps(event).encode(), 0, {})
        self.assertIn("@nix", decode(b"@nix {broken", 0, {})["text"])
        self.assertIsNone(
            decode(b'@nix {"action":"result","type":105,"fields":[1,2,3]}', 0, {})
        )

    def request(self, path, query="", method="GET"):
        status = []
        response = application(self.state)(
            {"REQUEST_METHOD": method, "PATH_INFO": path, "QUERY_STRING": query},
            lambda s, h: status.append((s, dict(h))),
        )
        try:
            body = b"".join(response)
        finally:
            if hasattr(response, "close"):
                response.close()
        return *status[0], body

    def test_http_scoping_and_raw_download_preserve_evidence(self):
        raw = record("α\x1b[31m") + record("β", 8)
        self.capture(raw)
        status, _, body = self.request(
            "/api/build-log", urlencode(dict(attempt=self.aid, drv=A))
        )
        self.assertEqual(status, "200 OK")
        self.assertEqual(len(json.loads(body)["entries"]), 1)
        status, headers, body = self.request(
            "/api/log/download", urlencode(dict(attempt=self.aid))
        )
        self.assertEqual(body, raw)
        self.assertIn("attachment", headers["Content-Disposition"])
        self.assertEqual(
            self.request(
                "/api/log/download", urlencode(dict(attempt=self.aid)), "HEAD"
            )[2],
            b"",
        )
        for route in ("/api/build-log", "/api/log/download"):
            self.assertTrue(
                self.request(route, "attempt=../../etc/passwd")[0].startswith("400")
            )


if __name__ == "__main__":
    unittest.main()
