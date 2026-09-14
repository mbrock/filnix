import unittest

from experiment.capture import BuildLogFilter


class CaptureTests(unittest.TestCase):
    def test_chunk_boundaries_preserve_evidence(self):
        progress = b'@nix {"action":"result","type":105,"fields":[1,2,3,4]}\n'
        evidence = (
            b'@nix {"action":"start","type":105,"fields":["drv"]}\n'
            b'@nix {"action":"result","type":101,"fields":["output"]}\n'
            b'@nix {"action":"result","type":104,"fields":["checkPhase"]}\n'
            b'@nix {"action":"result","type":105,"fields":["unknown"]}\n'
            b"@nix []\n@nix invalid\nraw \xff text\n"
        )
        raw = progress + evidence + progress + b"partial"
        for size in (1, 7, 65, len(raw)):
            capture = BuildLogFilter()
            output = b"".join(
                capture.feed(raw[i : i + size]) for i in range(0, len(raw), size)
            )
            self.assertEqual(output + capture.finish(), evidence + b"partial")
            self.assertEqual(capture.omitted_records, 2)
            self.assertEqual(capture.omitted_bytes, len(progress) * 2)

    def test_oversized_line_is_forwarded_and_never_reinterpreted(self):
        capture = BuildLogFilter()
        large = b"x" * (1024**2 + 1)
        progress = b'@nix {"action":"result","type":105,"fields":[1,2,3,4]}\n'
        self.assertEqual(capture.feed(large), large)
        self.assertEqual(capture.pending, b"")
        self.assertEqual(capture.feed(progress + progress), progress)
        self.assertEqual(capture.omitted_records, 1)
