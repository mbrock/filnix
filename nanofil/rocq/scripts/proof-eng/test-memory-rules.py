#!/usr/bin/env python3
"""Check the stage's public rewrite contract on unseen proof files."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

STAGE = Path(__file__).parent / "stages/60-memory-rules.py"


class MemoryRules(unittest.TestCase):
    def test_recognized_and_unrecognized_scripts(self):
        source = '''(* iApply (wp_raw_store_w with "H"); [vx|vx|reflexivity|ar|reflexivity|wi_store|]. *)
Definition marker := "iApply (wp_raw_store_w with H)".
Local Lemma unseen : True.
Proof.
  iApply (wp_raw_load_sub_bytes_dq with "[Hl Hb]");
    [reflexivity | vx | reflexivity | apply extended_chr | exact Hcap | ar |].
  iApply (wp_raw_store_w registry (os_wi w0) ge with "Hl Hb");
    [vx | vx | reflexivity | ar | reflexivity | wi_store |].
  iApply (wp_raw_store_w with "Hl Hb");
    [vx | vx | reflexivity | custom [left | right] | reflexivity | wi_store |].
Qed.
'''
        with tempfile.TemporaryDirectory(prefix="memory-rules-test-") as directory:
            path = Path(directory) / "Unseen.v"
            path.write_text(source)
            def run():
                return subprocess.run([sys.executable, '-I', str(STAGE), directory],
                                      check=True, text=True, capture_output=True).stdout
            output = run()
            result = path.read_text()
            self.assertIn('wp_raw_store_w: rewritten 1, left 1', output)
            self.assertIn('wp_raw_load_sub_bytes_dq: rewritten 1, left 0', output)
            self.assertIn('2 declarations byte-identical', output)
            self.assertIn('Local Lemma unseen : True.', result)
            self.assertNotIn('Local #[local]', result)
            self.assertIn('load_bytes_dq uconstr:(wp_raw_load_sub_bytes_dq) "[Hl Hb]" ltac:(apply extended_chr)', result)
            self.assertIn('store_word uconstr:(wp_raw_store_w registry (os_wi w0) ge) "Hl Hb"', result)
            self.assertIn('custom [left | right]', result)
            self.assertIn(source.splitlines()[0], result)
            self.assertIn(source.splitlines()[1], result)
            run()
            self.assertEqual(path.read_text(), result)


if __name__ == '__main__':
    unittest.main()
