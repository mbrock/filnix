#!/usr/bin/env python3
"""Check the stage's public rewrite contract on unseen proof files."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

STAGE = Path(__file__).parent / "stages/60-memory-rules.py"


class MemoryRules(unittest.TestCase):
    def test_private_name_collision(self):
        with tempfile.TemporaryDirectory(prefix="memory-rules-test-") as directory:
            path = Path(directory) / "Unseen.v"
            path.write_text('Ltac load_pointer H := idtac.\n')
            result = subprocess.run([sys.executable, '-I', str(STAGE), directory],
                                    text=True, capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("wrapper names collide with private tactics: ['load_pointer']", result.stderr)
            self.assertEqual(path.read_text(), 'Ltac load_pointer H := idtac.\n')

    def test_recognized_and_unrecognized_scripts(self):
        source = '''(* iApply (wp_raw_store_w with "H"); [vx|vx|reflexivity|ar|reflexivity|wi_store|]. *)
From Glibc Require Import GlibcTactics WordString.
Definition marker := "iApply (wp_raw_store_w with H)".
Local Lemma unseen : True.
Proof.
  iApply (wp_raw_load_sub_bytes_dq with "[Hl Hb]");
    [reflexivity | vx | reflexivity | apply extended_chr | exact Hcap | ar |].
  iApply (wp_raw_store_w registry (os_wi w0) ge with "Hl Hb");
    [vx | vx | reflexivity | ar | reflexivity | wi_store |].
  iApply (wp_raw_store_w with "Hl Hb");
    [vx | vx | reflexivity | ar | reflexivity | wi_store |].
  iApply (wp_raw_load_pointer_dq with "Htl Hn Hcapn");
    [reflexivity | vx | exact Hcap | rawa | al8 | exact Hn0 |].
  iApply (wp_check_read_dq with "Hl");
    [reflexivity | exact Hx | exact Hcap | arith | arith | apply Z.mod_1_r |].
  iApply (wp_check_read_dq (glibc_program := glibc_program)    with "Htl");
    [reflexivity | vx | exact Hcap | rawa | rawa | apply Z.mod_1_r |].
  iApply (wp_check_read_dq (glibc_program := other_program) with "Hother");
    [reflexivity | vx | exact Hcap | rawa | rawa | apply Z.mod_1_r |].
  iApply (wp_check_read_dq (glibc_program := glibc_program) (p := ptr) with "Hp");
    [reflexivity | vx | exact Hcap | rawa | rawa | apply Z.mod_1_r |].
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
            self.assertIn('wp_raw_store_w: rewritten 2, left 1 (explicit rule terms 0)', output)
            self.assertIn('wp_raw_load_sub_bytes_dq: rewritten 1, left 0', output)
            self.assertIn('2 declarations byte-identical', output)
            self.assertIn('From Glibc Require Import LibioTactics GlibcTactics WordString.', result)
            self.assertIn('check_read_dq "Hl" by arith', result)
            self.assertIn('check_read_dq "Htl" by rawa', result)
            self.assertIn('wp_check_read_dq: rewritten 2, left 2 (explicit rule terms 2)', output)
            self.assertIn('wp_check_read_dq (glibc_program := other_program) with "Hother"', result)
            self.assertIn('wp_check_read_dq (glibc_program := glibc_program) (p := ptr) with "Hp"', result)
            self.assertIn('Local Lemma unseen : True.', result)
            self.assertNotIn('Hint Extern', result)
            self.assertIn('load_bytes_dq "[Hl Hb]" decode (apply extended_chr) by ar', result)
            self.assertIn('store_word "Hl Hb" by (ar) preserving wi_store', result)
            self.assertIn('load_pointer_dq "Htl Hn Hcapn" by first [rawa | al8]', result)
            self.assertNotIn('iApply (wp_raw_store_w registry (os_wi w0) ge with "Hl Hb")', result)
            self.assertIn('custom [left | right]', result)
            self.assertIn(source.splitlines()[0], result)
            self.assertIn(source.splitlines()[2], result)
            run()
            self.assertEqual(path.read_text(), result)
            path.write_text(source.replace(
                'wp_check_read_dq (glibc_program := glibc_program)    with "Htl"',
                'wp_check_read_dq with "Htl"'))
            run()
            self.assertEqual(path.read_text(), result)

    def test_context_arguments(self):
        cases = {
            'wp_raw_load_pointer_dq': ('load_pointer_dq', 'reflexivity|vx|left; reflexivity|ar|ar|lia|'),
            'wp_check_read_dq': ('check_read_dq', 'reflexivity|vx|exact Hcap|ar|ar|apply Z.mod_1_r|'),
            'wp_raw_load_sub_bytes_dq': ('load_bytes_dq', 'reflexivity|vx|reflexivity|apply extended_chr|exact Hcap|ar|'),
            'wp_raw_load_pointer': ('load_pointer', 'reflexivity|vx|reflexivity|ar|ar|lia|'),
            'wp_raw_store_pointer': ('store_pointer', 'vx|vx|reflexivity|ar|ar|wi_store|'),
            'wp_raw_store_w': ('store_word', 'vx|vx|reflexivity|ar|reflexivity|wi_store|'),
        }
        with tempfile.TemporaryDirectory(prefix="memory-rules-test-") as directory:
            path = Path(directory) / 'Unseen.v'
            for rule, (wrapper, solvers) in cases.items():
                for context in ('registry (os_wi w0) ge', 'w0 registry ge',
                                'registry ( os_wi  w0 )\n ge',
                                'registry (os_wi other_world) ge', 'w0 other_registry ge',
                                'w0 registry other_ge', 'w0 registry ge (p := ptr)',
                                'registry ge w0'):
                    with self.subTest(rule=rule, context=context):
                        call = f'iApply ({rule} {context} with "Hl"); [{solvers}]'
                        source = 'From Glibc Require Import GlibcTactics.\nLemma unseen : True.\nProof.\n' + call + '.\nQed.\n'
                        path.write_text(source)
                        subprocess.run([sys.executable, '-I', str(STAGE), directory],
                                       check=True, text=True, capture_output=True)
                        result = path.read_text()
                        if context in ('registry (os_wi w0) ge', 'w0 registry ge',
                                       'registry ( os_wi  w0 )\n ge'):
                            self.assertNotIn(call, result)
                            self.assertIn(f'{wrapper} "Hl"', result)
                        else:
                            self.assertEqual(source, result)


if __name__ == '__main__':
    unittest.main()
