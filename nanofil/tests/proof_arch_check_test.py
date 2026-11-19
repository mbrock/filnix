#!/usr/bin/env python3
"""Unit tests for proof_arch_check.py."""
import json
import tempfile
import unittest
from pathlib import Path

from proof_arch_check import analyze, compare_against_baseline, make_baseline


BASE_MANIFEST = {
    "layers": {
        "L0": {
            "dirs": ["gen"],
            "files": ["CodePrelude"],
            "forbid_external_prefixes": ["iris."],
            "forbid_modules": ["Fix"],
        },
        "L1": {"dirs": [".", "base", "zsys"], "may_import_layers": ["L0", "L1"]},
        "L2": {"dirs": ["tactics"], "may_import_layers": ["L0", "L1", "L2"]},
        "L3a": {"dirs": ["string", "stdlib"], "may_import_layers": ["L0", "L1", "L2", "L3a"]},
        "L3c": {"dirs": ["libio"], "may_import_layers": ["L0", "L1", "L2", "L3a", "L3c"]},
        "L5": {
            "dirs": ["hello", "hi_atexit"],
            "may_import_layers": ["L0", "L1", "L2", "L3a", "L3c"],
            "isolate_siblings": True,
        },
    },
    "functor_instantiation_modules": ["Fix", "FixVariadic"],
    "tactic_export_dirs": ["tactics"],
    "tactic_export_module_suffixes": ["Tactics"],
    "tactic_export_modules": ["CFrame"],
    "require_export_modules": ["CodePrelude"],
    "critical_path_targets": ["HelloMain"],
    "baseline": {},
}


def write_files(root, mapping):
    for rel, content in mapping.items():
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content)


class ProofArchCheckTest(unittest.TestCase):
    def test_clean_tree_passes_strict(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            write_files(
                root,
                {
                    "base/CodePrelude.v": "From Stdlib Require Export ZArith.\nDefinition cp := 0.\n",
                    "base/Fix.v": "Module LG0 := Logic R.\nModule ML0 := MemLogicOn R LG0.\n",
                    "gen/StrCode.v": "From Glibc Require Import CodePrelude.\nDefinition f := cp.\n",
                    "tactics/OsTactics.v": 'From Glibc Require Import Fix.\nLtac os_step := idtac.\nTactic Notation "load_w" := idtac.\nDefinition td := LG0.\n',
                    "string/Strlen.v": "From Glibc Require Import StrCode OsTactics.\nLocal Ltac priv := os_step.\nDefinition s := f.\n",
                    "libio/FileInv.v": "From Glibc Require Import Strlen.\nDefinition fi := s.\n",
                    "hello/HelloMain.v": "From Glibc Require Import FileInv.\nDefinition hm := fi.\n",
                    "hi_atexit/HiMain.v": "From Glibc Require Import FileInv.\nDefinition hi := fi.\n",
                },
            )
            res = analyze(root, BASE_MANIFEST)
            failures, _ = compare_against_baseline(res, {}, strict=True)
            self.assertEqual(failures, [])
            self.assertEqual(res["target_depths"]["HelloMain"][0], 5)

    def test_detects_layer_and_sibling_violations(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            write_files(
                root,
                {
                    "string/StrA.v": "From Glibc Require Import FileInv.\nDefinition a := fi.\n",
                    "libio/FileInv.v": "Definition fi := 1.\n",
                    "hello/H.v": "From Glibc Require Import Hi.\nDefinition h := hi.\n",
                    "hi_atexit/Hi.v": "Definition hi := 2.\n",
                },
            )
            res = analyze(root, BASE_MANIFEST)
            self.assertEqual(res["layer_edges"], {"hello -> hi_atexit": 1, "string -> libio": 1})
            failures, _ = compare_against_baseline(res, {}, strict=True)
            self.assertEqual(len(failures), 2)

    def test_detects_l0_iris_and_functor_and_tactics(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            write_files(
                root,
                {
                    "gen/BadGen.v": "From iris.proofmode Require Import proofmode.\nDefinition g := 0.\n",
                    "string/BadStr.v": (
                        "From Glibc Require Import BadGen.\n"
                        "From Glibc Require BadGen.\n"
                        "Module VL := VariadicLogicOn R LG0.\n"
                        "Ltac leaked := idtac.\n"
                        "Local Ltac ok_local := idtac.\n"
                        "Definition x := g.\n"
                    ),
                },
            )
            res = analyze(root, BASE_MANIFEST)
            self.assertEqual(len(res["l0_violations"]), 1)
            self.assertEqual(len(res["functor_apps"]), 1)
            self.assertEqual(len(res["exported_tactics"]), 1)
            self.assertEqual(len(res["duplicate_require_files"]), 1)

    def test_ignores_comments_and_strings(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            write_files(
                root,
                {
                    "string/Clean.v": (
                        '(* (* nested *) From Glibc Require Import FileInv.\n'
                        '   Module VL := VariadicLogicOn R LG0.\n'
                        '   Ltac fake := idtac. *)\n'
                        'Definition doc := "Ltac in_string := idtac. ""Module X := MemLogicOn R LG0.""".\n'
                    ),
                },
            )
            res = analyze(root, BASE_MANIFEST)
            failures, _ = compare_against_baseline(res, {}, strict=True)
            self.assertEqual(failures, [])

    def test_ratchet_allows_baseline_and_catches_regression(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            write_files(
                root,
                {
                    "libio/FileInv.v": "Definition fi := 1.\n",
                    "string/S1.v": "From Glibc Require Import FileInv.\nDefinition s1 := fi.\n",
                },
            )
            res1 = analyze(root, BASE_MANIFEST)
            base = make_baseline(res1)
            failures, improvements = compare_against_baseline(res1, base, strict=False)
            self.assertEqual(failures, [])
            self.assertEqual(improvements, [])

            # Adding a second violation fires the tripwire.
            write_files(root, {"string/S2.v": "From Glibc Require Import FileInv.\nDefinition s2 := fi.\n"})
            res2 = analyze(root, BASE_MANIFEST)
            failures2, _ = compare_against_baseline(res2, base, strict=False)
            self.assertTrue(any("string -> libio" in f for f in failures2))

            # Removing the first violation reports an improvement.
            (root / "string/S1.v").unlink()
            (root / "string/S2.v").unlink()
            res3 = analyze(root, BASE_MANIFEST)
            failures3, imp3 = compare_against_baseline(res3, base, strict=False)
            self.assertEqual(failures3, [])
            self.assertTrue(any("string -> libio" in i for i in imp3))


if __name__ == "__main__":
    unittest.main()
