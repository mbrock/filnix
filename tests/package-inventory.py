#!/usr/bin/env python3
"""Selection regressions and the no-build evaluation boundary."""

import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("inventory", ROOT / "scripts/package-inventory.py")
inventory = importlib.util.module_from_spec(spec)
spec.loader.exec_module(inventory)


def package(name="example", **metadata):
    return {"attrPath": [name], "status": "evaluated", "unavailableFields": [],
            "metadata": {"pname": name, "hasSource": True, "hasCompiler": True,
                         "availableOnLinux": True, "nativeBuildInputs": [],
                         "buildInputs": [], "propagatedBuildInputs": [],
                         "builderHints": {}, **metadata}}


class SelectionTests(unittest.TestCase):
    def test_build_tools_do_not_disqualify_c(self):
        row = inventory.classify(package(nativeBuildInputs=["python3", "cbindgen", "pkg-config"]))
        self.assertEqual(row["decision"], "candidate")

    def test_assembly_is_included_even_when_recipe_disables_it(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            file = root / "pkgs/example/package.nix"
            file.parent.mkdir(parents=True)
            file.write_text('configureFlags = [ "--disable-asm" ];\n')
            (file.parent / "intrinsics.patch").write_text('+ __asm__("pause");\n')
            row = package(nativeBuildInputs=["nasm"], position=str(file) + ":1")
            selected = inventory.classify(row, *inventory.source_evidence(row["metadata"], root))
            self.assertTrue(selected["selected"])
            self.assertIn("assembly-mentioned", selected["tags"])
            self.assertIn("assembler-build-input", selected["tags"])
            self.assertTrue(selected["evidence"])

    def test_active_rust_builder_is_excluded(self):
        row = inventory.classify(package("ripgrep", builderHints={"rust": True},
                                         nativeBuildInputs=["cargo-build-hook.sh"], buildInputs=["pcre2"]))
        self.assertEqual(row["decision"], "excluded")

    def test_compiler_input_without_active_rust_builder_is_uncertain(self):
        row = inventory.classify(package(nativeBuildInputs=["rustc", "cargo", "cmake"]))
        self.assertEqual(row["decision"], "uncertain")
        self.assertTrue(row["selected"])

    def test_ruby_optional_rust_component_is_not_a_rust_application(self):
        row = inventory.classify(package("ruby", builderHints={"rust": True},
                                         nativeBuildInputs=["rustc", "cargo"]))
        self.assertTrue(row["selected"])
        self.assertEqual(row["decision"], "uncertain")
        self.assertIn("rust-dependencies-declared", row["tags"])

    def test_nested_builder_source_mention_does_not_exclude(self):
        row = inventory.classify(package(), source_tags=["other-language-builder-mentioned"])
        self.assertEqual(row["decision"], "uncertain")

    def test_interpreters_remain_candidates(self):
        for name in ("python3", "perl", "ruby", "lua", "tcl", "nodejs"):
            with self.subTest(name=name):
                self.assertTrue(inventory.classify(package(name))["selected"])

    def test_native_extension_stays_in_scope(self):
        row = inventory.classify(package(builderHints={"python": True}, nativeBuildInputs=["cmake"]))
        self.assertEqual(row["decision"], "uncertain")

    def test_python_application_hooks_and_node_source_remain_uncertain(self):
        row = inventory.classify(package(nativeBuildInputs=["python-imports-check-hook.sh", "meson"]))
        self.assertEqual(row["decision"], "uncertain")
        row = inventory.classify(package(), source_tags=["script-package-builder-mentioned"])
        self.assertTrue(row["selected"])
        self.assertEqual(row["decision"], "uncertain")

    def test_active_dotnet_and_dart_builds_are_outside_scope(self):
        for hook in ("dotnet-build-hook", "dart-build-hook"):
            self.assertEqual(inventory.classify(package(nativeBuildInputs=[hook]))["decision"], "excluded")

    def test_package_name_prefix_is_not_language_evidence(self):
        self.assertTrue(inventory.classify(package("go-library-helper"))["selected"])

    def test_disabled_checks_and_broken_marker_do_not_exclude(self):
        row = inventory.classify(package(broken=True, doCheck=False, doInstallCheck=False))
        self.assertTrue(row["selected"])
        self.assertIn("marked-broken-in-native-nixpkgs", row["tags"])
        self.assertNotIn("native-check-enabled", row["tags"])

    def test_missing_source_metadata_is_uncertain(self):
        value = package(hasSource=None)
        value["unavailableFields"] = ["hasSource"]
        row = inventory.classify(value)
        self.assertTrue(row["selected"])
        self.assertIn("incomplete-metadata", row["tags"])

    def test_outside_scope_and_deferred_are_distinct(self):
        for value in (package(availableOnLinux=False), package(builderHints={"go": True}),
                      package(sourceProvenance=["binaryNativeCode"])):
            self.assertEqual(inventory.classify(value)["decision"], "excluded")
        self.assertEqual(inventory.classify(package(hasCompiler=False))["decision"], "deferred")
        self.assertEqual(inventory.classify(package(hasSource=False))["decision"], "deferred")
        self.assertEqual(inventory.classify(package(), "pkgs/os-specific/linux/kernel/generic.nix")["decision"], "excluded")

    def test_shared_expression_does_not_supply_other_packages_signals(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            file = root / "pkgs/top-level/all-packages.nix"
            file.parent.mkdir(parents=True)
            file.write_text("unrelated = buildRustPackage { asm = true; };\n")
            _, tags, evidence = inventory.source_evidence({"position": str(file) + ":1"}, root)
            self.assertEqual(tags, [])
            self.assertEqual(evidence, [])

    def test_failed_batch_is_split_without_losing_other_records(self):
        class FakeEvaluator(inventory.Evaluator):
            def metadata(self, names):
                if "bad" in names:
                    raise RuntimeError("bad expression")
                return [package(name) for name in names], ""
        with tempfile.TemporaryFile(mode="w+") as log:
            records = FakeEvaluator().batch(["a", "bad", "z"], log)
        self.assertEqual([r["attrPath"] for r in records], [["a"], ["bad"], ["z"]])
        self.assertEqual(records[1]["status"], "evaluation-error")


class EvaluationTests(unittest.TestCase):
    def test_real_metadata_and_ifd_boundary(self):
        evaluator = inventory.Evaluator()
        nixpkgs = evaluator.resolve()
        records, _ = evaluator.metadata(["hello", "ripgrep", "pandoc", "libvpx", "ruby"])
        by_name = {r["attrPath"][0]: r for r in records}
        self.assertTrue(inventory.classify(by_name["hello"])["selected"])
        self.assertFalse(inventory.classify(by_name["ripgrep"])["selected"])
        self.assertFalse(inventory.classify(by_name["pandoc"])["selected"])
        self.assertTrue(inventory.classify(by_name["libvpx"])["selected"])
        self.assertTrue(inventory.classify(by_name["ruby"])["selected"])

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "default.nix").write_text('''args:
              let
                pkgs = import (builtins.toPath (builtins.getEnv "FILNIX_INVENTORY_FIXTURE_BASE")) args;
                forbidden = builtins.derivation {
                  name = "filnix-inventory-must-not-build";
                  system = "x86_64-linux";
                  builder = "/bin/sh";
                  args = [ "-c" "echo unexpected-build > $out" ];
                };
              in pkgs // {
                ifd = {
                  type = "derivation";
                  pname = "ifd-fixture";
                  version = builtins.readFile forbidden;
                  meta = { platforms = [ "x86_64-linux" ]; };
                };
                partial = {
                  type = "derivation";
                  pname = "partial-fixture";
                  version = throw "unavailable version";
                  meta = { platforms = [ "x86_64-linux" ]; };
                };
                failure = throw "fixture evaluation error";
              }
            ''')
            import os
            previous = os.environ.get("FILNIX_INVENTORY_FIXTURE_BASE")
            os.environ["FILNIX_INVENTORY_FIXTURE_BASE"] = nixpkgs
            try:
                evaluator.nixpkgs = str(root)
                with tempfile.TemporaryFile(mode="w+") as log:
                    records = evaluator.batch(["hello", "ifd", "partial", "failure"], log)
            finally:
                if previous is None:
                    del os.environ["FILNIX_INVENTORY_FIXTURE_BASE"]
                else:
                    os.environ["FILNIX_INVENTORY_FIXTURE_BASE"] = previous
            self.assertEqual(records[0]["status"], "evaluated")
            self.assertEqual(records[1]["status"], "evaluation-error")
            self.assertIn("allow-import-from-derivation", records[1]["error"])
            self.assertIn("version", records[2]["unavailableFields"])
            self.assertIsNone(records[2]["metadata"]["version"])
            self.assertEqual(records[3]["status"], "evaluation-error")


class ArtifactTests(unittest.TestCase):
    def test_resume_recovers_only_a_partial_tail(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "metadata.jsonl"
            valid = json.dumps(package("first")) + "\n"
            path.write_text(valid + '{"attrPath": ["second')
            self.assertEqual(len(inventory.read_jsonl(path, recover_tail=True)), 1)
            self.assertEqual(path.read_text(), valid)
            path.write_text(valid + "invalid\n" + valid)
            with self.assertRaises(json.JSONDecodeError):
                inventory.read_jsonl(path, recover_tail=True)

    def test_manifest_preserves_literal_attribute_names_and_partial_status(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp)
            inventory.write_json(output / "run.json", {
                "nixpkgs": {"rev": "fixture"}, "nixpkgsPath": tmp,
                "scope": "fixture", "universe": ["literal.dot", "pending"],
            })
            record = json.dumps(package("literal.dot")) + "\n"
            (output / "metadata.jsonl").write_text(record)
            inventory.render_report(output)
            manifest = json.loads((output / "candidates.json").read_text())
            self.assertEqual(manifest["attrPaths"], [["literal.dot"]])
            self.assertFalse(manifest["complete"])
            (output / "metadata.jsonl").write_text(record + record)
            with self.assertRaisesRegex(ValueError, "duplicate"):
                inventory.render_report(output)


if __name__ == "__main__":
    unittest.main()
