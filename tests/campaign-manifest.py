#!/usr/bin/env python3
"""Exercise manifest freezing through Nix, without building package outputs."""
import json
from pathlib import Path
import subprocess
import tempfile


repo = Path(__file__).resolve().parents[1]
manifest_expr = repo / "experiments/campaign-next/world.nix"


def evaluate(expr):
    return subprocess.run(["nix", "eval", "--impure", "--raw", "--expr", expr],
                          text=True, capture_output=True)


nixpkgs = evaluate(f'(builtins.getFlake "path:{repo}").inputs.nixpkgs.outPath')
assert nixpkgs.returncode == 0, nixpkgs.stderr

with tempfile.TemporaryDirectory(prefix="campaign-manifest-") as tmp:
    source = Path(tmp)
    for directory in ("ports", "shells", "scripts"):
        (source / directory).mkdir()
    (source / "flake.nix").write_text('''
    {
      inputs.nixpkgs.url = "path:NIXPKGS";
      outputs = { self, nixpkgs }: let
        good = { drvPath = "/nix/store/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa-good.drv"; };
        bad = { drvPath = throw "fixture failure"; };
      in {
        packages.x86_64-linux.leader = good;
        legacyPackages.x86_64-linux.pkgsFilc = {
          inherit good bad;
          pipewire = bad // { meta = {
            broken = true;
            filcBrokenReason = "fixture cancellation unsupported";
          }; };
          wireplumber = bad;
          sdl3 = bad;
          sdl2-compat = bad;
          cava = bad;
          sfml_2 = bad;
          SDL_compat = bad;
          smpeg = bad;
        };
      };
    }
    '''.replace("NIXPKGS", nixpkgs.stdout))
    (source / "scripts/ci-outputs.txt").write_text("packages.x86_64-linux.leader\n")
    (source / "shells/world-packages.nix").write_text('[ "good" ]')
    (source / "ports.nix").write_text('{ ... }: [ { pname = "bad"; } ]')
    expected = source / "ports/expected.nix"
    expected.write_text('[ "good" ]')

    def freeze(scope="expected"):
        return evaluate(f'import {manifest_expr} {{ source = "path:{source}"; '
                        f'revision = "fixture"; scope = "{scope}"; }}')

    result = freeze()
    assert result.returncode == 0, result.stderr
    manifest = json.loads(Path(result.stdout).read_text())
    assert [r["name"] for r in manifest["roots"]] == ["leader", "good"]
    assert manifest["scope"] == "expected"
    assert len(manifest["excluded"]) == 8
    assert all(not e["selected"] for e in manifest["excluded"])
    assert all("cancellation unsupported" in e["reason"] for e in manifest["excluded"])

    # A selected failure must not silently disappear, including a known blocker.
    for name in ("bad", "pipewire"):
        expected.write_text(f'[ "good" "{name}" ]')
        result = freeze()
        assert result.returncode != 0
        assert f"Expected campaign evaluation failed: {name}" in result.stderr

    result = freeze("ports")
    assert result.returncode == 0, result.stderr
    manifest = json.loads(Path(result.stdout).read_text())
    excluded = {e["name"]: e for e in manifest["excluded"]}
    assert excluded["bad"]["selected"]
    assert "unresolved" in excluded["bad"]["reason"]
    assert [r["name"] for r in manifest["roots"]] == ["leader", "good"]

    expected.write_text('[ "good" ]')
    (source / "scripts/ci-outputs.txt").write_text(
        "legacyPackages.x86_64-linux.pkgsFilc.bad\n")
    result = freeze()
    assert result.returncode != 0
    assert "Expected campaign evaluation failed: bad" in result.stderr

print("campaign manifest: selection, ordering, exclusions and strict freezing passed")
