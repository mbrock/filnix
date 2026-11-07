#!/usr/bin/env python3
"""Public capture CLI regression, running the pinned real Rocq."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

source = r'''(** Unicode λ, nested (* comments *) and a quoted "period.". *)
From Stdlib Require Import Arith.
Lemma rewriting : forall n : nat, n + 0 = n /\ True.
Proof.
  intro n.
  pose (saved := n).
  split.
  - rewrite Nat.add_0_r.
    reflexivity.
  - exact I.
Qed.
Goal True /\ True.
Proof. split. shelve. exact I. Unshelve. exact I. Qed.
Goal False.
Proof. Abort.
Goal False.
Proof. Admitted.
'''

here = Path(__file__).resolve().parents[1]
with tempfile.TemporaryDirectory() as tmp:
    root = Path(tmp)
    (root / "_RocqProject").write_text("-Q . Test\nExample.v\n")
    (root / "Example.v").write_text(source)
    result = root / "states.json"
    subprocess.run(["python3", str(here / "capture.py"), str(root), str(result)], check=True)
    entry = json.loads(result.read_text())["files"]["Example.v"]
    assert entry["sha256"] == hashlib.sha256(source.encode()).hexdigest()
    states = entry["states"]

    def after(command):
        return states[str(source.index(command) + len(command))]

    assert after("intro n.")[0]["hypotheses"] == ["n : nat"]
    assert "saved := n : nat" in after("pose (saved := n).")[0]["hypotheses"]
    assert len(after("split.")) == 2
    rewritten = after("rewrite Nat.add_0_r.")
    assert rewritten[0]["conclusion"] == "n = n"
    assert rewritten[0]["role"] == "focused"
    assert rewritten[1]["conclusion"] == "True" and rewritten[1]["role"] == "deferred"
    assert after("reflexivity.")[0]["role"] == "deferred", "an unfocused goal is not completion"
    assert after("shelve.")[1]["role"] == "shelved", "shelved goals must not disappear"
    assert after("Abort.") is None and after("Admitted.") is None
    assert after("Qed.") is None
    assert after("exact I.") == [], "all goals solved, but proof not yet closed"

    # Exercise the renderer's public CLI too: capture is an exact-source
    # build input, and aborted/admitted proofs must never look checked.
    page_source = root / "nanofil/rocq/Example.v"
    page_source.parent.mkdir(parents=True)
    page_source.write_text(source)
    out = root / "html"
    out.mkdir()
    render = ["swipl", str(here / "dterm_rocq.pl"), str(out), str(root),
              f"--states={result}", "nanofil/rocq/Example.v"]
    subprocess.run(render, check=True, stdin=subprocess.DEVNULL)
    html = (out / "rocq-Example.html").read_text()
    assert html.count("Proof checked and closed by Rocq.") == 2
    assert html.count("Proof ended without a checked closure.") == 2
    assert 'data-role="shelved"' in html and 'data-role="deferred"' in html
    assert "saved" in html and "No remaining goals" in html
    page_source.write_text(source + "\n")
    stale = subprocess.run(render, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    assert stale.returncode != 0 and "stale_proof_capture" in stale.stdout, stale.stdout

    # Invalid tactics must fail the build, never produce an empty success.
    (root / "Example.v").write_text(source.replace("rewrite Nat.add_0_r.", "exact false."))
    bad = subprocess.run(["python3", str(here / "capture.py"), str(root), str(root / "bad.json")],
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    assert bad.returncode != 0 and not (root / "bad.json").exists(), bad.stdout
    print("ok: real rewrites, contexts, branching, deferred/shelved goals, closure, Unicode offsets and failure")
