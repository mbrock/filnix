#!/usr/bin/env python3
"""Public capture CLI regression, running the pinned real Rocq."""
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import subprocess
import tempfile

source = r'''(** Unicode λ, nested (* comments *) and a quoted "period.". *)
From Stdlib Require Import Arith.
Module Nested.
Lemma rewriting : forall n : nat, n + 0 = n /\ True.
Proof.
  intro n.
  pose (saved := n).
  split.
  - rewrite Nat.add_0_r.
    reflexivity.
  - exact I.
Qed.
End Nested.
Lemma focusing : True /\ (True /\ True).
Proof.
  split.
  2: { pose proof I as kept2. split; exact kept2. }
  1: { pose proof I as kept1. exact kept1. }
Qed.
Lemma nested_focusing : True /\ (True /\ True).
Proof.
  split.
  2: { split. 2: { exact I. } { exact I. } }
  1: { exact I. }
Qed.
Lemma counted : forall a b : nat, a = a /\ b = b.
Proof. do 2 intro; split; reflexivity. Qed.
Lemma matching_goal : forall b : bool,
  (if b then 0 else 1) = (if b then 0 else 1).
Proof.
  intro b.
  do 1 match goal with |- context [if ?x then _ else _] => destruct x end; reflexivity.
Qed.
Goal True /\ True.
Proof. split. shelve. exact I. Unshelve. exact I. Qed.
Goal False.
Proof. Abort.
Goal False.
Proof. Admitted.
'''


class BalancedHTML(HTMLParser):
    """Streaming must preserve enclosing elements across fragments."""
    def __init__(self):
        super().__init__()
        self.stack = []

    def handle_starttag(self, tag, attrs):
        if tag not in {"meta", "link", "br", "hr", "img", "input"}:
            self.stack.append(tag)

    def handle_endtag(self, tag):
        assert self.stack and self.stack.pop() == tag, (tag, self.stack)


here = Path(__file__).resolve().parents[1]
with tempfile.TemporaryDirectory() as tmp:
    root = Path(tmp)
    (root / "_RocqProject").write_text("-Q . Test\nExample.v\nClient.v\n")
    (root / "Example.v").write_text(source)
    client = """From Test Require Import Example.
Definition imported := Nested.rewriting.
Lemma rewriting : forall b : bool, b = b.
Proof. intro b. reflexivity. Qed.
"""
    (root / "Client.v").write_text(client)
    result = root / "states.json"
    subprocess.run(["python3", str(here / "capture.py"), str(root), str(result)], check=True)
    files = json.loads(result.read_text())["files"]
    assert set(files) == {"Example.v", "Client.v"}
    # Dependent files must find checked imports, while concurrent prover
    # sessions keep their distinct contexts, offsets and source hashes.
    client_entry = files["Client.v"]
    assert client_entry["sha256"] == hashlib.sha256(client.encode()).hexdigest()
    client_goal = client_entry["states"][str(client.index("intro b.") + len("intro b."))][0]
    assert client_goal["hypotheses"] == ["b : bool"] and client_goal["conclusion"] == "b = b"
    assert client_entry["states"][str(client.index("Qed.") + len("Qed."))] is None
    entry = files["Example.v"]
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
    assert "kept2 : True" in after("pose proof I as kept2.")[0]["hypotheses"]
    assert "kept1 : True" in after("pose proof I as kept1.")[0]["hypotheses"]
    counted = after("do 2 intro; split; reflexivity.")
    assert counted == [], "counted repetition and its following chain must execute"
    assert after("destruct x end; reflexivity.") == []

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
    assert html.count("Proof checked and closed by Rocq.") == 6
    assert html.count("Proof ended without a checked closure.") == 2
    assert 'data-role="shelved"' in html and 'data-role="deferred"' in html
    assert "saved" in html and "No remaining goals" in html
    assert 'id="Nested.rewriting"' in html
    assert "rq-unparsed" not in html, "supported tactics must use the structured printer"

    # Grow one page, not the number of pages. Copy the real captured
    # proof with renamed lemmas and shifted character offsets, and have
    # coqc check the resulting source too. Whole-page DCG output exceeds
    # 64 MiB; streaming must keep every state and nested module intact.
    start = source.index("Lemma rewriting")
    end = source.index("Qed.") + len("Qed.")
    block = source[start:end]
    large = source[:start]
    large_states = {}
    copies = 200
    for i in range(copies):
        copy = block.replace("rewriting", f"rewriting_{i}")
        shift = len(large) - start + len(copy) - len(block)
        large_states.update({str(int(k) + shift): v for k, v in states.items()
                             if start <= int(k) <= end})
        large += copy + "\n"
    large += "End Nested.\n"
    large_source = page_source.with_name("Large.v")
    large_source.write_text(large)
    subprocess.run(["coqc", str(large_source)], check=True)
    large_capture = root / "large.json"
    large_capture.write_text(json.dumps({"files": {"Large.v": {
        "sha256": hashlib.sha256(large.encode()).hexdigest(), "states": large_states}}}))
    subprocess.run(["swipl", "--stack_limit=64m", str(here / "dterm_rocq.pl"), str(out), str(root),
                    f"--states={large_capture}", "nanofil/rocq/Large.v"],
                   check=True, stdin=subprocess.DEVNULL)
    large_html = (out / "rocq-Large.html").read_text()
    assert large_html.count("Proof checked and closed by Rocq.") == copies
    assert large_html.count('class="rq-snapshot"') == 8 * copies
    for document in [html, large_html]:
        parser = BalancedHTML()
        parser.feed(document)
        parser.close()
        assert not parser.stack, parser.stack

    page_source.write_text(source + "\n")
    stale = subprocess.run(render, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    assert stale.returncode != 0 and "stale_proof_capture" in stale.stdout, stale.stdout

    # Invalid tactics must fail the build, never produce an empty success.
    (root / "Example.v").write_text(source.replace("rewrite Nat.add_0_r.", "exact false."))
    bad = subprocess.run(["python3", str(here / "capture.py"), str(root), str(root / "bad.json")],
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    assert bad.returncode != 0 and not (root / "bad.json").exists(), bad.stdout
    print("ok: real rewrites, contexts, branching, deferred/shelved goals, closure, Unicode offsets, failure and 200 proofs in 64 MiB")
