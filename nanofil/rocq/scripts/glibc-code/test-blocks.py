#!/usr/bin/env python3
"""Check the block-analysis CLI on a diamond, parallel loop phis and dead code."""
import json
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
MODULE = """module([func(example,export,w,
 [param(w,tmp(p)),param(w,tmp(carry)),param(w,tmp(cond)),param(w,tmp(dead))], [
 block(start,[],[let(tmp(discarded),w,copy,[const(1)])],branch(tmp(cond),left,right)),
 block(right,[],[let(tmp(b),w,copy,[tmp(carry)])],goto(join)),
 block(left,[],[let(tmp(a),w,copy,[tmp(p)])],goto(join)),
 block(join,[phi(tmp(q),w,[left-tmp(a),right-tmp(b)])],
       [let(tmp(z),w,copy,[tmp(q)])],goto(loop)),
 block(loop,[phi(tmp(x),w,[join-tmp(z),loop-tmp(y)]),
             phi(tmp(y),w,[join-tmp(carry),loop-tmp(x)])],[],branch(tmp(cond),poll(loop),done)),
 block(done,[],[],ret(tmp(y))),
 block(orphan,[],[let(tmp(gone),w,copy,[tmp(dead)])],ret(tmp(gone)))
])]).
"""

with tempfile.TemporaryDirectory(prefix="block-analysis-test-") as tmp:
    term = Path(tmp) / "example.term"
    term.write_text(MODULE)
    command = [os.environ.get("SWIPL", "swipl"), str(HERE / "blocks.pl"), str(term), "example"]
    result = subprocess.run(command, text=True, capture_output=True, check=True)
    blocks = {b["label"]: b for b in json.loads(result.stdout)}
    assert len(blocks) == 7
    assert blocks["start"]["entries"] == [{"predecessor": None, "reads": ["cond"]}]
    assert blocks["start"]["live_out"] == ["carry", "cond", "p"]
    join = blocks["join"]
    assert join["predecessors"] == ["left", "right"]
    assert join["reads"] == []  # q is a phi destination, not an entry lookup.
    assert join["entries"] == [{"predecessor": "left", "reads": ["a"]},
                               {"predecessor": "right", "reads": ["b"]}]
    assert join["live_out"] == ["carry", "cond", "z"]
    assert join["keeps"] == ["carry", "cond"]
    assert join["outputs"] == ["z"]  # A new value cannot be kept from e.
    loop = blocks["loop"]
    assert loop["successors"] == ["done", "loop"]  # Strip poll/1.
    assert loop["entries"] == [{"predecessor": "join", "reads": ["carry", "cond", "z"]},
                               {"predecessor": "loop", "reads": ["cond", "x", "y"]}]
    assert loop["live_out"] == ["cond", "x", "y"]
    assert loop["keeps"] == ["cond"]  # Parallel phis overwrite both x and y.
    assert loop["outputs"] == ["x", "y"]
    assert blocks["done"]["reads"] == ["y"]
    assert blocks["done"]["live_out"] == []
    assert blocks["orphan"]["entries"] == []  # Only the first block gets None.
    assert blocks["orphan"]["reads"] == ["dead"]
    assert blocks["orphan"]["live_out"] == []
    # Unknown instruction syntax must not silently lose environment reads.
    term.write_text(MODULE.replace("let(tmp(discarded),w,copy,[const(1)])", "unknown(tmp(p))"))
    result = subprocess.run(command, text=True, capture_output=True)
    assert result.returncode != 0 and "instruction" in result.stderr
print("block analysis: edge-specific inputs, loop liveness, keeps and unreachable entries passed")
