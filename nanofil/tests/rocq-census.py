#!/usr/bin/env python3
"""Check fixture census totals through the command-line interface."""

import json
import os
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
SWIPL = os.environ.get("SWIPL", "swipl")
CENSUS = ROOT / "nanofil/rocq/scripts/census.pl"
GALLINA = ROOT / "nanofil/rocq/scripts/gallina.pl"


def fixture(path, term, chunk=True):
    result = subprocess.run(
        [SWIPL, "-q", str(GALLINA), *(["--chunk"] if chunk else []), "sample", "census-test"],
        input=term, text=True, capture_output=True, check=True,
    )
    path.write_text(result.stdout)


def census(*paths, ok=True):
    result = subprocess.run(
        [SWIPL, "-q", str(CENSUS), *map(str, paths)],
        stdin=subprocess.DEVNULL, text=True, capture_output=True,
    )
    if not ok:
        assert result.returncode != 0, result.stdout
        return
    assert result.returncode == 0, result.stderr
    return json.loads(result.stdout)


with tempfile.TemporaryDirectory(prefix="rocq-census-") as work:
    work = Path(work)
    a, duplicate, changed, chunked, broken = [
        work / f"{name}.v" for name in ("a", "duplicate", "changed", "chunked", "broken")
    ]
    # Three instructions include two opcodes the former regex omitted.
    # The nested raw_store atom is an operand, not a fourth instruction.
    insts = "raw_store(w,0,const(1),tmp(p)),poll([]),let(tmp(x),w,copy,[global(raw_store)])"
    fixture(a, "module([func(f,export,w,[],["
            f"block(start,[phi(tmp(p),w,[])],[{insts}],goto(done)),"
            "block(done,[],[],ret(const(0)))])]).")
    duplicate.write_text("(* Different source positions. *)\n\n" + a.read_text())
    fixture(changed, "module([func(f,export,w,[],["
            f"block(start,[phi(tmp(p),w,[])],[{insts},poll([])],goto(done)),"
            "block(done,[],[],ret(const(0)))])]).")
    result = census(a, duplicate, changed)
    expected = dict(functions=2, blocks=4, phis=2, instructions=7,
                    terminators=4, instructions_and_terminators=11)
    assert {key: result[key] for key in expected} == expected, result
    assert sorted(len(row["files"]) for row in result["rows"]) == [1, 2], result
    assert len({row["sha256"] for row in result["rows"]}) == 2, result

    # --chunk splits this instruction list at 64; append is not an opcode.
    term = ("module([func(g,export,w,[],[block(start,[],["
            + ",".join(["poll([])"] * 65) + "],ret(const(0)))])]).")
    fixture(chunked, term)
    fixture(duplicate, term, chunk=False)
    result = census(chunked, duplicate)
    assert (result["instructions"], result["terminators"], result["phis"]) == (65, 1, 0)
    assert result["functions"] == 1 and len(result["rows"][0]["files"]) == 2

    # hi_atexit slices split one function's blocks across named definitions.
    chunked.write_text('''
Definition left : list term := [
  TApp "block" [TAtom "start"; TList []; TList [TApp "poll" [TList []]];
                TApp "goto" [TAtom "end"]]].
Definition right : list term := [
  TApp "block" [TAtom "end"; TList []; TList []; TAtom "ret_void"]].
Definition sample : term := TApp "func" [TAtom "split"; TAtom "export";
  TAtom "void"; TList []; TList (left ++ right)].
''')
    result = census(chunked)
    assert (result["functions"], result["blocks"], result["instructions"]) == (1, 2, 1)
    broken.write_text(chunked.read_text().replace("left ++ right", "missing ++ right"))
    census(broken, ok=False)

    broken.write_text(a.read_text().replace('TApp "block"', 'TApp "broken"', 1))
    census(broken, ok=False)
    census(ok=False)

print("rocq-census: exact lists, duplicate bodies, variants, chunking, slices and rejection passed")
