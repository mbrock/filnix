#!/usr/bin/env python3
"""Wrap recognized memory-rule applications without changing declarations."""
import collections
import importlib.util
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("tactics", Path(__file__).with_name("30-tactics.py"))
tactics = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tactics)

RULES = {
    "wp_raw_load_pointer_dq": "load_pointer_dq",
    "wp_check_read_dq": "check_read_dq",
    "wp_raw_load_sub_bytes_dq": "load_bytes_dq",
    "wp_raw_store_pointer": "store_pointer",
    "wp_raw_load_pointer": "load_pointer",
    "wp_raw_store_w": "store_word",
}
ARITH = re.compile(r"(?:[A-Za-z_][\w']*\.)?(?:arith|ar|a2|rawa|al8)")
EXACT = re.compile(r"exact [A-Za-z_][\w']*")
VALUE = {"reflexivity", "vx"}
CAP = {"left; reflexivity", "right; reflexivity"}
DECLARATION = re.compile(
    r"(?:#\[[^\]]*\]\s*)*(?:(?:Local|Global|Polymorphic|Monomorphic)\s+)*"
    r"\b(?:Lemma|Theorem|Definition|Corollary|Proposition|Fact|Remark)\s+")


def close(code, start):
    stack = []
    for i in range(start, len(code)):
        if code[i] in "([":
            stack.append(code[i])
        elif code[i] in ")]":
            if not stack or stack.pop() != {')': '(', ']': '['}[code[i]]:
                raise ValueError("unbalanced tactic argument")
            if not stack:
                return i
    raise ValueError("unterminated tactic argument")


def split_solvers(text):
    code = tactics.masked(text)
    start = depth = 0
    result = []
    for i, c in enumerate(code):
        if c in "([":
            depth += 1
        elif c in ")]":
            depth -= 1
        elif c == '|' and depth == 0:
            result.append(' '.join(text[start:i].split()))
            start = i + 1
    result.append(' '.join(text[start:].split()))
    return result


def declarations(text):
    code = tactics.masked(text)
    result = []
    for m in DECLARATION.finditer(code):
        end = re.search(r"\.(?=\s|$)", code[m.end():])
        if not end:
            raise ValueError("unterminated declaration")
        result.append(text[m.start():m.end() + end.end()])
    return result


def recognized(name, solvers):
    """Recognize each premise separately; never guess a rule's argument layout."""
    if len(solvers) != 7 or solvers[-1]:
        return False
    a, b, c, d, e, f, _ = solvers
    cap = lambda s: s in CAP or EXACT.fullmatch(s)
    bound = lambda s: s in {"lia", "cbn; lia"} or EXACT.fullmatch(s) or ARITH.fullmatch(s)
    if name == "wp_raw_load_pointer_dq":
        return a == "reflexivity" and b in VALUE and cap(c) and ARITH.fullmatch(d) and ARITH.fullmatch(e) and bound(f)
    if name == "wp_check_read_dq":
        return a == "reflexivity" and (b in VALUE or EXACT.fullmatch(b)) and cap(c) and ARITH.fullmatch(d) and ARITH.fullmatch(e) and (f == "apply Z.mod_1_r" or ARITH.fullmatch(f))
    if name == "wp_raw_load_sub_bytes_dq":
        decode = d in {"reflexivity", "cbn; reflexivity", "apply extended_chr", "apply load_sw_int; assumption"} or EXACT.fullmatch(d)
        return a == "reflexivity" and b in VALUE and (c == "reflexivity" or EXACT.fullmatch(c)) and decode and cap(e) and ARITH.fullmatch(f)
    if name == "wp_raw_load_pointer":
        return a == "reflexivity" and b in VALUE and c == "reflexivity" and ARITH.fullmatch(d) and ARITH.fullmatch(e) and bound(f)
    if name == "wp_raw_store_pointer":
        return a in VALUE and b in VALUE and c == "reflexivity" and ARITH.fullmatch(d) and ARITH.fullmatch(e) and f == "wi_store"
    if name == "wp_raw_store_w":
        return a in VALUE and b in VALUE and c == "reflexivity" and ARITH.fullmatch(d) and (e == "reflexivity" or EXACT.fullmatch(e)) and f == "wi_store"
    return False


def edit_imports(text):
    """Reuse the stream extension's rules instead of instantiating MemLogic again."""
    if re.search(r"From Glibc Require Import [\w\s]*\bLibioTactics\b", tactics.masked(text)):
        return text
    imports = re.search(r"From Glibc Require Import\s+", tactics.masked(text))
    if imports:
        return text[:imports.end()] + "LibioTactics " + text[imports.end():]
    first = re.search(r"^From\s", tactics.masked(text), re.M)
    if not first:
        raise ValueError("proof has no import header")
    return text[:first.start()] + "From Glibc Require Import LibioTactics.\n" + text[first.start():]


def rewrite(text, counts):
    code = tactics.masked(text)
    proofs = []
    for p in re.finditer(r"\bProof\s*\.", code):
        end = re.search(r"\b(?:Qed|Defined)\.", code[p.end():])
        headers = list(DECLARATION.finditer(code[:p.start()]))
        if end and headers:
            proofs.append((p.end(), p.end() + end.start(), headers[-1].start()))
    edits = []
    stream = False
    for m in re.finditer(r"\biApply\s*\(", code):
        end = close(code, m.end() - 1)
        expression = text[m.end():end]
        rule = re.search(r"\b(wp_\w+)\b", tactics.masked(expression))
        if not rule:
            continue
        name = rule[1]
        args = re.fullmatch(r'([\s\S]+?)\s+with\s+("(?:[^"]|"")*")\s*', expression)
        tail = re.match(r"\s*;\s*\[", code[end + 1:])
        if not tail or not re.search(r'\bwith\s+"', expression):
            continue
        counts[name][1] += 1
        if name not in RULES or not args:
            continue
        # Stage 50 may spell out the current program instance. No other
        # instantiation is redundant: preserve alternate programs and arguments.
        if not re.fullmatch(re.escape(name) + r"(?:\s*\(\s*glibc_program\s*:=\s*glibc_program\s*\))?",
                            args[1].strip()):
            counts[name][2] += 1
            continue
        opening = end + tail.end()
        finish = close(code, opening)
        solvers = split_solvers(text[opening + 1:finish])
        proof = next((h for a, b, h in proofs if a <= m.start() < b), None)
        if proof is None or not recognized(name, solvers):
            continue
        varying = list(dict.fromkeys(s for s in solvers if ARITH.fullmatch(s)))
        side = varying[0] if len(varying) == 1 else 'first [' + ' | '.join(varying) + ']'
        invocation = f'{RULES[name]} {args[2]}'
        if name == "wp_raw_load_sub_bytes_dq":
            invocation += f' decode ({solvers[3]})'
        if name in {"wp_raw_store_pointer", "wp_raw_store_w"}:
            invocation += f' by ({side}) preserving wi_store'
        else:
            invocation += f' by {side}'
        edits.append((m.start(), finish + 1, invocation))
        stream |= name in {"wp_check_read_dq", "wp_raw_load_sub_bytes_dq", "wp_raw_store_w"}
        counts[name][0] += 1
        counts[name][1] -= 1
    for a, b, value in sorted(edits, reverse=True):
        text = text[:a] + value + text[b:]
    return edit_imports(text) if stream else text


def main(root):
    counts = collections.defaultdict(lambda: [0, 0, 0])
    total = 0
    before_lines = after_lines = 0
    for path in sorted(root.rglob("*.v")):
        before = path.read_text()
        collisions = set(RULES.values()) & {name for name, _, _ in tactics.tactics(before)}
        if collisions:
            raise ValueError(f"{path}: wrapper names collide with private tactics: {sorted(collisions)}")
        after = rewrite(before, counts)
        original = declarations(before)
        if original != declarations(after):
            raise ValueError(f"{path}: declaration changed")
        total += len(original)
        before_lines += len(before.splitlines())
        after_lines += len(after.splitlines())
        if after != before:
            path.write_text(after)
    for name in RULES:
        rewritten, left, explicit = counts.get(name, (0, 0, 0))
        print(f"memory-rules: {name}: rewritten {rewritten}, left {left} (explicit rule terms {explicit})")
    print(f"memory-rules: counted {sum(sum(v[:2]) for v in counts.values())} iApply applications "
          f"over {len(counts)} rules; {total} declarations byte-identical")
    print(f"memory-rules: lines {before_lines} -> {after_lines}")


if __name__ == '__main__':
    main(Path(sys.argv[1]))
