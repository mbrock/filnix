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
STANDARD = {"reflexivity", "vx", "lia", "cbn; lia", "left; reflexivity",
            "right; reflexivity", "apply Z.mod_1_r", "assumption"}
REGISTER = re.compile(r"(?:(?:[A-Za-z_][\w']*\.)?(?:arith|ar|a2|rawa|al8|wi_store)|"
                      r"apply extended_chr|apply load_sw_int; assumption)")
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


def rewrite(text, counts):
    code = tactics.masked(text)
    proofs = []
    for p in re.finditer(r"\bProof\s*\.", code):
        end = re.search(r"\b(?:Qed|Defined)\.", code[p.end():])
        headers = list(DECLARATION.finditer(code[:p.start()]))
        if end and headers:
            proofs.append((p.end(), p.end() + end.start(), headers[-1].start()))
    edits = []
    hints = collections.defaultdict(set)
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
        opening = end + tail.end()
        finish = close(code, opening)
        solvers = split_solvers(text[opening + 1:finish])
        proof = next((h for a, b, h in proofs if a <= m.start() < b), None)
        if proof is None or len(solvers) != 7 or solvers[-1]:
            continue
        if any(s not in STANDARD and not REGISTER.fullmatch(s) and
               not re.fullmatch(r"exact [A-Za-z_][\w']*", s) for s in solvers[:-1]):
            continue
        hints[proof].update(s for i, s in enumerate(solvers[:-1]) if REGISTER.fullmatch(s)
                            and not (name == "wp_raw_load_sub_bytes_dq" and i == 3))
        invocation = f'GlibcTactics.{RULES[name]} uconstr:({args[1].strip()}) {args[2]}'
        if name == "wp_raw_load_sub_bytes_dq":
            invocation += f' ltac:({solvers[3]})'
        edits.append((m.start(), finish + 1, invocation))
        counts[name][0] += 1
        counts[name][1] -= 1
    for position, solvers in hints.items():
        registrations = ''.join(f'#[local] Hint Extern 2 => solve [{s}] : glibc_memory.\n'
                                for s in sorted(solvers))
        edits.append((position, position, registrations))
    for a, b, value in sorted(edits, reverse=True):
        text = text[:a] + value + text[b:]
    return text


def main(root):
    counts = collections.defaultdict(lambda: [0, 0])
    total = 0
    for path in sorted(root.rglob("*.v")):
        before = path.read_text()
        after = rewrite(before, counts)
        original = declarations(before)
        if original != declarations(after):
            raise ValueError(f"{path}: declaration changed")
        total += len(original)
        if after != before:
            path.write_text(after)
    for name in RULES:
        rewritten, left = counts.get(name, (0, 0))
        print(f"memory-rules: {name}: rewritten {rewritten}, left {left}")
    print(f"memory-rules: counted {sum(sum(v) for v in counts.values())} iApply applications "
          f"over {len(counts)} rules; {total} declarations byte-identical")


if __name__ == '__main__':
    main(Path(sys.argv[1]))
