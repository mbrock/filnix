#!/usr/bin/env python3
"""Put the profile's marks into a marked nanofil's .s (docs/perf.md).

The marked emitter (marks.patch) runs the post-emission passes (register
homes, operands, cells) on the stream without its marks, so the code is
the unmarked compiler's. After each function's code it writes, as `#PF`
comments, the marked stream those passes ran on. This script aligns the
two block by block (labels survive the passes verbatim) and puts each
mark before the final line its pre-pass line became. Marks of lines the
passes deleted go before the next surviving line; lines the passes
inserted (saves, restores) get none. Only comments are removed and
local labels added, so the object code is unchanged.

usage: remark.py IN.s OUT.s
"""
import re, sys

LABEL = re.compile(r"^[^\s#][^:]*:$")
MARK = re.compile(r"^\.Lpf\.[RS]\.")


def parse(line):
    """(op, operands) of an instruction line, or None."""
    if not line.startswith("\t") or line.startswith("\t."):
        return None
    op, _, rest = line[1:].partition(" ")
    return op, rest.split(", ") if rest else []


def score(p, f):
    """How well pre-pass line p matches final line f; 0 if they cannot."""
    if p == f:
        return 4
    a, b = parse(p), parse(f)
    if not a or not b or len(a[1]) != len(b[1]):
        return 0
    mov = lambda op: op.startswith("mov")
    if a[0] != b[0] and not (mov(a[0]) and mov(b[0])):
        return 0
    for x, y in zip(a[1], b[1]):
        # A frame operand became a register or constant; a register was
        # retargeted or replaced by a constant.
        if not (x == y or "(%rbp)" in x or (x.startswith("%") and y[:1] in "%$")):
            return 0
    return 2 if a[0] == b[0] else 1


def align(pre, fin):
    """{final index: pre index}, a maximum-score monotone matching."""
    n, m = len(pre), len(fin)
    if n * m > 4_000_000:  # one huge straight-line block: greedy
        out, j = {}, 0
        for i, f in enumerate(fin):
            for k in range(j, min(j + 8, n)):
                if score(pre[k], f):
                    out[i], j = k, k + 1
                    break
        return out
    prev = [0] * (m + 1)
    back = []
    for j in range(1, n + 1):
        cur = [0] * (m + 1)
        row = bytearray(m + 1)  # 0 diagonal, 1 skip pre, 2 skip final
        p = pre[j - 1]
        for i in range(1, m + 1):
            best, how = prev[i], 1
            if cur[i - 1] > best:
                best, how = cur[i - 1], 2
            s = score(p, fin[i - 1])
            if s and prev[i - 1] + s > best:
                best, how = prev[i - 1] + s, 0
            cur[i], row[i] = best, how
        back.append(row)
        prev = cur
    out, j, i = {}, n, m
    while j > 0 and i > 0:
        how = back[j - 1][i]
        if how == 0:
            out[i - 1] = j - 1
            j, i = j - 1, i - 1
        elif how == 1:
            j -= 1
        else:
            i -= 1
    return out


def segments(lines, label):
    """Lines split before each label: [[label?, ...], ...]."""
    segs = [[]]
    for x in lines:
        if label(x):
            segs.append([])
        segs[-1].append(x)
    return segs


def remark(fin, pre_lines):
    # Pre-pass lines with the marks before each.
    pre, marks, pending = [], [], []
    for x in pre_lines:
        if MARK.match(x):
            pending.append("\t" + x)
        else:
            pre.append(x)
            marks.append(pending)
            pending = []
    tail = pending
    is_label = lambda x: bool(LABEL.match(x))
    idx = list(range(len(pre)))
    psegs = segments(idx, lambda k: is_label(pre[k]))
    fsegs = segments(fin, is_label)
    plabels = [pre[s[0]] for s in psegs if s and is_label(pre[s[0]])]
    flabels = [s[0] for s in fsegs if s and is_label(s[0])]
    if plabels != flabels:
        psegs, fsegs = [idx], [fin]
    out = []
    for ps, fs in zip(psegs, fsegs):
        match = align([pre[k] for k in ps], fs)
        done = 0  # marks of ps[:done] are out
        for i, f in enumerate(fs):
            if i in match:
                for k in ps[done:match[i] + 1]:
                    out.extend(marks[k])
                done = match[i] + 1
            out.append(f)
        for k in ps[done:]:
            out.extend(marks[k])
    return out + tail


def main(src, dst):
    out, fin, pre, state = [], [], [], None
    for line in open(src):
        line = line.rstrip("\n")
        if line == "\t#PF begin":
            state, fin, pre = "fin", [], []
        elif line == "\t#PF end":
            state = "pre"
        elif line == "\t#PF done":
            out.extend(remark(fin, pre))
            state = None
        elif state == "fin":
            fin.append(line)
        elif state == "pre":
            pre.append(line[len("\t#PF "):])
        else:
            out.append(line)
    with open(dst, "w") as o:
        o.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main(*sys.argv[1:])
