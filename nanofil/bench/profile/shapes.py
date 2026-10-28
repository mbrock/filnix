#!/usr/bin/env python3
"""Attribute a binary's executed instructions to coarse shapes from its
disassembly: frame-slot loads and stores, moves between register homes
(rbx, r12-r15, r10, r11) and scratch registers, constants, booleans and
control. Unlike profile.py it needs no marked build, so it works with
builds whose checker rejects marked prologues.

usage: shapes.py BINARY CALLGRIND_OUT
  valgrind --aspace-minaddr=0x100000000 --tool=callgrind --dump-instr=yes \
    --compress-pos=no --compress-strings=no --callgrind-out-file=OUT BINARY ...
"""
import collections, os, re, subprocess, sys

exe, cg = sys.argv[1], sys.argv[2]
ir = collections.Counter()
skip, ob, other = False, None, 0
for line in open(cg):
    if line.startswith("ob="):
        ob = line[3:].strip(); continue
    if line.startswith("calls="):
        skip = True; continue  # the next line is the call's inclusive cost
    f = line.split()
    if len(f) == 3 and f[0].startswith("0x") and not skip:
        if ob and os.path.realpath(ob) == os.path.realpath(exe):
            ir[int(f[0], 16)] += int(f[2])
        else:
            other += int(f[2])
    skip = False
total = sum(ir.values()) + other
ir_other = other
dis = subprocess.run(["objdump", "-d", "--no-show-raw-insn", "-M", "att", exe],
                     capture_output=True, text=True).stdout
fn, insns = None, {}
for line in dis.splitlines():
    if m := re.match(r"^[0-9a-f]+ <(.*)>:$", line):
        fn = m.group(1)
    elif m := re.match(r"^\s+([0-9a-f]+):\s+(\S+)\s*(.*)$", line):
        insns[int(m.group(1), 16)] = (fn, m.group(2), m.group(3))
ALLOC = r"%(r1[0-5]d?|rbx|ebx)"
SCRATCH = r"%(r[abcd]x|e[abcd]x|r[sd]i|e[sd]i|r[89]d?|[abcd]l)"
cat = collections.Counter({"other objects": ir_other})
for addr, n in ir.items():
    if addr not in insns:
        cat["unknown"] += n; continue
    fn, op, args = insns[addr]
    if not fn.startswith("pizlonated"):
        cat["runtime/libc"] += n; continue
    rbp = "(%rbp)" in args
    if op.startswith("mov") and rbp:
        cat["frame load" if args.index("(%rbp)") < args.index(",") else "frame store"] += n
    elif rbp:
        cat["other frame operand"] += n
    elif op.startswith("mov") and re.fullmatch(ALLOC + "," + SCRATCH, args.replace(" ", "")):
        cat["home -> scratch"] += n
    elif op.startswith("mov") and re.fullmatch(SCRATCH + "," + ALLOC, args.replace(" ", "")):
        cat["scratch -> home"] += n
    elif op.startswith("mov") and re.fullmatch(ALLOC + "," + ALLOC, args.replace(" ", "")):
        cat["home -> home"] += n
    elif op.startswith("mov") and args.startswith("$"):
        cat["constant"] += n
    elif op.startswith(("set", "movzb")) and re.search(r"%(al|eax)", args) and op != "movzbl" or op == "movzbl" and args.replace(" ", "") == "%al,%eax":
        cat["boolean"] += n
    elif op.startswith("j") or op in ("call", "ret", "callq", "retq"):
        cat["control"] += n
    else:
        cat["other"] += n
print(f"{exe}: {total/1e9:.2f}G")
for k, v in cat.most_common():
    print(f"  {k:22} {v/1e9:6.2f}G {100*v/total:5.1f}%")
