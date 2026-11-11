#!/usr/bin/env python3
"""Simulate Campaign 5 (`discharged(Cert)`) check erasure on kernels_checked.s.

Given an assembly file emitted by `nanofil-backend compile-allocated` for
pure-arena kernels whose entry wrapper (`driver.c`) already validates the
`arena`, `roots`, and `st` capabilities at the FFI boundary, strips the
inline capability-check branch blocks (`testq %rcx, %rcx; jz .L..fail...`
through `jnz .L..fail...`) while keeping all Pizderson frames, stack-overflow
checks, shadow-root spills, Cheney `minor_gc` logic, and `poll` safepoints
intact.
"""
import re, sys

lines = open(sys.argv[1]).readlines()
out = []
i = 0
removed_checks = 0
removed_insts = 0

FAIL_BR = re.compile(r"^\tj(?:z|nz|b|a|ae|be) \.L[A-Za-z0-9_.]*\.\.fail\.")

while i < len(lines):
    # Match optional `movq -SLOT(%rbp), %rcx` immediately before `testq %rcx, %rcx` + fail branch
    if (
        i + 2 < len(lines)
        and lines[i].startswith("\tmovq ") and lines[i].endswith(", %rcx\n")
        and lines[i + 1] == "\ttestq %rcx, %rcx\n"
        and FAIL_BR.match(lines[i + 2])
    ):
        # Also drop an immediately preceding dead lower-slot copy:
        #   movq -SRC(%rbp), %rcx
        #   movq %rcx, -DST(%rbp)
        # only when followed by `addq ...` + `movq ..., %rax` into this check
        j = i + 3
        while j < len(lines):
            if FAIL_BR.match(lines[j]):
                j += 1
                continue
            if (
                j + 1 < len(lines)
                and lines[j].startswith("\t")
                and not lines[j].startswith("\t.")
                and FAIL_BR.match(lines[j + 1])
            ):
                j += 2
                continue
            if (
                j + 2 < len(lines)
                and lines[j].startswith("\tmovq -16(%rcx), %rdx")
                and lines[j + 1].startswith("\tsubq $")
                and FAIL_BR.match(lines[j + 2])
            ):
                j += 3
                continue
            break
        removed_checks += 1
        removed_insts += j - i
        i = j
        continue
    out.append(lines[i])
    i += 1

open(sys.argv[2], "w").writelines(out)
sys.stderr.write(f"erased {removed_checks} check blocks ({removed_insts} asm instructions)\n")
