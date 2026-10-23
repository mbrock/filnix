# Lua 5.4 integration (M9)

`nix build .#checks.x86_64-linux.nanofil-lua` builds unpatched Lua 5.4.7
and luac through the shared `nix/nanofil-cc.nix` wrapper. Filcc only
preprocesses and links; nanofil compiles every C translation unit. The
check compares all 34 object names with the wrapper's compilation log,
separately without and with nanofil's `-O` middle end. Both builds use
Lua's supported `LUA_USE_JUMPTABLE=0` switch dispatch, not GNU label
addresses. The filcc reference uses the same source and configuration.

Three `lua -e` scripts compare byte-identical stdout and stderr for
floating arithmetic/conversions, number parsing, signed zero, subnormals,
halfway rounding, string.format (including variadic doubles), libm and
deterministic random numbers. The unchanged official 5.4.7 **basic** suite
runs with `_U=true`: portable/soft tests, without internal C extensions.
This is not a claim to pass the internal suite. Its assertions, exit
status and `final OK !!!` marker are checked, not its nondeterministic
clock/memory/seed output. Both script and official runs repeat under
`FUGC_SCRIBBLE=1 FUGC_VERIFY=1`.

The output retains both binaries, object inventories and runtime logs.
`checks.x86_64-linux.nanofil-lua.reference` exposes the reference build
and its self-check independently.

## Native stack gap and slot reuse

Measured on x86_64 Linux at nanofil revision `c93fdda12696`, using the
same binaries and unchanged `lua -e '_U=true' all.lua` suite, with only
the subprocess's `ulimit -s` changed. Each run used a fresh suite copy;
the environment was the same apart from GC stress. Binary search used
**1 MiB resolution**, not an exact byte-level minimum:

| Compiler | Largest failing boundary | Smallest passing boundary | GC stress at passing boundary |
| --- | ---: | ---: | --- |
| filcc `-O2` reference | not searched | 8 MiB | passes |
| nanofil, no middle end | 18 MiB | 19 MiB | passes |
| nanofil `-O` | 12 MiB | 13 MiB | passes |

The default 8 MiB stack fails in `calls.lua`'s deep C recursion/error
handler stress for nanofil. Failures include a Fil-C stack-overflow trap
and a segmentation fault; they must not be described as a successful
graceful overflow check. The filcc reference passes the **same whole
suite** at 8 MiB, both plain and under GC stress.

`objdump -d` of the fast entries gives this concrete frame-size gap.
Numbers are bytes below RBP after the prologue (stack reservation plus
saved GPRs), excluding saved RBP, return address and dynamic outgoing
arguments:

| Function | filcc `-O2` | nanofil | nanofil `-O` |
| --- | ---: | ---: | ---: |
| `luaV_execute` | 640 | 82,160 | 56,048 |
| `luaD_precall` | 208 | 1,648 | 1,024 |
| `luaD_rawrunprotected` | 224 | 528 | 528 |
| `luaG_errormsg` | 144 | 928 | 496 |

For example, `luaV_execute` reserves `0x258` bytes and saves five GPRs
in filcc, versus reservations `0x140f0` / `0xdaf0` in nanofil. That is
about **128x / 88x** the reference frame, not evidence of a setjmp bug.
This was a backend allocation problem, not an integration-check fix.

### Reduction from the staging baseline

Re-measured before changing the allocator at staging revision `8dc4efe`:
`luaV_execute` had 7,405 dedicated eight-byte temp payload slots, 142
phi shadow payload slots and 2,719 scanned lower words. With `-O`, those
counts were 5,501, 296 and 1,205. The sum, plus thread/aux and the 16-byte
frame header and alignment, explains the entire 82,160 / 56,048 bytes.
`alloc` is heap-backed; there are no native local-allocation payloads or
stack-aux words multiplying this frame (`num_stack_auxes` remains zero).

The backend now reuses slots with disjoint **closed live intervals**.
Intervals include every definition (even dead writes), explicit use,
CFG live-in/out boundary, and all incoming parameter stores. Fixed-point
liveness includes phi edge uses, loops and unreachable blocks. Reuse
requires old end < new start, so operands and all results of one lowered
instruction remain distinct through its internal helper calls. Pointer
payload/lower pairs share one allocation in a pool separate from scalars.
Physical lowers are zeroed on entry and origins report their physical
count; stale dead lowers are valid conservative roots. Phi shadows stay
dedicated and disjoint from temps. The implicit variadic snapshot is
reserved for the entire invocation.

**Any function containing setjmp retains the complete original unique
layout**, including unreachable sites, payload snapshots, eager roots
and final jmpbuf lowers. See [setjmp.md](setjmp.md). Oracle reviewed this
design before implementation: approved with no memory-safety blocker,
conditional on these invariants. No ABI, runtime or toolchain change.

Frames below RBP, measured with the same preprocessed Lua sources and
confirmed against emitted fast-entry prologues:

| Function | Before | After | Before `-O` | After `-O` |
| --- | ---: | ---: | ---: | ---: |
| `luaV_execute` | 82,160 | 8,224 | 56,048 | 4,304 |
| `luaD_precall` | 1,648 | 288 | 1,024 | 256 |
| `luaD_rawrunprotected` | 512 | 512 | 512 | 512 |
| `luaG_errormsg` | 928 | 192 | 496 | 128 |
| `luaY_parser` | 1,856 | 368 | 1,136 | 272 |
| `lua_getinfo` | 1,264 | 304 | 768 | 272 |

The staging setjmp layout makes `luaD_rawrunprotected` 512 bytes, rather
than the historical 528 above; slot reuse leaves it unchanged.
`luaV_execute`'s scanned lowers drop to 442 / 159. The remaining gap to
filcc includes conservative convex intervals, unpromoted heap-local
pointers and dedicated shadows; this is not register allocation.

For a broader corpus, all **309 functions** in `lvm.c`, `ldo.c`,
`ldebug.c`, `lparser.c` and `lapi.c` were measured before and after using
identical IR. Sums below are storage totals across functions, not the
stack consumption of one execution:

| Metric | Before | After | Before `-O` | After `-O` |
| --- | ---: | ---: | ---: | ---: |
| Sum of frame bytes | 287,728 | 63,472 | 181,408 | 50,096 |
| Largest frame | 82,160 | 8,224 | 56,048 | 4,304 |
| Sum of scanned lower words | 11,968 | 2,694 | 5,754 | 1,658 |

The official basic suite now passes **at 8 MiB** in both optimization
modes, normally and with `FUGC_SCRIBBLE=1 FUGC_VERIFY=1`. The harness
enforces `ulimit -s 8192` for both reference and candidate: the former
32 MiB candidate-only allowance is gone. This is also a frame-growth
regression check, exercising `calls.lua`'s deep C recursion. Rebuilding
the original allocator and running it through the new harness fails in
`calls.lua` in both modes (exit 1, no final success marker); restoring
slot reuse passes.

To reproduce, copy the official archive unpacked by `nix/lua.nix` into a
writable directory and run there:

```sh
(ulimit -s 8192; /path/to/reference/bin/lua -e '_U=true' all.lua)
(ulimit -s 8192; /path/to/check/plain/bin/lua -e '_U=true' all.lua)
(ulimit -s 8192; /path/to/check/optimized/bin/lua -e '_U=true' all.lua)
# Repeat with FUGC_SCRIBBLE=1 FUGC_VERIFY=1 in the environment.
```

Harness mutation checks planted wrong number parsing, math and formatting,
extra stdout, and a false-success official-suite invocation without its
marker. All five were caught before restoring the real candidate.
