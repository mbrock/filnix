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

## Native stack gap: backend follow-up

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
Reducing nanofil's frame footprint is backend work, not fixed by this
integration check.

The harness therefore keeps the reference official suite explicitly at
8 MiB and raises **only the distinct nanofil candidate's official-suite
subprocess** to 32 MiB, leaving headroom above the measured boundary.
The deterministic `-e` scripts do not get a larger stack. A reference
self-check also stays at 8 MiB. Revisit this allowance when the backend
frame problem is fixed; do not silently raise the reference limit.

To reproduce after building, copy the official archive unpacked by
`nix/lua.nix` into a writable directory, then run there:

```sh
(ulimit -s 8192; /path/to/reference/bin/lua -e '_U=true' all.lua)
(ulimit -s 19456; /path/to/check/plain/bin/lua -e '_U=true' all.lua)
(ulimit -s 13312; /path/to/check/optimized/bin/lua -e '_U=true' all.lua)
# Repeat with FUGC_SCRIBBLE=1 FUGC_VERIFY=1 in the environment.
```

Harness mutation checks planted wrong number parsing, math and formatting,
extra stdout, and a false-success official-suite invocation without its
marker. All five were caught before restoring the real candidate.
