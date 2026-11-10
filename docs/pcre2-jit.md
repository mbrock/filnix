# PCRE2's JIT (sljit) and the Fil-C LLVM JIT

PCRE2's JIT compiles a pattern to machine code with sljit, a small portable
assembler. Fil-C has no executable memory, so that JIT cannot run. This note
records what the Fil-C package does today, whether sljit could emit LLVM IR
for Fil-C's own JIT instead, and what a prototype measured. The prototype is
in `experiments/pcre2-sljit-llvm`.

## Summary

- `pkgsFilc.pcre2` (10.48) is built with `--enable-jit=auto
  --enable-jit-sealloc`. It reports JIT support (`pcre2test -C jit` prints 1),
  but every `pcre2_jit_compile` fails with "no more memory" and matching falls
  back to the interpreter. Callers pay for a failed JIT compile per pattern.
- An sljit backend that emits LLVM IR for the Fil-C LLVM JIT is feasible. A
  prototype lowers real sljit LIR for ten patterns to IR, compiles it with
  `FilLLVMJIT_CompileModule`, and gets the same matches as the interpreter.
  The generated code is instrumented like any Fil-C code, so a wrong lowering
  traps instead of corrupting memory.
- Matching is 1.3 to 21 times faster than the Fil-C interpreter, and 0.9 to
  18 times against the interpreter with `patches/pcre2-10.48-filc-match.patch`.
  It is still 1.3 to 7 times slower than native sljit on nine of ten patterns.
- Compiling is the problem: 44 to 300 ms per pattern at `opt-level` 2, against
  0.03 to 0.12 ms for native sljit. JIT on first use is not viable. It needs a
  hotness threshold or an explicit opt-in, and the shared object cache.
- The cheap step is independent of all this: build the shared pcre2 with
  `--disable-jit` and the match patch, as PHP's private copy already is.

## Why sljit cannot run

sljit writes machine code into memory it maps executable and then calls it.
Fil-C's runtime rejects `PROT_EXEC` in `mmap` and `mprotect` (`from_user_prot`
in `filc_runtime.c` returns `EINVAL`), and a function pointer without a
function capability cannot be called. `--enable-jit-sealloc` does not help:
it only changes how the executable mapping is obtained.

The staging toolchain has a different route. `filc_llvm_jit.h` exposes a
subset of the LLVM-C API and `FilLLVMJIT_CompileModule`, which runs the module
through the Fil-C pass and links it into the process. PHP's opcache JIT
already uses it (`.#php85-jit`). So the question is whether sljit's LIR can
be lowered to LLVM IR.

## How the lowering works

`pcre2_jit_compile.c` (14,400 lines) calls about 45 `sljit_emit_*` functions:
moves, two-operand arithmetic that sets flags, compare and jump, labels, calls
to C helpers, and a "fast call" that stores a return address in a register.
A backend implements those and `sljit_generate_code`. The prototype does the
same lowering from a text dump of the LIR:

- Each sljit register is an `alloca` of `ptr`. Machine words are `ptr` so
  that capabilities survive moves and stores to the backtrack stack. Fil-C
  gives `inttoptr` a capability only when the integer came from a `ptrtoint`
  in the same function, so words that may hold pointers are never kept as
  integers across a store.
- Word loads and stores are `ptr` loads and stores. Add and subtract are GEPs
  on the first operand. Other arithmetic goes through `ptrtoint`.
- Flags are three hidden slots (result and both operands), turned into an
  `icmp` at the jump that reads them.
- Labels are basic blocks. `fast_call`, `fast_return`, `mov_addr` and indirect
  jumps use small integers as addresses and a `switch`.
- Immediates that are host addresses become GEPs on external globals, bound
  with `FilLLVMJIT_SetGlobalMapping`.

The last point is the one that reaches into PCRE2. It embeds host pointers as
plain word immediates and displacements: the UCD tables, `utf8_table4 - 0xc0`,
the character tables, class bitmaps inside the compiled pattern, and tables
from `allocate_read_only_data`. A backend cannot tell these from integers.
A real port tags them at about 40 sites in `pcre2_jit_compile.c`, or addresses
pattern data relative to the `pcre2_code` argument.

## Measurements

Nanoseconds per `pcre2_match` call over an HTML-like subject, PCRE2 10.49,
16-core orb. "Native" is gcc with sljit and the SIMD fast-forward paths off;
they are x86-specific and optional, and with them native is up to 3 times
faster again on literal scans. Reproduce with
`experiments/pcre2-sljit-llvm/run.sh`.

| Pattern | Native sljit | Fil-C interpreter | with match patch | Fil-C LLVM JIT | JIT compile, ms |
| --- | ---: | ---: | ---: | ---: | ---: |
| tag | 75 | 1250 | 1020 | 347 | 217 |
| email | 702 | 33500 | 27500 | 1706 | 135 |
| word | 24 | 422 | 193 | 93 | 44 |
| alt | 259 | 4060 | 3320 | 535 | 111 |
| entity | 82 | 571 | 330 | 286 | 112 |
| shortcode | 588 | 1220 | 805 | 861 | 302 |
| key | 25 | 404 | 163 | 97 | 47 |
| date | 24 | 524 | 301 | 171 | 216 |
| utf | 2369 | 34200 | 26400 | 1450 | 75 |
| lit | 258 | 2270 | 1880 | 342 | 67 |

The patterns are in `pats.h`. Runs vary by about 10%.

- The big wins (`email`, `utf`, `alt`, `lit`) are patterns where the JIT's
  generated scan loop replaces the interpreter restarting at each offset.
  Anchored and short patterns gain 1.2 to 3 times over the patched interpreter,
  and `shortcode` gains nothing.
- `opt-level` 1 compiles a little faster (37 to 238 ms) and runs as fast as 2.
  Level 0 compiles in 28 to 108 ms but its code is no faster than the
  interpreter. Level 3 gains nothing.
- Building the IR takes 4 to 8 ms; the rest is LLVM.
- With `FilLLVMJIT_EnableSharedObjectCache`, a process that compiles a module
  a forked sibling already compiled takes 1.4 to 3.2 ms. A hit needs the same
  mapped pointers, so a real backend must keep per-process addresses out of
  the module.

A warm WordPress request makes 331,164 `pcre2_match` calls over 206 patterns
(`docs/php-port-notes.md`). Compiling all of them costs roughly 25 seconds per
process without the cache. Against the patched interpreter, `email` pays
back its compile after about 5,000 calls, but `tag`, `word` and `key` save
under 1 µs per call and need 300,000 to 700,000. So only scan-heavy or very
hot patterns in long-lived workers are worth compiling.

## What a real backend needs

- **sljit**: a new `sljitNativeLLVM.c` and config entry. The RISC-V backend
  (5,300 lines) is the closest model; an estimate is 3,000 to 5,000 lines.
  SIMD operations report unsupported, which PCRE2 already handles.
- **PCRE2**: tag pointer immediates, and route `sljit_generate_code` and
  `sljit_free_code` through the JIT module. The JIT reads `pcre2_real_code`
  and `pcre2_match_data` at fixed offsets, so it must agree with the match
  patch, which adds a field.
- **Toolchain**: the LLVM JIT is only in the staging toolchain.
  `-enable-filc-jit` is a link flag of the executable, and setuid processes
  are refused, so a shared `libpcre2` cannot opt in by itself; every program
  that wants it must be linked with the flag.
  The C API lacks an error string, `LLVMVerifyModule`, and the dispose
  functions. `FilLLVMJIT_BlessPointer` and `zblessedptr` were not exercised.
- **Policy**: compile only when asked (`pcre2_jit_compile` from callers that
  opt in, such as PHP with `pcre.jit=1`) or past a call-count threshold.

A rough estimate is 4 to 8 weeks to pass PCRE2's JIT tests, before the
toolchain questions.

## What the prototype does not cover

It replays LIR that a native build dumped, so there is no sljit backend yet.
Callouts, script runs and `(*MARK)` searches abort. Partial matching,
`sljit_emit_select`, backtrack stack growth past 32 KiB, and the 16- and
32-bit libraries are untested. Ten patterns are not PCRE2's test suite.

## Another route: a regex compiler on nanofil

`experiments/regex-nanofil` tries a compiler that does not involve sljit or
LLVM: 728 lines of Prolog turn the bytecode `pcre2_compile` makes into
nanofil's unchecked IR, and nanofil, `as` and `ld -shared` make a shared
object to `dlopen`. PCRE2 keeps parsing, numbering groups and finding where
a match can start; a pattern with an opcode the compiler does not know stays
on the interpreter.

On nine of the ten patterns here, and on 27 more that exercise atomic and
possessive groups, lookbehind, multiline and group loops, it agrees with the
interpreter from every start offset of the subject. The nine are 4.8 to 25
times faster than the interpreter: at or above native sljit's speed on five
of them and ahead of the LLVM JIT on seven. It needs no executable memory,
no link flag and no LLVM in the process.

nanofil takes 0.15 to 0.8 s per pattern, so the experiment also has a patch
to libpcre2 that serves `pcre2_jit_compile` from a cache directory of shared
objects, named by `PCRE2_RX_CACHE`, and runs the compiler on a miss. With it
`pcre2_match` is 3 to 17 times faster than the patched interpreter on the
nine patterns, and a cache hit costs 0.1 to 0.9 ms. PCRE2's `testinput1` and
`testinput2` give the interpreter's output with `-jit`; 1383 of their 2485
patterns are compiled and the rest stay on the interpreter. It is not wired
into `pkgsFilc.pcre2`.

The compiler also runs on Trealla alone, with the same output as on
SWI-Prolog, but a miss then takes 1 to 4 s with a native Trealla and 0.9 to
17 s inside a Fil-C one, against 0.15 to 0.8 s. The README has the numbers,
the cache rules and what is not compiled.
