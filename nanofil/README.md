# nanofil

A C compiler and an executable model of
[Fil-C](https://github.com/pizlonator/fil-c)'s capability semantics,
written in Prolog. It emits x86-64 assembly that links with clang-built
Fil-C code. For its supported subset, it implements capability-checked
accesses, collector roots and checked indirect calls.

The aim is a compiler whose meaning can also be worked on directly:
inspect object identity and pointer authority, search for counterexamples
to transformations, and state what justifies replacing a runtime check
with other evidence. Runtime checks are one implementation of safety
obligations, not the obligations themselves. FilPizlonator's abstract
interpreters are a reference for that separation, not a mandate to
reproduce LLVM's optimizer.

Today nanofil has executable IR semantics, structural validation,
differential tests and bounded symbolic comparisons. It does not have a
universal correctness proof or an access-proof certificate system. The
[foundation and direction](docs/campaign.md) distinguish what exists from
what we want to establish. The compiler runs on SWI-Prolog; Trealla's
dialect is retained, with active work currently on SWI.

## A look

```c
int sum(int *a, int n) {
    int s = 0;
    for (int i = 0; i < n; i++)
        s += a[i];
    return s;
}
```

`nanofil -O cc-ir sum.c` prints the IR, nanofil's own: Prolog terms
([src/ir.pl](src/ir.pl)), one clause per function or data object, which
`print`, `compile` and the tests read back. Its classes are `w l s d`
and the pointer class `p`, and [src/interp.pl](src/interp.pl) defines
what it means:

```prolog
func(sum, export, w, [param(p, tmp(v0)), param(w, tmp(v2))], [
    block(start, [], [], goto('L6')),
    block('L6', [
        phi(tmp('pr.2'), w, ['L8'-tmp(v22), start-const(0)]),
        phi(tmp('pr.1'), w, ['L8'-tmp(v20), start-const(0)])
    ], [
        let(tmp(v12), w, cmp(slt, w), [tmp('pr.2'), tmp(v2)])
    ], branch(tmp(v12), 'L7', 'L9')),
    block('L7', [], [
        let(tmp(v16), l, ext(sw), [tmp('pr.2')]),
        let(tmp(v17), l, mul, [tmp(v16), const(4)]),
        let(tmp(v18), p, add, [tmp(v0), tmp(v17)]),
        let(tmp(v19), w, load(sw), [tmp(v18)]),
        let(tmp(v20), w, add, [tmp('pr.1'), tmp(v19)])
    ], goto('L8')),
    block('L8', [], [
        let(tmp(v22), w, add, [tmp('pr.2'), const(1)])
    ], goto('L6')),
    block('L9', [], [], ret(tmp('pr.1')))
]).
```

Without `-O` the IR also says where its code comes from: each block
begins with `loc(File, Line)`, and each statement's code follows the
`loc` of its line. The middle end and the backends drop them for now.

`nanofil -O cc sum.c` turns that into assembly that checks the load
against `a`'s capability and polls for the collector on the back edge.

## How it is built

```diagram
C source ──▶ preprocess, parse, elaborate, lower
                                          │
                                          ▼
                                     unchecked IR
                                          │ selected middle-end passes
                                          │ pizlonate
                                          ▼
assembly ◀── AMD64 ◀── Fil-C ABI plans ◀── checked IR
                                         checks, flight, effects
```

The IR has a reference semantics: an interpreter written with CLP(Z)
constraints. Differential fixtures compare interpreted and native
outcomes, and optimized results against the unoptimized IR. Symbolic
integers can search for counterexamples; complete finite searches establish
absence only within their bounds. Memory addresses, capabilities and
allocation sizes must be concrete when used, as must floating-point values.
The interpreter abstracts GC and concurrency; native tests cover runtime
integration. Neither kind of test proves the compiler correct universally.

In [checked IR](docs/pizlonation.md), an access cites a proven address
and the validator checks its coverage. Currently that evidence must come
from a runtime check, either immediately preceding or, under the opt-in
`--checks=reuse`, an earlier one still valid ([M7](docs/m7.md)); static
discharge remains planned. The interpreter distinguishes an invalid raw access
(`unchecked`) from a program's legitimate safety trap. Keeping access
safety separate from behavior preservation is the basis for future work.

The [playground](https://mbrock.github.io/filnix/nanofil/play/) exposes
the actual intermediate IR for independently selected promotion, copy
elimination and local storage. It is a view of the compiler's computations,
not a second implementation. Explaining why an obligation is discharged
is a future extension of that same pattern.

## Trying it

From a filnix checkout:

```sh
nix build -o /tmp/filcc .#filcc-staging
export FILCC=/tmp/filcc/bin/clang          # used to preprocess and link
cd nanofil/src
../bin/nanofil -O cc ../tests/c/prog/hello.c </dev/null > hello.s
as -o hello.o hello.s && $FILCC -o hello hello.o && ./hello
```

`bin/nanofil` uses `swipl` from `PATH` (or `SWIPL`); set
`NANOFIL_HOST=trealla` to use Trealla. Other commands: `cc-ir`,
`tokens`, `print` and `compile` (for IR files), `run FILE FN ARGS...`
(interpret), and `difftest`. See the top of
[src/main.pl](src/main.pl).

`--registers=local` before `cc` or `compile` enables integer immediate
selection followed by validated block-local stack caching. It is independent of
`-O`; `--registers=stack` is the default reference without `-O`, and
`-O` defaults to whole-function registers with register operands and
forwarded frame-word loads (`--registers=cells`, [docs/perf.md](docs/perf.md)). Build/test harnesses
accept the same choice as `NANOFIL_REGISTERS=local`. This does not change
pointer/root placement, and setjmp functions retain their original code.
See [docs/m6.md](docs/m6.md) for the deliberately limited scope and cost.

`-O` also copies small constant `memcpy` and `memmove` inline (1 to 16
bytes) when the runtime's checks would pass and neither object has aux,
and calls the runtime otherwise. `--memcpy=call` (or `NANOFIL_MEMCPY=call`)
keeps every call, the reference; nanofil-cc passes it for `-fno-builtin`
and `-ffreestanding` ([docs/perf.md](docs/perf.md) item 7a).

`nix build .#checks.x86_64-linux.nanofil` runs everything: unit tests,
differential tests of the interpreter against native code and clang,
whole programs under GC
stress, and a 416-file survey of the cproc and c-testsuite corpora.

## What it compiles

C17 code with integers, `float`, `double` and x87 `long double`:
structs, unions (passed and returned by value as SysV says), enums,
bit-fields, arrays and VLAs, pointers, function pointers, globals with
initializers, `switch` and `goto`, compound literals, variadic
functions, C99 `extern inline`, `__atomic` loads and stores, C23
keywords and `[[...]]` attributes (`-std=c23`), and the GNU extensions
glibc and gnulib lean on: statement expressions, computed `goto`,
`_Thread_local`/`__thread` variables, packed layout, range
designators, `_FORTIFY_SOURCE` and the
`__builtin_*_overflow` family. Of the corpus
programs that have a `main`, all 262 that clang itself builds and runs
match clang's output; what nanofil does not support it refuses with a
message, never miscompiles ([docs/corpus.md](docs/corpus.md)). GNU
hello, zlib, Lua, bzip2, lz4, SQLite, GNU sed, jq and dash build with
nanofil alone and behave exactly like their clang builds, each checked
by a `checks.x86_64-linux.nanofil-<name>` build ([PLAN.md](PLAN.md),
M4); zlib's compressed output is byte-identical, at about five times
clang's time.

It refuses `_Complex`, `_Atomic`, inline `asm` other than an empty
barrier, and K&R definitions. Without
`-O` every temporary lives in a stack slot; `-O` promotes locals and
allocates scalar registers ([docs/perf.md](docs/perf.md)).

## Reading on

- [docs/campaign.md](docs/campaign.md): the semantic foundation, evidence
  and trust boundaries, upstream analyses, and current priorities.
- [PLAN.md](PLAN.md): milestones, decisions, what is next.
- [docs/pizlonation.md](docs/pizlonation.md) and
  [docs/lifetime.md](docs/lifetime.md): the current check/effect contract
  and explicit-free model, including what they do not establish.
- [docs/abi-findings.md](docs/abi-findings.md): the Fil-C ABI as checked
  against filnix's pinned Fil-C.
- [docs/m1.md](docs/m1.md) to [docs/m5.md](docs/m5.md): the IR and
  interpreter, the plain backend, the Fil-C lowering, the C frontend,
  and the middle end.
- [docs/handoff.md](docs/handoff.md): the original design notes.
- [AGENTS.md](AGENTS.md): tools, tests and conventions for working on it.
- The wiki's [nanofil pages](https://mbrock.github.io/filnix/nanofil/):
  the source drawn as terms by [web/dterm.pl](web/dterm.pl) (SWI-Prolog),
  built with the site, `nix build .#site`.
- [docs/dterm.md](docs/dterm.md): where dterm comes from, and `doc/3`,
  documentation as a relation whose examples are tests.
