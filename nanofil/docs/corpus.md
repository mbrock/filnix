# M4f: real C corpus

## Reproduce

```sh
nix build .#checks.x86_64-linux.nanofil
# For a retained survey (after building the tools in AGENTS.md):
nix build --impure --no-link --print-out-paths --expr '
  let pkgs = import (builtins.getFlake (toString ./.)).inputs.nixpkgs {
    system = "x86_64-linux";
  }; corpus = import ./nanofil/nix/corpus.nix { inherit pkgs; };
  in [ corpus.cproc corpus.c-testsuite ]'
export SWIPL=/tmp/swipl/bin/swipl FILCC=/tmp/filcc/bin/clang
python3 nanofil/tests/corpus.py CPROC_STORE_PATH C_TESTSUITE_STORE_PATH \
  --work /tmp/corpus
# Narrow a rerun with --test c-testsuite/00205.c (repeatable).
# Review results.tsv and per-test log/output/diffs before using --record.
```

The sources are fixed-output Nix fetches in [corpus.nix](../nix/corpus.nix):

- cproc at `d1c53ddf56571573a7025324c8dd5c6d547a4d1f`:
  `sha256-u9zlMI0NOLUXCXtEWw/c8gOgqeH6yAq+ZIqIoywPitU=`.
  **License correction:** cproc itself is ISC, but this revision's LICENSE
  explicitly dedicates `test/*` to the public domain under the Unlicense.
- c-testsuite at `5c7275656d751de0e68b2d340a95b5681858ed07`:
  `sha256-bKfdr7veh+UJvvlumm7vxRyP5uO9uelZziBsp30HbgU=`.
  Its runner is MIT; individual tests have their own `.otag` provenance,
  as explained by `tests/LICENSE`. The fetched trees retain all licenses.

`corpus.py` inventories every `.c` recursively in cproc's `test/` and
c-testsuite's `tests/single-exec/`. Programs with `main(` (allowing
whitespace, ignoring comments) go through **the existing `progtest.sh`**:
filcc `-E` → nanofil → GNU as → filcc link; the reference is filcc `-O1`.
Both links include `-lm`, needed by c-testsuite 00174. No source rewrites,
private headers, synthesized main functions, or architecture-name skips.
In particular, a test named `+aarch64` is compared against the x86-64 oracle,
not checked against cproc's architecture-specific `.qbe` expectation.

Since M4e, nanofil preprocesses `.c` files itself (`c_pp.pl`); filcc
only builds the reference. `corpus.py` runs programs in parallel
(`--jobs`, default the CPU count). stdout, stderr and exit status are compared separately; stderr with a
Fil-C safety panic and its exit status normalize to `trap`. For single-exec
tests the reference must additionally exit 0 and match `.c.expected`
(stdout followed by stderr; these pinned tests do not interleave the two).
Compilation is bounded to 20 seconds and each execution to 10 seconds;
timeouts never count as passes, even if both executables time out.
Each executable gets a fresh working directory, so file-I/O tests neither
write into the checkout nor share files with the other executable.

The complete [expected-results list](../tests/corpus-expected.tsv) is checked
in Nix, not just a whitelist of passes. An added/removed test, a regression,
or **a newly passing test** fails with a baseline diff and diagnostics.
`no-main` entries explicitly inventory function-only/preprocessor/constraint
fixtures, which are not executable programs. Reference compilation failures
are distinct from nanofil rejections. A matching expected failure means
the survey is stable, **not** that the compiler implements that feature.

## Current counts (M9)

The checked baseline now has **243 passes, 19 rejections, 7 reference
errors and 147 without main**. Floating-point support adds eleven passes:
cproc `conditional`, `convert-char-float`, `logical-and`, `logical-or`,
`while-condition`; c-testsuite `00113`, `00119`, `00123`, `00174`, `00175`,
`00195`. They cover conversions, truth and comparisons, gradual underflow,
variadic float promotion, libm calls and float fields accessed by pointer.
Every newly passing test matches clang through `progtest.sh`; the full
survey still checks all other outcomes unchanged.

## Historical M4 counts and triage

The remaining sections retain the earlier survey and its diagnostics;
the floating-point rejections below are resolved by M9.

Baseline after M4d (struct values) and the array-length fix. The M4c
baseline had pass 19 / 198 / 217, reject 22 / 21 / 43 and wrong result
1 / 1 / 2; `conditional-struct` and `struct-copy` (M4d) and `00205`
(array length) now pass.

| Source | `.c` files | No main | With main | Pass | Reject | Wrong result | Reference error |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| cproc | 196 | 147 | 49 | 28 | 14 | 0 | 7 |
| c-testsuite | 220 | 0 | 220 | 203 | 17 | 0 | 0 |
| **Total** | **416** | **147** | **269** | **231** | **31** | **0** | **7** |

There were no preprocessing, assembler, nanofil-link, reference-output or
timeout failures. Of 38 non-passes, 27 are planned exclusions, 4 are
other gaps, and 7 cannot be compiled by the reference in its default mode.
Each program appears in exactly one primary-cause group below; secondary
features may be hidden behind the first error. All IDs below are `.c`
basenames, under the named source. Every C block is a standalone minimal
reproduction; diagnostics omit only the path/line prefix.

## Planned exclusions — 27

### Floating-point values — 11 rejections

**Planned:** M4 is integers only, including when real headers declare floats.
cproc: `conditional`, `convert-char-float`, `logical-and`, `logical-or`,
`while-condition`. c-testsuite: `00113`, `00119`, `00123`, `00174`, `00175`,
`00195`.

```c
int main(void) { double x = 1; return x; }
```

nanofil: `cannot assign int to double`. Other members report
`loading a float/double value is not supported yet`, `cannot convert uchar
to float`, or `floating point is not supported`.

### VLAs / variably modified types — 7 rejections

**Planned:** PLAN decision 6 rejects VLAs. cproc: `func-vla`, `sizeof-vla`,
`vla-deref`, `vla-nested`, **`cast-vm`**. c-testsuite: `00162`, `00207`.

```c
int main(void) {
    int n = 0;
    (int (*)[++n])0;
    return n;
}
```

All reject. `cast-vm` was accepted with its size side effect silently
dropped (nanofil exited 0, filcc 1); every variably modified type name, in
casts, `sizeof`, declarations and parameters, now fails with `variably
modified types (non-constant array size) are not supported`
(`tests/c/reject/vm_cast.c`, `vm_pointer.c`).

### Bitfields — 4 rejections

**Planned:** PLAN decision 6. cproc: `bitfield-assignment-sign-extend`,
`bitfield-integer-promotion`, `bitfield-short`; c-testsuite: `00218`.

```c
struct S { unsigned x : 1; };
int main(void) { struct S s; s.x = 1; return s.x; }
```

nanofil: `s has a type nanofil does not support (bitfields)`. In the full
tests the unsupported bitfield contaminates the enclosing layout and the
diagnostics instead say `no member named x/a/common`. Those should name
bitfields rather than a missing member. No support added.

### Variadic definitions / va builtins — 3 rejections

**Planned:** PLAN decision 6; variadic *calls* remain supported.
cproc: `builtin-vaarg-vm`; c-testsuite: `00140`, `00204`.

```c
int f(int n, ...) { return n; }
int main(void) { return f(0); }
```

nanofil: `defining variadic function f is not supported`. The other two
stop earlier at `__builtin_va_start is not supported, at (`.

## Fixed since the M4f survey

- **GNU statement expressions**: c-testsuite `00214` now passes;
  `00213` still rejects its floating-point values. The survey at that stage was
  231 passes, 31 rejections, 7 reference errors and 147 without main.
- **Wide literals** (cproc `wchar-sign+*` ×3, c-testsuite `00098`,
  `00220`): `L`, `u`, `U` character and string literals, `u8` strings.
- **Compound literals** (cproc `conditional-compound-literal`,
  c-testsuite `00149`, `00150`): block scope as an unnamed local, file
  scope as unnamed static data.
- **GNU `c ?: b`** (cproc `conditional-omit`) and **`__builtin_expect`**
  (cproc `builtin-expect`).

- **Struct values (M4d):** cproc `conditional-struct`, `struct-copy` (were
  `loading a struct(0) value is not supported yet`). This cproc snapshot
  has no executable struct-argument/return tests; its `struct-passing*`
  and `struct-return*` fixtures have no main.
- **Unsized array length with brace-elided struct initializers:**
  c-testsuite `00205`. `struct S { int a, b; } s[] = {1, 2, 3, 4};` had 4
  elements instead of 2; the frontend now counts the entries each element
  takes, as initialization does. Regression cases are in
  [tests/c/structs.c](../tests/c/structs.c).

## Other gaps — 4

### Abstract array parameter declarator — 1 rejection

**Gap:** c-testsuite `00209`. The earlier complex function declarators
parse, but an unnamed parenthesized array parameter does not.

```c
int f(int ([4]), int);
int main(void) { return 0; }
```

nanofil: `expected a parameter declaration, at [`.

### Attribute inside a function-pointer declarator — 1 rejection

**Gap:** c-testsuite `00210`. Its earlier packed unions are not used;
the first actual failure is a GNU attribute in a pointer cast, not
aggregate ABI lowering.

```c
int f(void) { return 42; }
int main(void) {
    void *p = &f;
    return ((int(__attribute__((noinline)) *)(void))p)();
}
```

nanofil misbuilds the declarator and rejects a pointer conversion (the
full test: `cannot convert ptr(void) to func(func(int,[],fixed),[ptr(int)],fixed)`).

### `_Generic` — resolved

C11 selection now passes c-testsuite `00219`, including qualified pointer
targets, lvalue conversion, compatible typedefs, function/array decay,
struct identity and `default`. cproc `generic.c` also compiles, but stays
`no-main` in the executable survey because it only defines a global.

### GNU range designators — 1 rejection

**Extension gap:** c-testsuite `00216`.

```c
int main(void) { int a[2] = {[0 ... 1] = 3}; return a[1]; }
```

nanofil: `GNU range designators are not supported, at int(1,none-dec)`.

### C23 attribute spelling — 1 rejection

**Outside the C11 contract:** cproc `struct-packed` uses `[[gnu::packed]]`.
Packed structs themselves are already an intentional rejection in M4's
tests; this particular failure is earlier, at the new attribute syntax.

```c
struct [[gnu::packed]] S { char x; int y; };
int main(void) { return 0; }
```

nanofil: `expected a declaration, at struct`.

## Reference limitations — 7

### C23 keywords in filcc's default language mode — 6 reference errors

**Not measured nanofil failures.** cproc: `alignas-local-strict`,
`alignas-local`, `alignas-vla-strict`, `cast-bool-char`, `thread-local`,
`constraint/c23-6.7.7.3p2-vm-declaration-3`. No C23 flags or compatibility
macro rewrites are injected into either compiler.

```c
int main(void) { alignas(16) char x; return 0; }
```

filcc: `call to undeclared function 'alignas'; ISO C99 and later do not
support implicit function declarations`. The others use `bool` without
stdbool.h (`use of undeclared identifier 'bool'`) or `thread_local`
(`unknown type name 'thread_local'`). Several also need VLA/TLS support
that nanofil explicitly excludes. Whether to add a separate C23 mode is
an orchestrator decision, not a reason to count these as passes.

### filcc LLVM assertion on typeof of a VM expression — 1 reference error

**Reference compiler bug, not investigated in the toolchain.** cproc:
`typeof-vm`.

```c
int main(void) {
    int n = 1;
    int (*p)[n] = 0;
    typeof(typeof(n++, p)) q;
    return n;
}
```

filcc `-O1`: `CodeGenFunction::EmitDeclRefLValue` assertion
`E->isNonOdrUse() != NOUR_Unevaluated && "should not emit an unevaluated operand"`
in `clang/lib/CodeGen/CGExpr.cpp:3038`. No compiler pin or runtime changes
belong in this milestone.

## Follow-ups

1. The remaining gaps are small parser items (GNU range
   designators, two declarator forms, C23 attribute spelling).

## Harness validation

All 18 minimal reproductions above were executed through `progtest.sh`
(including the reduced filcc assertion). A deliberately wrong baseline
(`hello.c` marked `reject`) failed with a `reject` → `pass` diff; restoring
it passed the focused survey. A scratch infinite-loop program produced
`run-timeout`, not pass, with **both** executions exiting 124; a 1 ms compile
budget produced `compile-timeout`. Test `00187` passed with its two
`fred.txt` files isolated in separate temporary directories. The existing
whole-program tests still cover stderr differences and normalized safety
panics, including under GC scribbling/verification.
