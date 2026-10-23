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
export TPL=/tmp/tpl-native/bin/tpl FILCC=/tmp/filcc/bin/clang
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

`preprocess()` in `progtest.sh` is the one corpus preprocessing hook for
M4e. stdout, stderr and exit status are compared separately; stderr with a
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

## Counts

Baseline on the M4c compiler, before the concurrent struct-value work:

| Source | `.c` files | No main | With main | Pass | Reject | Wrong result | Reference error |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| cproc | 196 | 147 | 49 | 19 | 22 | 1 | 7 |
| c-testsuite | 220 | 0 | 220 | 198 | 21 | 1 | 0 |
| **Total** | **416** | **147** | **269** | **217** | **43** | **2** | **7** |

There were no preprocessing, assembler, nanofil-link, reference-output or
timeout failures. Of 52 non-passes, 27 are planned exclusions (including
one VLA wrongly accepted), 2 are struct-value work in progress, 16 are
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

### VLAs / variably modified types — 7 (6 rejections, 1 wrong result)

**Planned:** PLAN decision 6 rejects VLAs. cproc: `func-vla`, `sizeof-vla`,
`vla-deref`, `vla-nested`, **`cast-vm`**. c-testsuite: `00162`, `00207`.

```c
int main(void) {
    int n = 0;
    (int (*)[++n])0;
    return n;
}
```

**Unsafe acceptance of an unsupported construct (wrong semantics, not a
demonstrated memory-safety escape):** nanofil exits 0, filcc exits 1.
The full `cast-vm` exits 1 vs filcc's 0: neither cast's size side effect
is evaluated. This should reject, not silently compile. Other members
already reject with `sizeof: non-constant array size`, `variable length
arrays are not supported`, or `... has a type nanofil does not support
(non-constant array size)`.

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

### GNU statement expressions — 2 rejections

**Planned:** explicitly in M4's rejection suite/docs. c-testsuite: `00213`,
`00214` (the latter also exercises floating point).

```c
int main(void) { return ({ int x = 0; x; }); }
```

nanofil: `statement expressions are not supported, at {`.

## In progress elsewhere — 2

### Struct values — 2 rejections

**M4d, not chased here.** cproc: `conditional-struct`, `struct-copy`.
No executable struct-argument/return tests occur in this cproc snapshot;
its `struct-passing*`/`struct-return*` fixtures have no main and are
inventoried as such, not counted as passing ABI tests.

```c
struct S { int x; };
int main(void) { struct S a = {1}, b; b = a; return b.x; }
```

nanofil: `loading a struct(0) value is not supported yet`.

## Other gaps — 16

### Wide literals — 5 rejections

**Gap**, not a planned M4 exclusion. cproc: `wchar-sign+aarch64`,
`wchar-sign+riscv64`, `wchar-sign+x86_64-sysv`; c-testsuite: `00098`, `00220`.

```c
int main(void) { return L'\0'; }
```

nanofil: `expected ;, at chr(0)`. The lexer treats `L` as an identifier
separate from the literal. `00220` similarly stops before a wide string.
Supporting wide strings needs their element type/encoding too, not just
discarding the prefix in the lexer.

### Compound literals — 3 rejections

**Gap:** C99, not excluded by the plan. cproc:
`conditional-compound-literal`; c-testsuite: `00149`, `00150`.

```c
int main(void) { return ((int[]){1})[0]; }
```

nanofil: `compound literals are not supported yet`. The two file-scope
address initializers stop at `initializer is not an address constant`.

### Unsized array length with brace-elided struct initializers — 1 wrong result

**Gap:** c-testsuite `00205`, a real J interpreter snippet. Not a struct
copy/argument/return; it is array-length inference.

```c
struct S { int a, b; } s[] = {1, 2, 3, 4};
int main(void) { return sizeof(s) / sizeof(s[0]); }
```

nanofil exits **4**, filcc exits **2**. The full test infers 63 elements
instead of 9, emitting 432 extra stdout lines for zero-filled elements;
both exit 0. This is not a Fil-C panic or a padding/bounds difference.

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

### `_Generic` — 1 rejection

**Gap:** C11, not a planned exclusion. c-testsuite: `00219`.

```c
int main(void) { return _Generic(1, int: 0, default: 1); }
```

nanofil: `_Generic is not supported, at (`.

### GNU omitted-middle conditional — 1 rejection

**Extension gap:** cproc `conditional-omit`.

```c
int main(void) { return 1 ?: 2; }
```

nanofil: `expected an expression, at :`.

### GNU range designators — 1 rejection

**Extension gap:** c-testsuite `00216`.

```c
int main(void) { int a[2] = {[0 ... 1] = 3}; return a[1]; }
```

nanofil: `GNU range designators are not supported, at int(1,none-dec)`.

### `__builtin_expect` — 1 rejection

**Extension gap:** cproc `builtin-expect`.

```c
int main(void) { return __builtin_expect(0, 0); }
```

nanofil: `undeclared identifier __builtin_expect`.

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

1. Reject VM casts before lowering; planned unsupported syntax must not
   silently lose side effects.
2. Fix unsized aggregate-array inference in the frontend's type/lowering
   workstream. This is the only wrong-result case inside the intended
   integer/aggregate subset observed here.
3. Fold in M4d by rerunning the survey and intentionally updating its
   expected list; do not delete those entries or weaken pass detection.
4. Decide scope for wide literals, compound literals, `_Generic` and GNU
   declarator/extension gaps. No parser/lexer changes were made in M4f.

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
