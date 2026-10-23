# nanofil

A C compiler written in Prolog that emits x86-64 assembly in the
[Fil-C](https://github.com/pizlonator/fil-c) ABI. Its object files link
with clang-built Fil-C code, and they keep Fil-C's guarantees: every
access is bounds-checked against a capability, pointers are rooted for
the garbage collector, and calls go through checked function objects.

It is meant as a small reference for what Fil-C's LLVM pass does, in a
form you can read, test and run backwards. About 13,000 lines of Prolog
run on SWI-Prolog or Trealla.

## A look

```c
int sum(int *a, int n) {
    int s = 0;
    for (int i = 0; i < n; i++)
        s += a[i];
    return s;
}
```

`nanofil -O cc-ir sum.c` prints the IR, which is QBE's plus a pointer
class `p`:

```
export function w $sum(p %v0, w %v2) {
@start
	jmp @L6
@L6
	%pr.2 =w phi @L8 %v22, @start 0
	%pr.1 =w phi @L8 %v20, @start 0
	%v12 =w csltw %pr.2, %v2
	jnz %v12, @L7, @L9
@L7
	%v16 =l extsw %pr.2
	%v17 =l mul %v16, 4
	%v18 =p add %v0, %v17
	%v19 =w loadsw %v18
	%v20 =w add %pr.1, %v19
	jmp @L8
@L8
	%v22 =w add %pr.2, 1
	jmp @L6
@L9
	ret %pr.1
}
```

`nanofil -O cc sum.c` turns that into assembly that checks the load
against `a`'s capability and polls for the collector on the back edge.

## How it is built

```diagram
C source ──▶ preprocessor ──▶ parser ──▶ lowering ──▶ IR
             (DCG)            (DCG)      (cproc style)  │
                                                        ▼
assembly ◀── Fil-C backend ◀── middle end (-O): SSA, promote,
                               copies, alias, escape, loops
```

The IR has a reference semantics: an interpreter written with CLP(Z)
constraints. That interpreter is the test oracle. Every test input runs
in the interpreter and natively, and the results must agree. With `-O`,
each run is repeated on the unoptimized IR and the optimized result must
refine it. Because the interpreter is a relation, it can also run with
unknown inputs, for example to search for arguments on which two
functions differ.

## Trying it

From a filnix checkout:

```sh
nix build -o /tmp/filcc .#filcc
export FILCC=/tmp/filcc/bin/clang          # used to preprocess and link
cd nanofil/src
../bin/nanofil -O cc ../tests/c/prog/hello.c </dev/null > hello.s
as -o hello.o hello.s && $FILCC -o hello hello.o && ./hello
```

`bin/nanofil` uses `swipl` from `PATH` (or `SWIPL`); set
`NANOFIL_HOST=trealla` to use Trealla. Other commands: `cc-ir`,
`tokens`, `print` and `compile` (for QBE text), `run FILE FN ARGS...`
(interpret), and `difftest`. See the top of
[src/main.pl](src/main.pl).

`nix build .#checks.x86_64-linux.nanofil` runs everything: unit tests,
differential tests against real qbe and clang, whole programs under GC
stress, and a 416-file survey of the cproc and c-testsuite corpora.

## What it compiles

C17 code with integers, `float` and `double`: structs, unions, enums, arrays, pointers, function
pointers, globals with initializers, `switch` and `goto`, compound
literals, variadic functions, C99 `extern inline`, C23 `[[...]]`
attributes, and the GNU extensions glibc and gnulib lean on: statement
expressions and the `__builtin_*_overflow` family. Of the corpus
programs that have a `main`, 243 match clang's output; the rest are
refused with a message, never miscompiled
([docs/corpus.md](docs/corpus.md)). GNU hello and zlib build with
nanofil alone and behave exactly like their clang builds; zlib's
compressed output is byte-identical, at about five times clang's time.

It supports `float` and `double`, but refuses `long double`, `_Complex`,
float-containing structs and unions passed or returned by value, bitfields,
VLAs, `_Atomic`, inline `asm` and K&R definitions.
The code generator is deliberately naive: every temporary
lives in a stack slot.

## Reading on

- [PLAN.md](PLAN.md): milestones, decisions, what is next.
- [docs/abi-findings.md](docs/abi-findings.md): the Fil-C ABI as checked
  against filnix's pinned Fil-C.
- [docs/m1.md](docs/m1.md) to [docs/m5.md](docs/m5.md): the IR and
  interpreter, the plain backend, the Fil-C lowering, the C frontend,
  and the middle end.
- [docs/handoff.md](docs/handoff.md): the original design notes.
- [AGENTS.md](AGENTS.md): tools, tests and conventions for working on it.
