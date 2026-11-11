# The Gallina backend through λANF (`nanofil/anf/backend/`)

Milestone M3 of [lambda-anf.md](../../docs/lambda-anf.md): the reader
of IR text and the three compilers of [rocq/backend](../../rocq/backend)
(`compile`, `compile_promoted`, `compile_allocated`), the same Gallina
that `nanofil-backend` is extracted from, compiled by CertiRocq to λANF,
lowered by [AnfLower.v](../lower/AnfLower.v) and compiled by
`nanofil-backend compile-allocated` into a Fil-C program over the arena
of [nanofil/anf](../).

## Files

- `Drive.v`: what the OCaml driver's `compile`, `compile-promoted` and
  `compile-allocated FILE.ir` do, in Gallina: `run` reads the text,
  compiles it and gives the assembly as a stream of chunks of 64 lines,
  each computed when the one before it is printed, then the exit status
  and its reason (0; 1 for a module that is refused or text that is not
  read; 3 for one outside the compiler).
- `Tap.v`: registers the backend's own string functions
  (`Maps.string_hash`, `Order.atom_compare`, `IrText.string_of_rev`, ...)
  as primitives, besides those of [../lower/Prims.v](../lower/Prims.v),
  and taps `run`'s λANF.
- `driver.c`: reads FILE.ir in pieces of 1 MB, applies `run` to the
  command and the pieces, writes each chunk and exits as
  `nanofil-backend` does.
- `run.sh`: the gate. On every IR fixture (`tests/filc` and
  `rocq/backend/tests`), for each of the three commands, the program
  must print what `nanofil-backend` prints, say the same on stderr and
  exit with its status, with the default nursery and with a 4096-word
  one under `FUGC_SCRIBBLE=1 FUGC_VERIFY=1`. `ANF_BENCH="rx.ir lvm.ir"`
  also times both builds on those files.

## Running the gate

As a Nix check, only when asked: it builds CertiRocq, and compiling the
lowered backend takes about 5 minutes and 1.4 GB (the whole check, 9
minutes on an orb).

```sh
nix build -L .#checks.x86_64-linux.nanofil-anf-backend
```

Or by hand, from the repository's root, as for [../lower](../lower/README.md):

```sh
nix build -o /tmp/filcc .#filcc-staging
nix-shell nanofil/anf/lower/shell.nix --run \
  'python3 nanofil/tests/watch.py --label anf-backend --timeout 5400 -- nanofil/anf/backend/run.sh'
```

On an orb, tapping takes 2 minutes (21.6 MB of λANF), `anf-lower` 38 s
and 1.1 GB (18,487 hoisted functions into 3,089 IR functions, 64 MB of
IR), and `nanofil-backend compile-allocated` about 5 minutes and 1.4 GB,
most of it in the validator, whose lookups grow with the square of a
function's temporaries (the largest has 66,000).

## Results

All 156 runs (52 fixtures, three commands) print what `nanofil-backend`
prints, with both nurseries. On the two large inputs of
[lambda-anf.md](../../docs/lambda-anf.md), best of seven runs for rx.ir
and one for lvm.ir, with the same assembly as the OCaml build:

| input | command | arena | ocamlopt | ratio |
| --- | --- | ---: | ---: | ---: |
| rx.ir (367 KB) | compile | 0.97 s | 0.23 s | 4.2× |
| rx.ir | compile-allocated | 1.24 s | 0.30 s | 4.2× |
| lvm.ir (4.4 MB) | compile | 15.7 s | 3.5 s | 4.5× |
| lvm.ir | compile-allocated | 11.0 s | 2.6 s | 4.2× |

The arena peaks at 89 MB on rx.ir and 423 MB on lvm.ir, against 57 MB
and 279 MB. Without the simplification, the tables, the calling
convention and the closure facts of `AnfLower.v`, the same runs took
2.2 s, 2.9 s, 43.8 s and 26.8 s.

Where the rest goes, on rx.ir: 88% of the time is in the lowered
functions, 4% in the string primitives, 1.5% in the collector. The
hottest functions are small and called very often (the atom case of
`term_eqb`, `Z_as_OT.compare`, `ZMap`'s `bal`, `find` and `create`,
`gt_le_dec`), each 3 to 14 times slower than its ocamlopt build: every
call pays the IR function's prologue and epilogue (the stack check, five
callee-saved registers, the Fil-C frame, arguments past the sixth on the
stack) and every arena access a bounds check. Inlining every function of
ten nodes or fewer, with join points for the rest of the caller, made
rx.ir only 5% faster, made the IR 37% bigger and the frames of deep
recursions bigger (the rec_clos2 program of [../lower](../lower/README.md)
took 1.8 times as long), so
`AnfLower.v` does not do it.
