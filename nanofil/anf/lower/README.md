# λANF to nanofil IR (`nanofil/anf/lower/`)

Milestone M2 of [lambda-anf.md](../../docs/lambda-anf.md): CertiRocq's
core λANF, lowered to checked nanofil IR over the 32-bit `w` arena of
[nanofil/anf](../), judged by the proved validator (`ValidFast.valid_fast`)
and compiled by `nanofil-backend compile-allocated`.

```diagram
 Gallina program
    │  CertiRocq Show IR -O 1 --anf-variant 8   nix/certirocq-anf.nix (tap: nix/certirocq-anf-tap.patch)
    ▼
 PROGRAM.ir: anf_ctor, anf_ftag, anf_name and anf_body clauses
    │  ./anf-lower (AnfLower.v, extracted)
    ▼
 checked module(Items) as IR text
    │  nanofil-backend compile-allocated       valid_fast, then Regs.v
    ▼
 x86-64 assembly, linked with anf_arena.c, anf_lower_rt.c and driver.c
```

## Files

- `AnfLower.v`: the lowering, in Gallina. Join continuations and loops
  (a hoisted function never used as a value and never called but in
  tail position, all of whose callers are in one cluster) become blocks
  with phis of their cluster's IR function; tail calls within a cluster
  are `goto`, polled when they go back; other tail calls are `call` and
  `ret`. Functions used as values get dense fids, and a call through a
  closure goes to `anf_applyN`, a binary search on the fid. One nursery
  test at the head of each stretch without a call reserves its words (at
  most 128) and one check covers them; values live across a collection
  go to the shadow roots and come back. The program body's constants are
  allocated once, in the major heap.
- `AnfExtract.v`, `main.ml`, `Makefile`: `./anf-lower FILE.ir` prints the
  module as IR text.
- `anf_lower_rt.c`: `anf_lower_reserve` (the nursery test's slow path)
  and `anf_lower_major` (the constants' major words).
- `driver.c`: makes the arena, runs `anf_main`, writes the value, a
  `list Byte.byte`, to stdout.
- `tests/`: the gate. `Programs.v` holds CertiRocq's standalone programs
  and tests of the Gallina backend's `Asm.v` printer and `Order.v` sort,
  each showing its value as bytes (`Show.v`); `Tap.v` taps their λANF,
  `Ref.v` extracts them to OCaml, and `run.sh` compares the arena's bytes
  with `ocamlopt`'s, with the default nursery and with a 256-word one
  under `FUGC_SCRIBBLE=1 FUGC_VERIFY=1`.

## Running the gate

From the repository's root, with Fil-C's clang at `/tmp/filcc` (or
`FILCC` naming it) and `shell.nix` giving Rocq, CertiRocq with the tap,
OCaml and `CERTIROCQ_SRC`:

```sh
nix build -o /tmp/filcc .#filcc-staging
nix-shell nanofil/anf/lower/shell.nix --run \
  'python3 nanofil/tests/watch.py --label anf-gate --timeout 3000 -- nanofil/anf/lower/tests/run.sh'
```

`ANF_PROGRAMS="demo1 color"` runs some of the programs; the whole gate
takes about four minutes on an orb.

`Eprim_val` and `Eprim` (primitive integers, floats and strings) are
refused until M3.
