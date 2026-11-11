# λANF to nanofil IR (`nanofil/anf/lower/`)

Milestones M2 and M3 of [lambda-anf.md](../../docs/lambda-anf.md):
CertiRocq's core λANF, lowered to checked nanofil IR over the 32-bit `w`
arena of [nanofil/anf](../), judged by the proved validator
(`ValidFast.valid_fast`) and compiled by `nanofil-backend
compile-allocated`. The stdlib's numbers, characters and strings are
represented as integers, codes and bytes, and the Gallina backend
itself goes through it ([../backend](../backend/README.md)).

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

- `AnfLower.v`: the lowering, in Gallina. First it simplifies:
  functions that only build constructors and project fields (eight at
  most) before they return or tail-call, which are CertiRocq's closure
  builders and uncurry wrappers, are inlined four deep; projections and
  cases of a known constructor are folded; and the constructors and
  functions no one reads are dropped. So a curried call is one direct
  call. CertiRocq passes the global functions around as closures in
  environments. The closures' and environments' tags are the anonymous
  ones of the tap, which only the program builds, so when every record
  of a tag holds the same function, or a closure of it, in a field, a
  projection of that field is known and a call through it is a direct
  call (in the backend, 816 calls through a table are left of 3,039).
  Join continuations and loops (a hoisted function never used as a
  value and never called but in tail position, all of whose callers
  are in one cluster) become blocks with phis of their cluster's IR
  function; tail calls within a cluster are `goto`, polled when they go
  back; other tail calls are `call` and `ret`. Functions used as values
  get fids, dense within each arity, and a call through a closure loads
  the function from the table of its arity (`anf_fnsN`) and calls it
  through the pointer. A lowered function takes the arena,
  the state, the young index, the roots' top and the nursery's end,
  and returns its value with the young index above it in one 64-bit
  word, so a call between lowered functions reads and writes nothing of
  the state; only a call that may collect (`anf_lower_reserve`, a
  primitive that allocates) stores the young index and the roots' top.
  One nursery test at the head of each stretch without a call reserves
  its words (at most 128) and one check covers them; values live across
  a call go to the caller's shadow-root frame and come back. `nat`,
  `positive`, `N` and `Z` are 31-bit immediates or bigint blocks,
  `ascii` its code and `string` a block of bytes, or a slice of one
  past 64 bytes, so that matching a string byte by byte does not copy
  it. `String.eqb` is decided inline when the two words suffice.
  Constants are folded into a pool that the exported `anf_main` copies
  to the major heap; it and `anf_applyN` keep M2's C signatures.
- `Prims.v`: the stdlib's constants (`Z.add`, `Nat.eqb`,
  `String.append`, ...) that CertiRocq leaves as primitives, each named
  for a target of `AnfLower.v`'s `prim_table`.
- `anf_prims.c`: the targets that are calls: bigint arithmetic, which
  never collects, and the string and list makers, which may.
- `AnfExtract.v`, `main.ml`, `Makefile`: `./anf-lower FILE.ir` prints the
  module as IR text.
- `anf_lower_rt.c`: `anf_lower_reserve` (the nursery test's slow path)
  and `anf_lower_pool` (the constants' pool).
- `driver.c`: makes the arena, runs `anf_main`, writes the value, a
  `list Byte.byte`, to stdout.
- `tests/`: the gate. `Programs.v` holds CertiRocq's standalone programs
  and tests of the Gallina backend's `Asm.v` printer and `Order.v` sort,
  each showing its value as bytes (`Show.v`); `Tap.v` taps their λANF,
  `Ref.v` extracts them to OCaml, and `run.sh` compares the arena's bytes
  with `ocamlopt`'s, with the default nursery and with a 256-word one
  under `FUGC_SCRIBBLE=1 FUGC_VERIFY=1`. The `selftest` program holds
  the primitives to `vm_compute` on values across 2^30, 2^31, 2^32 and
  2^64.

## Running the gate

As a Nix check, run only when asked (it builds CertiRocq, which is not
in the binary cache, so no workflow and no default
`scripts/nanofil-checks` run builds it):

```sh
nix build -L .#checks.x86_64-linux.nanofil-anf-lower
```

Or by hand, from the repository's root, with Fil-C's clang at `/tmp/filcc` (or
`FILCC` naming it) and `shell.nix` giving Rocq, CertiRocq with the tap,
OCaml and `CERTIROCQ_SRC`:

```sh
nix build -o /tmp/filcc .#filcc-staging
nix-shell nanofil/anf/lower/shell.nix --run \
  'python3 nanofil/tests/watch.py --label anf-gate --timeout 3000 -- nanofil/anf/lower/tests/run.sh'
```

`ANF_PROGRAMS="demo1 color"` runs some of the programs; the whole gate
takes about 70 seconds on an orb once CertiRocq is built.

`Eprim` is lowered for the targets of `prim_table`; `Eprim_val`
(primitive integers, floats and strings) is refused.
