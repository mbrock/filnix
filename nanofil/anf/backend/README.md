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

All 159 runs (53 fixtures, three commands) print what `nanofil-backend`
prints, with both nurseries. The table gives the times on the two large
inputs of [lambda-anf.md](../../docs/lambda-anf.md): the best of 15
interleaved runs for rx.ir and the median of two interleaved runs for
lvm.ir. Both builds print the same assembly.

| input | command | arena | ocamlopt | ratio |
| --- | --- | ---: | ---: | ---: |
| rx.ir (367 KB) | compile | 0.75 s | 0.23 s | 3.3× |
| rx.ir | compile-allocated | 0.95 s | 0.29 s | 3.3× |
| lvm.ir (4.4 MB) | compile | 13.7 s | 3.4 s | 4.0× |
| lvm.ir | compile-allocated | 8.3 s | 2.6 s | 3.2× |

Times on this orb vary by about 10% from run to run. The arena peaks at
89 MB on rx.ir and 422 MB on lvm.ir, against 57 MB and 279 MB. Without
the simplification, the tables, the calling convention and the closure
facts of `AnfLower.v`, the same runs took 2.2 s, 2.9 s, 43.8 s and
26.8 s. M3 as first pushed (3a14460) took 0.90 s, 1.22 s, 15.4 s and
11.0 s in the same runs. Since then, calls between lowered functions
have become cheaper:

- `AnfLower.v` returns a lowered function's value and the young index
  in two registers instead of one packed word. It finds a block from its
  word with one shift instead of two, and it builds the frame of shadow
  roots only in a function that spills to it. Its arena checks ask for
  alignment 1, so the backend emits no alignment test.
- `Regs.v` gives each local function a private entry for the module's
  direct calls, which takes two more words in registers. A function that
  calls nothing links no Fil-C frame. The entry stores the catching
  origin once, where every call used to store it, and it does not zero
  the roots that the incoming arguments fill. A frame holds slots only
  for what the function spills, so the mean frame is 159 bytes instead
  of 483.
- `AnfLower.v` inlines `orb`, `andb` and the like, so `existsb` and
  `forallb` stop at the first element that decides them, as in OCaml.
  Before, they walked every list to its end. A PCRE2 function of 521
  blocks went from 7.1 s to 2.7 s in compile-allocated, against
  0.57 s in the OCaml build.

Both builds need a stack that grows with the input, and run.sh gives
them 1 GB. On lvm.ir the arena build needs 9.9 MiB. It needed 15.0 MiB
with the frames of 4a2ef2a, and 12.1 MiB while `existsb` still walked
whole lists ([../lower](../lower/README.md) explains why it did). At
the deepest point, 44,101 of its 44,111 frames now belong to the body
of `app`, at 208 bytes a frame. `app` and Order.v's `merge_steps`
cons after their recursive calls in both builds.

Where the rest goes, on rx.ir: 86% of the time is in the lowered
functions, 4% in the string primitives, 1.5% in the collector. The
hottest functions are small and called very often (the atom case of
`term_eqb`, `Z_as_OT.compare`, `ZMap`'s `bal`, `find` and `create`,
`gt_le_dec`).

Calls, prologues and epilogues take about 23% of all the time. A call
still pays for the stack check, up to five callee-saved registers and
the Fil-C frame. It also passes the nursery's end and the arguments on
the stack, because the arena and the state take the four argument
registers of the fast convention. Bounds checks take another 11%, spills
12% and arena address arithmetic 9%. The spills come from register
pressure: the arena, the state, the young index, the roots' top and the
nursery's end are live through every function and compete for the seven
register homes. Inlining every function of
ten nodes or fewer, with join points for the rest of the caller, made
rx.ir only 5% faster, made the IR 37% bigger and the frames of deep
recursions bigger (the rec_clos2 program of [../lower](../lower/README.md)
took 1.8 times as long), so
`AnfLower.v` does not do it.
