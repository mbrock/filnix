# M0 benchmark: 32-bit `w` arena on Nanofil IR

Hand-lowered checked Nanofil IR kernels (`kernels.ir`) for M0 of
[docs/lambda-anf.md](../../docs/lambda-anf.md), validated by
`ValidFast.valid_fast` and compiled by `nanofil-backend compile-allocated`
(`Regs.v`), measured against `ocamlopt -O2`, `filcc -O2` over the same C
arena, CertiRocq-style `-DVERIFFI` `void *` nurseries, and per-node Fil-C
heap objects collected by FUGC.

## Workloads (`scale = 3` default)

- **`list_sum`**: 6,000 rounds building a 4,096-element `Cons` list
  (24.58M `Cons` allocations through a 1 MiB nursery, ~281 Cheney minor
  GCs) while keeping one 4,096-element list promoted in `major`, summing
  both on every round (`49.2M` tail-loop iterations).
- **`term_eqb`**: 600 rounds building ternary `Nanofil.Term`-shaped ASTs
  of depth 8 (19,681 blocks per tree = 11.83M blocks, ~120 minor GCs
  mid-construction across `roots[]` spills) and running structural
  equality (`11.81M` recursive calls, flipping the final rightmost leaf
  on odd rounds).
- **`avl`**: 300 rounds inserting 2,048 LCG keys into a persistent
  `FMapAVL`-style height-2 balanced tree (~7.2M 24-byte `Node`
  allocations, ~150 minor GCs mid-insertion) followed by 5,120 lookups
  per round.

## Running

```sh
python3 nanofil/tests/watch.py --label arena-m0 -- python3 nanofil/bench/arena/run.py
```

`run.py` first runs `nanofil/tests/difftest.sh` on `kernels.ir` with a
64-word nursery so `interp.pl` (`Semantics.v`) and native Fil-C verify
every Cheney evacuation path, then stresses a 1,024-word nursery under
`FUGC_SCRIBBLE=1 FUGC_VERIFY=1` (47,434 minor GCs), and finally runs
interleaved CPU-pinned timing trials across all seven modes.
