# λANF 32-bit Arena Runtime (`nanofil/anf/`)

Milestone M1 of [lambda-anf.md](../docs/lambda-anf.md): the single-capability
32-bit `w` arena, zero-barrier Cheney minor collector, inline shadow root
stack, packed byte blocks, and canonical 31-bit / multi-limb `Z` integers,
compiled as a verified-clean Fil-C module by both Prolog `nanofil` and the
extracted Gallina backend (`Compile.compile_allocated`).

## Files

- `anf_arena.h` — value tagging (`(val << 1) | 1` immediates, `idx << 1`
  boxed words), block header layout `(arity << 10) | (st << 8) | ord`
  (`ANF_ST_SCAN = 0`, `ANF_ST_BYTES = 1`, `ANF_ST_BIGINT = 2`, forwarding
  marker `0xFFFFFFFFU`), `struct anf_state` with inline `roots[]` at `st + 1`,
  and C/IR entry declarations.
- `anf_arena.c` — `anf_arena_init` / `anf_arena_reset` / `anf_arena_destroy`
  over `zsys_mmap` (`MAP_NORESERVE`) and `zsys_madvise` (`MADV_DONTNEED`),
  `anf_minor_gc`, `anf_alloc_words`, shadow root helpers, `ANF_ST_BYTES`
  helpers, canonical 31-bit / base-`2^32` bigint `Z` operations, and `anf_oom`
  (`__builtin_alloca((1ULL << 48) - 1)`, which lowers to a core `alloc(16)`
  refused with `OutOfMemory`).
- `test_arena.c` — capability bounds & `FILC_OBJECT_FLAG_MMAP` check on the
  full `8 GiB + 4 KiB` arena, differential `Z` suite across `2^30`, `2^31`,
  `2^32`, `2^63`, `2^64` and `2^192`, adversarial no-scan packed byte tests,
  10,000-step randomized algebraic tree-rewrite stress in a 256-word nursery
  under `FUGC_SCRIBBLE=1 FUGC_VERIFY=1`, and `OutOfMemory` boundary refusal
  tests.
- `probe_mmap.c` — `zsys_mmap` (`MAP_NORESERVE`) reservation sweep (`512 MiB`
  to `4 TiB`) and `8 GiB + 4 KiB` RSS lifecycle / `zsys_madvise`
  (`MADV_DONTNEED`) probe.
- `run.sh` — builds `anf_arena.c` through `nanofil-backend` (`compile`,
  `compile-promoted`, `compile-nfb`, `compile-allocated`) and `nanofil -O cc`,
  verifies byte-identity, and runs `test_arena` and `probe_mmap`.

## Running

```sh
FILCC=/tmp/filcc/bin/clang SWIPL=/tmp/swipl/bin/swipl \
  NANOFIL_BACKEND=/tmp/nanofil-backend/bin/nanofil-backend \
  nanofil/anf/run.sh
```
