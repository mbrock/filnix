# Focused repairs after the shared-cancellation campaign

Campaign `3eaf2f72-7c12-4bf2-9934-9646ea9dab4d` finished its original work
with 3,722 built attributes, 6,978 blocked, 1,762 failed, 1,143 evaluation
errors, 159 inconclusive and eight excluded. Its frozen source remains
`f07cf499adf233bb7dd85ea95e1b63f63a89776a`.

## Choosing the next work

Traverse each unsuccessful candidate's recorded dependency graph, stopping at
available derivations. Count each failed derivation once per candidate, and
also count candidates for which it is the only recorded failure. These are
attribute counts (including aliases), not independent programs or predicted
successes. Failure groups overlap.

| Failed dependency | Affected candidates | Sole recorded failure |
| --- | ---: | ---: |
| Rust compiler dependency | 2,325 | 40 |
| dav1d | 2,299 | 1 |
| Cross gfortran | 2,168 | 147 |
| Opus | 1,851 | 10 |
| tpm2-tss | 1,846 | 6 |
| FLAC | 1,815 | 6 |
| mpg123 library | 1,805 | 1 |
| cryptsetup | 1,710 | 4 |
| VMAF | 1,644 | 2 |
| GLU | 1,377 | 133 |

This first pass selects five small shared libraries with concrete packaging or
instruction-compatibility failures. Rust and Fortran dependencies need a separate
scope/build-tool investigation; their fanout does not establish that those
languages can compile to Fil-C.

## Changes and evidence

The recipes live in `ports/media.nix`; local patches remain in `patches/`,
outside the upstream patch extractor's output directory.

- **GLU 9.0.3:** declare its own math-library link dependency. The installed
  consumer verifies projection, inverse projection and polygon tessellation
  callbacks without a display server.
- **dav1d 1.5.1:** use its upstream portable C implementation. NASM emitted
  native-ABI symbols that the Fil-C objects could not link. Six header tests
  pass. A separate installed consumer decodes lossless 8-bit and 10-bit AV1
  fixtures and checks every Y/U/V sample against its generating formula.
  Assembly-comparison tests do not run in this configuration.
- **VMAF 3.0.0:** use its portable implementation instead of native assembly,
  and enable its previously disabled check phase. All 14 tests pass.
- **mpg123 1.32.10:** select its upstream generic C decoder and enable checks.
  All seven tests pass, including decoding and seeking. `libmpg123` inherits
  the change through its override of `mpg123`.
- **FLAC 1.5.0:** spell the CPU probe as `xgetbv` instead of raw `.byte`
  directives. The next failure was the unsupported `vzeroupper` intrinsic;
  omit four explicit register-transition hints at function return under
  `__FILC__`. CPU dispatch and optimized C intrinsics remain enabled.
  All ten upstream test groups pass, including the exhaustive stream suite.

The portable implementations trade assembly acceleration for a working Fil-C
build. They do not bridge into uninstrumented native codec code. No upstream
test assertion was relaxed and no failing test was excluded.

For each of these five packages, comparing recursive derivation inputs with its
original failed recipe found **exactly one new derivation: the package itself**.
The compiler, runtime, libc and all existing input derivations are reused.

```sh
nix build .#legacyPackages.x86_64-linux.pkgsFilc.mesa_glu \
  .#legacyPackages.x86_64-linux.pkgsFilc.dav1d \
  .#legacyPackages.x86_64-linux.pkgsFilc.libvmaf \
  .#legacyPackages.x86_64-linux.pkgsFilc.libmpg123 \
  .#legacyPackages.x86_64-linux.pkgsFilc.flac \
  --no-link --keep-going --max-jobs 4 --cores 7 -L
nix build --impure --file tests/media.nix --no-link -L
```

## Bounded downstream follow-up

The baseline graph identifies **180 candidates** whose complete set of recorded
failures is contained in these five libraries. This includes the libraries
and consumers such as SDL, FLTK, Graphviz, gnuplot, MuPDF and libavif. Replan this
cohort explicitly from the committed repair revision, using batches of at most
64 candidates. Keep the original recipes and evidence in the campaign history;
do not clear the old shared derivations' failure facts or reopen unrelated
failures. Further failures in this cohort are new evidence, not regressions
in the original campaign totals.

The local baseline, selected IDs, old/new derivations, closure comparisons and
full logs are retained in `results/triage-20260915/` in the repairs checkout.
The controller records each submitted selection and its previous recipes.

## Next unresolved lead: Opus

Opus 1.5.2 passes 12 of 14 groups but fails its decoder assertion and encounters
a null mode pointer during the encoder/decoder tests. A separate build with
intrinsics and runtime CPU dispatch disabled reproduces both failures. That
rules out simply selecting the scalar implementation as a repair. Keep its
normal recipe and tests unchanged until the decoder-state failure is reduced
and understood; do not count the diagnostic build as a successful port.
