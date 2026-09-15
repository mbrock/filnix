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

The cohort was submitted from repair commit
`1c0dc8dce048ee9cb5bdd6f5ce1c96bc22964b31` in these recorded plans:

| Plan | Candidates |
| --- | ---: |
| `938a20f1-7084-48cf-a9ab-ca59169cea4f` | 64 |
| `d57f576a-96e5-4f6e-85cc-93fbf7e8e65b` | 64 |
| `508c54ac-1a75-40f2-919a-3de7e1ccbcd4` | 52 |

The first two plans evaluated every candidate successfully. Follow-up build
batches `b1784834-ec79-48fb-b913-1922208f993a` and
`6f31e916-8266-42bc-afd6-38dd9d5a2ec7` began while the last plan evaluated.
Their eventual package results belong to the live campaign, not this initial
submission snapshot. Both cache publishers remain enabled.

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

## Second pass: consumers and test infrastructure

The first bounded cohort exposed further independent failures after the shared
libraries built. The second pass keeps the compiler, runtime and libc unchanged.

### FLTK 1.4

Declare libm on both CMake library targets. `tests/fltk.nix` then builds an
installed consumer against each of the static and shared variants. It checks
nontrivial rotations and every pixel of a scaled RGB image, without a display
server. Both consumers pass. Since this Nixpkgs configuration enables FLTK's
Cairo extension, the consumers link its companion Cairo library explicitly
(the same choice as `fltk-config --use-cairo`). This is build and API evidence;
it is not an interactive GUI test or FLTK's disabled example suite.

### Coin3D

The math dependency also belongs on Coin's exported target. Enabling its
previously unrun `CoinTests` exposed an initialization failure: the `realTime`
field is a separate allocation, but `SoFieldData` reconstructs its address by
adding an integer offset to its owner. That retains the owner's capability,
which does not permit accessing the separately allocated field.

`coin-external-fields.patch` preserves the actual field pointer and owner for
separately allocated fields. Embedded fields retain their original offset
representation. The retained pointer is used only for that owning instance;
this does not grant access to unrelated allocations or change how metadata is
interpreted for another instance.

Boost.Test also needs its portable execution monitor: framework initialization
installs fault-signal handlers before it parses runtime options, and Fil-C
rejects these handlers and alternate signal stacks. The local test entry point
loads Boost's configuration and clears `BOOST_HAS_SIGACTION` for Fil-C only.
All test cases, assertions and C++ exception handling remain enabled; a runtime
trap still fails the process instead of being recovered as a signal. The full
`CoinTests` suite now passes (2.63 seconds).

### TPM2-TSS

The original check phase could not link because GNU ld `--wrap=write` (and
similar options) intercepted native calls from `libpizlo`, while the test's
mock functions used instrumented Fil-C symbols. The package-local compiler
adapter in `toolchain/test-wrap.nix` redirects only the instrumented symbols.
It renames object-file `__wrap`/`__real` symbols before linking; it does not
replace or rebuild the shared compiler. It supports the separate compilation
and `--wrap=NAME` link options used by this test suite.

`tests/link-wrap.nix` verifies both wrapped calls and calls through `__real`
for `write` and `calloc`, then reads back the pipe data and checks the allocated
bytes. Native runtime I/O continues to link normally.

This let all 267 upstream test programs run: initially 168 passed, five skipped
and 94 failed. Inspection found an actual use-after-free in the FAPI test
harness: `init_fapi` calls `putenv(config_env)` and then frees `config_env`.
`putenv` retains that pointer. The local patch uses `setenv`, which copies the
value. The full rerun improves to **242 passed, 11 skipped, 14 failed**. Every
remaining failure is in a unit-test program; the additional skips are upstream
unsupported-TPM-feature cases reached after initialization was repaired. No
integration assertions or unit tests are disabled. This is still a failing
package build and is not submitted as a successful campaign unblock.

There is also a distinct cmocka pointer-mocking problem: the test suite passes
pointers through `LargestIntegralType` values, and several returned mock
pointers reach the consumer without capabilities. Examples include
`tctildr`, `tctildr-dl` and the mocked TCTI transport tests. This remains a
separate porting task, not evidence that the underlying TPM operation failed.
Two other unit programs (`fapi-io` and `fapi-helpers`) exhaust mock expectations;
the remaining work is not uniformly a pointer-conversion fix.

### Opus: retained diagnostic evidence

The normal Opus recipe still fails and is unchanged. A diagnostic library plus
the upstream `test_opus_decode.c`, compiled as a separate unoptimized caller,
reproduces decoder-state corruption. Raising `FUGC_MIN_THRESHOLD` to 1 GiB
moves the failure later, immediately after the first logged collection.
Disabling intrinsics, selecting stop-the-world collection, or disabling the
header's pointer-check macro did not repair it. Optimized caller builds passed
the initial section in short probes; that is not a full-suite success and is
not being used as a workaround.

A native GDB hardware watchpoint on the decoder's `channels` field catches the
write that changes it from one to zero. The stack is:

```
libyolocimpl memory clearing
finish_allocate_large
filc_allocate
opus_decode
test_decoder_code0 (invalid-length input)
```

The decoder remains referenced by the test when another allocation is being
initialized over its storage. This strongly implicates allocation/lifetime
tracking, but the source-level root cause is not yet established. Smaller
create/copy/collect/allocate probes pass, so the full caller's shape still
matters. Preserve this as a compiler/runtime investigation rather than
silencing the test or triggering a campaign-wide compiler rebuild.

The precise commands, generated diagnostic variants, full logs and watchpoint
trace remain under `results/triage-20260915/round-2/` in the repairs checkout.
The original upstream tests are in the pinned Opus 1.5.2 source; the ordinary
`libopus` build is also a reproducer for its failing decoder/encoder checks.

For Coin and FLTK, recursive derivation comparisons each find exactly one new
build: the library itself. Their compiler, libc and dependency derivations are
identical to the previous recipes. The intended second retry cohort is the
inactive candidates whose complete recorded failure set is contained in these
two repaired libraries; unresolved TPM2 and Opus consumers remain excluded.

Selected attributes: `coin3d`, `fltk14`.

Plan `4224c45b-9424-4bd4-a58e-5ec0aac0ae6b` replanned these two attributes
from repair commit `f3846d414f2ed3ef52552f81253752c506bc3cb7` and finished
successfully. Both are now recorded as built in the live campaign. The graph
found no additional inactive consumers blocked solely by these two libraries;
other recorded blockers must be repaired before retrying those consumers.

After the first cohort and this retry settled, the 180 selected attributes stood
at **37 built, 56 failed, 84 blocked and three inconclusive**. These are package
attribute counts, including aliases, not independent projects. There were no
remaining active attempts at this snapshot (2026-09-15 20:18 UTC). The new
failures now supply the next bounded repair targets.
