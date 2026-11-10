# Trealla with Fil-C

The Fil-C package tracks upstream commit
[`98a821db66715618e358c36c7d7164213c0f6820`](https://github.com/trealla-prolog/trealla/commit/98a821db66715618e358c36c7d7164213c0f6820),
HEAD when checked on November 10, 2026. The previous pins were
`12f4cbd7` (September 5, 2026, one commit after v3.9.40; 630 commits
earlier) and v2.84.14 (November 5, 2025). All were built with the existing
Fil-C toolchain; LLVM and the runtime were unchanged.

```sh
nix build .#pkgsFilc.trealla
./result/bin/tpl
nix build .#checks.x86_64-linux.trealla
```

## Packaging changes

- Adapt nixpkgs' makefile substitutions to `GNUmakefile`.
- Select `READLINE=1` explicitly; the new default is editline.
- Set the installed library search path and install the Prolog source
  library tree, including subdirectories. The hosted build also embeds
  many libraries.
- Refresh the existing FFI handle patch against the new source layout.
- Preserve tabling iterator pointers across backtracking.

The new tabling patch fixes two pointer-to-integer-to-pointer round trips
in `bif_tbl_get_answer_2` and `bif_tbl_wkl_work_3`. Each now stores its
cursor and generation in a pointer-typed member of the existing saved-state
union. Choice-point copies consequently preserve the cursor's capability.
The generation checks that reject invalidated enumerations remain intact.
This is ordinary C and does not require a Fil-C-specific escape hatch.

### November 2026 update

- Both Fil-C patches are redone against the new source. The tabling patch
  now covers a third cursor, and the FFI handle patch covers the new
  `'$dlsym_deref'/3`.
- `trealla-runtime-atom-arity-unify.patch` is dropped: upstream's
  `unify.c` now refuses to unify a run-time atom with a compound of the
  same name.
- `trealla-goal-expansion-share-cells.patch` stays. Unpatched HEAD still
  reads a freed bigint in the runtime check's `bigint_expansion.pl`.
- `trealla-heap-page-mark.patch` is new and fixes wrong answers in
  unpatched HEAD. A clause that builds a term and tail-calls with it
  could have its frame reused and the term cut short when the term began
  a new heap page; `msort(Xs, Ys), merged(Ys, Zs)` then failed for some
  list lengths, which stopped `experiments/regex-nanofil/rx.pl` on the
  pattern `word`. Upstream
  [`ccb10b7d`](https://github.com/trealla-prolog/trealla/commit/ccb10b7db513ed9fc4194c08a458d68d42314b01)
  (October 12) exposed it by allowing more tail calls; the cause is an
  older off-by-one in how a heap mark names its page. The patch
  describes it, the runtime check has the reproduction, and upstream's
  688 tests pass with it. It is not reported upstream yet.
- Upstream added foreign callbacks (`foreign_callback/4`, libffi
  closures) and passes more C pointers through Prolog integers. Those
  paths are not converted to handles and are untested under Fil-C; a
  pointer that travels through an integer loses its capability, so they
  would trap rather than work.
- `(1<<64) /\ \1` now evaluates correctly and `atom_number/2` fails on
  a non-number instead of throwing, two defects nanofil had worked
  around (`nanofil/docs/archive/hosts.md`).

## Validation

Before the cursor patch, the latest revision built successfully but failed
five of 402 upstream tests: `dcg_tabling`, `tabling`, `tabling_incremental`,
`tabling_reconstruct`, and `tabling_subsumption`. Fil-C reported a pointer
with a null capability in the tabling implementation. The other 397 passed.
After the cursor patch, all 402 upstream tests passed in 2 minutes
10 seconds on the development host.

The Nix runtime check exercises all six tabling regression files and five
DCG files, plus CLP(Z), installed-library association maps, exact integer
arithmetic, a tail call whose argument starts a new heap page, and a call
from Prolog into a Fil-C-built shared library through
`use_foreign_module`. It checks both exit status and expected output;
Trealla can report an initialization error while exiting successfully.
Package build-time checks remain disabled in favor of this explicit check.

This is not comprehensive FFI validation. An exploratory call through the
private `$register_function` evaluable-function interface reached a Fil-C
trap in `ffi_prep_cif`; the public `use_foreign_module` predicate interface
passed. That private-interface problem remains outside this refresh.

The full upstream suite can also be run from an extracted source checkout:

```sh
ln -s /absolute/path/to/result/bin/tpl tpl
./tests/run.sh
```

## What is developing upstream

The recent history is predominantly Andrew Davison's work and combines
language/runtime fixes with substantial new facilities. The following are
source-history observations, not a claim that every feature is production
ready:

- **Tabling is new.** Native tabling landed in July 2026. Late August and
  early September added resource restraints, answer subsumption,
  incremental invalidation, shared completed tables, and answer
  reconstruction changes. The
  [phase-two design](https://github.com/trealla-prolog/trealla/blob/12f4cbd7fc2269265e7306775ded2f6410671499/docs/DESIGN-tabling-phase2.md)
  records tests, measurements, and revisions to the design.
- **DCG implementation is changing.** August introduced native translation
  and subsequent refinements. The regression suite compares the native
  translator with a Prolog reference and exercises tabled DCGs.
- **Embedding is expanding.** August added `libtrealla.a` and Janus work;
  the README explicitly labels the Python interface experimental.
  Freestanding ports now cover embedded boards, and the pinned HEAD adds
  Raspberry Pi Ethernet support. These suggest active interest in uses
  beyond an interactive Prolog executable.
- **Core correctness work continues.** Recent commits fix term expansion,
  Logtalk behavior, indexing races, and process/socket portability.
  CLP(Z)'s most recent source update was in July. Passing its focused tests
  is useful evidence, but does not establish the stability of the whole
  constraint solver.

For a compiler experiment, DCGs, structured terms, and explicit worklists
are a reasonable starting point. Tabling deserves dedicated completeness
and error-propagation tests: the pinned
[driver](https://github.com/trealla-prolog/trealla/blob/12f4cbd7fc2269265e7306775ded2f6410671499/library/tabling.pl)
still catches worker exceptions as branch failure and resets incomplete
tables. A caller must not infer that a returned answer set is complete
merely because no exception escaped.
