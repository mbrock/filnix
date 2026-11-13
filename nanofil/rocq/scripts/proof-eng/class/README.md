# Runtime-class spike

This directory contains a scratch-tree converter and measurements, not a proposed
change to the production proofs. The source revision is
`82a091b43c79b394131f60c4921f7139855b1677` on `proof-eng`. Nothing in this experiment
lands on main. The branch is `proof-eng-class`.

## The runtime remains arbitrary

The class stores exactly the data and laws a caller previously supplied through
a module. `convert.py` keeps the original `Runtime` module type and interpreter.
It appends `R.RuntimeClass`, copying all seven data fields and fourteen laws from
the module type. The two derived lemmas, `safepoint_lifetime` and `rooting`, are
proved again outside the class. `results/interface.txt` prints both interfaces.
The namespace `R` keeps statements readable as `R.ready s m`.

`interp_runtime` is a transparent record, not a globally registered instance.
`ClassOf` constructs such a record from any module satisfying `Runtime`.
Generic proofs have a section context ``Context `{rt : R.RuntimeClass}``.
Concrete entry files select `interp_runtime` locally. Runtime-independent
definitions do not acquire an unused class argument.

The converter replaces the runtime module argument with an implicit argument
on each theorem, so each proof is compiled once. Theory namespaces keep their
names. Aliases and nested namespace modules move outside runtime sections,
because Rocq forbids them inside. Non-runtime module parameters remain where a
sealed interface needs them.

The glibc converter is a copy of stage 10, not an edit to the shared pipeline.
It rewrites dependency paths and closes and reopens the runtime section around
exported tactics. Stage 15 and the pipeline overlay are applied afterwards.

Every original theory comment survives byte-for-byte, in order; generation
asserts this. The glibc variant inherits stage 10's rewriting of documentation
paths and removal of wrapper-only comments. This is not a prose modernization.

## The headline audits pass

`AuditClass.v` checks all of the following in one compiled tree:

- The safety theorem is proved without global assumptions and still applies
  to every runtime. Its state type, readiness premise, initial debt, and safety
  conclusion all use that same runtime argument.
- The proof works with either an unknown implementation or the interpreter.
  Both applications print Closed. There is no global interpreter instance for
  inference to choose in a generic proof.
- The audit can still treat every interface member as a separate assumption.
  Applying the theorem to `ClassOf AuditRuntime`, declared against
  the original module type, reports all 21 separate runtime parameters and laws.
- Both `hi_atexit_initialized_entry` and `hi_atexit_never_panics` remain Closed.

The conversion does not weaken the initial resources a caller must supply.
The resource hypothesis still quantifies over every ghost-heap instance and
requires `exists debt : D.HelloDebts w0 ge o`. All link, layout, OS, resource, and
argument antecedents are unchanged. `check-statements.py` compares all three
source statements modulo module paths and explicit interpreter selection.

The full, untruncated statements and outputs are in `results/audit-class.txt`.
`results/headline-statements.txt` gives the original and converted source
statements, including their surrounding runtime binders.

The assumption listing becomes less selective, but a dependency query recovers
the fields the proof uses. `Print Assumptions` reports every field of the supplied
record. `Dependencies.v` runs `Print All Dependencies hello_never_panics`.
The query finds these 12 projections, including both operations and laws:

```text
state, ready, alloc, fresh_allocation, address_space, ready_kept,
at_safepoint, safepoint, collector_live, non_moving, aux_round_trip,
safepoint_ready
```

The filtered output is in `results/hello-runtime-dependencies.txt`. No
opaque-field rebuild or split into smaller classes was needed.
The original functor audit and the independently built abstract-flat audit both
report exactly this same set of 12 names. `results/audit-summary.txt` records the
set comparison. The general dependency query reports no interpreter constants.

## Sections have observable costs

Closing a section resets explicit `Arguments` declarations. The converter
re-emits ten declarations. Each was checked with `About` against the functor
tree, including argument order, names, scopes, and implicit status:

| Namespace | Checked declarations | Result |
| --- | --- | --- |
| `ExternalMachine` | `Running`, `Stopped`, `step`, `run` | Existing arguments unchanged; `rt` is additionally implicit. |
| `ExternalMachine` | `admissible` | Unchanged; it does not depend on the runtime. |
| `Language` | `mkLstate`, `ls_mem`, `ls_rt`, `ls_fuel`, `ls_world` | Existing arguments unchanged; `rt` is additionally implicit. |

The evidence is in `results/arguments-class.txt` and
`results/arguments-functor.txt`. No other `Arguments` declarations are re-emitted.

Exported Ltac definitions disappear at section close; putting `Global Ltac`
inside the section is rejected. Moving those definitions outside the section
fixes their clients. Modules, includes, and declared modules also cannot occur
inside sections. Real nested namespaces must move as a whole. Ordinary notation
lifetimes were not separately probed.

Iris language canonical structures compile, with redundant-projection warnings.
Public instances need re-registration after section close: `closed_irisGS`,
`no_world_stable`, and `os_wi_stable`. No universe inconsistency was observed.
Keeping projections behind `R` avoids field-name collisions; the converter also
avoids a section binder named `rt` when a theorem already binds that name.

`SafepointStable` needs a mode that delays search until the world interpretation
is known. The class version has an additional runtime argument, so its mode is
`+ + !`, not the fixed-runtime tree's `+ !`.
In the controlled test, the only differing source was `theories/logic/Logic.v`.
Without the mode, `LibioDoAllocBase.v` fails at the `iApply` on generated line
269; with it, the file passes. `StrlenLogic.v` and the other rebuilt prerequisites
pass with either setting. The log is `results/mode-off.log`, and
`test-mode.sh` reproduces the test. The mode-off experiment covers those two
targets and their prerequisites, not the whole 269-file union.

There is one proof-body residue: in `LibcCallFixtures.malloc_resource_calls`,
`all: try solve [vm_compute; intuition congruence]` becomes
`all: try solve [cbn; intuition congruence | lia]`. The original tactic exceeded
four minutes and reached roughly 17 GB in the class tree; a separate 90-second
watchdog run also timed out. The replacement compiled the whole file in 17.0 s.
The earlier suspicion about `HelloGlibcProgName` was wrong: it compiled in 7.0 s,
and its `End RuntimeSection` took 0.002 s. That single observation does not bound
the cost of closing every section.

Concrete allocator numerals require explicit runtime specialization before Rocq
can check them against `R.state`. The converter supplies it for concrete safety
calls and for `InterpStrings.c_string_length` in `LibcCallFixtures`.

## Reproduce the experiment

Run from the repository root, at the pinned source revision:

```sh
source nanofil/rocq/scripts/proof-eng/env.sh
scratch=$PWD/.amp/in/orb-backup/class
python3 nanofil/rocq/scripts/proof-eng/class/generate.py "$scratch"
cp -a nanofil/rocq/glibc "$scratch/functor"
nanofil/rocq/scripts/proof-eng/apply.sh nanofil/rocq/glibc "$scratch/flat"
rocq makefile -R "$scratch/theories" Nanofil -R "$scratch/glibc" Glibc \
  $(find "$scratch/theories" "$scratch/glibc" -name '*.v') -o ClassMakefile
make -f ClassMakefile -j4 "$scratch/glibc/hello/HelloGlibcJoin.vo" \
  "$scratch/glibc/hi_atexit/HiAtexitSafe.vo" \
  "$scratch/glibc/stdio/PrintfBufferXsputnHeapSwitch.vo"
bash nanofil/rocq/scripts/proof-eng/class/measure.sh
python3 nanofil/rocq/scripts/proof-eng/class/summarize.py "$scratch"
```

`measure.py` recompiles every file in the requested closure, even if an object
already exists. Layouts run serially, each at fanout four and
`OCAMLRUNPARAM=o=200`, with no competing compilation. Each CSV retains wall time,
CPU time, maximum RSS, object bytes, and exit status for every file. The measured
targets include both headlines, `PrintfBufferXsputnHeapSwitch`, `LibioPutsNl`,
and every file under `string/`. The summaries distinguish whole closures from
the intersection of filenames, since flattening introduces `Fix.v` and `CodePrelude.v`.
These are single runs, not confidence intervals. Theory compilation is outside
the glibc measurements; the original theories come from Nix, and the class
theories are built locally.

## The class tree saves space but makes Hello slower

All measured files passed. The table compares identical filenames, excluding
the two files introduced by flattening. Seconds are sums of per-file wall times,
not elapsed parallel build times. Object sizes are bytes.

| Closure | Files | Functor seconds / bytes | Interpreter-flat seconds / bytes | Class seconds / bytes |
| --- | ---: | ---: | ---: | ---: |
| Hello | 103 | 843.812 / 388,237,116 | 664.739 / 110,288,443 | 874.892 / 111,243,948 |
| Hi | 207 | 1,811.741 / 645,223,006 | 1,123.601 / 37,767,580 | 1,161.806 / 37,889,614 |
| Xsputn | 39 | 292.554 / 93,325,642 | 237.003 / 8,598,165 | 239.531 / 8,626,149 |
| Puts | 33 | 202.868 / 53,630,795 | 174.661 / 6,805,506 | 178.998 / 6,846,448 |
| Measured union | 267 | 2,408.493 / 963,059,792 | 1,582.005 / 137,281,501 | 1,818.213 / 138,375,024 |

Including the introduced files, the flat and class runs each compile 269 files.
Their sums are 1,583.649 s and 1,819.905 s. The corresponding elapsed parallel
build times are 680.978 s for functors, 411.291 s for interpreter-flat, and
484.696 s for class. Maximum per-process RSS is respectively 4,829,844,
2,177,940, and 4,605,680 KiB. This does not measure aggregate concurrent RSS.
The machine has 16 vCPUs and 32 GB RAM. Raw machine information is beside each
CSV. All 116 original Nix model source files were checked byte-for-byte against
the source checkout; none differs.

The class overhead is concentrated in Hello. On the matched files it is 3.7%
slower than the functor tree and 31.6% slower than interpreter-flat. The Hi and
Xsputn closures are respectively 3.4% and 1.1% slower than interpreter-flat.
The entire matched class union is 24.5% faster than functors but 14.9% slower
than interpreter-flat, with essentially the same object-size benefit as flat.

The final files make that distinction particularly clear:

| File | Functor seconds / bytes | Interpreter-flat seconds / bytes | Class seconds / bytes |
| --- | ---: | ---: | ---: |
| `hello/HelloGlibcJoin.v` | 12.154 / 6,506,490 | 6.268 / 515,155 | 23.882 / 502,312 |
| `hi_atexit/HiAtexitSafe.v` | 19.334 / 18,777 | 2.154 / 18,854 | 2.091 / 18,683 |
| `stdio/PrintfBufferXsputnHeapSwitch.v` | 21.594 / 19,631,334 | 7.389 / 126,797 | 6.987 / 127,045 |

These measurements include the committed stdio chain at the pinned revision,
not the unpublished work-in-progress file with the three reported slow module
lines. `HelloGlibcLibsSys`, `HelloGlibcXmalloc`, `HelloGlibcMainLibs`, and
`HelloGlibcLibsExit` each add roughly 18–20 s compared with interpreter-flat.
This experiment does not attribute that difference to individual sentences.

## The remaining theory files are not certified by this spike

The generator copies 116 theory files and changes 78. The required closures
compile 64 theory files. The other 52 are listed in
`results/unbuilt-theories.txt`; they include soundness, programs, and additional
Hello contracts. Their generated output exists, but it was not compiled.
That distinction matters: the script having rewritten a file is not evidence
that its proof works.

Those clients cannot simply remain unchanged against the converted core. They
apply modules such as `Run R`, which are no longer functors. They would need the
same conversion of binders and aliases, followed by compilation and any fixes
for section lifetimes, implicit arguments, concrete runtime selection, or
computation. The original files can continue working against a separately kept
original theory tree, as the baseline here does. No compatibility layer was
built or tested.

The glibc generator changes 365 of 376 original files and adds two files. Only
the 269-file measured closure union is certified here, not the whole 378-file
generated tree. The script emits 97 theory runtime sections and 371 glibc
runtime sections, including reopened sections around tactics. It emits 34
theory and 79 glibc local interpreter instances. There are three explicit
interpreter arguments: one in `LibcCallFixtures` and two in `HiAtexitSafe`.
All changes are generated; no scratch proof was maintained by hand. The one
proof-body replacement, ten repeated `Arguments`, instance exports, and hint
mode are the deliberate residue rules described above.

The experiment does not run the full theory suite, full glibc gate, strict
reprint, docs/site build, extraction, or runtime execution tests. It does not
measure a clean theory build in all three layouts or claim a statistical bound
from these single measurements.

## Prefer two flat trees for this cutover

The typeclass design preserves both kinds of theorem, but its measured advantage
over two flat trees is small. I recommend the two-tree fallback for this cutover,
not adoption of this converter. The class design is a viable alternative, not a
failed proof experiment; its migration and validation costs are the reason for
this recommendation.

`measure-abstract.sh` builds the abstract-flat Hello closure separately, with
the same machine, fanout, source revision, compiler, and GC setting. It passes
all 105 files: 646.772 s summed wall time, 110,362,092 object bytes, and
226.983 s elapsed time. Its final Hello theorem reports the expected 12
assumptions. This is a measurement, not a proxy using interpreter timings.

| Layout for both headlines | Compilations | Summed seconds | Object bytes |
| --- | ---: | ---: | ---: |
| Abstract-flat Hello plus interpreter-flat Hi | 314 | 1,772.017 | 148,322,369 |
| One class tree, union of both closures | 258 | 1,725.565 | 135,858,284 |

The class tree avoids compiling 56 common files twice, but saves only 2.6% of
summed compile time and 8.4% of object bytes in these runs. Those sums count each
file once per required layout; they do not add parallel elapsed times from
different dependency graphs. The class tree also has higher peak process RSS
and requires changes to the theory API, public instances, tactics, implicit
arguments, and one computation-heavy proof. There are still 52 unbuilt theory
files. A single-run 2.6% difference does not establish a dependable speed gain.

The fallback retains the selective 12-entry assumption audit unchanged and
does not require a theory migration. Its cost is duplicate compilation and
storage of the shared closure. It also fixes a runtime at the build boundary:
it does not provide the class theorem's explicit runtime argument within one
compiled library. The choice to accept that build boundary belongs to mbrock.
