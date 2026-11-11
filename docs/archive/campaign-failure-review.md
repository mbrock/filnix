# Campaign failure review, October 6, 2026

The latest recording is the 300-root release campaign frozen at
`01e875b67b93089452f3e20e00b7a9341180ed01`. It stopped after 279 attempts:
265 successful, 13 failed, one incomplete (GTK2), and 21 unattempted.
The restarted service serves observations and does not retry builds.

## Observer memory

The kernel recorded a cgroup OOM at 10:59:55 CEST on October 6 and killed the
observer, whose anonymous RSS was about 4 GiB. The native Nix worker was small.
The unit's allowance is 4 GiB, but an unconfigured DuckDB on SWA selects a
99.9 GiB budget and 32 threads from host resources. Dashboard queries repeatedly
joined the full 13,166,583-event journal for per-root metadata. The journal also
kept ART indexes for offsets and `(run,seq)`; a two-million-event measurement
found about 33 MiB of index memory versus 2 MiB of base-table buffers. Indexes
are an additional growth cost, not evidence that indexes alone caused the OOM.

The runner now configures DuckDB before opening with a 1 GiB budget and two
threads. New schema-2 recordings omit the redundant raw event/log indexes;
transactional writer ordering remains enforced. Small entity-table constraints
remain. A temporary per-run overview cache is rebuilt once at startup and
updated in append transactions. Polling no longer joins the raw journal.
Existing schema-1 recordings remain readable without migration.

The budget leaves headroom for allocations outside DuckDB's budget; it is not a
process RSS ceiling. Graph materialization remains per selected run, and very
large individual records still need byte-budgeted paging. See the runner README.

## Infrastructure checks and fixes

- Record/replay/export, exact binary logs, committed output validity,
  shared/failed dependencies and private-store real builds pass.
- Root timeout continues admission; total budget stops it. Worker cancellation
  drains and reaps, with a two-second SIGKILL escalation. Remote build completion
  is independent of observer-client death.
- Abrupt death recovers committed WAL observations without marking an unfinished
  build successful or automatically retrying. Inactive incomplete roots now
  count as incomplete, and their cohort reports `recording-interrupted`.
- A broken worker protocol stops admission. A committed recorder error now
  explains that stop after reopening, even without a `cohort.finished` event.
- Manifest validation rejects empty/duplicate root names and relative drv paths.
  Different names may refer to the same derivation: the current manifest has
  one such alias, which is valid.
- Publication remains outside the recorder loop and reads the owner's HTTP
  feed. All eight publisher tests pass. Both deployed publishers reported
  `pending=0` and `retrying=0` during this review; receipts are not continuous
  verification of remote NAR availability.

The native dataset and nine integration tests pass. The committed memory fixture
uses two million events, 300 roots, and output/progress observations. A separate
13,200,302-event fixture with approximately one million log lines passed for
schema 2 and indexed schema 1; viewer peaks were 442,789,888 and 444,661,760 bytes
(about 424 MiB). This checks reopening and HTTP queries at campaign scale;
it does not claim an end-to-end replay of every original build or payload.

## Package failures

Ten failed roots originate in release-toolchain pthread cancellation: eight from
PipeWire and two from LTTng-UST. The three staging patches and their limits are
reviewed in [the cancellation overview](pthread-cancellation-implementation.md).
Both current x86-64 staging cancellation checks were freshly rebuilt and passed.
The release pin and its runtime semantics remain unchanged.

BusyBox's SHA acceleration assembly lacks SaRCAsm signatures. Its package now
selects portable C SHA1/SHA256 via actual package arguments; the old `use` step
set attributes without changing the configure arguments. The fixed derivation
builds, and the installed SHA1/SHA256 applets produce the expected hashes.

Redis's built-in vectorset and loadable modules export the same entrypoint.
Fil-C function-descriptor interposition made module loading call the wrong
entrypoint. `-Bsymbolic` fixes the focused ACL module suite (16 tests); the package
patch places it in the test-module Makefile because the Tcl runner rebuilds
modules outside stdenv's build flags. No ACL tests are skipped. The full configured
Redis suite passed all 141 test groups, followed by the installed version check.

The remaining Nix utility-test failure happens before tests start, while a global
constructor copies `../alignment.cc` through libc++'s builtin memmove. GDB
confirmed an eight-byte access starting seven bytes into the literal, with an
incorrect eight-byte alignment requirement. Simple string and GoogleTest
reproductions, and the isolated original alignment test source at O2/O3, pass;
the failing whole-program optimization is not reduced yet. No memory
checks were weakened and no utility tests were disabled. Compiler/runtime
changes need the review and regressions required by `AGENTS.md`.

## Delivery

After explicit deployment approval, `/opt/filnix-v2` was switched to the checked
runner (`ddnrfa7dljp92w0xcq8mml43q1dgsbnz-filnix-campaign-next-0.1.0`) and the
service restarted. The closed database and frozen manifest were backed up at
`/var/lib/filnix-v2/archives/before-memory-fix-20261006T135923Z`; the old application
remains GC-rooted for rollback.

The public dashboard and `/api/resources` confirm the 1 GiB/two-thread settings.
Repeated overview/detail reads of the actual recording kept process peak RSS
around 1.1 GiB and cgroup peak around 1.4 GiB, below the unchanged 4 GiB allowance.
The watermark remains 13,166,583 and all root counts are unchanged; the cohort
now reports `recording-interrupted`. Publication paths are unchanged. The service
log confirms serving only without automatic retries. This updates the viewer,
not the unfinished campaign: a later campaign needs a freshly frozen manifest
and an empty recording.
