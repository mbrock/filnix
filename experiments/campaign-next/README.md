# Campaign, again

A C++/NXT campaign service and the canonical viewer at <https://nix.swa.sh/>.
It queues and runs every survey-style build filnix does: port campaigns, the
nanofil survey, benchmarks, lists of flake outputs. Its model, admin CLI and
deployment are in [docs/campaign-service.md](../../docs/campaign-service.md);
this file describes the recording and viewer underneath.
The former Python coordinator and dashboard are retired on SWA; their data
remains available for historical analysis. This application builds through
the Nix C++ API, records its observations
in DuckDB, presents a live dependency-graph viewer, and exports Parquet archives.
There is no Python application or web server; Python drives integration tests.

## Try it

From the Filnix repository root:

```sh
nix build path:./experiments/campaign-next --out-link result-campaign-next
nix flake check path:./experiments/campaign-next

result-campaign-next/bin/filnix-campaign watch /nix/store/…-example.drv campaign.duckdb --port 8080
```

`watch` really requests a build. It defaults to the daemon store; `--store URI`
selects another store. Nix's configured jobs, cores, substituters, and remote
builders are respected rather than replaced with a second scheduler. The viewer
listens on IPv4 loopback only. Use an SSH tunnel to view it from another machine.
There are no HTTP build, cancel, or filesystem-mutation endpoints.

After the build finishes, the viewer stays up until SIGINT/SIGTERM. A signal
during the build requests cancellation, drains the recording, and shuts down.
The final summary is JSON on stdout; stderr carries startup/error diagnostics,
not a second copy of every build log. Exit status follows the build worker:
0 success, 1 package failure, 2 worker/API/recorder error, or 128 + signal.

The other commands are:

```sh
filnix-campaign record DRV campaign.duckdb [--store URI]
filnix-campaign service STATE-DIRECTORY [--port 8080] [--socket PATH]
filnix-campaign serve campaign.duckdb [--port 8080]
filnix-campaign inspect campaign.duckdb [--run ID]
filnix-campaign replay campaign.duckdb [--run ID] [--speed 10] [--json]
filnix-campaign export campaign.duckdb archive-directory
```

`record` has no HTTP server. Multiple recordings can share one database over
successive invocations; each has a fresh random identity. Inspect/replay select
the latest run unless given an ID. Replay defaults to 1×; speed 0 is unpaced.
Export includes all recorded runs, not just the latest one, and refuses an
existing destination. **Stop the database-owning server before invoking these
offline commands.** This is a single-process DuckDB owner, not a multi-process
database service. Offline commands do not append campaign events, but opening
the database permits DuckDB to recover its WAL and checkpoint normally.

For development:

```sh
nix develop path:./experiments/campaign-next
meson setup .amp/in/campaign-next-build experiments/campaign-next
meson compile -C .amp/in/campaign-next-build
meson test -C .amp/in/campaign-next-build --print-errorlogs
CAMPAIGN_STATIC_DIR="$PWD/experiments/campaign-next/static" \
  .amp/in/campaign-next-build/filnix-campaign serve campaign.duckdb
```

The subflake pins NXT's blocking pool and upstream Nix 2.34.8 independently of
the main toolchain. This is native C++23 on x86_64 Linux, not a Fil-C build. It
does not install or replace the host daemon. Checks run real builds in disposable
local stores with remote hooks disabled **in test configuration**, not in the
worker. A cached Fil-C Bash request has also been verified against SWA's actual
Determinate daemon. A daemon-store smoke request also built successfully on the configured igloo remote builder before the full port campaign launch.

## Bounded world campaign and deployment

`world.nix` defaults to `scope = "expected"`: CI/distribution leaders followed
by the explicit compatibility list in `ports/expected.nix`. Selected evaluation
failures block freezing, rather than silently shrinking the obligation. See
[selection policy](../../docs/campaigns.md) and run
`python3 tests/campaign-manifest.py` from the repository root to test freezing.

`scope = "world"` uses `shells/world-packages.nix`, the 82-root shell/VM
composition: userland, libraries, GTK/Wayland, runtimes and applications. It
remains separate from the expected compatibility contract.

`scope = "ports"` is exploratory: the union of world roots and active
`ports.nix` declarations. Evaluation failures remain in `excluded`, with known
broken reasons where available; exclusions never count as successes. Manifest
counts vary with the frozen revision. The runner accepts up to 1024 roots, retaining all
cohort summaries while the table renders 100 rows per page.

`service` runs campaigns: frozen manifests of `{name, drv, tags, requires}`
roots with a policy, queued and controlled over a Unix socket by
`campaignctl` (installed beside it). Each root admission is an attempt and a
fresh journal run in that campaign's own recording; the catalog keeps every
attempt's outcome, times, machine and first error. Nix still schedules each
root's complete dependency graph. Package failures and per-root timeouts do
not prevent later roots; a campaign's budget stops admission. Recorder
errors pause the campaign rather than pretending a root was observed
correctly. These are client-observation/build budgets, not a guarantee that a
daemon build shared with another client has stopped.

Intent events retain the campaign, root index, attempt, policy and load.
`run.limit-reached` distinguishes deadlines from cancellation. The viewer shows
settled, successful, failed/interrupted, timed-out, and unattempted roots.
Success includes already-valid and substituted results, **not just new
compilations**. Each campaign's viewer lives under `/c/ID/`; its default page
is the campaign overview, `?follow=1` follows the latest root, and `?run=…`
links stay pinned. All links and polls are relative.

Evaluate a frozen source into a store manifest without realising its packages:

```sh
revision=$(git rev-parse HEAD)
manifest=$(nix eval --impure --raw --expr \
  "import ./experiments/campaign-next/world.nix { source = \"git+file:$PWD?rev=$revision\"; revision = \"$revision\"; }")
nix-store --query --references "$manifest"
```

The manifest retains GC references to the source and root derivations, not a
build dependency on their outputs. `campaignctl submit` freezes it and the
service roots it beside the campaign. `deploy/filnix-campaign.service`
documents the SWA deployment: an independently installed package at
`/opt/filnix-campaign`, state under `/var/lib/filnix-campaign`, loopback port
8778 behind Caddy (`deploy/nix.swa.sh.Caddyfile`), and the admin socket in
`/run/filnix-campaign`. The service uses the trusted Nix user `mbrock` so each
campaign's per-client settings (jobs, cores, builders, limits) take effect; it
does not change the daemon's shared configuration. Its memory limit bounds
the observer, not daemon-owned compiler processes. The public viewer exposes
only read endpoints, but build output is public too: only use intentionally
public source/package builds and no secret-bearing jobs.

`/healthz` checks HTTP service availability. `/api/outputs` exposes deduplicated,
verified output paths from successful attempts of campaigns whose policy
publishes. The independent cache timers query it over loopback; they never open
the live DuckDB file. Publication includes root reference closures. Successful
dependencies of a failed root are not separately discovered by this feed.
See [port campaign operations](../../docs/port-campaign-operations.md).

## Execution and ownership

Nix's public `buildPathsWithResults()` is blocking, and its logger, configuration,
and interrupt machinery are process-global. A dedicated `filnix-nix-worker`
process owns those globals. It reads derivations, observes logger callbacks,
asks Nix to build the root's outputs, and verifies returned output paths. Nix
owns the dependency scheduler and its local/remote builders. The supervisor
does not recreate Nix's worker implementation or parse ordinary CLI log output.

The supervisor runs a single cooperative NXT deck. Pipe reads, pidfd waits,
cancellation timers, and HTTP connections are asynchronous tasks on that deck.
DuckDB is the other blocking component: a `blocking_pool{1, 16}` gives it one
persistent OS thread. Database construction, every query/write, and destruction
occur there. Only owned, materialized results cross back to the deck. This is
one serial database owner, not multiple decks or coroutine migration; DuckDB
can still use its own internal query threads.

```text
Nix worker                 NXT supervisor                  DuckDB owner thread
  readDerivation             durable run.requested ----------> transaction
  discover static graph      spawn worker
  buildPathsWithResults      capture task <--- private fd 3
  Logger callbacks --------> bounded capture batches --------> events + projections
                             HTTP requests ------------------> materialized queries
                             monitor/cancellation task
  final typed result         drain pipe, reap worker
                             durable run.finished ------------> transaction
                             stop/drain HTTP
                             destroy connection on worker; close/join pool
```

The worker serializes callbacks under a mutex. Its private descriptor carries
JSON transport records; stdout/stderr cannot corrupt that protocol. The pipe
provides bounded backpressure. Capture commits the complete observations from
each pipe read as a transaction before reading more. HTTP admits eight clients,
leaving enough blocking-pool capacity for capture and cancellation calls. That
keeps producers below the admission limit: one-worker FIFO then preserves their
assigned event order. This bound is part of the ordering contract, not a promise
that a saturated blocking pool has fair admission.

Commit waits are stop-shielded: cancellation cannot discard an acknowledgement
for a write that may already have committed. Intent commits before spawning;
cancellation commits before signalling Nix; completion commits after the event
pipe has drained and the worker has been reaped. A two-second cancellation grace
period precedes SIGKILL. Exceptions terminate/reap the worker, and a parent-death
signal helps prevent an abandoned worker client. Killing a client is not a
transactional guarantee that an already-dispatched remote build stopped.

## The dataset

Schema version 2 has six data tables and a schema metadata table:

| Table | Role and identity |
| --- | --- |
| `events` | Append-only observations; global `offset`, unique `(run, seq)` |
| `runs` | Request metadata and the latest committed root summary; `run` |
| `recipes` | Recorded derivation name/system; `(run, drv)` |
| `edges` | Static input derivations, requested outputs, dynamic-input flag; `(run, parent_drv, child_drv)` |
| `activities` | Nix IDs/parents, type, phase, host, observed start/stop; `(run, id)` |
| `logs` | Captured output bytes and their observation/sequence identity; `offset` |

The event history is the observation record. The other tables are read
projections updated in the **same transaction**, not independent sources of
campaign decisions. The in-memory root projection is published only after
COMMIT. A failed transaction consumes neither offsets nor projection state.
The single writer enforces contiguous run sequences and assigns global offsets
inside the transaction. Version 2 omits the large ART primary/unique indexes on
`events` and `logs`, including the ineffective composite log cursor index; the
small entity tables keep their uniqueness constraints. Version 1 recordings
remain readable without an in-place migration. Archives retain their original
schema version. There is no general projection-rebuild command.

DuckDB is configured before opening with a **1 GiB memory budget and two threads**.
Host RAM cannot be used to size a service with a 4 GiB cgroup limit. DuckDB's
budget is not a process RSS ceiling: JSON, worker memory and some database
allocations need additional headroom. `/api/resources` reports the actual settings
and memory categories; monitor process/cgroup peaks as well.

A temporary `run_info` table caches duration, request, first top-level error,
latest native result status and cohort completion. It is rebuilt once from the
journal when opening, including after WAL recovery, and updated in the same
append transaction. Overview and cohort-count queries join only the small
per-run tables. Reopening scans fixed-width timing columns and filtered metadata
events once; ordinary dashboard polling does not join the full journal. The
cache is disposable and does not alter the six-table archive format.

Every replay envelope has version, run, contiguous run-local sequence, global
offset, recorder wall-clock nanoseconds, recorder monotonic elapsed nanoseconds,
kind, and a kind-specific JSON payload. Worker observations also preserve
callback-capture wall and monotonic timestamps in `payload.capture`. Global
offset orders committed observations, not simultaneous real-world events on
different machines. Nix activity IDs are scoped to a run, never global keys.

Event payloads retain all typed logger fields, including unknown result types.
The Nix boundary normalizes the pinned `actBuild` field contract into derivation
and machine, while the projection recognizes `resSetPhase`. Logger strings are
hex in the transport/events because arbitrary builder bytes need not be UTF-8;
native log/text/phase columns are BLOBs. The HTML view replaces invalid display
bytes and escapes untrusted content without altering the stored bytes.

A stopped activity is not a successful derivation. Only the root's typed build
result, verified output paths, and normal worker completion establish its final
outcome. Built, substituted, already-valid, failed, cancelled, worker error, and
recorder error remain distinct. A missing terminal event means **incomplete**,
not failed or safely retryable. The viewer labels a run live only while its own
supervisor is observing it; an offline incomplete recording is not called live.
Cancellation is a request; verified success wins if the build finished first.

DuckDB handles transaction/WAL crash recovery. There is no ad-hoc JSONL sync
policy or application SQLite database. A crash may still lose uncommitted or
undelivered observations. Database write failures can prevent recording even
the error/completion events, leaving an honestly incomplete prefix. Runs are
never silently resumed or retried after such a failure.

## Viewer and archive

The NXT HTTP server renders HTML in C++. The front page is a campaign overview:
a proportional outcome bar with filter chips and one page-scrolling Package /
Version / Status / Duration / Detail table, problems first, with Find, filters
and 100-row windows. Unsuccessful roots name their first recorded error. Names
drop the repeated host triple (shown once above). Unattempted roots
remain visible without invented session links. Overview/rail reads materialize
summaries only, not a selected graph or log. A session link opens the graph and
console; `Follow latest` explicitly opts into the current/latest session.

While recording/admitting, HTMX polls summary/state every two seconds and the
list every three, without replacing the log pane. Settled recordings have no
periodic state/list/log requests; hidden pages suppress background requests.
The rail is scoped to the selected cohort (at most 1024 roots); standalone views
retain the latest 256 recordings. Campaign counts apply the matching list filter.

The graph foreground shows the root, recorded phases, useful direct inputs
and active reachable builds. Static closure is an exact collapsed count with
no descendant DOM until expanded. Expansion uses 500-row replacement windows,
one omission notice and real previous/next controls. Shared vertices and cycles
are references, not recursively revisited. Drv fragments load their containing
window and retain the human package title.

Output is a visible peer pane. Polls use an exclusive run-local sequence
cursor, optionally filtered to an exact activity ID. Initial logs show the
latest 200 records, polling returns at most 256, and the browser retains at
most 256. Find searches this loaded window and reports its size. Pause stops
log requests and pins the current recording; scrolling away or using Find
also pauses. Follow refreshes the tail and follows new output; End refreshes
the tail without changing pause state. Phase jumps use recorded event cursors.
Full activity IDs and times stay visible while messages scroll horizontally.
SGR renders escaped spans for ANSI16, indexed256 and truecolor, with bold, dim,
italic, underline, strike and inverse/reset support. Styling is per observation,
not a terminal emulator or reconstruction of style across record boundaries.
Unsupported controls stay visibly sanitized. Raw events, APIs, replay and
Parquet retain the original bytes. Find preserves styled spans, including
matches crossing them, and caches unchanged rows rather than rewriting every
message during empty searches. Batch appends keep the console bounded.

`src/html.hh` supplies a small Tagflow-like block writer for the overview table
and styled output: owned response bytes, callback-scoped children and escaped
text/attributes, without an AST, ambient coroutine state or raw-HTML interface.
The existing renderer shares its escaping; this is a foundation, not a complete
Tagflow port. [DESIGN.md](DESIGN.md) contains exact labels, component contracts,
URL state, limits and visual tokens.

Static derivation edges and Nix activity parents are different relationships.
The graph uses recorded input derivations, overlays observed phase/host/time,
and represents shared dependencies with explicit references. Unreadable input
recipes and dynamic inputs stay unknown. It does not invent wait counts or
per-dependency successes. Graph metadata is currently queried per run; very
large graphs and unusually large log records still need byte-budgeted paging.
`/api/state` and `/api/logs` expose the same owned JSON observations. This is
incremental polling, not SSE or a streaming HTTP response API.

Export runs all six `COPY … FORMAT PARQUET, COMPRESSION ZSTD` operations in one
snapshot transaction. Binary data stays binary, raw events stay available for
new analyses, and `manifest.json` records schema version and the global
watermark. The manifest is written last; a directory without it is not a
published archive. Failed exports clean up only their newly-created destination.
This is not an fsync-hardened, atomically renamed archive-publication protocol.

Timed replay uses the recorded recorder-observation timeline anchored to one
clock, so rendering time does not accumulate drift. It does not rerun builds.
Nix has already merged builder stdout/stderr into logger observations: neither
the original stream labels/write boundaries nor exact producer emission times
are recoverable here. Callback and recorder timestamps measure observation,
including any transport/backpressure delay. Separate raw stream recording needs
a different Nix capture boundary or a controlled builder wrapper.

## Still deliberately absent

There is no evaluation service (manifests are frozen by `campaignctl`, as the
caller), new Nix builder, or authentication beyond the admin socket's file
permissions.
Recordings can contain secrets printed by builds; do not publish databases,
logs, or archives indiscriminately.

Checks cover transaction rollback across all projections, exact large activity
IDs and arbitrary bytes, unknown events, real artifacts, cached repeats, shared
dependencies, failed prerequisites, API errors, cancellation/draining, abrupt
observer death and WAL recovery, replay pacing, HTTP cursor semantics, HTML
escaping/OOB row structure, schema rejection, and native/Parquet equality.
Service tests cover requirements and skipped roots, the survey's first-error
and counts extraction, publication by policy, timeouts, budgets, priority,
pause/resume/cancel/retry, restart after a service stop, recorder errors,
registering recordings and duplicate detection, and manifest validation.
A two-million-event/300-root fixture exercises overview/detail polling, database
settings, process peak RSS and v1 compatibility. For campaign-scale validation:

```sh
CAMPAIGN_STATIC_DIR="$PWD/experiments/campaign-next/static" \
CAMPAIGN_MEMORY_TEST_ROWS=13200000 nix develop path:./experiments/campaign-next \
  --command python3 experiments/campaign-next/tests/test_campaign.py \
  .amp/in/campaign-next-build/filnix-campaign \
  CampaignTests.test_large_journal_budget_and_v1_compatibility
```

Inactive incomplete roots are displayed as incomplete. A cohort with unfinished
recordings and no durable terminal event reports `recording-interrupted`; this
is viewer state, not a fabricated journal event or permission to retry builds.

An additional ASan/UBSan build passes the dataset test, but its leak-enabled
integration suite is not clean: LeakSanitizer reports allocations in Nix's
build-goal machinery, including successful builds. A minimal Nix-only
`buildPathsWithResults` client, without NXT, DuckDB, or the campaign logger,
also reproduces goal leaks. This experiment does not suppress those reports
or patch the Nix dependency.
