# Campaign, again

A C++/NXT campaign runner and the canonical viewer at <https://nix.swa.sh/>.
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
filnix-campaign cohort manifest.json campaign.duckdb --budget 7200 --root-timeout 900
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

`shells/world-packages.nix` is the ordered, reusable root set for both the world
shell/VM and this campaign. It includes 82 roots: Linux userland, foundational
libraries, GTK/Wayland, language runtimes, and applications. Emacs is headless;
GTK uses the existing Wayland/Broadway port configuration. Custom Qt ports are
not selected. FFmpeg and GTKmm are last to avoid delaying the core landmarks.

`world.nix` with `scope = "ports"` expands this to the union of the world roots
and all active `ports.nix` declarations. Evaluations that fail are retained in
the manifest's `excluded` array. The initial full port manifest has 300 admitted
roots and 12 exclusions. The runner accepts up to 1024 roots, retaining all
cohort summaries while the table renders 100 rows per page.

`cohort` accepts an immutable JSON manifest with `id`, `name`, and a `roots`
array of `{name, drv}` objects. It admits one root request at a time; Nix still
schedules that root's complete dependency graph. Package failures and per-root
timeouts do not prevent subsequent roots. An overall monotonic deadline stops
admission and interrupts the active worker. Defaults are two hours overall and
15 minutes per root, with the normal two-second termination grace. These are
client-observation/build budgets, not a guarantee that a daemon build shared
with another client has stopped. Recorder errors stop admission rather than
pretending the root was observed correctly.

Intent events retain the manifest, source revision, root index and budgets.
`run.limit-reached` distinguishes deadlines from operator cancellation;
`cohort.finished` durably records why admission ended. The viewer shows settled,
successful, failed/interrupted, timed-out, and unattempted roots. Success includes
already-valid and substituted results, **not just new compilations**. The default
page is a campaign overview; `?follow=1` explicitly follows the latest root,
and `?run=…` links stay pinned. All links and polls work under a stripped
reverse-proxy prefix such as `/v2/`.

After admission ends, the viewer stays up. Restarting `cohort` against any
nonempty recording serves it without resuming or retrying builds, including
after a crash. Starting a new campaign requires a new database; there is no
batch scheduler, durable work queue, or automatic lease recovery.

Evaluate a frozen source into a store manifest without realising its packages:

```sh
revision=$(git rev-parse HEAD)
manifest=$(nix eval --impure --raw --expr \
  "import ./experiments/campaign-next/world.nix { source = \"git+file:$PWD?rev=$revision\"; revision = \"$revision\"; }")
nix-store --query --references "$manifest"
```

The manifest retains GC references to the source and root derivations, not a
build dependency on their outputs. Give it a persistent GC root before launch.
`deploy/filnix-v2.service` documents the SWA deployment: an independently
installed package at `/opt/filnix-v2`, state under `/var/lib/filnix-v2`, an
immutable `manifest.json` symlink there, and loopback port 8778. Root both the
package and manifest under `/nix/var/nix/gcroots/`. The service uses the existing
trusted Nix user `mbrock` to make its per-client configuration effective:
two local jobs, four cores per job, the configured remote builders, and thirty
minutes of silence allowed. The deployed port campaign has a 24-hour overall
budget and two hours per root. It does not change the daemon's shared configuration. Its 4 GiB
memory limit bounds the observer, not daemon-owned compiler processes.

`deploy/nix.swa.sh.Caddyfile` routes the root to this viewer, preserves the public
cache, and redirects `/v2/` URLs to the root while retaining their queries.
Merge it with existing site-specific routes rather than replacing the entire
host configuration. Validate Caddy and the unit before reloading/enabling.
The public viewer exposes only read endpoints, but build output is public too:
only use intentionally public source/package builds and no secret-bearing jobs.

`/healthz` checks HTTP service availability. `/api/outputs` exposes deduplicated,
verified output paths from complete successful root recordings at a committed
watermark. The independent cache timers query it over loopback; they never open
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

Schema version 1 has six data tables and a schema metadata table:

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
This version does not yet expose a projection-rebuild command or migrations.

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

There is no general campaign planner, evaluation service, admission/lease
recovery, new Nix builder, authentication, or online export API. The bounded
manifest runner deliberately does not copy the existing campaign's batch model.
Recordings can contain secrets printed by builds; do not publish databases,
logs, or archives indiscriminately.

Checks cover transaction rollback across all projections, exact large activity
IDs and arbitrary bytes, unknown events, real artifacts, cached repeats, shared
dependencies, failed prerequisites, API errors, cancellation/draining, abrupt
observer death and WAL recovery, replay pacing, HTTP cursor semantics, HTML
escaping/OOB row structure, schema rejection, and native/Parquet equality. Cohort
tests distinguish failure continuation, per-root timeout continuation, overall
budget cutoff, pinned views, durable stop events, and restart without retries.

An additional ASan/UBSan build passes the dataset test, but its leak-enabled
integration suite is not clean: LeakSanitizer reports allocations in Nix's
build-goal machinery, including successful builds. A minimal Nix-only
`buildPathsWithResults` client, without NXT, DuckDB, or the campaign logger,
also reproduces goal leaks. This experiment does not suppress those reports
or patch the Nix dependency.
