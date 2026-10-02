# Campaign, again

A greenfield, event-first experiment alongside the existing Python campaign.
Nothing here replaces its coordinator, database, dashboard, or systemd services.
The first slice is intentionally small: **build one derivation through the Nix
C++ API, supervise it with NXT, record what happens, and replay the recording.**

## Try it

From the Filnix repository root:

```sh
nix build path:./experiments/campaign-next --out-link result-campaign-next
nix flake check path:./experiments/campaign-next
```

The package's checks run real builds in disposable local stores. They do not
connect to the host daemon or touch the existing campaign. Python is used for
these tests, not for the implementation.

For a derivation already present in your chosen store:

```sh
result-campaign-next/bin/filnix-campaign record /nix/store/…-example.drv run.jsonl
result-campaign-next/bin/filnix-campaign inspect run.jsonl
result-campaign-next/bin/filnix-campaign replay run.jsonl --speed 10
result-campaign-next/bin/filnix-campaign replay run.jsonl --speed 0 --json
```

`record` defaults to the daemon store; `--store URI` selects another store. It
really requests a build, so use the isolated tests if you only want to explore.
It never overwrites an existing journal. Observations are displayed on stderr;
the final projection is JSON on stdout. SIGINT/SIGTERM requests cancellation.
Exit codes follow the worker's result (0 for success, 1 for a build failure,
2 for an API/worker error, or 128 + signal for signal termination).

Replay defaults to 1×. `--speed 10` accelerates it, `--speed 0` removes delays,
and `--json` emits the recorded envelopes rather than rendering their messages.
Inspect needs only the journal, not Nix or a running recorder.

For local development:

```sh
nix develop path:./experiments/campaign-next
meson setup .amp/in/campaign-next-build experiments/campaign-next
meson compile -C .amp/in/campaign-next-build
meson test -C .amp/in/campaign-next-build --print-errorlogs
```

The subflake pins NXT and Nix's C++ libraries independently of the main Filnix
toolchain. This is currently native C++23 on x86_64 Linux, not a Fil-C build.
It links upstream Nix 2.34.8; it does not install or replace the host daemon.
Daemon compatibility is a separate integration milestone: the tests exercise
the linked library's local store, not the existing Determinate daemon.

## The shape of it

The existing campaign combines durable SQLite state, event history, attempt
workers, and dashboard queries. This experiment starts from a different
direction: the recording is the durable object; a description of current state
is something computed from it. We can change that description without changing
or rerunning the experiment that produced the observations.

NXT contributes the ownership and concurrency model. NixB supplies the precedent
for using Nix's actual C++ objects rather than reverse-engineering CLI output.
NixB's current build UI simulates builds; this slice exercises the real build
API. It does not reuse NixB's old synchronous coroutine logger bridge.

There are two executables for a reason. Nix's public `buildPathsWithResults()`
is blocking, and its configuration, logger, and interrupt machinery have
process-global state. Calling that API on NXT's cooperative deck would block
every other task on the deck. Instead, `filnix-nix-worker` owns Nix and performs
the blocking operation. `filnix-campaign` owns its lifetime and recording.

```text
NXT supervisor                    Nix worker
  durable run.requested             initNix / openStore
  spawn --------------------------> readDerivation
  capture task <--- private fd 3 --- Logger callbacks
  monitor task                      buildPathsWithResults
    periodic journal sync           verify returned output paths
    cancellation                    emit typed build result
  drain pipe / reap <-------------- exit
  durable run.finished
             |
             v
       append-only journal -------> projection / inspect / timed replay
```

Capture and monitoring are scoped together with NXT's `when_all`. The supervisor
reads the event pipe asynchronously and uses a pidfd to wait for the worker.
It drains the pipe before recording process completion. Cancellation is first
journaled, then delivered to the worker; a two-second grace period precedes
SIGKILL. Exceptional recorder failure also terminates and reaps the worker.
A parent-death signal prevents an abandoned worker client if the supervisor
dies. This is process supervision, not systemd integration.

The worker uses a dedicated protocol descriptor, not diagnostic stdout/stderr.
Its logger serializes callbacks under a mutex and writes them to that pipe.
The pipe is a bounded backpressure boundary: a slow recorder eventually slows
the worker instead of accumulating an unbounded queue. The worker reads the
root derivation, asks Nix to build all outputs, then checks that the returned
outputs are valid in the store. A stopped activity is *not* a success signal.
Built, substituted, already-valid, and failed are distinguished using the actual
build result. Nix remains responsible for scheduling the root's dependencies.
The prototype requests one local job and one core and disables the remote build
hook in the worker's configuration. A daemon may impose its own configuration
and trust rules; these are not host-wide settings changes.

## The recording is the model

Each invocation gets a fresh random run identity and an exclusively created
JSONL file. Every envelope has:

| Field | Meaning |
| --- | --- |
| `version` | Envelope version, currently 1 |
| `run` | Run identity |
| `seq` | Contiguous recorder-assigned sequence, starting at 1 |
| `wall_ns` | Recorder wall-clock timestamp |
| `elapsed_ns` | Recorder monotonic time since journal creation |
| `kind` | Event kind |
| `payload` | Kind-specific data |

The event vocabulary currently includes request, worker startup, root recipe
metadata, Nix messages/errors, activity start/stop, every Nix activity-result
type, the final Nix build result, cancellation, recorder errors, and process
completion. Worker observations also retain callback-capture wall and monotonic
timestamps inside `payload.capture`. String fields supplied by the logger are
hex-encoded because builder output need not be UTF-8. Activity IDs, parents,
types, and typed fields survive intact; they are not inferred from log text.
The final result includes Nix's own serialized result plus verified output paths.

This gives one ordered history **per run**, not yet a globally ordered campaign
history. A future scheduler needs its own durable admission and dispatch events,
with attempts linked to those decisions. Local sequence numbers or Nix activity
IDs must not be mistaken for global identities.

The same projection code consumes live events and offline recordings. Its small
summary counts activities/output lines and describes the root outcome. Without
`run.finished`, the outcome remains incomplete even if some promising build
observations were captured. Cancellation is recorded as a request; if the worker
actually finished successfully before it took effect, the verified success wins.
Missing completion is uncertainty, not permission to silently declare failure
or to retry an attempt.

The intent is synced before spawning; completion is synced before reporting.
Intermediate data is flushed at 64 KiB or roughly one second. The journal's
parent directory is synced on creation. A crash can therefore lose the most
recent intermediate observations; this is **not** per-event durable delivery.
Readers validate envelope versions, identities, sequence numbers, and monotonic
ordering. A partial last line is reported and ignored; a malformed complete
line is an error. Records are bounded at 8 MiB.

Replay uses the recorded monotonic observation timeline, anchored to a single
start time so time spent displaying a message does not accumulate drift. It
does not reproduce build side effects. Reading a journal can rebuild this
projection without consulting a writable database. There is no application
SQLite database here; Nix's own local store still uses its normal internals.

## What this cannot tell us yet

Nix has already merged builder stdout and stderr and converted output into
logger observations. We preserve the bytes exposed by those callbacks, not
the original stream labels, write boundaries, terminal control behavior, or
producer timestamps. Callback times and recorder times are observation times;
transport and buffering can delay them. Timed playback is therefore playback
of **what this observer saw**, not a claim about exact builder emission timing.
Recording separate raw stdout/stderr would need a different capture point in
Nix or a controlled builder wrapper.

The NXT pipe/timer/process operations are asynchronous, but journal writes,
syncs, JSON encoding, and terminal rendering are still synchronous. That is
acceptable for this single-attempt slice, not a finished high-throughput event
writer. Output rendering can also backpressure recording. Any redesign of the
writer must retain bounded admission, explicit commit acknowledgements, and
ordering between durable intent and execution.

There is no campaign planner, evaluation service, dependency graph projection,
multi-builder pool, lease/restart recovery, systemd unit, dashboard, SQLite read
projection, or Parquet export yet. The journal is not authenticated or encrypted
and can contain secrets printed by builds. Do not publish it indiscriminately.

## Where to take it next

The next useful slice is several independent roots in a bounded NXT pool,
recording campaign admission/dispatch decisions and keeping package failures
as ordinary outcomes rather than pool-fatal exceptions. That makes scheduling
and lifecycle ownership concrete before choosing a service architecture.

Then separate the journal writer from producers and add a disposable read
projection. SQLite could still be an excellent projection format, without being
the place where unrelated pieces mutate campaign truth. A dashboard can read
that projection or periodic snapshots; HTMX need not participate in the build
control path. Immutable closed journal segments can feed Parquet/DuckDB without
turning an export into a second authority.

Those steps should be tested against interrupted dispatch, failed recording,
restarts, and slow readers, not just happy-path package builds. For now, the
integration tests cover real output/artifacts, cached reuse, blocked dependents,
arbitrary output bytes, cancellation, projection equality, lossless JSON replay,
1×/10× timing, torn tails, sequence corruption, and refusal to overwrite history.
