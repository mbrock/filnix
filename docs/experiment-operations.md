# Operating the Filnix experiment

The dashboard is **https://nix.swa.sh/**. It is read-only. The main campaign contains
13,772 selected attributes and was started on 2026-09-13. It continues planning
and building in bounded batches. Synthetic native runner calibrations are
separate campaigns, clearly labeled in the campaign selector.

## Dashboard layout

**Activity** is the default: inventory progress, current builds, a compact
campaign timeline, and the batch ledger. **Packages** provides the searchable
inventory and shared blockers; **Dependencies** contains the graph. The views
have URL fragments and support browser back/forward navigation. Campaign
selection, source revision, resource meters, and additional inventory counts
live in the run menu beside **Live logs**.

The design follows the build-to-job-to-log navigation used by
[Buildkite](https://buildkite.com/docs/pipelines/build-page) and the emphasis on
clear, dense information in [U.S. Graphics](https://usgraphics.com/). Current work
and changes stay visible; detailed evidence opens on demand. Shared typography,
restrained status colors, aligned rows, and small gaps replace repeated headings,
explanatory captions, and a permanent inspector. Phone layouts adapt the content
instead of shrinking a desktop table or retaining a wide sidebar.

**Available** counts selected attributes whose required outputs were observed.
**Checked** counts distinct selected derivations with successful check evidence;
it is not a count of every transitive dependency or individual test case. Batch
check counts include dependency derivations. A batch labeled **With errors** may
still contain successful builds and checks; **Plan finished** describes the
worker, not the acceptability of all recipes it evaluated.

## Watching dependencies

The live map follows an active build and draws its inputs on the left and direct
consumers on the right. Arrows point from dependency to consumer. Click a neighbor
to move through the graph; this pins the focus while its states keep updating.
Back returns to the previous node; Follow live resumes automatic selection.
Requested roots and active build phases are shortcuts into the same map, and a
package's detail view has an Explore on dependency map button.

Available inputs collapse into an expandable group. Neighbor pages limit the
display to six real nodes per side. The center also identifies the current batch
targets reachable downstream and counts selected dependent attributes (including
aliases), while the map itself deduplicates derivations. Shared native tools are
part of the build graph; role annotations are shown where recorded.

The map reports recipe evaluation progress and store preflight separately from
actual builds. It uses the recorded graph, active attempt's store observations,
and Nix phase events, without launching Nix queries from HTTP requests. A stopped
activity remains awaiting result until stronger evidence exists. A consumer
reaching a build phase establishes that its required input outputs were provided;
that availability is labeled as an inference in the node tooltip and never
creates a local-build or test-pass claim. This follows Nix's
[input realization before execution](https://github.com/NixOS/nix/blob/2.32.1/src/libstore/build/derivation-building-goal.cc#L180).
Edges use their required output names, so a consumer needing `dev` does not wait
for an unrelated missing output. The public `/api/graph` accepts `campaign`,
optional `focus` derivation, `available=1`, and a neighbor `page`.

## Following build output

**Live logs** opens the current build batch near the end of its captured
output. It follows subsequent batches while following output is enabled.
Opening an individual attempt pins that attempt; **Next batches: on** in the log options menu opts into
automatic transitions. Scrolling back, searching, or loading history pauses
both scrolling and batch transitions. **Resume** (or the new-output byte count) returns to the current
end of the selected attempt. Paused viewers keep their text and position while
checking for new output, and show how many captured bytes are waiting.

Select a build in the sidebar, or the source picker on phones, to isolate its output. Links from the dependency
map, current work, and recorded package/derivation results open that build's
log. The reader searches backward for recent output from quiet builds. Phase
boundaries and diagnostics stand out; Nix progress counters and cache-query
events are hidden. Output is attributed through recorded Nix activity IDs.
Native tools retain their own identities. Unattributed evaluator/Nix messages
remain in **All builds**. Ending an activity does not create a success claim.

**Earlier output** pages backward without moving the line being read.
Search highlights text within the loaded window; Enter/Shift+Enter or the arrow
buttons move among matches. Wrap controls long lines. The browser retains up to
2,000 records and approximately 1 MiB of decoded text; older/newer windows can
be loaded again. **Download raw log** in the options menu downloads the original captured stderr, including
event metadata, escape sequences and progress records omitted from the viewer.

The log options menu offers 12, 14, and 16 px text sizes (relative to the browser's
base text preference); the choice is saved locally when storage is available.
Changing size or wrapping retains the visible row when scrolling is paused.
Normal browser zoom remains available. On phones, the build picker becomes a
native select and consecutive rows share a source label above the output. Find
opens the search row; Escape closes it first. Wrapping and follow controls remain
visible. With search closed, output occupies over three quarters of the phone
viewport, including at a 320 px width.

`experiment/static/theme.css` owns the shared type, spacing, and color scale for
the dashboard, history, graph, and log viewer. Component styles consume those
variables directly; no CSS compilation or runtime styling dependency is needed.
The root and wide log blocks explicitly set `text-size-adjust: 100%` (including
the WebKit prefix) to prevent individual log rows from receiving different
mobile text inflation. Touch inputs use the larger control size. Browser checks
cover mixed and scoped logs, wrapping, uniform long/short row metrics, narrow
phone controls, persisted size choices, and scroll anchoring. Chromium touch
emulation is a layout check, not a substitute for validation on an actual iPhone.

The read-only `/api/build-log` accepts `attempt`, optional `drv`, a byte `cursor`,
and `direction=tail|before|after|status`. Each request reads bounded windows
(256 KiB normally, at most 1 MiB for a record); complete records retain their
original byte offsets. Oversized records are noted and remain in the raw log.
Live reads stop at the controller's committed ingestion offset, which commits
activity ownership and cursor together. This prevents a new build's lines being
consumed before their owner is known. UTF-8 records are decoded whole; terminal
fragments remain visible. No Nix queries or database writes occur on this path.
The older raw `/api/log` endpoint remains available.

Requests are serialized, aborted when switching views, and protected by a view
generation token. Reconnection resumes at the last consumed cursor. The log
viewer is independent of the controller and attempt processes; updating it only
requires restarting `filnix-web` after selecting the new application package.

## Responsibilities

- `experiment/model.py`: SQLite schema, campaign import, graph queries, events.
- `experiment/nix.py`: installed Nix JSON adapter, store validity, cgroup readings.
- `experiment/controller.py`: single writer, queue admission, recovery, local commands.
- `experiment/attempt.py`: independent unit, bounded evaluation/build processes,
  raw logs and atomic completion record. Never writes the database.
- `experiment/web.py` and `experiment/static/`: read-only WSGI app, Waitress,
  ordinary browser JavaScript. No frontend dependency installation.
- `experiment/graph.py`: live, campaign-scoped graph neighborhoods and readiness
  evidence. No database writes and no change to build admission.
- `deploy/experiment/`: fixed systemd units, narrow launcher, installation helper,
  and Caddy snippet. No automatic build activation.

The app is independently packaged by `experiment/default.nix`; importing it does
not evaluate the Fil-C compiler. It uses the repository's locked Nixpkgs and
records the installed Nix version with each campaign. A Nix upgrade requires a
new campaign before further attempts. Source recipes come from an immutable
`git archive` added to the Nix store, including their lockfile; local uncommitted
changes do not enter that campaign. Attempts also record fixed policy and source.

## Local commands

Run administration over SSH as the experiment user:

```sh
sudo -u filnix-experiment /opt/filnix-experiment/bin/filnix-experiment status
```

The CLI's `--state` defaults to `/var/lib/filnix-experiment`. It talks to the
controller's mode-0600 Unix socket. If the controller is stopped, commands use an
exclusive file lock; a second writer cannot acquire it. `import` requires the
controller to be stopped, and a repository readable by the invoking account.

```sh
filnix-experiment import /path/to/inputs.json --name 'Campaign name' \
  --repo /path/to/filnix --revision COMMIT --inventory /path/to/inventory.jsonl
filnix-experiment plan CAMPAIGN CANDIDATE_ID [CANDIDATE_ID ...]
filnix-experiment build-once CAMPAIGN CANDIDATE_ID [CANDIDATE_ID ...]
filnix-experiment schedule CAMPAIGN --batch-size 32 --plan-ahead 128
filnix-experiment pause CAMPAIGN
filnix-experiment cancel ATTEMPT_UUID
filnix-experiment retry CAMPAIGN CANDIDATE_ID [CANDIDATE_ID ...]
filnix-experiment retry-derivation CAMPAIGN /nix/store/NAME.drv
filnix-experiment backup /path/to/backup.sqlite
```

Candidate IDs appear in `/api/snapshot`, which supports `campaign`, `q`, `state`,
and `offset` parameters. The exact input manifest is at
`/api/manifest?campaign=CAMPAIGN`. Package details are at `/api/package?id=ID`;
`/api/derivation` expands a dependency, its role annotations, and paginated
selected dependents. Logs use bounded byte offsets. `/api/events?after=SEQ`
exposes a durable event cursor. The browser refreshes a paginated snapshot every
five seconds and bounded log chunks every 1.5 seconds.

`plan` accepts up to 64 IDs, uses no IFD and no builds, and records errors per
candidate. `build-once` respects the configured batch size in a paused campaign;
it checks containment and budgets and leaves the campaign paused afterward.
`pause` drains both active lanes. `cancel` pauses its campaign, terminates only
the named attempt, and reconciles its eventual exit; the other lane drains. It never stops the shared daemon.
`retry` requeues an inconclusive or failed candidate. A shared failed dependency
can be cleared with `retry-derivation`; other known blockers stay in force.

**`filnix-experiment run CAMPAIGN` enables the continuing experiment.** Newly
imported campaigns never become running just because services restart. Ordering
remains deterministic by attribute name, deduplicated by derivation. Cost/fanout
scheduling is a future policy change.

## Keeping builds supplied

Version 0.6 permits one planner and one Nix build client in the same campaign.
The main campaign uses **32 roots per build batch** and a **128-derivation ready
buffer**. The planner evaluates at most 32 inputs per attempt and stops admitting
work when the buffer is full. Evaluation failures, cached outputs, aliases, and
known blockers do not consume ready slots. The last planning chunk is bounded by
remaining buffer capacity. Only finished plan records enter the queue.

This addresses two observed gaps: an eight-root batch often ended with one large
build while other packages waited, and evaluation began only after all ready work
was exhausted. A 176-second sample during `aws-sdk-cpp` used 6.0 of 28 allowed CPU
threads, with about 55.5 GiB in the 100 GiB workload limit and no pressure/OOM
events. The first 24 plan attempts consumed 858 seconds, averaging 36 seconds each.
Larger batches expose more independent work to Nix; overlapping planning removes
most evaluation gaps. This is not a measured overall speedup, and a batch can still
end with one long build.

Use `schedule CAMPAIGN` to inspect settings. `--batch-size` accepts 1–64 roots;
`--plan-ahead` accepts 0–256 ready derivations; `--build-lanes` accepts 1–2 clients. Zero keeps the original serial
admission behavior; new imports default to eight roots and no lookahead until
explicitly configured. Settings apply to future attempts. Setting lookahead to
zero lets any existing overlap finish without cancelling it. `schedule` does not
start a paused campaign.

The local command records old/new settings and the runner version as a
`scheduling-updated` event. Every new attempt freezes its complete policy and
runner version in `spec.json`; existing attempts retain their original specs.
Source revision, input manifest, recipe derivations, test settings, and historical
results remain unchanged. Resource caps cannot be edited by `schedule`.

A long batch tail can still strand ready work. Opt into **two build lanes** with:

```sh
sudo /opt/filnix-experiment/bin/filnix-experiment schedule CAMPAIGN --build-lanes 2
```

Lookahead must also be nonzero to admit overlapping work. Normally each client
gets two jobs with six requested cores per job: four jobs in total. Admission
reserves each active client's full `max_jobs * cores` request, using its immutable
spec, against the 28 allowed workload CPUs. It never treats momentarily idle jobs
as spare reservations. While an older four-job/six-core batch drains, the second
lane gets only one job with four cores. Each new attempt records its effective
limits. The CPU set and 80% aggregate memory cap remain the hard limits; Nix's
`cores` is a build-system hint. The planner still uses at most two allowed CPUs
and 4 GiB. No running attempt or daemon needs restarting to enable this policy.

Before admitting another batch, the controller walks required dependency outputs,
stopping at outputs previously observed available. A new batch cannot overlap
another active batch's potentially unrealized derivations or their output paths.
Already available tools and libraries can be shared. Dependencies are reserved
until their owning attempt reconciles, even if some finish early. Unknown outputs
are treated conservatively. Selection scans up to the lookahead window (at most
256 queued roots), skips overlapping work, and retains skipped roots in the queue.
If that entire window shares unfinished dependencies, it waits. This is a bounded
scheduler, not a guarantee of full utilization.

Memory pressure, disk reserve, and retained log budget gate all new automatic
work. Existing wall-time and 128 MiB per-attempt log budgets remain in force.
Other campaigns cannot occupy a spare lane. Lowering `--build-lanes` or disabling
lookahead drains already admitted workers without cancellation. Restart recovery
preserves every attempt. Cancelling one attempt pauses new admission while other
workers keep running. Completion updates only that attempt's candidate roots;
reuse of cached dependencies preserves their earlier local-build/test provenance.
The graph and live cards include both build lanes and open the correct logs.

Plan reconciliation immediately applies recorded availability and shared failure
facts to new recipes. It also marks newly discovered aliases of active build roots
as running. This prevents freshly discovered dependents of a known failed library
from being submitted again, while preserving check evidence and inconclusive
results. The dashboard keeps active attempts visible even if many newer plans
finish, and reports planning alongside build activity.

## Installed host configuration

Build and install a new app version:

```sh
nix build --impure --file experiment/default.nix --out-link result-experiment
sudo deploy/experiment/install "$(readlink -f result-experiment)"
sudo systemctl restart filnix-controller filnix-web
```

`/opt/filnix-experiment` selects the packaged application. Keep the previous store
path for rollback. Existing attempt processes keep their original application
version and continue independently when the controller/web restart. On a fresh
host, import a campaign before enabling `filnix-controller` and `filnix-web`.
The installer does not modify the daemon or Caddy configuration.

The host-specific resource configuration is installed separately as
`/etc/systemd/system/nix-daemon.service.d/filnix-workload.conf`, sourced from
`deploy/experiment/nix-daemon.conf`. Moving the daemon into its slice requires a
daemon restart; first check for active builders. This intentionally affects all
daemon builds, including builds requested outside the experiment.

The actual cgroup is
`/sys/fs/cgroup/filnix.slice/filnix-workload.slice`: systemd adds the parent slice
because the name contains a hyphen. It contains the daemon and attempt units.
The controller, web server, SSH and Caddy are outside it.

| Setting                     | Installed value                                                           |
| --------------------------- | ------------------------------------------------------------------------- |
| CPUs                        | `2-15,18-31`; two complete physical cores reserved                        |
| MemoryHigh / MemoryMax      | 70% / 80%; observed maximum 107,296,374,784 bytes                         |
| Swap                        | 2 GiB                                                                     |
| Nix admission               | One client, 32 roots, four jobs, six requested cores per job              |
| Build wall / silence budget | 7,200 / 900 seconds                                                       |
| Evaluator                   | Two CPUs, 4 GiB address space, 90 seconds per candidate                   |
| Attempt service             | 8 GiB client/evaluator memory, 1,024 tasks, three-hour backstop           |
| Log budgets                 | 128 MiB per attempt; 20 GiB retained logs                                 |
| Disk reserve                | Stop admission below 50 GiB free                                          |
| Scratch                     | `/var/tmp/filnix-build` for daemon, `/var/tmp/filnix-eval` for evaluation |

Memory figures are aggregate cgroup readings, not per-package peaks. Aggregate
OOM changes make failure attribution inconclusive. Per-build cgroups remain
disabled; the verified aggregate ceiling already includes actual builder PIDs.
Systemd services do not make Nix's requested job thread count a hard CPU limit;
the shared CPU set supplies the hard boundary.

The explicit `nix.swa.sh` vhost proxies loopback port 8777. To change Caddy, stage
the complete configuration, validate with
`caddy validate --config CANDIDATE --adapter caddyfile --envfile /etc/caddy/dnsimple.env`,
install it readable by the `caddy` user, reload, and check the public `/healthz`.
The live Caddyfile is root-owned, group `caddy`, mode 0640. The pre-install copy
is `/etc/caddy/Caddyfile.before-filnix-20260913`. Credentials stay in the existing
environment file. No dashboard route provides administrative actions.

## Recovery, retention and evidence

SQLite uses WAL and full synchronization. Attempts commit intent before launch;
the worker creates a started marker once per UUID, captures raw logs, fsyncs
them, and atomically publishes `exit.json`. Recovery reconciles those records,
unit state, and store validity. Log offset and observations commit together.
Incomplete final lines are retained; oversized lines are skipped with an event,
without wedging the controller. A missing exit record is not a success.

`roots` in the state directory points to the actual owned directory
`/nix/var/nix/gcroots/filnix-campaigns`. The directory must be real at the GC-root
location: a symlink from the GC-root tree to another directory does not root all
its contents. Verify roots with `nix-store --gc --print-roots` (this does not
collect). Source, planned derivations, and observed successful outputs are rooted.

Use `backup`, which invokes SQLite's online backup API, and archive attempt
directories along with it. Do not copy just a live WAL database file. Automatic
admission stops at the log/disk budgets; this release does not automatically
discard evidence. Archive only finished attempts, preserve manifests, raw logs,
and exit records, and stop the controller when restoring state. Output
availability is the last observation, not a promise that a manually removed
root or subsequently collected output still exists.

Root build failures are distinguished from dependency failures using a fixture
from the installed Nix 2.32.1 / Determinate 3.12 logger. Compile and link errors
within `buildPhase` remain `compile-or-link`. Unknown/fetch diagnostics are
conservative inconclusive results until the adapter has stronger evidence.
Local build activity plus newly realized outputs can substantiate observed check
phases. Existing outputs create no new test passes. Realization without a local
activity is currently `unknown`, which can include substitution; it is never
reported as a fresh local build.

Compiler provenance currently means the evaluated recipe selects the Fil-C
compiler. Independent binary instrumentation checks, installed-output reference
graphs, native comparison automation, per-build memory accounting, and automatic
test-suite name extraction remain extensions. The persisted graph is the build
derivation graph. Downstream check claims follow only explicitly evaluated host
dependency edges; unknown/native edges cannot produce a positive claim.

## Following history

The Activity view starts with inventory counters, current work, and a campaign-wide timeline.
Builds and recipe evaluations have separate lanes, positioned by their recorded
admission and finish times. Gaps represent time without a recorded attempt; all
labels use UTC. Range controls zoom the timeline without changing the ledger's
search or filters. Select an interval or a ledger row to inspect its targets,
duration, result, observed build activities, and logs in a detail sheet. No batch
is opened automatically.

The ledger covers every attempt, newest first, with package/attempt search,
job/outcome filters, and pages of 24. Selecting an attempt, scrolling down the ledger, or opening an older page holds
its admission cursor. New attempts are counted without displacing the
page; **Latest** returns to the newest page. Timeline and current work
continue updating while history is held. Connection failures retain the last
view and report staleness. On phones, time, package names, duration, and result
fit each row without horizontal scrolling. Tap a row for the remaining facts and
logs. Scrolling down the page holds the admission cursor; changing ledger pages
returns to the first row under the sticky filters.

History uses facts attached to the original attempt. Observed build counts
include dependencies and are not success counts. Successful check counts come
from persisted test evidence, not a stopped activity or a configured check flag.
A failed batch can contain successful builds and checks. A completed evaluation
worker can contain individual evaluation refusals. Current inventory status is
shown separately; later realization or retry cannot change a historical batch's
result. There is no reconstructed per-package success curve: the first runner
did not persist complete output-availability snapshots at every batch boundary.

The web process queries SQLite read-only and never launches Nix for history.
`/api/history` returns a bounded ledger page and overview; `/api/history/attempt`
returns one campaign-scoped record and up to 100 observed activities. Above 400
visible attempts, the timeline aggregates occupancy into 160 time intervals
instead of silently dropping older work. A long attempt can touch multiple
intervals, so occupancy counts must not be summed. Shorter ranges expose
individual attempts again. No controller restart or database migration is
required for this view.

## Reacting to failures

While working on the experiment, inspect new failures and their explaining
dependency chains. Prefer small fixes with a clear cause, especially shared
dependencies. Record larger investigations in [the triage ledger](experiment-triage.md)
with the original derivation and evidence before moving on. A failure in one
dependency can block many selected roots; those roots are not independent
compiler failures.

Keep the first campaign's source and observations immutable. Validate recipe
changes with separate, bounded builds from a committed follow-up revision,
recording old and new derivations. Compare their input closures before building
to catch unintended compiler/runtime rebuilds. During the sweep, use one job
and two cores for these probes; daemon builds remain under the installed cgroup
ceiling. Passing a modified recipe does not change the original campaign's
result. Include fixes in a subsequent campaign when testing their wider effects.

Retain upstream tests. A missing test tool, missing link dependency, evaluator
policy refusal, unsupported language dependency, safety trap, and resource limit
are different findings. Do not turn a failure into success by disabling its
checks, and do not retry a deterministic failure without a relevant change.
Use `retry` for a changed external condition on the same recipe; a changed recipe
requires a new source revision. This is an operator workflow, not an unattended
patching or retry loop.

## Verification recorded on 2026-09-13

- The frozen 13,772-attribute inventory imported paused from commit `b14a53e`.
  Twelve real recipes planned: bzip2, gdbm, hello, libffi, Lua, Perl, Python,
  Ruby, SQLite, Tcl, xz and zlib. No Fil-C package build was admitted.
- A synthetic native batch ran through the installed attempt template. The
  good package passed `checkPhase`; the deliberately bad library failed in
  `configurePhase`; its two dependents were blocked. The raw logger fixture is
  `tests/experiment-fixtures/nix-2.32.1-partial-batch.jsonl`.
- Restarting the real controller during the 25-second build preserved the
  attempt's PID and execution; its terminal result was recovered afterward.
  Its builder PID was observed in the daemon's workload
  cgroup, with the expected CPU affinity.
- Cancelling a 90-second synthetic build stopped its builder and child process.
  A separate two-second timeout campaign ended inconclusive with `timeout`.
  These calibrations are paused and separate from the real input manifest.
- Unit tests exercise intent recovery, no duplicate launch, cancellation before
  launch, torn/unknown/oversized logs, atomic-offset replay, shared aliases and
  blockers, cached output evidence, OOM attribution, explicit retry, resource
  gating, read-only HTTP, escaping, traversal rejection and stale heartbeats.
- Chromium exercised the installed HTTP app: actual inventory counts, search,
  recipe details, desktop/mobile layouts, no horizontal mobile overflow, and
  disconnect/reconnect. Captures are in ignored `results/experiment-ui/`.

```sh
python3 -m unittest discover -s tests -p 'test_experiment*.py' -v
python3 tests/package-inventory.py
# With a local headless Chromium debugging port 9228:
node tests/experiment-browser.mjs https://nix.swa.sh results/experiment-ui
node tests/experiment-logs-browser.mjs https://nix.swa.sh results/experiment-log-ui
node tests/experiment-history-browser.mjs https://nix.swa.sh results/experiment-history-ui
```

`tests/experiment-calibration.py` prepares fresh native fixtures with the
controller stopped and queues one bounded attempt; it requires the installed
units and resource policy before execution. It deliberately does not modify the
main inventory. Adapt its state/pinned-Nixpkgs arguments for another host.

## Excluding Linux kernels

Linux kernel images are outside this userspace experiment. Inventory policy 2
recognizes the actual kernel build flags and the overridden metadata location of
hardened kernels (`pkgs/top-level/linux-kernels.nix`). A `linux` substring alone
is not an exclusion: kernel headers, Linux-PAM, linuxptp, and similar userspace
packages remain eligible.

Planning records a separate derivation `exclusion` when it encounters the kernel
builder's `vmlinux` and `KBUILD_BUILD_VERSION` flags, including renamed kernels
and dependencies. Excluded roots and queued consumers are not admitted. Manual
build and retry commands also check the recorded dependency graph. This is a
conservative scope filter: a dependency on an excluded kernel is sufficient to
refuse new work, including when outputs happen to be cached.

For an older campaign, pause admission, cancel a batch containing kernels, then
apply the scope correction through the controller:

```sh
sudo /opt/filnix-experiment/bin/filnix-experiment cancel ATTEMPT
sudo /opt/filnix-experiment/bin/filnix-experiment exclude-kernels CAMPAIGN --attempt ATTEMPT
sudo /opt/filnix-experiment/bin/filnix-experiment run CAMPAIGN
```

Wait for cancellation to reconcile before invoking `exclude-kernels`. The command
requires a paused campaign and a finished cancelled build. It inspects existing
Linux-named derivations without building, reclassifies old inventory metadata,
and records a `kernels-excluded` event. Without `--attempt`, it only applies the
scope correction. For an attached cancelled batch, the displayed outcome becomes
**Kernel excluded**, retaining `worker_reason=cancelled` and the explanation.
Original `spec.json`, `exit.json`, and logs remain unchanged. Only that batch's
nonexcluded candidates left inconclusive by cancellation are explicitly requeued;
older interruptions remain held. Independent active workers continue running.

The original manifest and selection evidence remain frozen. Excluded candidates
stay inspectable through the package filter and are counted separately from
compatibility failures. Existing output availability and check records are kept;
excluded kernel outputs no longer count as eligible package successes. Database
schema 2 adds the independent exclusion field; the controller migrates schema 1
transactionally. Older controllers do not support the new schema.
