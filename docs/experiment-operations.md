# Operating the Filnix experiment

The dashboard is **https://nix.swa.sh/**. It is read-only. The active campaign is
**Fil-C b6dd634 · shared cancellation** (`3eaf2f72-7c12-4bf2-9934-9646ea9dab4d`),
started on 2026-09-14 at source `f07cf499adf233bb7dd85ea95e1b63f63a89776a`.
It repeats the same 13,772 selected attributes with the updated shared toolchain.
The first inventory, started on 2026-09-13, has completed its queue and remains
paused with all history preserved. Synthetic native runner calibrations remain
separate campaigns in the selector.

The active campaign uses 32 roots per batch, a 256-derivation ready buffer and
two build lanes: four jobs in total with seven requested cores per job. The
30-CPU workload slice retains a 20% memory reserve for the host. Both binary
cache publishers discover the active campaign; outstanding uploads from the
first campaign retain their receipts and continue to drain.

## Dashboard layout

The live viewer uses Tagflow, htmx 4 and Tailwind. See
[dashboard architecture](dashboard-architecture.md) for the resource contracts,
module responsibilities and development checks.

**Activity** shows counts, current work, a Build/Plan timeline and recent batches.
**Packages** shows the complete selected result set with no pagination or virtual
rows: names, versions, descriptions and results. Built is muted; Tested is stronger.
Use browser Find. Source links, diagnostics, test evidence and dependencies are in
the package's own page. The options menu contains refresh and CSV export.
**Batches** holds the timing data, with all attempts, outcome/type filters, search
and duration/date sorting. **Dependencies** follows a current build, or a pinned
package, with inputs and consumers. Built inputs can be expanded.

The campaign menu retains the first campaign and calibration histories. Canonical
page URLs, GET filters and Back/Forward work with ordinary browser navigation.
Old query links and view fragments redirect into the new pages. Only package
column headings remain sticky. All timestamps use UTC.

Inventories and batch lists stay still while reading. Explicit refresh loads a new
snapshot. Current work and dependency states refresh independently using HTML;
SSE supplies revision hints with polling recovery. Paused or completed history
remains browsable. A completed batch may contain failed individual recipes; a
batch with errors may contain successful builds and successful checks.

**Built** counts selected attributes whose required outputs were observed.
**Tested** counts distinct selected derivations with successful check evidence in
this campaign. It is not a count of every dependency or individual test case.
Aliases remain separate package rows. No package or batch timing is shown in the
package list; batch wall time includes preparation, dependencies and all roots.

**Live log** follows a current build and moves to the next batch at EOF. An
individual batch or package link pins its own log. Source selection isolates a
build. Scrolling upward or pressing Pause holds the reading position; Resume
returns to the current tail. Earlier output, wrapping, 12/14/16 px font size,
window search and raw download are available. The reader is bounded to 2,000
records, with raw-byte cursors and retry after failed or slow requests. The raw
captured evidence is unchanged.

Evaluation errors show Nix's final diagnostic; full observations are available in
package details. The planner's 4 GiB address-space limit produces a heap-expansion
warning even for successful evaluation of `1`; that warning alone does not prove
an out-of-memory failure. Inspect the terminal error before changing limits.

## Binary caches

Successful campaign outputs and their reference closures are published in the
background to Cachix and <https://nix.swa.sh/cache>. Each cache has independent
receipts and retries; upload failures do not change build outcomes. See
[binary cache operations](binary-caches.md) for client configuration, status,
installation, and restore verification.

## Responsibilities

- `experiment/model.py`: SQLite schema, campaign import, graph queries, events.
- `experiment/nix.py`: installed Nix JSON adapter, store validity, cgroup readings.
- `experiment/controller.py`: single writer, queue admission, recovery, local commands.
- `experiment/attempt.py`: independent unit, bounded evaluation/build processes,
  raw logs and atomic completion record. Never writes the database.
- `experiment/dashboard/`: read-only Tagflow/Starlette HTML viewer on Hypercorn.
- `experiment/web.py`: compatibility JSON API, raw logs and health checks.
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

The full catalog, including candidate IDs, is at `/api/packages?campaign=CAMPAIGN`.
The older bounded `/api/snapshot` supports `campaign`, `q`, `state`, and `offset` parameters. The exact input manifest is at
`/api/manifest?campaign=CAMPAIGN`. Package details are at `/api/package?id=ID`;
`/api/derivation` expands a dependency, its role annotations, and paginated
selected dependents. Logs use bounded byte offsets. `/api/events?after=SEQ`
exposes a durable event cursor. The browser refreshes status every
five seconds and bounded log chunks every 1.5 seconds. The package catalog refreshes
only on request.

`plan` accepts up to 64 IDs, uses no IFD and no builds, and records errors per
candidate. `build-once` respects the configured batch size in a paused campaign;
it checks containment and budgets and leaves the campaign paused afterward.
`pause` drains both active lanes. `cancel` pauses its campaign, terminates only
the named attempt, and reconciles its eventual exit; the other lane drains. It never stops the shared daemon.
`retry` requeues an inconclusive or failed candidate. A shared failed dependency
can be cleared with `retry-derivation`; other known blockers stay in force.

For an explicit follow-up to **evaluation or build failures**, plan only the selected IDs
from a committed revision:

```sh
filnix-experiment plan CAMPAIGN ID [ID ...] --repo /path/to/filnix --revision COMMIT
```

The CLI archives that commit into the store, excluding worktree changes. The
controller roots it and records the revision, source, and previous candidate
observations in the new plan's immutable spec. Successful evaluations enter the
ordinary build queue; the campaign's mode and resource limits still control
admission. No other failed evaluation is reset. A queued, failed, blocked, or inconclusive
recipe can be replaced; its old recipe and result remain in the new attempt's
spec. The selected candidate is detached from that recipe while planning, so a
restart cannot accidentally requeue the old build. Successful, excluded,
and active inputs (including dependencies of active builds) are refused.
The original manifest, campaign source, attempt records,
and raw logs stay unchanged. The planner lane must be free, as for ordinary `plan`.

Each resulting recipe records its plan attempt and source revision. Build batches
realize those fixed derivations without evaluating the flake again; `recipe_sources`
in their specs records the source of every root, including mixed-revision batches.
The package catalog prefers the evaluated version while preserving the frozen
inventory metadata. This is an explicit per-package follow-up, not a campaign-wide
source update or an automatic downstream retry.

For a larger cohort of **failed evaluations**, enqueue the complete selection:

```sh
filnix-experiment queue-replan CAMPAIGN ID [ID ...] --repo /path/to/filnix --revision COMMIT
```

Version 0.12.4 persists these requests in schema 4's `replans` table. Only inactive
evaluation failures without recipes are accepted, up to 8,192 distinct IDs per
request. Validation is atomic; repeating a still-pending ID at the same source
and revision does not duplicate it. `status` includes `pending_replans` per campaign.
The `replan-queued` event retains the full selection, request UUID and frozen source.

The queue survives controller restarts and waits while its campaign is paused.
Normal admission takes up to 32 IDs from one request, subject to resource limits,
the single planner lane and the ready-buffer budget. Follow-ups take priority over
the original unplanned inventory. Previous observations remain visible until an
attempt is admitted; the attempt then preserves them along with the request's
provenance. Intent creation and queue consumption commit together. New evaluation
failures are recorded once and require another explicit request to try again.

An explicit `plan --revision` can supersede a queued request for the same ID; its
attempt records both the pending request and the actual revision. Exclusions or
other intervening outcomes are skipped with a `replan-skipped` event. The queue
does not change the campaign's original source, enable a paused campaign, or reset
any other failures. Existing build workers keep running during the controller upgrade.

**`filnix-experiment run CAMPAIGN` enables the continuing experiment.** Newly
imported campaigns never become running just because services restart. Ordering
remains deterministic by attribute name, deduplicated by derivation. Cost/fanout
scheduling is a future policy change.

## Keeping builds supplied

New campaigns imported with runner 0.12.5 use CPUs `1-15,17-31` and four
build jobs with seven requested cores each. With two build lanes, each client
gets two jobs. That reserves 28 of the 30 workload CPUs for builds and leaves
room for the planner; CPUs 0 and 16, one physical core, remain outside the
workload slice. The aggregate memory high/max limits remain 70%/80%.
Existing campaigns retain their frozen policy and need not be rewritten.


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

Lookahead must also be nonzero to admit overlapping work. New 0.12.5 campaigns give each client
two jobs with seven requested cores per job: four jobs in total. Admission
reserves each active client's full `max_jobs * cores` request, using its immutable
spec, against the 30 allowed workload CPUs. It never treats momentarily idle jobs
as spare reservations. Historical 28-CPU policies keep their original limits; while an older
four-job/six-core batch drains, the second lane gets only one job with four cores. Each new attempt records its effective
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
| CPUs                        | `1-15,17-31`; one complete physical core reserved                        |
| MemoryHigh / MemoryMax      | 70% / 80%; observed maximum 107,296,374,784 bytes                         |
| Swap                        | 2 GiB                                                                     |
| Nix admission               | New campaign policy: four jobs, seven requested cores per job; up to two clients |
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

Activity shows recent attempts; Batches shows the entire filtered ledger. Both
hold their snapshot until refresh. Select a batch for requested roots, observed
activities, original result and logs. These facts belong to the attempt; later
realization or retry does not rewrite its historical outcome. Successful checks
require persisted evidence, not a stopped activity or a recipe flag.

The compatibility `/api/history`, `/api/history/attempt` and `/api/batches` endpoints
remain available. The HTML viewer does not fetch them or launch Nix from requests.

## Reacting to failures

While working on the experiment, inspect new failures and their explaining
dependency chains. Prefer small fixes with a clear cause, especially shared
dependencies. Record larger investigations in [the triage ledger](experiment-triage.md)
with the original derivation and evidence before moving on. A failure in one
dependency can block many selected roots; those roots are not independent
compiler failures.

Keep the first campaign's default source and historical observations immutable.
Use targeted revision planning above for explicit retries of evaluation failures.
Otherwise validate recipe changes with separate, bounded builds from a committed
follow-up revision,
recording old and new derivations. Compare their input closures before building
to catch unintended compiler/runtime rebuilds. During the sweep, use one job
and two cores for these probes; daemon builds remain under the installed cgroup
ceiling. Passing a modified recipe does not rewrite the original attempt's
result. Include fixes in a subsequent campaign when testing their wider effects.

Retain upstream tests. A missing test tool, missing link dependency, evaluator
policy refusal, unsupported language dependency, safety trap, and resource limit
are different findings. Do not turn a failure into success by disabling its
checks, and do not retry a deterministic failure without a relevant change.
Use `retry` for a changed external condition on the same recipe; a changed recipe
requires an explicitly recorded new source revision. This is an operator workflow, not an unattended
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
# Current viewer checks and build instructions: docs/dashboard-architecture.md
node tests/dashboard-browser.mjs https://nix.swa.sh results/tagflow
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

## Download-progress telemetry

Runner 0.12.3 omits Nix `result` records of type 105 containing four integer
progress counters before applying the retained-log byte budget. Download-heavy
batches emitted roughly 1.5 million such records in half a minute, filling the
128 MiB cap before useful compilation. The viewer does not consume these
counters. Build starts (also numbered 105, but with action `start`), phases,
compiler output, errors, stops, malformed input, and partial records remain in
order. Attempt results record the omitted record and byte counts. Old logs are
preserved. Real output still has the same byte limit.

This change applies to newly launched workers. Retry affected `inconclusive`
roots explicitly after upgrading; restarting the controller does not replace
an already running worker.
