# Operating the Filnix experiment

The dashboard is **https://nix.swa.sh/**. It is read-only. The main campaign contains
13,772 selected attributes and was started on 2026-09-13. It continues planning
and building in bounded batches. Synthetic native runner calibrations are
separate campaigns, clearly labeled in the campaign selector.

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
candidate. `build-once` admits at most eight unique roots in a paused campaign;
it checks containment and budgets and leaves the campaign paused afterward.
`pause` drains an active attempt. `cancel` also pauses its campaign, requests
termination, and reconciles the eventual exit. It never stops the shared daemon.
`retry` requeues an inconclusive or failed candidate. A shared failed dependency
can be cleared with `retry-derivation`; other known blockers stay in force.

**`filnix-experiment run CAMPAIGN` enables the continuing experiment.** It builds
queued roots in batches, then plans another 32 unplanned inputs when the queue is
empty. This command has been issued for the main inventory. Newly
imported campaigns never become running just because services restart. Automatic
ordering is initially deterministic by attribute name. Cost/fanout scheduling is
a future policy change, not an undocumented heuristic in this release.

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

| Setting | Installed value |
| --- | --- |
| CPUs | `2-15,18-31`; two complete physical cores reserved |
| MemoryHigh / MemoryMax | 70% / 80%; observed maximum 107,296,374,784 bytes |
| Swap | 2 GiB |
| Nix admission | One client batch, four jobs, six requested cores per job |
| Build wall / silence budget | 7,200 / 900 seconds |
| Evaluator | Two CPUs, 4 GiB address space, 90 seconds per candidate |
| Attempt service | 8 GiB client/evaluator memory, 1,024 tasks, three-hour backstop |
| Log budgets | 128 MiB per attempt; 20 GiB retained logs |
| Disk reserve | Stop admission below 50 GiB free |
| Scratch | `/var/tmp/filnix-build` for daemon, `/var/tmp/filnix-eval` for evaluation |

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
```

`tests/experiment-calibration.py` prepares fresh native fixtures with the
controller stopped and queues one bounded attempt; it requires the installed
units and resource policy before execution. It deliberately does not modify the
main inventory. Adapt its state/pinned-Nixpkgs arguments for another host.
