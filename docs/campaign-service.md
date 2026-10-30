# The campaign service

nix.swa.sh becomes the one place where filnix's survey-style builds run:
port campaigns, the nanofil package survey, compiler-speed benchmarks and
lists of flake outputs. Each is a **campaign**, queued, run, recorded and
shown by one long-running service, so that every root's timing, machine,
outcome and complete log stay durable and visible. An admin CLI on swa
controls it; the public web stays read-only.

This replaces the one-campaign-per-database `cohort` mode of
[experiments/campaign-next](../experiments/campaign-next/README.md). Its
Nix worker, event journal, projections, viewer and Parquet export are
kept; what changes is everything around a single recording.

## The shared shape

Every survey-like tool in the repository does the same four things:

| Tool | Roots | How it builds | What it keeps |
| --- | --- | --- | --- |
| port campaigns (`world.nix`) | expected / world / ports | runner, one root at a time | DuckDB recording |
| nanofil survey (`run.py`) | `ref.X`, `nf.X` per C port | `nix build --keep-going` | `/tmp` log, `nix log`, TSV |
| `scripts/nanofil-checks` | `checks.*.nanofil*` | `nix build --keep-going` | a log file, pass/FAIL |
| `ci-outputs.txt`, `ship-outputs.txt` | flake attribute paths | `nix build`, ci-cache-check | nothing |
| gem scripts | native gems | one `nix build` per gem | per-gem log files |
| retired Python controller | port campaigns | its own scheduler | SQLite (historical) |

1. freeze a list of named derivations at a source revision,
2. build each with a policy (jobs, cores, builders, time limits),
3. record what happened to each (outcome, time, log),
4. reduce the records to a report (counts, a table, a TSV).

The service owns steps 2 and 3 for all of them. Step 1 is a **manifest
producer** per kind, versioned with the source it freezes; step 4 is a
report that reads the service's results rather than `nix log` or `/tmp`.

## Campaigns

A campaign is:

- a **frozen manifest**: a JSON store file that references the root
  derivations (so one GC root keeps them), with `id`, `name`, `kind`,
  `source`, `revision`, `options`, and `roots`. A root is
  `{name, drv, tags, requires, meta}`: `tags` such as `ref`, `nf`, `slow`;
  `requires` names roots that must succeed first (a survey's `nf.X`
  requires `ref.X`, as run.py only tried nanofil where filcc built);
  `meta` is passed through to reports (version, doCheck, C/C++ counts).
  A manifest may also carry `excluded` and `set_aside` rows: names the
  producer considered and did not admit, with reasons.
- a **policy**: `parallel_roots` (roots admitted at once), `max_jobs`,
  `cores`, `builders` (`default` or `local`), `max_silent_time`,
  `build_timeout` (Nix's own `timeout`, so a timed-out build is a typed
  `TimedOut` result), `root_timeout` (the client's deadline, a
  backstop), `budget` (seconds of running time), `rebuild` (rebuild
  roots that are already valid, for benchmarks), `graph` (`full` or
  `direct` dependency discovery), `retry_infrastructure` (automatic new
  attempts after a worker or daemon error, never after a package
  failure), and `publish` (whether successful outputs feed the caches).
  `max_jobs`, `cores`, `builders`, `max_silent_time` and `build_timeout`
  reach Nix as the worker's per-client `NIX_CONFIG`, as the deployed
  runner already does; the daemon's shared configuration and the remote
  builders' own limits are untouched.
- a **priority** and a **state**: `queued`, `running`, `paused`,
  `finished`, `cancelled`, or `historical` for imported recordings.

### Scheduling

One campaign runs at a time: the running one, else the queued one with
the highest priority, oldest first. Priority orders the queue; it does
not preempt (pause the running campaign to let another start). Within
the running campaign, up to `parallel_roots` lanes each admit the next
**admissible** root in manifest order: pending, with every `requires`
root settled. A root whose requirement failed is settled as `skipped`
without a build. Nix schedules each root's dependency graph as before.

Timing is only comparable within one machine and one load. Every attempt
records the machine that built the root (local swa, igloo or chapel), the
1-minute load average and the number of roots in flight when it was
admitted. A benchmark campaign uses `builders = local`,
`parallel_roots = 1`, `max_jobs = 1` and `rebuild`, so its times mean
something; a survey favours throughput.

### Attempts, pause, cancel, retry, restart

Each admission of a root is an **attempt**: a fresh journal run, never an
overwrite. The root's result is its latest attempt.

- **pause** stops admission; roots in flight finish and are recorded.
  **resume** queues the campaign again.
- **cancel** stops admission and interrupts roots in flight (their
  attempts end `cancelled`); unadmitted roots stay unattempted.
- **retry** makes chosen roots pending again (by name, or every root
  whose latest outcome is failed / timed out / cancelled / incomplete)
  and queues a finished or cancelled campaign.
- A **service stop** interrupts roots in flight; they end `cancelled`
  with `service-stopping` and are pending again when it starts, as new
  attempts. An attempt the service did not see end (a crash) is closed as
  `incomplete` at startup and likewise made pending. A running campaign
  continues with its remaining roots after a restart.

This changes the old runner's rule that a restart never resumes. The old
rule protected a single recording from silently mixing two runs of a
root; attempts keep both runs, so resuming no longer hides anything.
Package failures are never retried automatically.

## Storage

- `catalog.duckdb`: `campaigns` (manifest, policy, priority, state,
  times, recording path), `roots` (name, drv, tags, requires, meta,
  pending/running/settled) and `attempts` (run, times, machine, load,
  outcome, native status, failing derivation and phase, first error,
  analysis, outputs).
- one **recording** per campaign, `campaigns/ID/recording.duckdb`, in the
  existing schema-2 journal format.

The suggestion was one database for all campaigns. The code argues for a
small catalog plus a recording per campaign instead: a port campaign's
recording is 0.5–4 GB (the full static graph of every root), DuckDB
does not return space after deletes, and opening a recording rebuilds its
overview cache by scanning its journal, so one ever-growing database
would make startup and retention worse with every campaign. Per-campaign
files keep a finished campaign archivable as a file, let old recordings
be opened only when someone looks at them, and are already the format of
every existing recording. Cross-campaign questions (how long did
`nf.zlib` take at each revision?) are answered by `attempts`, which
holds every root of every campaign, including imported ones.

Writable recordings and the catalog live on one DuckDB thread, as now;
reading recordings of campaigns that are not running uses a second
thread, at most two open at once, so opening a 4 GB archive for a viewer
never delays capture of a running build.

### Existing recordings

Nothing is moved or rewritten. `register` adds an existing recording to
the catalog as a `historical` campaign: it opens the file read-only,
reads its manifest, and fills `attempts` from its run summaries with the
same analysis as live attempts. Registering a file whose content is
identical to an already registered one records it as a duplicate (hidden
from the default list). On swa that is seven distinct recordings: the
pilot, the 82-landmark world (seven identical `before-*` snapshots), the
first port campaign (two identical archives), the PHP campaign, the 0.687
campaign, the first expected campaign, and the current expected campaign
at `ce1ea54`. Their GC roots are kept as they are.

## Results per root

At the end of every attempt the service derives, from its own journal:

- `wall` (request to result) and `build` (the root derivation's own
  build activity, excluding waiting for dependencies);
- `machine` (the build activity's machine; empty is local);
- `outcome` (built, substituted, already-valid, failed, timed-out,
  cancelled, worker-error, skipped, incomplete) and Nix's native status
  (`PermanentFailure`, `TimedOut`, `DependencyFailed`, …);
- the failing derivation, from Nix's error, and its last phase;
- the first error line, chosen with the survey's preference order
  (nanofil's own message, the wrapper's refusal, configure's verdict, a
  compiler or make error, …), from that derivation's log after the start
  of its last phase;
- the `nanofil-survey: N objects, M C++, K fallbacks` line, when present.

The full logs stay in the recording; the web console and `export` reach
them.

## Kinds and manifest producers

Producers run in the CLI as the admin user, from the frozen source, never
inside the service. The source is `github:mbrock/filnix/REV`; `--rev`
defaults to `origin/main` resolved to a commit.

- `world --scope expected|world|ports`: `experiments/campaign-next/world.nix`.
- `nanofil-survey --opt plain|-O|--vectors [--select default|slow|all]`:
  `nanofil/survey/run.py manifest` evaluates, classifies (C vs C++ by
  source file names, LLVM/Rust/Go dependencies) and emits `ref.X` and
  `nf.X` roots, with the set-aside rows. The revision must contain the
  producer.
- `bench`: a nanofil survey of the `slow` packages with the benchmark
  policy (local, one root, one job, rebuild, long timeouts).
- `attrs --file scripts/ci-outputs.txt | --attr A …`, and
  `checks --prefix nanofil`: flake attribute paths, the shape of
  `ci-outputs.txt`, `ship-outputs.txt` and `scripts/nanofil-checks`.

The gem scripts and the retired Python controller are not migrated: the
gems are not flake attributes yet, and the controller's SQLite records are
a different schema kept for history (docs/experiment-*.md).

### Slow packages

`nanofil/survey/default.nix` lists packages tagged `slow`, with reasons:
`emacs30` (mostly Lisp byte-compilation; hits the 90-minute limit) and
`libgcrypt` (its tests time out in plain mode). The default survey leaves
them out and reports them as set aside (`slow`); the `bench` kind runs
exactly them. A package goes on the list when its builds are dominated by
something other than C compilation or regularly need more than the
survey's limit.

### Reports

`run.py report CAMPAIGN [--write]` reads `campaignctl results CAMPAIGN
--json` (the service's attempts plus the manifest's set-aside rows) and
writes `survey.tsv` / `survey-OPT.tsv` and the docs/survey.md table, with
two new columns, `ref_s` and `nf_s` (build seconds), and `nf_machine`.
The cause mapping stays in run.py. `run.py` no longer builds anything.

## Admin interface

The service listens on a Unix socket, `/run/filnix-campaign/admin.sock`,
in a directory only the service user (`mbrock`) and root can enter. It
speaks HTTP with JSON bodies, so `curl --unix-socket` works too.
`campaignctl` (installed beside the service, `--json` on every command)
wraps it:

```sh
campaignctl list [--all]
campaignctl status
campaignctl show ID
campaignctl results ID
campaignctl submit nanofil-survey --opt plain [--rev REV] [--priority N] [--set parallel_roots=4 ...]
campaignctl submit world --scope expected
campaignctl submit bench
campaignctl submit attrs --file scripts/ci-outputs.txt
campaignctl pause|resume|cancel ID
campaignctl priority ID N
campaignctl retry ID [--root NAME ...] [--outcome failed ...]
campaignctl export ID DIRECTORY
campaignctl register PATH [--manifest M] [--label L] [--publish]
```

`submit` roots the frozen manifest under the service's state directory
(an indirect GC root) before queueing it.

## Web

- `/` lists campaigns: kind, revision, options, state, roots, succeeded /
  failed / timed out / pending, start and wall time.
- `/c/ID/` is the existing viewer scoped to one campaign: overview,
  filters, live log, dependency graph. Its links are relative, so it is
  unchanged under the prefix.
- `/c/ID/survey` shows a survey's packages with `ref` and `nf` side by
  side: outcome, build time, machine, nanofil counts, first error.
- `/api/campaigns`, `/c/ID/api/results` and the existing `/c/ID/api/*`
  are read-only JSON. Old links (`/?run=…`) redirect to their campaign.
- `/api/outputs` lists verified outputs of successful attempts of
  campaigns whose policy publishes, as the cache publishers expect. World
  and attrs campaigns publish; surveys and benchmarks do not, so
  nanofil-built packages never reach the public caches. Of the imported
  recordings, only the current expected campaign publishes, which keeps
  the feed what it is today.

The public listener answers only GET and HEAD. Build output is public, as
before: only public sources go into campaigns.

## Deployment

`filnix-campaign.service` replaces `filnix-v2.service`: same user, port
8778 and Caddy upstream, state in `/var/lib/filnix-campaign`, existing
recordings read in place from `/var/lib/filnix-v2`, `RuntimeDirectory`
for the socket, and a 6 GiB memory limit for one writer and two readers.
The application is installed at `/opt/filnix-campaign` and rooted under
`/nix/var/nix/gcroots`. The old unit is stopped and disabled, not
deleted.
