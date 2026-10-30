# Native Fil-C port campaigns

The public, read-only dashboard is <https://nix.swa.sh/>. `/v2/` URLs redirect
to it. The native C++/NXT runner owns its DuckDB recording and listens on
loopback port 8778. `filnix-campaign.service` runs the campaign service
selected by `/opt/filnix-campaign`; state lives under `/var/lib/filnix-campaign`
([the campaign service](campaign-service.md)). The recordings of the former
`filnix-v2.service` stay in `/var/lib/filnix-v2` and are listed as historical
campaigns.

See [campaign purpose and selection policy](campaigns.md) before choosing a
scope. The normal per-revision campaign is `expected`; `ports` is exploration.

## Toolchain rollout workflow

1. Build the matched compiler/runtime and run focused semantic regressions
   for the upstream changes. Run the affected package smoke tests. Do not
   mix compiler and runtime ABIs or waive a safety regression to ship faster.
2. Run `scripts/ship`. Its cache gate is `scripts/ship-outputs.txt`: the
   compiler and the curated `baseline`, with their complete closures and
   baseline smoke tests. GTK, Emacs and distribution tarballs are not in
   this gate. `--no-publish` explicitly bypasses the cache guarantee and is
   not the normal toolchain rollout path.
3. Submit an expected campaign at the pushed revision:
   `campaignctl submit --rev REV world --scope expected`. The manifest starts with the wider
   `scripts/ci-outputs.txt` list, including the foundation and distribution
   artifacts, then the explicit `ports/expected.nix` compatibility list. Keep the
   previous recording and manifest together for comparison and rollback.
4. Watch the public campaign and both publishers. Report failures and
   unattempted roots separately from successful builds. A foundation-ready
   push is not a claim that the broader campaign passed.
5. Once the needed distribution artifacts are cached, rerun their CI job.
   A tagged Filnix release is a separate, explicitly requested operation;
   its full distribution cache gate is unchanged.

The campaign executes package builds, including each package's enabled
checks. It does not automatically execute every `flake.nix` check: those
additional integration/regression checks remain available for targeted or
broader validation, without delaying an urgent foundation-ready update.

The expected selection starts with the curated baseline packages and the 82
world landmarks, all successful in the `ports-a324a843` recording. It is an
independent list, not dynamically expanded by shell composition or new port
declarations. Unexpected selected evaluation failures block freezing.

For exploration, explicitly freeze `scope = "ports"`: the union of
`shells/world-packages.nix` and active `ports.nix` declarations. The original
full port launch admitted 300 roots; the later 0.687 recording admitted 327.
Counts are historical: read the new manifest rather than assuming either count.
Evaluation exclusions never count as successes. Broken-port reasons are retained
where known; unresolved evaluation errors remain labeled as such. PipeWire and
its seven observed blocked consumers are recorded even outside the expected
selection (`selected = false`), without expanding the attempted denominator.

Each root asks Nix to realise its complete dependency graph, using existing
valid outputs and substitutions where available. This is a build of the latest
package definitions, not a forced rebuild of unchanged outputs. Roots run in
distribution-priority order, then the chosen package-list order.
The service allows two
local jobs with four cores, respects configured remote builders, admits work
for at most 24 hours, and allows two hours per root and 30 minutes of silence.
A failed or timed-out root does not stop later roots. An exhausted overall
budget leaves remaining roots visibly unattempted.

## Freeze and launch

```sh
campaignctl submit --rev REV world --scope expected   # or --scope ports
campaignctl list
campaignctl show ID
```

`submit` evaluates `experiments/campaign-next/world.nix` from
`github:mbrock/filnix/REV` as the caller, without realising packages, and
the service roots the manifest beside the campaign and queues it. Review
`roots` and `excluded` with `campaignctl --json show ID` or the manifest.
The manifest retains the frozen source and derivations. Campaigns run one at
a time by priority; a new campaign no longer needs a fresh database, a
stopped service or an archive step, and the previous campaigns stay listed.
Transient failures get a new attempt with `campaignctl retry ID`;
recipe/toolchain changes need a new campaign at a new revision.

Deploy a new service build with `nix build path:./experiments/campaign-next`,
point `/opt/filnix-campaign` at it, root it under `/nix/var/nix/gcroots`, and
restart the unit: roots in flight end as `service-stopping` and run again
as new attempts. The unit is `experiments/campaign-next/deploy/filnix-campaign.service`;
Caddy's `reverse_proxy 127.0.0.1:8778` route is unchanged.

## Automatic cache publication

The independent `filnix-cache@local.timer` and `filnix-cache@cachix.timer` poll
successful outputs about once per minute. `/etc/filnix-cache/config.json` selects
the native recording with:

```json
"native_outputs_url": "http://127.0.0.1:8778/api/outputs"
```

The read-only feed includes verified output paths only after normal worker
completion and a committed successful root summary. Failed, interrupted and
incomplete roots do not qualify. Nix/Cachix copy complete reference closures;
successful dependencies of failed roots are not independently discovered here.
The publisher retains its previous durable destination receipts, retries,
credentials and signing keys. Pending old uploads continue to drain. Source
campaigns share the same feed URL and do not require new receipt databases.

Unrelated ad hoc `nix build` invocations are not automatically watched. Use
`filnix-publish-cache TARGET --extra-root OUTPUT` with the publisher service
identity and, for Cachix, its systemd-loaded credential. The OpenSSH 10.5p1
refresh and the other verified ports were explicitly published to both caches
before this campaign. See [binary caches](binary-caches.md).

## Observe and recover

```sh
curl -fsS https://nix.swa.sh/healthz
curl -fsS http://127.0.0.1:8778/api/outputs
curl -fsS http://127.0.0.1:8778/api/resources
campaignctl status
systemctl show filnix-campaign -p MemoryCurrent -p MemoryPeak
systemctl status filnix-campaign
journalctl -u filnix-campaign -f
sudo /opt/filnix-cache/bin/filnix-publish-cache local --status
sudo /opt/filnix-cache/bin/filnix-publish-cache cachix --status
```

`/api/state` exposes the cohort counts, frozen revision, exclusions and current
session; the dashboard supports filters and 100-row pages. Its name/scope now
distinguishes expected compatibility from exploratory ports. Exclusion disclosure
is currently in the API/manifest, not the main outcome arithmetic.
An output receipt means upload completion, not continuous remote verification
or test success. Compare cache NAR hashes/sizes/references and restore into a
fresh store when testing actual cache availability.

The service sets a running campaign's DuckDB budget to 1 GiB (512 MiB for each
of at most two archives open for viewing) and two threads. Its 6 GiB service
allowance also covers the workers and allocations outside DuckDB's budgets. New recordings use schema 2 without large raw-journal
indexes. Schema 1 recordings remain readable, using a temporary overview cache
rebuilt when a recording is opened. A restart continues a running campaign;
attempts it interrupted are recorded and run again as new attempts.

The rollout passed the native dataset and real-build integration checks,
including successful-root publication and restart behavior. The dataset test
covers incomplete results, output validity/deduplication and a 300-root view.
Publisher tests cover the new feed's validation and switching from SQLite
without losing receipts. The existing browser suite was exercised through the
public prefix and the canonical root before launching the fresh campaign.

## Distributed builds: nanofil checks and the ports survey

swa's nix-daemon sends builds to the remote builders in `/etc/nix/machines`
(root-owned; earlier versions are kept beside it as `machines.before-*`):

| Builder | CPU | Jobs | Notes |
|---|---|---|---|
| swa (local) | Ryzen 9 7950X3D, 32 threads, 124 GB | `max-jobs = 32` | |
| igloo | i5-13500, 20 threads, 62 GB | 5 | |
| chapel | i7-10700K, 16 threads, 31 GB | 3 | sqlite -O peaks at about 2.3 GB per compile |
| squire | aarch64 | 1 | cannot build x86_64 Fil-C |

Jobs × `--cores` must not oversubscribe a builder. At 8 jobs × 8 cores,
igloo ran at load 38: nanofil's 8-thread atomic progtests went from 3 s to
26 s and hit their run timeout. Orbs cannot reach these builders, so run
the costly work from swa:

```sh
scripts/nanofil-checks                         # all nanofil* checks, pass/FAIL each
campaignctl submit checks --prefix nanofil     # the same, recorded as a campaign
campaignctl submit nanofil-survey --opt plain  # the survey (eight roots at a time)
```

A check that compares against a reference must run both sides in one
derivation whenever the result depends on the machine, because the
reference may have been built on a different builder (nanofil-bash's test
suite statuses do).

The old `run.py` survey twice lost the nix daemon mid-run (`error: Nix daemon
out of memory`, with no kernel OOM), failing every build still running. In
the service each root has its own daemon connection, and a worker error
gets a new attempt (`retry_infrastructure`), never a package failure. igloo and chapel set `max-silent-time = 900`,
and Nix does not forward a client's limit, so a nanofil compile that prints
nothing for 15 minutes fails there but not on swa.
