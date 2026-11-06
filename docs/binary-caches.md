# Publishing campaign builds

The campaign publishes successful outputs to two public caches:

- **Cachix:** `https://filc.cachix.org`, with standard dependencies also available
  from `https://cache.nixos.org`. Run `cachix use filc` to configure a client.
- **This server:** `https://nix.swa.sh/cache`, a signed, static Nix file cache
  served by the existing Caddy vhost. It includes complete reference closures.

The self-hosted public key is published at
<https://nix.swa.sh/cache/cache.pub>. Its current value is:

```text
nix.swa.sh-1:DgkPkGAie779HuF0oEkglCmDUoDGcK21mM2DT+0Fgj0=
```

To use it, add these settings to a client's `nix.conf`:

```ini
extra-substituters = https://nix.swa.sh/cache
extra-trusted-public-keys = nix.swa.sh-1:DgkPkGAie779HuF0oEkglCmDUoDGcK21mM2DT+0Fgj0=
```

Cachix and the local cache contain the experiment's actual outputs, including
the first campaign's private-libc profiles and subsequent shared-libc builds.
Cache presence establishes output
availability; it does not establish tests passed or comprehensive POSIX
cancellation support. Source revisions, compiler choices, profiles, and test
evidence remain in the campaign records.

Disk images and container tarballs (`scripts/swa-cache-outputs.txt`: the
NixOS qcow2 and AMI image, the `*-docker` archives) go to this server's cache
only. No machine substitutes them, and at gigabytes each they evicted the
toolchain and the NixOS closures from Cachix's free plan on 2026-11-06. Their
dependencies, the toplevels and packages, still go to Cachix. Release and CI
workflows add `https://nix.swa.sh/cache` as a substituter for them, and
`scripts/ci-cache-check.py` looks for those outputs there.

## Automatic publication

A receipt records only that a push once succeeded, and Cachix evicts paths
later (in November 2026 it had lost nearly every root older than a week).
So each Cachix run also checks narinfos. It checks the 50 least recently
checked published roots, and 800 paths of the closures of the current extra
roots (the newest of each name: the toolchain, the baseline from
`scripts/ship`, and the release toplevels from `scripts/release`), which
cover the ~1000 paths machines and CI substitute in two runs. A path that
neither Cachix nor cache.nixos.org has clears the receipt of its root, and
the normal queue pushes its closure again. Lost roots published more than a
week ago are only counted (`old_roots_lost`): re-sending all of them would
not fit the cache.

`filnix-cache@local.timer` and `filnix-cache@cachix.timer` independently run the
publisher, initially on activation and again one minute after each run finishes.
Each run discovers outputs from the configured campaign and submits at most
eight batches of 64 roots. Pending backfill continues on subsequent runs.

The canonical native campaign is selected with
`"native_outputs_url": "http://127.0.0.1:8778/api/outputs"` in
`/etc/filnix-cache/config.json`. The publisher queries the single database owner
over HTTP rather than opening the live DuckDB file. This feed includes only
verified outputs of complete successful root requests, with their full reference
closures copied by Nix/Cachix. It does not independently discover successful
dependencies of failed roots. Destination receipts, credentials, signing keys,
retry behavior, and timers are shared with the previous publisher deployment.

Legacy SQLite discovery reads the campaign database without writing it. It includes realized
selected packages and realized dependencies actually observed in that campaign,
including successful dependencies from a batch with errors. Merely starting a
build or entering a check phase does not qualify an output. Aliases and repeated
observations are deduplicated by store path. Each upload includes the root's
reference closure, following the ordinary
[Cachix closure workflow](https://docs.cachix.org/pushing).

The deployed application also publishes the `filcc` toolchain of the revision
it was built from. Campaign outputs reference the Fil-C runtime libraries but
not the compiler, so their closures alone would leave `filc0` and the compiler
wrappers out of the caches. Redeploy the publisher after a compiler update.

This covers subsequent builds recorded by this campaign automatically. It does
not watch the entire host store or automatically publish unrelated ad hoc
builds. The existing `push-baseline` and `push-pkg` commands remain available
for explicit Cachix publication outside the campaign.

For either cache, `filnix-publish-cache TARGET --extra-root /nix/store/OUTPUT`
explicitly adds an ad hoc output to the same durable queue. Run it with the
publisher's service identity; Cachix also needs its systemd-loaded credential.
For a root whose closure is confirmed missing now, use `--republish-root`
instead: it clears only that destination's receipt and retry delay for the
named root and queues its closure again. Ordinary `--extra-root` preserves
receipts. `scripts/ship` uses targeted retries for consumer-cache misses;
it does not clear unrelated receipts or audit independent swa-cache losses.
Install an updated publisher package on swa before using this option;
shipping detects an older publisher and stops rather than pushing uncached.

Each target keeps its own durable SQLite receipts under `/var/lib/filnix-cache`.
Only a successful upload records publication. Upload failures and timeouts
retain the work with exponential retry delays, capped at one hour. Failed
batches retry one root at a time so an unavailable path cannot permanently hold
up its neighbors. A crash between upload and receipt commit safely repeats the
idempotent copy. Destination configuration changes require a fresh receipt
state directory rather than silently reusing receipts for another cache.

The publisher runs as `filnix-cache`, with read access to campaign observations.
Cachix credentials are loaded by systemd only for the Cachix unit. The signing
key stays in the publisher's private state directory. Neither secret is in Git,
the Nix store, or the public cache directory.

Each service has a two-CPU quota, a 4 GiB memory limit, and lower CPU/I/O priority.
Local publication checks a 100 GiB free-space reserve before each batch. Cache
uploads have no role in build success, test evidence, or scheduling. Keeping
network operations outside the build loop follows the
[Nix post-build hook guidance](https://nix.dev/guides/recipes/post-build-hook.html).
No change to the Nix daemon or shared compiler derivations is necessary.

## Continuous integration

There are two readiness levels:

- **Foundation / push gate:** `scripts/ship-outputs.txt` lists `filcc`,
  `filcc-staging` (nanofil and its pre-push fleet need it) and `baseline`,
  with the site's `site-swipl` and `site-play`. The baseline retains every output of the curated packages in
  `shells/baseline.nix`, including Bash, Perl, Python, build tools, shared
  libraries and development headers. Publishing the complete closures means
  a toolchain update does not make ordinary consumers rebuild LLVM or these
  foundational packages.
- **Distribution / campaign:** `scripts/ci-outputs.txt` retains the wider
  PHP, BIND, staging, tarball and image output list. This is not a push gate.
  The campaign builds these first, followed by the broader port set.

Two things publish them:

- `scripts/ship`, which agents and people use to push to `main`. On swa it
  checks the candidate revision first, builds only attributes with incomplete
  closures, queues only their missing outputs with both publishers, waits for
  consumer-cache availability, and then pushes. Cachix gets targeted retries
  for those roots even if an old success receipt exists; the local publisher
  gets ordinary idempotent submissions. A complete cache hit needs no build
  or publisher access. Hosts with SSH/sudo access may publish through swa;
  other hosts stop on a miss rather than silently pushing without publication.
- Campaign manifests (`experiments/campaign-next/world.nix`), which start with
  the wider distribution list ahead of the package roots. See the
  [operations workflow](port-campaign-operations.md).

GitHub Actions never compiles Fil-C. `.github/workflows/cache.yml` runs on
pushes, pull requests and daily:

- The core job checks `scripts/ship-outputs.txt`. `scripts/ci-cache-check.py`
  walks the closures through
  narinfo lookups on Cachix and cache.nixos.org, and fails naming any path
  neither has. It downloads nothing and runs locally too.
- It substitutes the cached `filcc` and checks that it stops an
  out-of-bounds write.
- A distribution readiness job checks the complete closures of the five
  artifacts used by the optional tarball/image job. Missing artifacts are
  reported as pending and skip that job, not as a failed foundation update.
  Evaluation errors and failed artifact tests still fail CI.
- When ready, with `max-jobs = 0`, it substitutes the tarballs and images,
  tests the tarballs in Debian and Alpine containers, and uploads both PHP
  tarballs as workflow artifacts. On `main` it pushes the images to
  `ghcr.io/mbrock/filnix-php` with their version tags. Only the default,
  patched PHP also gets `latest`; vulnerable 8.4.25 is for isolated
  reproductions only (see [PHP](php.md)).

Rerun the workflow after the campaign publishes pending artifacts (the daily
run also rechecks readiness). A skipped distribution job is not a claim that
the artifacts passed. Calling `scripts/ci-cache-check.py` without attributes still
checks the full distribution list, as required by the release workflow.

### Strict main and publish-only repair

The gate is **consumer availability through Cachix + cache.nixos.org**,
not independently complete copies in both filnix caches. It covers complete
closures of all five foundation attributes, including `filcc-staging` and
`site-play`. Fresh narinfo queries, not upload receipts, establish readiness.
Missing paths fail main pushes; evaluation/network errors are errors, not
pending publication. The pre-push hook checks the committed tip in a clean
worktree and is strict for destination `refs/heads/main`; feature branches
can carry unpublished candidates. Local hooks guard accidental pushes, not
deliberate bypasses; do not use Git's `--no-verify` to evade them.

`scripts/ship --no-publish` skips publication but still requires complete
caches. There is no uncached-main override. To repair a revision already
pushed, or publish a candidate without landing it, use
`scripts/ship --publish-only --rev REV`. This reads the manifest and evaluates
outputs at REV, builds/publishes only incomplete outputs, and changes no refs.
Repeating it on a cache hit performs no foundation build or publication.
`scripts/ci-cache-check.py --json --flake FLAKE ATTR...` exposes the output
paths and each output's missing closure paths; exit codes remain 0 ready,
1 missing, and 2 evaluation/checker failure.

### Exact-head Nanofil handoffs

Rebase before the final candidate X, then run
`scripts/nanofil-fleet run --rev X --shards 6`, adding
other affected roots (`--roots auto,LIST` or `--roots all`). The fleet checks staging's public
closure before launching any worker. It does not require cached test results
or candidate `site-play`; the latter gates landing instead.

Hand the swa lander the repository/branch and full X, observed main, command,
pass/coverage and `results.json`. Retain `fleet.json`, `summary.md`, worker
links and raw event logs. Transfer a feature branch or Git bundle and the
receipt files explicitly; paths in an orb do not exist on swa. Keep the
candidate ref frozen, and do not commit receipts after testing.

The lander fetches and confirms the branch/bundle resolves to X, checks it out
cleanly, and runs `scripts/ship --exact X --fleet-results FILE`. This verifies
the worker revisions, six distinct complete shards and successful exactly-once
coverage, plus the quick Rocq root when model/compiler/validator or gate inputs
changed. Unrelated web/docs changes skip Rocq. `--roots LIST` adds required
checks; `--roots all` requires normal candidate roots, excluding the deliberate
`nanofil-rocq-full` mutation campaign. The standalone `scripts/nanofil-fleet verify FILE --rev X`
checks the same receipt without launching workers. Receipts are evidence from
trusted workers, not cryptographic attestations.

Exact landing never rebases or cherry-picks. It requires main to be an ancestor
of X, repairs X's foundation caches, rechecks main, and normally fast-forwards
exactly X with no second fleet. Diverging main means stop, rebase and obtain a
new pass at the new SHA. A concurrent conflicting push is rejected, never
forced. Keep one normal lander on swa without locking main for an entire
fleet. Plain `scripts/ship` still rebases for non-handoff work; a pre-rebase
receipt does not apply to its new SHA. Subscribe to CI for the actual landed
SHA, separately from the fleet and cache results.

`scripts/release --fleet-results FILE` requires six complete shards and
`nanofil-rocq-full` at the exact release SHA, then tags `origin/main` as
`vYYYY.MM.DD` once it is cached. The mutation campaign is selected explicitly
before a release or a soundness-relevant change, not on every push. Routine
relevant pushes use the 1–2 minute model/parse/base-verdict smoke check, and
`.github/workflows/release.yml` publishes a GitHub release with the PHP
tarball, the image as a docker-archive, the `/opt/fil` and filroot tarballs
and their SHA-256 sums, and pushes the image as `PHPVERSION-TAG`.

## Status and recovery

```sh
sudo /opt/filnix-cache/bin/filnix-publish-cache local --status
sudo /opt/filnix-cache/bin/filnix-publish-cache cachix --status
systemctl list-timers --all 'filnix-cache*'
journalctl -u filnix-cache@local -u filnix-cache@cachix -f
```

Status reports discovered roots, published roots, pending roots, and retry
errors. Counts exclude additional paths uploaded recursively. Receipts mean the
copy command completed successfully; they are not continuous remote audits.
Deletion or cache retention changes require verification and resubmission.

```sh
sudo systemctl stop filnix-cache@local.timer filnix-cache@cachix.timer
# Stop the services too if an active upload must be interrupted.
sudo systemctl stop filnix-cache@local.service filnix-cache@cachix.service
sudo systemctl enable --now filnix-cache@local.timer filnix-cache@cachix.timer
```

Retain `/var/lib/filnix-cache/{secret-key,public-key}` with the cache. Do not
regenerate the key pair when updating the publisher. The installer preserves
existing keys and configuration. Credential rotation uses the installer with
the replacement private Cachix config; active runs finish with their loaded
credential, and the next run loads the replacement.

## Installation

The publisher is independently packaged; building it does not evaluate Fil-C:

```sh
nix build --impure -f deploy/cache/default.nix --out-link result-cache-publisher
sudo deploy/cache/install "$(readlink -f result-cache-publisher)" \
  CAMPAIGN /path/to/private/cachix.dhall
```

Review `/etc/filnix-cache/config.json`. Install the `/cache` route from
`deploy/cache/nix.swa.sh.Caddyfile` into the existing Caddy configuration,
validate and reload it, then enable the two timers. Preserve the Caddy user's
read access when atomically replacing its config. `deploy/experiment/install`
does not modify this route or these units.

The local cache is under `/var/www/filnix-cache`. The application is selected by
`/opt/filnix-cache` and pinned through a Nix GC root. The campaign separately
roots realized outputs while the publication backfill runs.

## Verification

The initial rollout published all eight outputs of SDL3, SDL2 compatibility,
CAVA, and WirePlumber. Their combined reference closure contains 65 paths.
All 65 are in the self-hosted cache; Cachix supplies 63 and the official NixOS
cache supplies the other two. Metadata comparisons check NAR hash, size, and
references against the local store.

Download into a fresh store, with builds disabled, to verify actual availability
without accidentally reusing this server's installed packages:

```sh
nix build --store 'local?root=/var/tmp/filnix-cache-check' --no-link --max-jobs 0 \
  --option substituters 'https://filc.cachix.org https://cache.nixos.org' \
  /nix/store/OUTPUT
nix store verify --store 'local?root=/var/tmp/filnix-cache-check' \
  --recursive --sigs-needed 1 /nix/store/OUTPUT
```

For the self-hosted cache, use its URL and pass its public key with
`--option extra-trusted-public-keys` to both commands. Both independent restore
checks passed for the entire initial cohort, including content and signature
verification. `tests/test_cache_publication.py` covers discovery boundaries,
partial batch success, durable deduplication, independent destinations,
retry isolation, timeouts, and the disk reserve.

## Moving to a new campaign

Native campaigns keep the same output-feed URL when their recording is rolled
over. No publisher configuration change is needed; receipts from previous
campaigns remain and outstanding uploads drain normally.

For the archived SQLite runner, after importing a new campaign, change only `campaign` in
`/etc/filnix-cache/config.json` to its ID using an atomic file replacement.
The destination settings and receipt databases stay unchanged: receipts are
keyed by store path and cache destination, and pending uploads from the old
campaign continue to drain. An upload already running finishes with its loaded
configuration; the next timer run discovers the new campaign. Verify the
newly observed outputs appear in both receipt databases.
