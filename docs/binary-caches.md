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

## Automatic publication

`filnix-cache@local.timer` and `filnix-cache@cachix.timer` independently run the
publisher, initially on activation and again one minute after each run finishes.
Each run discovers outputs from the configured campaign and submits at most
eight batches of 64 roots. Pending backfill continues on subsequent runs.

Discovery reads the campaign database without writing it. It includes realized
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

After importing a new campaign, change only `campaign` in
`/etc/filnix-cache/config.json` to its ID using an atomic file replacement.
The destination settings and receipt databases stay unchanged: receipts are
keyed by store path and cache destination, and pending uploads from the old
campaign continue to drain. An upload already running finishes with its loaded
configuration; the next timer run discovers the new campaign. Verify the
newly observed outputs appear in both receipt databases.
