# Native Fil-C port campaigns

The public, read-only dashboard is <https://nix.swa.sh/>. `/v2/` URLs redirect
to it. The native C++/NXT runner owns its DuckDB recording and listens on
loopback port 8778. `filnix-v2.service` runs the application selected by
`/opt/filnix-v2`; state lives under `/var/lib/filnix-v2`.

The smaller campaign uses the current verified Fil-C 0.686 toolchain and the
union of `shells/world-packages.nix` with the active `ports.nix` declarations.
At the initial launch this selects 300 evaluable roots. Twelve declarations
are excluded by their existing unsupported-platform metadata: `onetbb`,
`valgrind`, `gnustep-libobjc`, `libbsd`, `go`, `luajit`, `rspamd`, `python311`,
`python313`, `colm`, `ragel`, and `rustc`. The frozen manifest records them in
`excluded`; this does not count them as successful builds.

Each root asks Nix to realise its complete dependency graph, using existing
valid outputs and substitutions where available. This is a build of the latest
package definitions, not a forced rebuild of unchanged outputs. Roots run in
world order followed by the remaining declarations. The service allows two
local jobs with four cores, respects configured remote builders, admits work
for at most 24 hours, and allows two hours per root and 30 minutes of silence.
A failed or timed-out root does not stop later roots. An exhausted overall
budget leaves remaining roots visibly unattempted.

## Freeze and launch

Build and check the application before changing the deployed package:

```sh
nix build path:./experiments/campaign-next --out-link result-campaign-next
nix flake check path:./experiments/campaign-next
revision=$(git rev-parse HEAD)
manifest=$(nix eval --impure --raw --expr \
  "import ./experiments/campaign-next/world.nix { source = \"git+file:$PWD?rev=$revision\"; revision = \"$revision\"; scope = \"ports\"; }")
```

Review `roots` and `excluded` in that manifest. Root both the immutable manifest
and application under `/nix/var/nix/gcroots` before starting the service. The
manifest retains the frozen source and derivations without realising package
outputs during evaluation. Install the unit from
`experiments/campaign-next/deploy/filnix-v2.service` and merge that directory's
`nix.swa.sh.Caddyfile` with existing site-specific routes. Validate both before
reloading; keep Caddy's existing configuration permissions and cache routes.

The runner deliberately has no implicit resume. Restarting with a nonempty
database serves its recording without issuing builds. To start another campaign,
stop the service, preserve the closed database and manifest together under a
dated archive directory, select the new manifest, and start with a fresh
`campaign.duckdb`. Never copy/open a live DuckDB recording from another process;
its owning process provides the online read APIs. Keep rollback packages rooted.

The Python controller, web, classification, retention and analytics services
are retired on SWA. Their recordings and GC roots are retained for historical
analysis. [Legacy operations](experiment-operations.md) describe those records;
they no longer control the public campaign.

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
rollovers retain the same feed URL and do not require new receipt databases.

Unrelated ad hoc `nix build` invocations are not automatically watched. Use
`filnix-publish-cache TARGET --extra-root OUTPUT` with the publisher service
identity and, for Cachix, its systemd-loaded credential. The OpenSSH 10.5p1
refresh and the other verified ports were explicitly published to both caches
before this campaign. See [binary caches](binary-caches.md).

## Observe and recover

```sh
curl -fsS https://nix.swa.sh/healthz
curl -fsS http://127.0.0.1:8778/api/outputs
systemctl status filnix-v2
journalctl -u filnix-v2 -f
sudo /opt/filnix-cache/bin/filnix-publish-cache local --status
sudo /opt/filnix-cache/bin/filnix-publish-cache cachix --status
```

`/api/state` exposes the cohort counts, frozen revision, exclusions and current
session; the dashboard supports filters and 100-row pages for all 300 roots.
An output receipt means upload completion, not continuous remote verification
or test success. Compare cache NAR hashes/sizes/references and restore into a
fresh store when testing actual cache availability.

The rollout passed the native dataset and real-build integration checks,
including successful-root publication and restart behavior. The dataset test
covers incomplete results, output validity/deduplication and a 300-root view.
Publisher tests cover the new feed's validation and switching from SQLite
without losing receipts. The existing browser suite was exercised through the
public prefix and the canonical root before launching the fresh campaign.
