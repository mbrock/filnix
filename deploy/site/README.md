# filnix.org hosting

The **Site** workflow (`.github/workflows/pages.yml`) builds and publishes only
to Cloudflare R2. Its `publish-r2` job verifies object paths/sizes and
`commit.txt`, then atomically replaces `current.json`. Concurrent publication
is serialized; an older build cannot replace a newer live commit. Upload
failures leave the previous release live. There is no GitHub Pages deployment,
Pages setup action or Pages/OIDC write permission. The artifact retains its
historical `github-pages` name and `artifact.tar` format so phone checks and
manual recovery work for both old and new runs; it is a normal Actions artifact.

`filnix-site` is a private Standard R2 bucket. `worker.mjs` is its only public
front end, bound as `SITE`. The Worker serves canonical paths directly from
one read of `current.json`, with `no-store` so reloads see the current release.
Before packaging, `prepare.py` pins local scripts, styles, media, frames and
explicit downloads to `/__releases/<commit>/…`, while page-navigation links
stay canonical. The playground resolves its worker and examples relative to
its pinned module URL. Thus a promotion cannot mix a page's assets with another
release, without putting a release prefix in the address bar. No cookie or
browser-history workaround is involved. Retained release URLs still work.
It streams downloads, supports HEAD, conditional and range requests, and caches
immutable release responses up to Cloudflare's ordinary 512 MiB object limit.
`/commit.txt` reports the canonical release without caching.

The Site workflow first prepares the four exact generated-page outputs and
publishes them to Cachix. This producer is serialized: one active run finishes,
with only the newest pending run kept. Proof captures are uploaded before the
renderers, not after the whole site. Site assembly depends on this job and
fetches these outputs with local/remote builders disabled, so it cannot silently
recompile proofs. A cache miss or failed upload is visible in the prerequisite.
The unrelated Binary cache workflow checks toolchain foundations; Site does
not wait for its distribution/image jobs. The producer uses Namespace 16 CPU /
32 GiB (no persistent volume), with a 30-minute timeout; ordinary site assembly
and browser checks remain on free GitHub runners. The previous cold 16-core
comparison cost about $0.14 per complete job at $0.024/minute; cached producers
and coalesced pushes cost less, but real proof growth can increase runtime.

The Actions `filnix-org` environment shows deployment status and its public URL.
Local phone checks remain independent of publication. `deployed-phone`
also checks the public site at 320 and 390 pixels and every deployed Rocq page.

## Credentials and costs

Actions uses `FILNIX_R2_ACCESS_KEY_ID` and `FILNIX_R2_SECRET_ACCESS_KEY`.
These are **object read/write only for this bucket**: no DNS, Worker editing,
bucket administration or other-bucket access. The trial expiration was removed
when ongoing hosting was approved; rotate/revoke through Cloudflare, never by
adding credentials to this repository. Worker deployments are separate administrative
operations using `wrangler.jsonc` or the Cloudflare connection, not this token.

R2 is metered with a free allowance, not a hard quota. The old **8 GiB trial
cap is removed**. After successful promotion, the serialized publisher deletes
only snapshots older than 24 hours, except the newest five and current release.
It uses each tree's youngest object so partial uploads also get a grace period.
Other bucket keys are untouched. Cleanup errors fail visibly but do not undo
promotion or skip deployed checks. `prune.py --dry-run` emits the deletion plan.
Expired snapshot page bookmarks redirect to the equivalent canonical path;
expired assets return 404 rather than mixing in another release's bytes. Missing
pages inside retained snapshots still return 404. The retained copies remain
byte-immutable. At $0.015/GB-month, 100 GB retained is about $1.50/month before
the allowance; operations/Workers requests are separately metered. No persistent
Namespace volume is enabled; the prerequisite's timeout bounds a single producer
to about $0.72 of compute at the listed rate, excluding rounding/teardown.

The manual `Site builder comparison` workflow builds one revision on GitHub
4-core and Namespace, both on Ubuntu 22.04 with the same public Nix
substituters. `namespace_runner` selects the existing `default` profile
(4-core / 16 GB) or a 16-core / 32 GB machine; the default is unchanged.
Its optional `revision` input pins the source independently of the workflow
revision.
It records elapsed time, hardware, output path and size as short-lived
artifacts. Namespace's 30-minute job limit bounds compute near $0.72/attempt
at the original 16x32 shape, or $0.36 with the default 4x16 shape, with no
volume storage charge. The initial 16x32 raw-label request remained queued
without an instance even after connecting GitHub and rerunning. The default
profile subsequently worked; a further 16x32 comparison was authorized after
activating Developer billing. The original allocation failure's cause was
not established.
The Namespace GitHub App must be
connected to this repository; an authenticated MCP session alone is not that
connection. This first comparison measures fresh runners, not persistent-store
caching. Following approval for ongoing operation, Namespace runs the serialized
generated-input producer; the comparison workflow remains a manual benchmark.

## Operations

- `node --test deploy/site/worker.test.mjs` checks the public serving contract.
- `moves.mjs` redirects pages a restructuring moved (301), so old links keep
  working; the Worker asks it only for a canonical path that is not found.
  When a change renames or moves pages, add a move there and a test case, then
  deploy the Worker.
- `python3 -m unittest discover -s tests -p 'test_site_*.py'` checks publication
  resource pinning and retention.
- `node packages/site/phone.mjs https://filnix.org/ 320 390` checks live pages.
- Build a Worker update, verify it, then deploy using `wrangler.jsonc`; site
  publication alone does not update Worker code or require a broader CI token.
- To roll back, stop/serialize the `filnix-org` publisher first, verify a retained
  release's objects, then replace `current.json` with `{"sha":"<full commit>"}`.
  Do not delete the current release or race an in-progress publisher.
- The existing GitHub Pages site and its `github.io` URL are left online at
  their last deployment, but this workflow no longer updates them. Repository
  Pages settings and DNS are unchanged; no redirect or site deletion is involved.
