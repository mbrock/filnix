# filnix.org hosting

The existing Pages workflow still builds and deploys to GitHub Pages. Its
independent `publish-r2` job uploads the **same artifact** to Cloudflare R2,
verifies object paths/sizes and `commit.txt`, then atomically replaces
`current.json`. Concurrent publication is serialized; an older build cannot
replace a newer live commit. Upload failures leave the previous release live.

`filnix-site` is a private Standard R2 bucket. `worker.mjs` is its only public
front end, bound as `SITE`. The Worker redirects canonical paths to
`/__releases/<commit>/…`; relative links consequently stay within one release.
It streams downloads, supports HEAD, conditional and range requests, and caches
immutable full responses up to Cloudflare's ordinary 512 MiB object limit.
`/commit.txt` reports the canonical release without caching.

The Pages workflow first prepares the four exact generated-page outputs and
publishes them to Cachix. This producer is serialized: one active run finishes,
with only the newest pending run kept. Proof captures are uploaded before the
renderers, not after the whole site. Site assembly depends on this job and
fetches these outputs with local/remote builders disabled, so it cannot silently
recompile proofs. A cache miss or failed upload is visible in the prerequisite.
The unrelated Binary cache workflow checks toolchain foundations; Pages does
not wait for its distribution/image jobs. Routine builds remain on GitHub.

The Actions `filnix-org` environment shows deployment status and its public URL.
Local phone checks remain independent of either publisher. `deployed-phone`
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
Expired snapshot bookmarks redirect to the equivalent canonical path; missing
pages inside retained snapshots still return 404. The retained copies remain
byte-immutable. At $0.015/GB-month, 100 GB retained is about $1.50/month before
the allowance; operations/Workers requests are separately metered. No persistent
Namespace volume or routine paid build shape is enabled.

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
caching. Namespace is **not** enabled for every push during the trial.

## Operations

- `node --test deploy/site/worker.test.mjs` checks the public serving contract.
- `node packages/site/phone.mjs https://filnix.org/ 320 390` checks live pages.
- Build a Worker update, verify it, then deploy using `wrangler.jsonc`; site
  publication alone does not update Worker code or require a broader CI token.
- To roll back, stop/serialize the `filnix-org` publisher first, verify a retained
  release's objects, then replace `current.json` with `{"sha":"<full commit>"}`.
  Do not delete the current release or race an in-progress publisher.
- Keep GitHub Pages and its `github.io` URL unchanged until a separate cutover
  decision. No redirect of the old site is part of this trial.
