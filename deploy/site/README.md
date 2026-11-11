# filnix.org hosting

The **Site** workflow (`.github/workflows/pages.yml`) builds and publishes only
to Cloudflare R2. Its single build/publish job verifies object paths/sizes and
`commit.txt`, then atomically replaces `current.json`. Concurrent publication
is serialized; an older build cannot replace a newer live commit. Upload
failures leave the previous release live. There is no GitHub Pages deployment,
Pages setup action or Pages/OIDC write permission. The artifact retains its
historical `github-pages` name and `artifact.tar` format so
manual recovery works for both old and new runs; it is a normal Actions artifact.

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

The Site workflow builds, prepares and publishes on one GitHub Ubuntu runner,
without artifact handoffs or browser gates. One active run finishes and seeds
the cache; only the newest pending push is kept. Cached staging Fil-C and
site SWI-Prolog are required, so CI never compiles LLVM. Exact generated-page
outputs substitute when unchanged; a cache miss builds the actual current
proof captures and pages, never a stale latest bundle. After the release is
live, those four outputs go to Cachix and the recovery artifact is uploaded.
The job has a 40-minute timeout and does not wait for Binary cache or its
distribution/image jobs. Cold proof edits can still be slower than prose edits.

Web prose and drawn terms use Public Sans; code uses DM Mono.
Equity, mbrock's licensed typeface for PDF prose, is not in the repository.
Its three OTFs are in this bucket under `private/fonts/equity/`, a key the
Worker never serves (it maps only `releases/` and `current.json`). The
build job's `equity.sh` reads them with the same credentials and sets each
nanofil document as a PDF beside its page. The OTFs never enter the site,
and the build publishes no Equity webfonts. Without the credentials the
web pages build as usual, but no PDFs are made.

The Actions `filnix-org` environment shows deployment status and its public URL.
Local phone checks remain independent of publication. The separate **Site
checks** workflow runs twice daily (05:17 and 17:17 UTC) or on demand. It pins
the live release, checks phone pages at 320 and 390 pixels, delayed browser
navigation and every deployed Rocq page. Publication itself checks the live
immutable and canonical commit endpoints immediately after promotion.

## Credentials and costs

Actions uses `FILNIX_R2_ACCESS_KEY_ID` and `FILNIX_R2_SECRET_ACCESS_KEY`.
These are **object read/write only for this bucket**: no DNS, Worker editing,
bucket administration or other-bucket access. The trial expiration was removed
when ongoing hosting was approved; rotate/revoke through Cloudflare, never by
adding credentials to this repository. Worker deployments are separate administrative
operations using `wrangler.jsonc` or the Cloudflare connection, not this token.

R2 is metered with a free allowance, not a hard quota. The old **8 GiB trial
cap is removed**. Twice daily, a retention job sharing the promotion lock deletes
only snapshots older than 24 hours, except the newest five and current release.
It uses each tree's youngest object so partial uploads also get a grace period.
Other bucket keys are untouched. Cleanup errors fail visibly in Site checks,
independently of publication. `prune.py --dry-run` emits the deletion plan.
Expired snapshot page bookmarks redirect to the equivalent canonical path;
expired assets return 404 rather than mixing in another release's bytes. Missing
pages inside retained snapshots still return 404. The retained copies remain
byte-immutable. At $0.015/GB-month, 100 GB retained is about $1.50/month before
the allowance; operations/Workers requests are separately metered. Between
cleanups storage can grow for up to twelve hours of pushes.

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
caching. The publisher now uses GitHub runners; the comparison workflow remains
a manual benchmark.

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
