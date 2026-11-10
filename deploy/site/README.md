# filnix.org hosting trial

The existing Pages workflow still builds and deploys to GitHub Pages. Its
independent `publish-r2` job uploads the **same artifact** to Cloudflare R2,
verifies object paths/sizes and `commit.txt`, then atomically replaces
`current.json`. Concurrent publication is serialized; an older build cannot
replace a newer live commit. Upload failures leave the previous release live.

`filnix-site` is a private Standard R2 bucket. `worker.mjs` is its only public
front end, bound as `SITE`. The free-plan Worker redirects canonical paths to
`/__releases/<commit>/…`; relative links consequently stay within one release.
It streams downloads, supports HEAD, conditional and range requests, and caches
immutable full responses up to Cloudflare's ordinary 512 MiB object limit.
`/commit.txt` reports the canonical release without caching.

The Actions `filnix-org` environment shows deployment status and its public URL.
Local phone checks remain independent of either publisher. `deployed-phone`
also checks the public site at 320 and 390 pixels and every deployed Rocq page.

## Credentials and costs

Actions uses `FILNIX_R2_ACCESS_KEY_ID` and `FILNIX_R2_SECRET_ACCESS_KEY`.
These are **object read/write only for this bucket**: no DNS, Worker editing,
bucket administration or other-bucket access. The initial trial token expires
on **2026-12-10 at 23:00 UTC**; renew/revoke through Cloudflare, never by adding
credentials to this repository. Worker deployments are separate administrative
operations using `wrangler.jsonc` or the Cloudflare connection, not this token.

No paid Workers plan or persistent Namespace volume is selected. Free Workers
has a daily request limit; exceeding it stops serving until reset rather than
automatically upgrading. R2 is metered with a free allowance, not a hard quota.
The publisher caps retained trial objects at **8 GiB**, conservatively counting
the whole incoming release before upload. At the listed $0.015/GB-month this
is about $0.13/month before free allowance. At the cap, new publishes stop;
existing releases remain live. Do not delete bookmarked immutable releases
without deciding a retention/redirect policy first. Operation charges remain
metered; monitor account usage during the trial.

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
