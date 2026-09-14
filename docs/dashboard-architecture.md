# The Tagflow campaign viewer

The viewer renders public, read-only HTML from the existing campaign database.
It uses [Tagflow aa07b0d](https://github.com/lessrest/tagflow/tree/aa07b0d7eec0b72a5dbc6a8d0ee1098c68b74d09),
htmx 4.0.0 and Tailwind 4.3.3. This follows the library's dashboard example and
uses its reading contracts directly. The controller, workers, stored evidence,
queue policy and binary-cache publishers are independent of this change.

## Ownership

| Module | Responsibility |
| --- | --- |
| `experiment/dashboard/resources.py` | Canonical URLs, explicit reading options, routes and links derived from one schema |
| `data.py` | One read-only SQLite transaction per representation; campaign ownership and evidence scope |
| `base.py`, `views.py` | Tagflow HTML, navigation and literal Tailwind utility lists |
| `logview.py` | Bounded byte-cursor readers, source selection and log controls |
| `app.py` | Starlette routes, conditional representations, SSE revision hints and Hypercorn hosting |
| `static/reader.js` | Scroll following, pause anchors, navigation scroll reset and old fragment bookmarks |
| `experiment/web.py` | Retained read-only JSON API, raw downloads and controller health for external clients |
| `experiment/python.nix` | Pinned Tagflow and Python runtime; no compiler build dependency |
| `deploy/dashboard/` | Locked Tailwind tooling; generated CSS is checked in |

Application JavaScript neither fetches JSON nor constructs content nodes. Package
metadata, diagnostics, status, dependency neighborhoods and log records all arrive
as escaped server-rendered HTML. Assets are served locally with content-versioned
URLs. Node is needed to regenerate CSS, not to run the installed viewer.

## Reading policies

Every page is a normal URL under `/campaigns/{id}`. Activity, packages, batches,
dependencies, individual packages and individual batch logs have full-page HTML
representations. Links and GET forms work without JavaScript. Enhanced navigation
uses `hx.navigate` to select `#workspace` from that same response. There is no
`HX-Request` response variant, viewer cookie or server-side viewer session.
Browser history retains the visited URL and scroll position.

Activity counts/current work, timeline/recent batches, package details, batch
status and dependency neighborhoods refresh
independently with `hx.refresh` and `outerMorph`. The campaign SSE connection sits
inside the workspace but outside these replacing regions. It emits named revision
hints, which trigger normal HTML requests. Reconnection announces the current
revision; a five-second poll also picks up phase/heartbeat changes that do not append
campaign events. `transport=poll` uses a
three-second poll without SSE. Finished resources stop refreshing.

Activity follows by default, with an explicit Pause/Follow control for its
timeline and recent batches. Concurrent attempts occupy separate timeline rows.
Inventories and the full batch table are held snapshots with a visible timestamp
and refresh notice. All matching rows are present in
the document, including all 13,772 inventory attributes if selected. Browser Find
works across them. The notice offers an explicit refresh; progress does not
continually reorder the list. Package rows show name, version, description and
result, with Built muted and Tested emphasized. Timings belong to the batch page.

The Tagflow boundary hashes the exact rendered HTML. The application exposes
that validator as a weak ETag because gzip can change the wire representation,
and uses `Cache-Control: public, no-cache`. Matching conditional requests return 304.
Rendering still happens before hashing. Gzip reduces repeated markup in large
lists; lists are deliberately not virtualized. Each representation is internally
consistent, although separate refreshed regions can show adjacent revisions.

## Logs

Logs retain the existing aligned raw-byte offsets and 256 KiB read windows. A
cursor requests the next full HTML page and selects only its new records and next
cursor. Replacing that cursor avoids duplicate append on retry. `hx.read_cursor`
uses recurring requests plus click-to-retry and `this:drop`, so another tick does
not abort a slow request. A source picker and capture metadata refresh separately
without rereading the raw log. Those automatic reads wait while the source
form or options menu is being used, so they cannot close the menu or reset a
selection. Open diagnostic sections also survive morph updates.

Invalid offsets and the 2,000-record display cap replace the requesting reader.
`hx.recover_reader(closest="#log-reader")` resolves relative to that requester:
a late response cannot reacquire a newer reader with the same global ID. Recovery
responses are not cached. The full raw download remains available.

Scrolling away from the end pauses using the first visible byte offset and its
pixel position. Manual Pause uses the same anchor. Resume returns to the current
tail. Paused cursors can load newer output explicitly. Earlier output, source,
wrapping, font size and window search are ordinary URL options. Live logs advance
to the next batch at EOF; a specific batch URL stays with that batch. Following
never invents successful results from the text stream.

The common font is 14 px sans serif; output is consistently 12 px monospace by
default, with 14/16 px options. There is no terminal escape interpretation or
untrusted HTML rendering. Search highlights escaped text within the loaded window.

## Development and verification

```sh
npm --prefix deploy/dashboard ci
npm --prefix deploy/dashboard run build
nix build --impure --file experiment/default.nix --no-link --print-out-paths
# Python environment including the HTTP test client:
nix build --impure --file experiment/python.nix --arg testing true -o result-dashboard-python
PYTHONPATH=.:tests result-dashboard-python/bin/python -m unittest discover -s tests -p 'test_dashboard.py'
PYTHONPATH=.:tests result-dashboard-python/bin/python -m unittest discover -s tests -p 'test_experiment*.py'
# A separate Chromium debugging endpoint must be listening on 127.0.0.1:9228:
node tests/dashboard-browser.mjs http://127.0.0.1:8788 results/tagflow
```

The browser regression uses the two real inventory campaign IDs, without writing
to either campaign. It checks full lists, mobile fonts and widths, package/detail
history with scroll restoration, batch filters, dependencies, live log cursors,
pause/resume, failed/slow cursor requests and visible recovery, options staying
open across refreshes, live/paused timeline sampling, duplicate offsets, desktop rendering,
no-JavaScript pages and the
absence of UI JSON requests. Inspect its captured images as well as the assertions.
Unit tests cover escaping, exact full-page/cache parity, ownership, validation,
reader reset headers, bounded cursors, completion, CSV, refresh contracts,
overlapping timeline rows and test evidence scoped to its campaign.

Dependency nodes say Ready when their required outputs are available; this does
not claim they were compiled in this campaign. The evidence tooltip distinguishes
a store observation from inference through a consumer reaching a build phase.
A stopped activity says Stopped until successful check evidence supports Tested.
Build failures and evaluation errors have separate filters, so the overview
counts lead to the matching rows; All failures combines the failure categories.
Failed refreshes display a notice until that reader successfully recovers.

Blocked packages distinguish their own planning/build history from the failed
dependency. Each blocker links directly to the batch that owns its evidence,
with a date, campaign provenance and the intervening dependency chain. Derivation
facts are shared by exact store path, so an earlier campaign's evidence may still
block a new campaign; its log URL belongs to that earlier campaign. Different
derivations of the same named package do not share this evidence. Blocked/failed
states do not imply an automatic retry. Cleared failures with queued candidates
show Queued and label the previous log as history.

Planning logs and failures before a builder starts open unfiltered batch output.
Only recorded build activities produce scoped build-log links. Scoped logs seek
backwards in at most eight 256 KiB windows per request. If the match is earlier,
an HTML search cursor continues automatically, with visible progress and a normal
link for readers without JavaScript. Search requests replace only their owning
reader, retry on failure, and pause while log controls are being edited. Empty
bookmarked source filters retain their selected source and explain that no build
output was recorded, with a link to the full batch output.

Build an immutable application, run a preview against the real read-only database
under `filnix-web`, then select that store path with `deploy/experiment/install`
and restart `filnix-web`. Existing workers keep their original executable and
source; a viewer update does not rebuild packages. Verify `/healthz`, public
navigation and captured mobile/log output after the switch.
