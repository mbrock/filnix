# Build Observatory instrument pass — 2026-10-03

## Evidence and boundaries

The public site was inspected before implementation: observing `libinput` and
built `libdrm`, including `Show all output` and the bottom of the graph. The
campaign had advanced from the supplied 56 settled roots to **65/82 settled,
65 successful, zero failures/timeouts, 16 unattempted**, with one observing root.
Initial DOM counts were 3,913 and 3,916: 500 graph rows, 19 repeated omission
notices, no buttons, inputs, or selects. `Show all output` actually cleared the
activity selection using `./?run=…`; it did not add an activity parameter.

The read-only public recheck during verification found **81/82 settled,
80 successful, one timed out, zero failures, zero unattempted**, with FFmpeg
still observing. Emacs was the timed-out root: its header said `Time limit
reached`, its graph said `timed-out`, there was no pinned reason strip or
console control, and output remained below the static tree. This is an
observed nonzero timeout case, not an inferred failure design.

This is the same one-page C++/NXT observer. No build scheduling, compiler,
runtime, event schema, Parquet export, service or campaign admission behavior
changes. No production database migration. The running campaign must not be
restarted merely to install presentation changes: restarting a nonempty cohort
serves its recording and does **not** resume its remaining roots.

Doctrine references below are the supplied numbered principles, checked against
[Office](https://usgraphics.com/) and
[DX-102-11](https://usgraphics.com/static/products/TX-02/datasheet/TX-02-datasheet.a43c0c7f8d8c.pdf).
`M1`, `M2`, `M3` mean Mikael Brockman's operator amendments: labels ≠ prose,
few font sizes, and minimal padding. They are not USGC quotations. System mono
fonts are used; no Berkeley Mono font files or license are assumed.

## Decisions: before → after

- **1. Rail:** Ellipsized name → full mono name wrapping above `built · 2216 ev`. Dense ruled list; 50-row replacement windows, `Previous 50`, `Show next 50`. `Filter` and name-only `Find`; state filters remain available at zero. Selected row and run links remain. **Doctrine 3, 4, 5, 7; M3.**
- **2. Campaign:** Passive arithmetic → clickable `N successful`, `N failed/interrupted`, `N timed out`, `N unattempted`. Single horizontally scrollable line retains roots, settled fraction, zero failure modes and admission-stop reason. `Follow latest` explicitly uses `./?follow=1`; `./` opens the overview. A root count already present in the recorded campaign line's name is not printed twice. **Doctrine 2, 4, 8; M1.**
- **3. Graph:** Recursive bootstrap closure → root, recorded phase jumps, exact `N static inputs` disclosure, useful direct children and additional currently active builds. Collapsed closure has no mounted descendants. `outputs · out` disappears; other requested sets remain, e.g. `outputs · out, dev`. Actual repeated vertices alone get `reference ·`. **Doctrine 2, 3, 4, 7, 10.**
- **4. Limit:** One notice per subtree → one `Remaining dependencies omitted (500-node limit).` per capped window. `Show next 500` and `Previous 500` replace that window; they do not accumulate DOM. **Doctrine 4, 7, 8.**
- **5. Output:** Footer below tree → visible peer pane with independent scrolling. `Build output`, `Live` / `Captured`, full IDs, `Find`, `Pause` / `Follow`, `End`, `Phase`, `All output`. Raw text, elapsed times and horizontal message scrolling remain. **Doctrine 2, 3, 5, 7, 13; M1.**
- **6. Eyebrow:** `SESSION OBSERVATION · DEPENDENCY GRAPH` → removed. Package title and campaign line already identify the context. **Doctrine 4, 12; M1.**
- **7. Facts:** Sole ellipsized drv → full horizontally scrollable mono drv plus `Copy drv`. `SYSTEM`, `EVENTS`, `OUTPUT LINES` remain. **Doctrine 2, 4, 8.**
- **8. Vocabulary:** Title-case badge variants → the same lower-case session status in rail, header and root. `Native result · <outcome>` exposes the unmodified underlying disposition rather than silently conflating it. **Doctrine 2, 4, 8.**
- **9. Failure:** No pinned reason; output below tree → recorded last phase/activity, root status and actual reason pinned above the graph; initial output tail is on screen. Real failed, interrupted and timed-out recordings are tested. **Doctrine 2, 4, 8, 12.**
- **10. Links:** Opaque keys → retained unchanged, with `Selected · <name>` for nonroot graph selection. A missing node loads its containing graph window; package title does not change. **Doctrine 4, 8, 10.**
- **11. DOM:** 500 graph rows always mounted → lazy graph windows and 50-row rail windows. Console starts with 200 rows and retains at most 256. Inputs, filter and open static snapshot survive state polls. **Doctrine 7.**
- **12. Type:** Many sizes / fluid display scale → 10 / 12 / 20 px only. Names, drvs, times, IDs, phase rows and messages remain mono. **Doctrine 5, 6; M2.**
- **13. Geometry:** Rounded / padded rows → square corners, hairlines, small horizontal-biased padding, no shadows, motion, blur or new decoration. `Live · recording` / `Recorded` replaces recording prose. **Doctrine 1, 3, 6, 9, 12; M3.**
- **14. Gloss:** Long activity-overlay sentence → `Static inputs · activity overlaid`. The meaning is retained, not a paragraph in the header. **Doctrine 4, 8; M1.**

**Deliberate limits / refusals:** no new tabs, card summaries, permanent hiding
of bootstrap, imaginary builder/dependency outcomes, or fake pagination. A
stopped Nix activity is `ended`, not proof that its derivation succeeded. A root
result does not reliably identify a failing dependency/phase: the failure strip
says `last phase · <phase> · #<activity>`, or `phase unavailable`, not a guessed
culprit. `Find` searches the loaded console window, explicitly counted as
`N matches · N loaded`; it is not advertised as whole-archive search. Expanded
static input windows are labeled snapshots, not claimed to be continuously live.

## Scroll-layout correction

The subsequent live inspection found **82/82 settled, 80 successful, one
failed, one timed out, zero unattempted**. At a 1440 × 900 viewport the shell
reported 900px height but its auto-sized grid row grew to 3,234px. The rail's
3,099px client height equalled its content height: `overflow: auto` could not
scroll it. Wheel input confirmed zero rail movement. The previous visual
checks did not exercise this interaction.

- **Sizing:** content-sized desktop grid → a viewport-bounded row with explicit
  `minmax(0,1fr)` tracks and zero minimum heights through the grid/flex chain.
  No wheel interception or page-level scrolling on desktop. **Doctrine 5, 7, 12.**
- **Rail:** unbounded list → fixed chrome plus a remaining-height scrolling
  list. Full names, two-line rows, filters, paging and URLs stay unchanged.
  **Doctrine 3, 4, 5; M3.**
- **Main:** graph above an oversized console → two equal bounded tracks. The
  upper track contains session facts and the graph; the lower contains the
  console. Graph/console headers stay outside their scrolling contents.
  In very short windows, facts scroll within a 25dvh maximum rather than
  pushing the graph or output out of view. **Doctrine 3, 5, 6; M3.**
- **Refresh:** reset horizontal positions and repeated fragment jumps → retain
  both axes, graph-region keyboard focus, selected-node label and native-result
  disclosure through state polls; Pause no longer clones state. Fragment selection
  scrolls on navigation, not every refresh. **Doctrine 5, 7, 12.**
- **Rail response order:** stale page-zero poll can replace page 50 → page
  intent is set before its request; only responses matching the current page,
  filter and Find text may swap. Filter/page changes start at the top; ordinary
  polling keeps the scroll offset. **Doctrine 4, 5, 7, 12.**
- **Narrow:** rail chrome nearly consumes its 20vh allowance → a 230–320px
  rail with usable rows, then normal document flow. Graph is capped at 32dvh;
  console has at least 260px. No nested desktop-height shell on phones.
  **Doctrine 3, 5, 12; M3.**

Named, focusable scroll regions support PageUp/PageDown/Home/End without
inventing controls. Stable scrollbar gutters reserve space without altering
the type scale or adding padding decoration. Raw messages and long paths
remain horizontally scrollable; visible edge clipping is not truncation.

## Native overview, terminal styling and idle work

The next public inspection confirmed the same completed 82-root campaign and
raw ESC bytes in the log API, including the reported FLAC dependency timeout.
The user's screenshot shows Chrome's Page Unresponsive dialog, but a 12-second
Chromium observation of the public FFmpeg view did not reproduce a long task
or JavaScript error. That page did repeatedly replace settled state/list HTML.
Reducing that unnecessary work is justified independently; it is not a proven
explanation of the reported freeze or a claim about the user's machine.

- **Entry:** silently selected latest FFmpeg session → campaign overview with
  `Package`, `State`, `Events`, `Output lines`, `Filter`, `Find` and clickable
  arithmetic. One flat table, not summary cards or a duplicate rail. Names wrap
  without clipping; states remain single words. Unattempted roots are included
  in `all`. `Follow latest` opts into details; the brand returns to the overview.
  **Doctrine 2, 3, 4, 10, 12; M1, M3.**
- **Read cost:** front-page/rail reads materialized a selected graph and output
  → summary-only queries. Fifty replacement rows, no collapsed graph or console
  mounted on the overview. **Doctrine 7.**
- **Idle:** settled pages polled and replaced state/list HTML → no periodic data
  requests when admission/observation has ended. Live polling remains, including
  gaps between roots; hidden pages suppress requests. **Doctrine 7, 12.**
- **Output:** replacement glyph plus `[31;1m` clutter → escaped, styled SGR spans
  using a paper-readable ANSI palette, indexed256 and truecolor. Failure reasons
  and initial/incremental output share the renderer. Unsupported controls stay
  visibly sanitized; original bytes stay in the record. **Doctrine 2, 4, 5, 8.**
- **Find/append:** repeated message reconstruction → highlights preserve SGR
  spans and cross-span matches, cached unchanged searches, one fragment append
  and bounded rows. Pause updates intent without cloning the graph and rejects
  stale implicit-latest responses. **Doctrine 5, 7, 12.**
- **Construction:** hand-built markup gains a small block-scoped C++ writer
  used by the overview and SGR output, sharing escaped text/attributes with the
  existing renderer. No AST or ambient coroutine state; not a complete Tagflow
  port or a new web framework. NXT is pinned to current main at verification,
  with its new structured task-group API. **Doctrine 6, 7, 12.**

## Component contracts before session/table separation

These describe the previous instrument. The current contracts are in
**Session/table separation** below; earlier evidence and deployments remain
historical records, not claims about the new layout.

### Overview

`./` shows the campaign name, `Recorded` or `Live · recording`, its arithmetic,
the list controls and the four-column table. There is no selected package,
derivation fact row, dependency graph or console. The table/list region scrolls
independently of this fixed chrome and has at most 50 rows; headers are sticky.
Counts, Find and pagination operate on this same table. `No sessions · <filter>`
is the empty filtered result. With no campaign, the heading is `Build observatory`
and the table contains available standalone recordings; an empty database has
zero rows, not an invented session. A root without an attempt has `unattempted`,
zero events/output and no link. No tabs, cards or explanatory subtitle are added.

### Rail and campaign

`Filter` options: `all`, `observing`, `built`, `already-valid`, `incomplete`,
`failed`, `interrupted`, `timed-out`, `successful`, `unattempted`.
`successful` matches built and valid-output recordings. `failed` includes
interrupted roots, matching the campaign's `failed/interrupted` arithmetic;
`interrupted` is also individually selectable. `Find` matches names only,
case-insensitively. Empty result: `No sessions · <filter>`.

The selected cohort is the rail's scope, not every historic campaign mixed
together. Its manifest is bounded to 256 roots. Standalone recording views
retain the latest 256 recordings. Pagination mounts at most 50 rows and keeps
the page through polling; changing Find/filter starts at the first page.
Unattempted rows come from manifest indices without a recorded attempt and say
`unattempted · 0 ev`. They have no invented run ID or session link. An empty
database says `No recorded session` and `No captured output`.

Campaign controls change the rail only; inspecting the current session is not
lost when the filter is empty. `Follow latest` clears the selected run/activity,
selects the active recording when there is one, otherwise the latest recording,
and initializes its output at the end. The full campaign arithmetic remains
available through horizontal scrolling on narrow screens.

### Facts and statuses

Title is the full recorded package name. Facts are `DERIVATION`, `SYSTEM`,
`EVENTS`, `OUTPUT LINES`; drv is never represented only by an ellipsis.
Clipboard copying reports `Copied` or `Copy unavailable` in the console status.

Canonical root/rail/header words: `observing`, `built`, `already-valid`,
`incomplete`, `failed`, `timed-out`, `interrupted`.
Observing uses the process's active run identity even while another run is
selected. Nonactive unfinished recordings remain incomplete.
Cancelled maps to interrupted; worker/recorder errors map to failed. Substituted
and resolves-to-already-valid map to the valid-output category, while the
visible `Native result` disclosure retains their exact dispositions and Nix
result JSON. No claim that substitution compiled a package.

### Graph

The root shows canonical root status, then observed phase, machine, activity
running/ended state and activity duration. Root phase buttons show elapsed time
and the recorded phase, and select that activity's output from the phase event.
The latest 256 phase observations are available through `Phase`; they update
with the state without resetting the operator's selection.

Direct bootstrap names `bash-*`, `hex0-*`, `hex1-*`, `hex2-*`, `kaem-*`,
`stage0-*` and `.tar.gz` / `.tar.xz` sources are static by default. Other direct
inputs and currently active reachable derivations stay visible. The disclosure
counts unique reachable inputs not shown in that foreground, not repeated tree
references. Expansion renders recorded relationships and activity overlays;
already-visible nodes appear as references there.

Foreground output labels use the root's direct edge, even when the same input
was first visited through a transitive edge requesting different outputs.

Traversal stops revisiting shared vertices and cycles, not at an arbitrary
depth. A window has at most 500 relationship rows, including references, and
shows `Snapshot · <watermark> · <start>–<end> / <rows> rows`. A drv fragment
can fetch a later window directly. Unknown dynamic edges and missing recipe
metadata stay labeled as such. There are no success labels inferred for inputs.

### Console and failure

Columns are 12ch time, 23ch activity, then unwrapped message. Time and activity
are sticky when scrolling horizontally; even unsigned 64-bit activity IDs fit
and copy exactly. No activity is `—`, with copying disabled. UTF-8 replacement
and nonprinting control-byte replacement are display-only. Recognized terminal
SGR renders ANSI16, indexed256 and truecolor, bold/dim/italic/underline/strike,
inverse and resets as escaped spans. Semicolon/colon parameters and the empty
reset are supported. Styling starts fresh per observation: no terminal cursor
emulation or cross-record state reconstruction is claimed. Incomplete and
unsupported controls remain visibly sanitized. BLOBs, JSON APIs, replay and
Parquet stay byte-exact. Find inserts text/mark nodes without destroying spans,
counts matches crossing styles once, and inherits the original foreground.
**Doctrine 4, 5, 8; M1.**

The initial window is the last 200 observations for the requested activity, or
all activities. Streaming appends exclusive-cursor pages of at most 256 rows
and trims the old window. `Pause` stops log requests and pins the current run;
graph/state recording continues. Scrolling away from the end or using Find
also pauses. `Follow` refreshes the tail and follows new output. `End` refreshes
the tail without changing the pause state. Settled pages do not poll logs or
state/list HTML. Active campaigns retain state/list updates; hidden pages pause
requests. Stopped admission does not turn an incomplete recording into live.
`Phase` / phase buttons pause and fetch the first page after that exact phase
event, with its activity ID; `All output` clears the activity restriction.

Failed, interrupted and timed-out roots put a reason at the top of the graph,
with their output tail already visible. Missing phase/reason is explicitly
`phase unavailable` / `no recorded reason`. Terminal SGR is styled in the report
reason and output pane; the native result retains the JSON representation. Errors remain text,
not a toast, modal or invented per-node verdict. Zero campaign failure counts
are not suppressed.

### URL table

| URL / state | Meaning |
| --- | --- |
| `./` | Campaign overview, no implicitly selected session |
| `./?follow=1` | Follow current/latest session and its output tail |
| `?run=<id>` | Pin a recording; its package remains the title |
| `&activity=<unsigned decimal id>` | Restrict output to that Nix activity |
| `#drv-<lowercase hex of full drv bytes>` | Existing stable node key; lazy-load containing window if necessary |
| `&filter=<word>&find=<name>` | Inspectable rail state, retained in session links |
| `./overview` | Native campaign-summary fragment; polled only while admitting/observing |
| `./sessions?run=…&filter=…&find=…&after=N` | 50-row replacement window; native rendered HTML |
| `./sessions?overview=1&filter=…&find=…&after=N` | Same window as the four-column overview table |
| `./graph?run=…&after=N` / `&node=<full drv>` | 500-row replacement window or window containing a node |
| `./logs?run=…&activity=…&after=<seq>` | Exclusive log cursor, native escaped HTML / OOB compatibility |
| `./logs?…&tail=1` | Latest 200 rows, independent of the previous cursor |
| `./api/state`, `./api/logs` | Existing owned JSON APIs; log tail is also supported |

All URLs and assets remain prefix-relative for Caddy's `/v2/` strip-prefix.
No HTTP writes or filesystem/build endpoints are introduced.

## Tokens before session/table separation

| Token | Value |
| --- | --- |
| Caption / body / display | 10 / 12 / 20 px; body line height 1.5 |
| Mono | `ui-monospace, SFMono-Regular, Consolas, monospace` |
| Paper / ink / rule | `#f5f5ef` / `#26332e` / `#cbd2c8` |
| observing | Word + amber `#875814` |
| built, already-valid | Words + muted green `#315b46` |
| failed, interrupted | Words + red `#962e29` |
| incomplete, timed-out | Words + amber `#875814` |
| unattempted | Word + muted `#596a62` |
| Rail / graph rows | 3px / 2px vertical, 6px horizontal; graph indent 12px/level |
| Controls / log cells | 2px / 1px vertical, 6px horizontal |
| Corners / shadows / motion | 0 / none / none |
| Desktop main tracks | Equal halves, each `minmax(0,1fr)` |
| Desktop session facts | Intrinsic height, max 25dvh; scroll if needed |
| Desktop rail / graph / console | Remaining track height; independent scrolling |
| Narrow graph | Max 32dvh |
| Narrow rail / console | `clamp(230px,34dvh,320px)` / `max(260px,50dvh)` |

Grayscale preserves every state word, selected-row rule, counts, phase and
reason. Color is never the only state encoding.

## Executed verification

The packaged Nix build and both Meson targets pass, including six native
integration groups. Targeted renderer/data regressions cover the 500-row
boundary and deep-link window, exact unsigned activity IDs, real phase
cursors, unsupported phase records remaining raw, direct/transitive output-set
differences, canonical failure states, escaped reasons and terminal SGR styling.
Unsupported phase fields, SGR-decorated reasons and differing output sets each
failed before their fixes.

Chromium browser checks exercised filters and unattempted entries, 50-row rail
paging through polls, static expansion through polls, next-500 replacement,
drv fragments, clipboard copies, sticky IDs during horizontal log scrolling,
loaded-window Find, phase jumps, Pause stopping requests, End restoring the
tail and Follow resuming. Real failing and timed-out local-store fixtures and
an archived interrupted session were inspected, including grayscale. Browser
checks reported no JavaScript errors. Narrow checks used a 390 × 844 Chromium
touch context at 2× resolution and confirmed coarse-pointer media and no
page-wide overflow; this is not a Safari/device claim.

The representative archived fontconfig view mounted **1,199 DOM nodes,
10 graph nodes and 200 log rows**. Its 10,974-row relationship graph advanced
from 0–500 to 500–1000 without accumulating rows. This fixture is a copy of an
immutable earlier campaign snapshot (52/82 settled), not the live production
database. Review screenshots and the browser verification script are retained
in the local `.amp/in/artifacts/` directory. No deployment or service restart
is part of these checks.

The scroll correction adds `tests/test_observatory.py`, an optional read-only
Playwright check against a representative served recording. It exercises six
desktop sizes from 1440 × 360 to 2560 × 1440 (including 801px just above the
narrow breakpoint): actual wheel and keyboard rail/graph scrolling, visible
console bounds, both-axis retention across refresh and Pause, rail pagination,
deliberately delayed stale rail responses, deep-link scrolling without periodic
snap-back, and short-window facts with an
open native result. A 390 × 844 touch context performs an actual touch-pan via
Chromium CDP. Built, failed and timed-out screenshots are inspected separately.
The fixture is a private copy of the closed pre-deployment backup, not a second
connection to the service's live database. No builds are started.

```sh
uv run --with playwright python experiments/campaign-next/tests/test_observatory.py \
  http://127.0.0.1:8112/ --screenshots .amp/in/artifacts
```

Use `--chromium` to specify a Chromium executable on another machine. Browser
dependencies are not added to the native package or its normal Meson tests.

The overview/SGR pass was also checked against the installed Nix package on a
private copy of that closed backup. Both native Meson targets and the packaged
check phase pass with NXT main pinned at
[`f810d9a`](https://github.com/mbrock/nxtui/commit/f810d9a27a6e74cbde721a8d36d718b2602efa01).
The browser suite measures **402 overview DOM nodes**, verifies no background
state/list/log requests during 6.5-second settled overview and failed-session
intervals, and confirms the existing output nodes are not replaced while idle.
It exercises overview wheel scrolling/sticky headers, next/previous 50-row
windows, count filtering, an empty Find result, actual SGR foreground/bold
styles, and Find crossing a styled/plain-text boundary without losing color.
The same six desktop sizes and Chromium touch checks pass without JavaScript
errors; overview, empty/failed filter, SGR, built, timed-out, short-window and
mobile captures were inspected. This does not establish that the reported
unresponsive-page failure is reproduced or fixed. FLAC's recorded build timeout
is unchanged; no production database connection, retry or deployment was made.

## Deployment — 2026-10-04, Europe/Riga

After operator approval, the verified package was installed at `/opt/filnix-v2`
and `filnix-v2.service` restarted. The old package remains GC-rooted; a closed
database/WAL backup was taken under
`/var/lib/filnix-v2/before-overview-sgr-20261003T232839Z` before the switch.
The service confirms `Existing recording: serving only, no automatic retries`.
The complete read-only browser suite passed through `https://nix.swa.sh/v2/`,
including prefix-relative links, overview filters/paging, styled Find, all six
desktop sizes and Chromium touch checks. Public overview, SGR failure output
and narrow overview captures were inspected. No JavaScript errors or service
restarts occurred; the settled views issued no periodic data requests.
After verification the watermark remained **299484**, with **82/82 settled,
80 successful, one failed, one timed out, zero unattempted**. No new campaign
events or builds were created. The original unresponsive-page report is still
not reproduced; the real recorded package failures are not reclassified.

## Session/table separation — 2026-10-04

The public recheck still showed the complete 82-root recording: 80 successful,
one failed and one timed out. The index had 50 rendered rows; selected sessions
still mounted a second session rail. This pass changes presentation and read
projections only. NXT, recording, scheduling, campaign limits and raw events are
unchanged. The preceding component contracts are superseded as follows.

### Decisions and current contracts

- **One index:** overview plus detail rail → one five-column session table at
  `./`: `Package`, `State`, `Events`, `Output lines`, `Phase / result`. Fifty-row
  replacement windows, name-only `Find`, state `Filter` and clickable campaign
  counts stay. The last root phase is a typed observation; failed rows show
  their exact native disposition (e.g. `DependencyFailed`) when available.
  Missing summary is `—`. Unattempted roots remain unlinked, with zero counts.
  **Doctrine 2, 3, 4, 7, 10; M1, M3.**
- **Campaign once:** repeated name/counts in detail → campaign arithmetic only
  on the index. The heading omits a redundant ` · N roots` suffix when the
  recorded name already includes it. Counts retain zero failure modes and
  `Follow latest`. Narrow arithmetic wraps at controls rather than clipping
  `1 timed out`; no count is shortened. **Doctrine 4, 5, 8, 10; M1.**
- **Dedicated detail:** rail plus vertically stacked graph/output → one package
  title/status, `Sessions` backlink, a 35% inspector beside a 65% full-height
  console. Both fit bounded grid/flex tracks, not content-sized overflow.
  `Hide details` / `Session details` controls the inspector with
  `aria-expanded` and `aria-controls`. Drv, native result, error reports and
  output paths are inspectable without repeating the campaign list.
  **Doctrine 2, 3, 5, 6, 12; M1, M3.**
- **Phase ledger, not pretend graph:** flat phase buttons in `Dependency graph`
  → separate `Phase ledger` with `Phase`, `Duration`, `Started`. It uses the
  latest root activity, coalesces consecutive identical phases, and measures
  time to the next distinct phase in that same activity, or its observed stop.
  Other derivations' phase events cannot shorten it. Live final duration adds
  ` · running`; an absent terminal observation is `— · end unobserved`.
  `local` or the recorded machine and exact activity ID remain visible.
  Phase-name buttons select that activity's output at the phase cursor.
  The source is the bounded latest 256 phase observations, not an invented
  complete timing trace. **Doctrine 2, 4, 8, 12; M1.**
- **Dependencies remain dependencies:** a separately labeled `Dependencies`
  section retains direct inputs, live activity overlays, actual references,
  nondefault output sets, static-input count, lazy 500-row windows and one
  omission notice. No root package heading is repeated there. Bootstrap stays
  reachable; collapsed children are not mounted. **Doctrine 2, 4, 7, 10.**
- **Console geometry:** competing Find/count/Phase controls and unstable message
  widths → two small tool rows and a read-only loaded/match count in the footer.
  Labels are `Build output`, `Live` / `Captured`, `Pause` / `Follow`, `End`,
  `Find`, `Wrap`, `All output`. Desktop columns are fixed time (10ch + 12px),
  full ID (22ch + 12px), remaining-width message. Default `Wrap` preserves all
  text; disabling it gives each raw message horizontal scrolling without moving
  metadata. The Phase dropdown is removed; ledger buttons are the phase control.
  SGR styles, copyable IDs, bounded 200/256-row windows, exclusive cursors and
  idle suppression stay. **Doctrine 3, 4, 5, 7; M1, M2, M3.**
- **Phone navigation:** table/rail/details stacked in one document → index
  alone, then a dedicated session route. Below 801px, each table row uses a
  full-width package line followed by aligned state/counts and a phase/result
  line. Details initially collapse, leaving output immediately visible; opening
  them caps the inspector at 40dvh. Metadata sits above each full-width message,
  rather than squeezing it into a thin third column. Touch scrolling uses the
  same native scroll regions; no wheel interception. **Doctrine 3, 5, 12; M3.**
- **Failure truth:** long repeated root error → a concise pinned Nix reason,
  visible even with mobile details closed. `Reported errors · N` contains the
  latest four severity-zero logger observations with exact `Output · <time>`
  jump controls. `Output paths · reported` distinguishes paths mentioned in a
  failed result from realized outputs. Empty paths say `No output paths recorded`;
  missing phases say `No recorded phases`. `Native result · <disposition>`
  retains raw result JSON. We refuse to label a proven failing dependency or
  phase without causal evidence; a logger error remains a report, not a verdict.
  **Doctrine 2, 4, 8, 12; M1.**
- **Navigation stability:** `?run=`, `&activity=` and `#drv-` remain stable.
  Selected dependencies show `Selected · <name>` without changing the package
  page title. Root fragments target the full drv fact. Inspector scrolling,
  keyboard focus, selected-node text, opened reports, static windows and the
  expansion control survive refresh; refreshing does not re-jump the fragment.
  `Sessions` carries `filter` / `find` back to the index. `./sessions` now always
  renders the same table; old `overview=1` parameters are harmless, not a second
  list format. **Doctrine 4, 5, 7, 12.**

### Current tokens

Caption/body/display remain **10/12/20px**, mono for names, drvs, times, IDs and
output. Paper/ink/rules and textual status/color pairs are unchanged from the
table above. Index/graph rows use 2px vertical, 6px horizontal padding; log cells
use 1px/6px; controls 2px/6px. All corners remain square, with no shadows,
decorative motion, cards or new tabs. **Doctrine 3, 5, 6, 9; M2, M3.**

Verification and delivery for this pass are recorded separately below; the
earlier deployment entry does not mean this version has been deployed.

### Executed checks and delivery

Both Meson targets pass (including the six campaign integration groups), as
does the packaged Nix build/check phase. New asymmetric regressions cover
interleaved activities, duplicate phase notifications, exact observed end vs
unobserved end vs running duration, typed error severity, and reported rather
than realized paths.

The installed package was served on port **8125** on runner **swa**, using a
private copy of the closed pre-deployment backup. The read-only Chromium suite
passes at 1440×900, 1440×360, 2560×1440, 1024×600 and 801×600, and in a
390×844 touch context at 2× resolution. It requires actual wheel movement in
the inspector, pane bounds, native keyboard scroll/paging, touch index scroll,
unclipped IDs/messages, styled Find, Wrap, phase jumps, End, Follow/Pause,
clipboard copying, stale-response rejection, lazy next-500 replacement,
fragments, refresh retention and zero idle polling. No JavaScript errors were
reported. Default DOM counts: **450 index**, **971 GTKmm detail**, with no
mounted collapsed static descendants. Built, failed, timed-out, index,
filtered/empty index, mobile detail and expanded mobile captures were inspected
under `.amp/in/artifacts/instrument-release/`.

The checks caught an intrinsic-size `<details>` wrapper that escaped its track:
the 1440×360 inspector was 873px tall despite its 319px parent. Explicit flex
children plus the accessible expansion button corrected it to **223px client
height / 873px scroll height**, with wheel and keyboard access to all content.
The suite now asserts inspector bottom bounds and real scroll movement so that
the previous false-positive geometric checks cannot accept that failure.

This is Chromium touch emulation, not a real iPhone/Safari claim. Original
package failures and the unresponsive-page report are not reclassified or
claimed fixed. Pre-deployment checks did not access the production database,
start a campaign, retry a build or switch the public service.

### Session inspector deployment — 2026-10-04

After explicit operator approval, `/opt/filnix-v2` and its package GC root were
switched to
`/nix/store/k5ikqhz3hhaglz93alqjcl07z8dmb6xs-filnix-campaign-next-0.1.0`,
and `filnix-v2.service` restarted. Before the switch, the service was stopped
and its closed database and manifest backed up to
`/var/lib/filnix-v2/before-session-inspector-20261004T042135Z`.
The previous package remains protected by
`/nix/var/nix/gcroots/filnix-v2-before-session-inspector-20261004T042135Z`.
Service configuration, budgets and manifest were not changed.

The service reports `Existing recording: serving only, no automatic retries`.
The full read-only browser suite passes through **https://nix.swa.sh/v2/**,
including five desktop sizes, Chromium touch navigation/scrolling, styled
Find, Wrap, phase jumps, clipboard copying, static windows, stable fragments,
refresh retention and settled-page idle suppression. No JavaScript errors
were reported. Public desktop, mobile index and mobile failure captures were
inspected under `.amp/in/artifacts/instrument-public/`.

The public API before and after deployment has the same cohort and watermark
**299484**, with **82/82 settled, 80 successful, one failed, one timed out and
zero unattempted**. Admission and live recording remain false; no campaign
events, builds or retries were created. The new version is deployed, not merely
available in a private preview.

## Legibility pass

The previous index gave every root equal weight: 82 identical monospace rows,
names dominated by `-x86_64-unknown-linux-gnufilc0-`, internal counters
(`Events`) and a `Phase / result` column that read `fixupPhase` for every
success. The failed root's actual culprit was only discoverable at the bottom
of its console. This pass changes presentation and two read projections; NXT,
recording, scheduling and raw events are unchanged. It supersedes the
**One index**, **Campaign once** and **Phase ledger** contracts above where
they conflict.

- **Outcome first:** campaign arithmetic → a proportional bar (failed, timed
  out, building, built, already valid, not attempted) with the same counts as
  clickable filter chips. `Follow latest`, settled count, platform and stop
  reason form one quiet line.
- **Needs attention:** every non-successful cohort root is listed above the
  table with its status, first top-level Nix error (e.g. `flac 1.5.0 timed out
  after 300 seconds of silence`) and elapsed time. Timed-out roots name the
  phase they were in.
- **Table:** `Package`, `Version`, `Status`, `Duration`, `Detail`. Names are
  parsed into package and version with the host triple removed; the full name
  remains the cell's `title`. Detail is the first error for failures, the phase
  for timeouts and live roots, and log volume for builds.
- **Projections:** session rows gain `duration_ns` (elapsed time of the run's
  last event, a primary-key lookup) and `cause_hex` (the first level-0
  `nix.message`). Cohorts gain `built` / `already_valid`. Log rows gain
  `activity_name`, the derivation name behind the activity.
- **Failure card:** the inspector's reason line → `Why it failed`, the recorded
  top-level errors in order from the derivation that broke first to the
  selected root, each with a `Show in log` jump to its sequence number. Nodes
  in that chain are highlighted in the dependency list. Timeouts and
  interruptions keep their single reason plus phase and elapsed time. These are
  Nix's own reports, not an inferred culprit.
- **Quieter inspector:** `Events` → `Duration`; an empty phase ledger is
  omitted; phases show a proportional bar; build-platform tools recede behind
  Fil-C packages in the dependency list. The console's `Activity` column shows
  the derivation name, with the numeric id kept for copying.
- **Visual system:** proportional type for UI and monospace only for
  paths, versions and logs; a type scale; status pills; fewer rules; a dark
  scheme via `prefers-color-scheme`.

`meson test` and the read-only browser suite (`tests/test_observatory.py`)
pass against a copy of the deployed recording.

### Deployment — 2026-10-04

`/opt/filnix-v2` and `/nix/var/nix/gcroots/filnix-v2-package` now point to
`/nix/store/0lnbz96zp2dx57w3p0lf4s7k05xh8js1-filnix-campaign-next-0.1.0`, built
from this pass. The service was stopped, and its closed database and manifest
were backed up to `/var/lib/filnix-v2/before-legibility-20261004T050129Z`. The
previous package remains rooted as
`/nix/var/nix/gcroots/filnix-v2-before-legibility-20261004T050129Z`. Service
configuration, budgets and manifest are unchanged.

The service reports `Existing recording: serving only, no automatic retries`.
The full read-only browser suite passes through **https://nix.swa.sh/v2/**
with no JavaScript errors. The public API still reports watermark **299484**,
**82/82 settled, 80 successful, one failed, one timed out, zero unattempted**.
