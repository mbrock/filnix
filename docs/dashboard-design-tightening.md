# Campaign monitor: design tightening

Implementation scope: `experiment/dashboard`, its compiled stylesheet, and
dashboard tests. No scheduler, compiler, outcome attribution, or production
configuration changes. The live review on 2026-10-01 found **Fil-C 0.686 ·
integrated ports · main c940a48**, campaign
`390c9340-6650-4458-99df-b113b3a6d3ce`. Campaign and batch IDs are discovered,
not fixed by the browser check.

## Decisions

- Keep the batch reader, not an invented campaign-wide interleaved stream.
  Name it **Current batch log**, identify the selected batch, and retain the
  next-batch follow mechanism.
- Keep **Built** as operator vocabulary; emit `state=built`. Old
  `state=available` package links redirect without losing other parameters.
  Stored controller state and the compatibility JSON API remain `available`.
- Packages: 100 rows/page. Batches: 50 rows/page, with a page-local timeline.
  Export the complete filtered package set, not the current page.
- Remove descriptions entirely from list HTML, including tooltip payloads.
  Keep them in package detail and CSV. Primary batch names use `name +N`.
- Expose reader controls and controller freshness. Move interpretive prose to
  disclosures, preserving the evidence and taxonomy behind it.
- Keep stone/paper chrome, tables, HTMX/SSE, inspectable URLs, and no motion.

## Doctrine and attribution

Sources: [Office](https://usgraphics.com/) and
[TX-02 Berkeley Mono datasheet DX-102-11, page 36](https://usgraphics.com/static/products/TX-02/datasheet/TX-02-datasheet.a43c0c7f8d8c.pdf).
Company framing: visual representation of information, relentlessly pursuing
accurate and truthful interpretation. Tagline: **Engineering graphics for
professionals.** Checklist numbering below follows the supplied wording:

1. Emergent over prescribed aesthetics.
2. Expose state and inner workings.
3. Dense, not sparse.
4. Explicit is better than implicit.
5. Engineered for human vision and perception.
6. Regiment functionalism.
7. Performance is design.
8. Verbosity over opacity.
9. Ignore design trends. Timeless and unfashionable.
10. Flat, not hierarchical.
11. Diametrically opposite of minimalism, as complex as it needs to be.
12. Driven by objective reasoning and common sense.
13. Don't infantilize users.

**Operator amendments — Mikael Brockman, not USGC quotations:**
M1: labels ≠ explanatory prose; put detailed truth in state, diagnostics,
details, and docs. M2: few font sizes, at most three stops. M3: skeptical of
padding; minimum functional spacing, horizontal usually greater than vertical.

## Per-surface rules

| Surface / work item | Before → after, exact strings, and contracts | Checklist |
| --- | --- | --- |
| Shared header / P0.1 | `Live log` → `Current batch log`. `/campaigns/{cid}/log` selects an active build before an active plan; an active plan outranks a finished build. With no active request it shows the latest build (or latest plan if no build exists), whose terminal status remains explicit. Page title includes the batch's eight-character ID; reader heading links to `Batch log · Build · {id}` or `Batch log · Plan · {id}`. No batch: `No batch has been requested in {campaign}.`, under `Current batch log`, with automatic retry. Captured-output absence names `Batch {id} has no captured diagnostic output.` Do not claim this is all concurrent campaign output. | 2, 4, 8, M1 |
| Activity / P0.2 | `Full request ledger →` → `All batches →`, destination Batches. Recent request membership is first requested name + `+N`; full membership on batch detail. Preserve the forest, phase text, failure taxonomy, blast radius, request-time tooltips, Pause, and collapsed request history. | 3, 4, 12, M1 |
| Packages / P0.3 | Canonical select pairs: `built` / `Built`, `tested` / `Tested`, `failed` / `Failed`, `failures` / `Failures`, `evaluation-error` / `Evaluation error`, `blocked` / `Blocked`, `tried` / `Tried`, `all` / `All`. Title: `Packages · {selected label} · filnix`. “Built” continues to include Tested; Failures continues to include failed, evaluation-error, and inconclusive. Do not rename database states or alter those predicates. | 4, 12, M1 |
| Packages / P0.4 | Prose beneath each name → `Package`, `Version`, `Status` columns. Package: proportional 14 px, one line with ellipsis and full name in `title`, persistent numeric ID in the detail URL. Version: mono 14 px, `—` if absent. Status: explicit existing text; diagnostic remains in `title`/detail. No synopsis/description bytes in list rows. No cards, no removed detail data. | 3, 5, 7, M1 |
| Packages / P0.5 | Long facet chrome and always-on disclaimer → `All facets`, `Pkg · {facet} ({count})`, `Diag · {facet} ({count})`, `Patch · {facet} ({count})`. Namespace and full facet name remain intact; a selected missing facet stays selectable with `(0)`. Closed `Notes` contains the ≥80% threshold, browsing-only qualification, unknown/unclassified notice, and evidence instruction. Count facets over the whole state-filtered set, not the page. Preserve provider comparisons and probabilities in detail. | 4, 8, 11, 13, M1 |
| Packages / P1.7, P2.12 | Overflow export → visible `CSV ↓`. Show `Snapshot · {time}`, total packages, `start–end / total`, `← Previous`, `Next →`. 100 rows/page; `page` is zero-based and preserved by refresh links. Filters reset page by omitting it from form submission. CSV ignores page. Snapshot rows do not silently morph while being scanned. | 2, 4, 7, M1 |
| Batches / P0.6 | Comma-list membership → first requested name plus `+N` in the Batch cell. Second line: `Build`/`Plan`, mono eight-character ID, mono UTC request start, tested count if present. Result retains the full outcome label and log link; Time is mono request elapsed time, not summed build time. Keep Gantt and full requested set in detail. | 3, 4, 5, M1 |
| Batches / P2.12–13 | Complete ledger dump → 50 rows/page after all filters and sorting. Same page controls as Packages. Search input `Batch or package`; simple selects immediately submit a GET and update the URL. `Search` is the explicit text-search submit and no-JS fallback. Preserve kind/outcome/sort/q/transport and reset page on filter changes. Searches still include all recorded package/build aliases, not merely the displayed first name. | 4, 7, 13, M1 |
| Batches timeline / P2.17 | Unexplained colored bars → adjacent `Request time · Build / Plan · this page` legend: `▶ Running`, `✓ Finished`, `! Errors / interrupted`, `? Outcome unknown`. Bars carry corresponding glyphs; running bars also have dashed outlines. Build and Plan lanes remain labelled. Tooltips include names, duration, and recorded status. The timeline covers the displayed page, not undisplayed history or machine utilization. | 2, 4, 5, 8 |
| Blockers / P1.8 | Definition paragraph → terse aggregate `N failures · N packages blocked · N with multiple blockers`. Closed `Notes`: `Only cause = sole blocker.` plus the original recovery implication. Keep `Failure`, `Blocks`, `Only cause`, ranking, counts, evidence-owner links, examples, and glyph-free text legibility. No change to the ranking algorithm. | 3, 4, 8, M1 |
| Dependencies / P2.14 | Three columns of neighbor boxes → full-width focused derivation followed by adjacent Inputs / Consumers tables (stacked at narrow widths). Focus includes mono full drv path, state, phase, evidence owner, `Request time`, aliases, selected-dependent count, and `Blockers` link. Neighbor columns: `Derivation / role / outputs`, `Status / phase`; derivation name links to focus, full path in title, role/origin and required outputs on caption line, Log when evidence exists. Both tables render even if empty: `None in this view`. Preserve bounded neighborhood paging, `available` toggle, `focus`, observation semantics, and retry warnings. Ready does not claim local build or tested output. | 2, 3, 4, 10, 11, M1 |
| Log / P1.7 | `•••` → no overflow: visible `Size 12 px` / `Size 14 px` / `Size 16 px`, `Wrap on` / `Wrap off`, `Find in window`, `Find`, `Download raw log ↓`. `Resume` → `Follow`; running reader control remains `Pause`. Selects submit immediately; `Show` remains for drv source. Preserve follow/wrap/size/q/drv/transport and next-batch-follow state, pause anchoring, byte cursors, bounded recovery, raw download, and search-window scope. | 2, 4, 7, 8, 13, M1 |
| Batch detail / P2.14 | Sparse requested-name list and two-column build list → `Requested packages · N` disclosure containing Package / Derivation table; open by default at ≤12 requested roots. Build table: `Build`, `Status`, `Phase`, `Build time`, `Dependencies`. Each build links to its drv-filtered log and `Inputs / consumers`; path is inspectable in title/focus. Build time uses recorded activity start/finish, running elapsed time only while building, `—` when unknown. Request elapsed time stays distinct in sticky heading. Preserve unknown/awaiting-result explanations and terminal error diagnostics. | 2, 3, 4, 8, M1 |
| Shared heartbeat / P2.15 | Stale-only Activity banner → every-page `Controller {mode} · fresh · {age} ago · {UTC}` when running and <30 s old; `stale` at ≥30 s or missing heartbeat; paused mode uses `last`, not `fresh`. Missing heartbeat: `never reported`. Independent five-second HTML refresh continues after SSE completion; a failed request uses the existing connection warning. Keep the stale Activity warning too. Do not equate a fresh controller with progressing/successful builds. | 2, 4, 7, 8 |
| Activity footnote / P2.16 | Long always-on view-semantics sentence → always-visible `stopped ≠ succeeded`; `View notes` disclosure holds `Partial dependency view; shared dependencies shown once per request.` Do not infer success from an ended Nix activity. | 4, 8, M1 |

## Shared tokens / P1.9–11

These apply checklist 5/6/9/10 and operator amendments M2/M3.

- Three stops: caption **12 px**, body/control **14 px**, display **16 px**.
  Existing log sizes share these stops. Body line-height 20 px; caption 16 px;
  no additional hero typography. SVG timeline glyph geometry is not UI prose.
- Proportional system sans for package names, labels, and status. System mono
  for UTC times, durations, versions, hashes, short IDs, store/drv paths, numeric
  comparisons, and log bodies. Disable mono ligatures. Do not add a font asset
  or imply that DX-102-11 requires licensing/installing Berkeley Mono.
- One-pixel stone rules, square controls. Text cells and controls: **8 px
  horizontal / 2 px vertical**. Section gaps 4–12 px, only where boundaries
  need separation. Preserve focus outlines, native select mechanics, horizontal
  scrolling on genuinely wide detail tables, and sufficient error-text contrast.
- Packages: Version 112 px; Status 144 px; Package takes the remainder. At
  narrow widths Version 72 px, Status 112 px; status may wrap, not disappear.
  Neighbor status column 144 px. Do not truncate diagnostics in detail to save
  a screenshot. Do not encode outcomes solely in bar widths or colors.
- Status supplement: Built = stone-600 + `Built`; Tested/Finished = emerald-800
  + their text; Running/Building/Starting = sky-800 + their text;
  Failed/Finished · errors/Eval error = red-800 + their text;
  Blocked/Timed out/Resource limit/Interrupted/Cancelled = amber-800 + their text;
  unknown/awaiting/queued = stone-500 + their specific text. Existing forest
  glyphs stay. The full taxonomy, not the hue, determines interpretation.

## Reviewable diff groups and verification

1. Resources + data + routes: canonical vocabulary, pagination, full CSV,
   batch timing reads, heartbeat endpoint, current-batch selection.
2. Views + reader: terse scan paths, visible controls, flat detail tables,
   disclosures, immediate select navigation, explicit timeline legend.
3. Styles + regression checks: repeatable stylesheet source, three stops,
   mono/padding rules, asymmetric pagination/timing/freshness regressions,
   live/local Chromium walk and screenshot evidence.

The initial design pass did not reload production services, push, or merge.
The subsequently authorized web-only deployment is recorded below.
List paging bounds HTML/DOM; catalog and batch reads still collect the full
filtered data before slicing. This is not SQL/keyset pagination and does not
claim to eliminate backend scan cost. Offset pages refer to a newly sampled
snapshot; use the snapshot time and refresh affordance rather than assuming
that page boundaries freeze a running campaign.

```sh
# Python environment: nix-build experiment/python.nix --arg testing true
python -m unittest discover -s tests -p test_dashboard.py
tailwindcss -i experiment/dashboard/static/dashboard.source.css \
  -o experiment/dashboard/static/dashboard.css --minify
# Tailwind CLI 4.3.1 from the pinned nixpkgs; compiled CSS is checked in.
node tests/dashboard-design-browser.mjs BASE OUTPUT
# Audit an unmodified live deployment without post-change assertions:
node tests/dashboard-design-browser.mjs https://nix.swa.sh OUTPUT audit
```

The browser walk uses the repository's existing Chromium CDP workflow. It
checks URL changes, page caps, HTML budgets, type stops, log settings and Pause,
desktop/narrow layout, and JavaScript errors; captures at 2×. Unit tests cover
first/second/final pages, clamping, full CSV, global facet counts, state aliases,
30-second heartbeat boundary, empty logs, and 17-second build timing versus a
133-second request. Screenshots are review evidence, not a substitute for those
executed checks.

Observed delivery checks (2026-10-01): 33 dashboard tests and 152 experiment
tests passed. The dynamic browser walk passed against the final read-only
preview on runner `swa`, loopback port 8796, at 1440 px and 390 px (2× captures).
It exercised recorded error logs and empty current-batch logs, including Pause
with zero lines, and captured a grayscale Batches check. The older browser
scripts' fixture-specific expectations were updated for paging and exposed
settings; those fixed-campaign scripts were syntax-checked, not rerun.

| Uncompressed HTML | Live before | Final preview | Visible rows after |
| --- | ---: | ---: | ---: |
| Packages, `state=all` | 12,834,066 bytes | 100,848 bytes | 100 |
| Batches, default filters | 4,334,562 bytes | 117,410 bytes | 50 |

The campaign continued changing during the walk; these are independently
sampled responses, not a frozen-data benchmark. The initial live inventory
contained 14,647 packages and its Batches response contained 2,266 requests.
No production changes were made during that initial review. The browser checks
read SQLite and recorded logs only; unit tests use isolated temporary fixtures.
The temporary whole-database snapshot was discarded; the preview reads the
existing state through the read-only dashboard connection.

## Authorized deployment: swa, 2026-10-01

The user subsequently requested deployment to `https://nix.swa.sh` through swa.
Built the existing Nix application package from the installed source with only
the nine reviewed dashboard files overlaid. A recursive comparison verified
that all non-dashboard application files remained identical to the installed
version; unrelated worktree changes were not included. The packaged dependency
environment is unchanged. The 33 dashboard tests passed against this isolated
source before installation.

Updated `/opt/filnix-experiment` atomically and restarted **only** `filnix-web`.
No controller restart, schema migration, unit-file update, or Git push/merge
was performed. Controller PID `2927760` remained unchanged. The old web process
reached systemd's stop timeout; public health recovered immediately after the
new process started.

The initial public browser walk passed all surfaces, paging/filter URL changes,
log Size/Wrap/Follow/Pause (including an empty current-batch log), no-JS Packages,
desktop/narrow layouts, and JavaScript exception checks. Inspected live Packages,
grayscale Batches, and log screenshots. Public SSE returned
`text/event-stream`, a campaign-change event and a heartbeat. Packages shipped
100,929 uncompressed bytes (100 rows), Batches 117,355 bytes (50 rows).

A separate proxy check found that the legacy `state=available` redirect used an
absolute HTTP URL behind Caddy. Changed it to a relative redirect and added
regression assertions for absent scheme/host and the exact path. All 33 tests
passed again; rebuilt and installed the corrected package. The public redirect
now preserves HTTPS, `page`, and `transport` while emitting `state=built`.
The complete public browser walk passed again against that final package;
Packages measured 100,928 bytes and Batches 117,292 bytes. Its representative
Packages screenshot was inspected, and `/healthz` remained healthy with zero
automatic web-service restarts.

Installed package:
`/nix/store/xd1pajh3qlys6ky0y5b0g9vbn2xzw8lx-filnix-experiment-0.18.0`.
Previous package, retained by a Nix GC root under the review artifacts:
`/nix/store/9fx89jqxhg9mvi4ig70dh1xgjk1izpwf-filnix-experiment-0.18.0`.
The source changes remain uncommitted. Review patches and live screenshots are
under `.amp/in/artifacts/design-tightening/`.

Web-only rollback, if needed:

```sh
sudo ln -s /nix/store/9fx89jqxhg9mvi4ig70dh1xgjk1izpwf-filnix-experiment-0.18.0 /opt/.filnix-experiment-rollback
sudo mv -Tf /opt/.filnix-experiment-rollback /opt/filnix-experiment
sudo systemctl restart filnix-web
curl -fsS https://nix.swa.sh/healthz
```
