# Shared-library campaign repairs

## ICU 76.1

The upstream `ports/patch/icu-76.1.patch` was already extracted, but no port
applied it to Nixpkgs' `icu76` attribute (`icu` aliases that attribute; its
package name is `icu4c`). The port now applies it and regenerates configure,
with pkg-config supplying the required Autoconf macro.

Nixpkgs cross builds use a native ICU build root. Its `pkgdata` can emit ELF
directly, bypassing Fil-C even when target configure disables assembly.
`patches/icu-cross-data.patch` adds `--without-assembly` to data, test fixture,
and uconv message generation. This uses pkgdata's C output and the target
compiler, preserving Fil-C symbols and capabilities. The native build root
and compiler are unchanged.

Validation on 2026-09-14:

- ICU and `checks.x86_64-linux.icu` build successfully.
- The package check and installed consumer exercise normalization, Windows-1252
  conversion, locale collation, and supplementary-character UTF-8 conversion.
- The package check also runs the target `uconv -V`.
- ICU disables its upstream suite for cross builds. The default Nix `make test`
  finds the `test/` directory and does nothing, so an explicit runtime check
  replaces it. These results do not claim the complete ICU suite passes.
- Final ICU derivation: `x0v906lxsgaf8l6q1hlnlp916cjjhlnk`.
- Compiler derivation remains `01r837vgn2lsxxv1bwxwi415zv77hds0`.

The current campaign graph identifies 307 failed/blocked package attributes
whose only recorded failing dependency is the old ICU derivation. They are a
bounded retry selection, not a prediction of 307 successful builds. This count
includes aliases and consumers in other languages and omits evaluation errors
without dependency graphs. Revised attempts retain their original history.

## Patch ownership

Generated upstream patches stay in `ports/patch/`; local integration changes
stay in `patches/`, applied afterwards. The extraction and clean commands now
protect the local directory. `tests/upstream-sources.py` passes all seven tests,
including real Projeny import and protection against symlinked output paths.
See [upstream updates](upstream-updates.md) and [local patches](../patches/README.md).

`ports/patch-sources.json` also supports verbatim standalone patch imports.
The pinned upstream revision already has `pizlix/boost-filc.patch`, which the
project-subtree extractor previously missed; it is now imported separately.
The Boost port explicitly applies it before the local integration patches.

## GLib type registration and introspection

`patches/glib-gtype-api-ceiling.patch` repairs GLib's old-API-ceiling branch.
Fil-C's GType is always a pointer, even when an application requests an API
older than 2.80. Private typed once helpers retain the atomic fast path and
use the pointer once functions internally. Availability-warning suppression is
limited to those helpers; the application's public API ceiling still applies.
The check compiles C and C++ against ceilings 2.38, 2.56, 2.74 and 2.80, then
concurrently exercises object/interface and boxed registration, and enum/flags
registration where available.

The Fil-C scope now supplies the Meson variant to all consumers. Its
`mkenums_simple` template is maintained as `patches/meson-gtype.patch` and is
verified with an actual generated enum library. Native Nixpkgs keeps its normal
Meson. The duplicate GTK4-specific Meson override is removed.

The introspection scanner previously mutated LD_LIBRARY_PATH for its target
dumper before launching the native linker. With zlib in the scan's library
paths, the linker loaded Fil-C's libz and failed to resolve native `compress2`.
`patches/gobject-introspection-link-environment.patch` snapshots the linker's
environment before preparing the dumper environment. A standalone scanner and
typelib compilation check deliberately adds target zlib to reproduce that case.
The modified introspection package passes its 60 tests.

The upstream libsoup 3.4.4 patch applies to Nixpkgs' 3.6.5 source. A separate
local adaptation covers libsoup 2.74.3's enum template, tagged signal types,
session feature keys and test fixtures. Both versions build, and installed
consumer checks verify loopback HTTP, cookie replacement signals, and disabling
a session feature for a request. Nixpkgs disables the complete libsoup suites
for known failures; these checks do not claim those suites pass.

Libnotify also builds with these changes. The compiler derivation remains
`01r837vgn2lsxxv1bwxwi415zv77hds0`; GLib and its consumers rebuild as expected.

GTK3 and PyGObject also pass their installed runtime checks with the repaired
stack. The first 17 GLib follow-up candidates produced eight built attributes:
cmusfm, gnome-autoar, libnotify, libsoup_2_4, libsoup_3, phodav, tg and wmderland.
Further failures are recorded separately rather than counted as successes.

## Libhandy and signal type consumers

Libhandy's tests need a display backend enabled in Fil-C GTK3. The reusable
`toolchain/broadway-check.nix` replaces Xvfb with Broadway, waits for a real GTK
connection, supplies fonts and respects the build's test parallelism limit.
It retains the package's surrounding environment and test command.

Running the suite exposed a use-after-free in libhandy 1.8.3. During container
destruction, `set_visible_child_info` skips transitions and returns without
clearing the visible-child pointer. Removing that child frees its bookkeeping;
removing the next child dereferences the stale pointer. The local
`libhandy-destroy-visible-child.patch` clears it during destruction, preserving
normal transitions outside destruction. Existing Deck and Leaflet navigation
tests reproduce the failure and verify the fix.

The target has no Rust SVG loader. Native GTK and librsvg tools convert the
five bundled SVG icons to GTK's encoded symbolic PNG format at build time.
The resulting resource keeps symbolic recoloring and removes the runtime SVG
loader requirement for these icons. This rasterizes them at 128 pixels; it does
not add general SVG support to the target. Libhandy passes all 30 test groups,
including avatar drawing, with no test exclusions.

GSSDP's static signal argument is adapted with Fil-C's pointer-tagging operation,
retaining the GType capability. Both its functional and regression groups pass.
GtkSourceView 3 and 4 need the same treatment for text-iterator and event types;
the release-specific patches stay separate because their surrounding code differs.
Version 3 passes its 22 program tests plus language/style validations after adding
the missing native xmllint tool. Version 4's suite is re-enabled and all 23 groups
pass against the pinned GLib stack. Both suites run through Broadway.

## Campaign retries and logging

The 307 ICU candidates were explicitly replanned from commit `438ffa8`, with
prior recipes and attempts preserved. At the first completed snapshot, six
attributes were built: icu, icu76, darling-dmg, hfst-ospell, prosody and thelounge.
Most remaining candidates have reached another failed dependency. In particular,
Node.js 22 now fails linking a V8 generator against `pizlonated___libc_stack_end`;
that is a separate runtime/porting issue, not an ICU data failure.

Those retries also exposed a runner problem: Nix's download progress counters
could consume the entire 128 MiB log allowance before meaningful work completed.
Runner 0.12.3 filters only those counters before accounting for retained logs;
build output, phase events, errors and unknown records remain intact. All 108
runner tests pass. A completed live batch omitted 2,065,525 such records
(185,323,508 bytes), retained its build output, and finished without truncation.
The existing CPU reservation and 80 percent memory limit remain in force.

## Boost 1.87

The pinned upstream revision already supports Boost.Context and Coroutine2 using
ucontext. Its standalone patch was previously absent from the project-subtree
imports. The port now applies that patch and follows the upstream build recipe:
`context-impl=ucontext --without-coroutine`. This excludes legacy Coroutine v1,
which requires fcontext; it does not exclude Coroutine2.

Two local integration patches follow the unchanged upstream patch:

- `boost-context-feature.patch` moves B2's existing context implementation feature
  declaration into the shared feature file, so Boost 1.87 recognizes the command
  line before lazily loading the Context Jamfile.
- `boost-gdb-scripts.patch` selects Boost's existing embedded-GDB-script opt-out
  in the Fil-C compiler configuration. This applies to installed headers too;
  JSON and Unordered otherwise emit module assembly rejected by Fil-C. See the
  [Boost maintainer discussion](https://listarchives.boost.org/Archives/boost/2024/09/257956.php)
  for the shared opt-out macro.

The checks exercise Coroutine2 yields and resumption, pointer mutation across
suspension, explicit GC on both sides, exception propagation, and destruction of
a suspended coroutine. They also cover MultiIndex insert/erase/lookup (including
the upstream capability-preserving node change), JSON parsing and Unordered
storage across GC. The continuation API has a separate executable because
Boost's two ucontext headers define conflicting internal forced-unwind types.
Neither check manually defines BOOST_USE_UCONTEXT: the installed headers must
select it automatically. These are focused runtime checks, not the entire Boost
suite. The full Boost package build and both installed-consumer executables
pass. The compiler derivation remains unchanged.

All 141 selected Boost candidates were replanned from `b60f3a2`; their first
batches are running. They were selected because Boost 1.87 was their only
recorded failing dependency. Older explicitly selected Boost versions are not
silently redirected to this release.

The five GTK follow-ups were also replanned from `b60f3a2`: libhandy, GSSDP and
both GtkSourceView versions became built; GUPnP reached its own GType failures.
The subsequent `gupnp-gtype.patch` preserves type pointers in resource tables,
uses pointer-valued GOnce for the default factory, and adapts fundamental-type
switches without reconstructing pointers from integers. Its existing context,
context-filter and bug-regression groups all pass. The old size-based once API
had caused a null-capability trap on the default factory in the bug suite.

Remaining follow-up candidates include gtk-doc's generated GType scanner
(librest still fails there) and the Node.js/V8 runtime assumptions described
above. These are recorded failures, not disabled tests or claimed successes.
