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
Importing the patch alone does not enable a Boost port.

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
