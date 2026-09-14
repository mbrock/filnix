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
