# Fil-C 0.687 port import

The release and ports pins select upstream tag `v0.687`, commit
`2db72c646daa1acad2754bcb0e2f220f732e9789` (October 23, 2026).
The previous ports tree was `b6dd63481f796f8bff8502165c7dfc61091dbbd6`;
the previous native Projeny tool was `a9656434c906`.

## Reproduction and boundaries

This follows the pinned-Git importer introduced in Filnix `75efb14609af`
and the version-audit boundary documented in `d077ec4e259e`:

```sh
python3 scripts/update-ports-pin.py --repo /tmp/filc-diff/fil-c --rev v0.687
nix build .#projeny -o .amp/in/projeny
mkdir -p .amp/in/tmp .amp/in/port-review
TMPDIR="$PWD/.amp/in/tmp" PROJENY="$PWD/.amp/in/projeny/bin/projeny" \
  make -C ports -k -j4 REPO_DIR=/tmp/filc-diff/fil-c REV=v0.687 \
  OUTPUT_DIR="$PWD/.amp/in/port-review"
```

Use disk-backed scratch space: concurrent large Projeny reconstructions
exhausted SWA's `/tmp` tmpfs on the first attempt. The affected imports were
rerun successfully with the workspace as `TMPDIR`, except for the three
missing archives below. The import reads committed Git blobs, not the
upstream checkout or its generated build files. URL downloads are verified
against the BLAKE3 hashes in the descriptors.

The refresh adds 41 patch files and regenerates ten existing files.
Review output is copied into `ports/patch/`. Historical patches for versions
no longer in the upstream tree remain available to existing consumers.
The unchanged Lute tree's 19 MiB vendor-removal diff is left in review output,
not introduced as an unrelated new patch by this update.
`ports/patches.nix` is an inventory, not the overlay: new inventory entries
do not switch the versions selected in `ports.nix` or `pyports.nix`.
No wholesale version upgrade or new GNOME package declaration is hidden in
this import. The audit still evaluates 300 declarations: 271 match Nixpkgs,
24 are older, two newer, and three have custom version schemes.

## Upstream changes and disposition

| Upstream change | Filnix disposition |
| --- | --- |
| Projeny descriptors grow from 18 to 80 (62 additions, none removed), with more ports converted to hash-verified URL downloads | Pin Projeny and the import tree together; import both directory and descriptor ports through the existing filters. |
| `b135de8b2863`: Projeny accepts more unified patch formats, including plain `---`/`+++` blocks and differently prefixed paths | Use the new native Projeny; its packaged suite passes 3,147 tests. The existing URL/archive importer remains compatible. |
| `0708cc768ace` and `2db72c646daa`: Peregrine distribution assembly copies the Cosmo license, changes welcome text and documents ARM64 binutils | These change upstream `package-build.sh`, **not Projeny's builder**. Filnix does not invoke that distribution script and remains glibc-only. |
| Added `usercosmo` and `yolocosmo` trees | Exclude them from the application importer alongside musl/glibc; they are compiler/runtime inputs, not ordinary ports. No Cosmo runtime patch is adopted here. |
| Added `zegarmistrz` | Retain its generated patch as an available input, without declaring a new Filnix package. |
| Removed directory trees: `coreutils-9.11`, `git-2.55.0`, `mesa-24.1.5`, `openssh-10.5p1`, `pcre2-10.48`, `xxHash-0.8.3` | These are conversions/rebases to descriptors, not removal of the applications. Preserve old patches used by curated versions and import their new descriptor versions. |
| New/rebased versions include Brotli 1.2.1, ICU 79.1, pkgconf 3.0.10, mg 4.5, curl 8.23.0, Git 2.56.0, OpenSSH 10.6p1, OpenSSL 3.6.5, PCRE2 10.49, PostgreSQL 18.6, PHP 8.4.25 and util-linux 2.42.4 | Import available patches; empty-patch ports such as Brotli/pkgconf need no patch file. Keep existing source/version selections unless an active patch changes. |
| GNOME/Mutter/GJS/SpiderMonkey and support-library ports | Import available descriptor patches, including the 46.9 shell/compositor and SpiderMonkey 115.10.0. These remain candidates, not a claim that Filnix builds a GNOME desktop. |
| libarchive 3.7.4 | Refresh the active patch: tolerate `EPERM` from `lchmod` on Linux symlinks and update its corresponding test. |
| libxkbcommon 1.11.0 | Import its conditional X11-test patch, but do not apply that new hunk to Nixpkgs' 1.13.1 source: the test layout has changed. Move the existing version-script adaptation to a separate local patch. Our port already disables X11, so it does not need the conditional X11 tests. |
| OpenSSL 3.6.4 directory port | Refresh the active SaRCAsm annotations/generators from upstream. Keep the separately imported 3.6.5 descriptor patch available without switching the safe-assembly package's source. |
| PyGObject 3.48.2 | Refresh its active pointer-valued GType handling and import/registration fixes. Upstream now includes the same bootstrap-metaclass NULL guard, so remove our redundant local patch rather than apply it twice. |
| Mesa 24.1.5, WebKitGTK 2.44.3, ICU and Linux | Refresh available patches; the changed historical patch files are not used by current active declarations. |
| Python 3.12.5 and Bash 5.3 | Move Python's existing C++ `void *` conversion fix out of generated material into `patches/python-code-header-cxx.patch`, applied after the exact upstream patch. Bash's generated patch gains `a/` and `b/` prefixes; apply it separately with `-p1` after Nixpkgs' `-p0` patches, for both shell variants. |
| Experimental zstd-sarcasm | Restore semicolon statement parsing only in the port's private assembler. This was already absent in release 0.686. Oracle review required preserving tagged diagnostics and all lock/rep prefixes; the rebased patch does so without changing codegen or the default assembler. Keep the original strict check and extend its prefix/location/numeric-label coverage. |
| OpenEXR rebuild | 125 of 126 tests passed; the exhaustive threaded tile test continued making progress but hit CTest's 1,500-second default under load. Give that single test a 7,200-second bound without removing cases or disabling it. |

The three descriptors `duktape.projeny`, `libsndfile.projeny` and
`pygobject.projeny` refer to `duktape-2.7.0.tar.xz`,
`libsndfile-1.2.2.tar.xz` and `pygobject-3.48.2.tar.xz`, respectively, but those
archives are absent from the tagged tree. The importer correctly fails those
targets. No unverifiable replacement archive or invented hash is used.
PyGObject's still-present directory port supplies its refreshed patch;
Duktape/libsndfile gain no new patch from these incomplete descriptors.

## Validation scope

The complete matched 0.687 compiler/runtime builds. Native Projeny's 3,147
tests and the 11 source/import isolation tests pass. The release driver
still emits ELF with the Filnix `ld-fil1-x86_64.so` loader, not a portable APE.
All 66 selected upstream setjmp, safepoint, memmove, fiber, by-value ABI and
UB regressions pass through the upstream harness with the release runtime.
Both Bash variants pass the errexit smoke; Python's decimal smoke and the
C++ internal-code-header compilation pass. The experimental Zstd check passes
its strict parser/access tests, 200 decoder comparisons and 36 cross-codec
round trips with the isolated assembler backport.
OpenEXR's full 126-test suite passes with the bounded timeout adjustment;
the threaded tile test completes in 723 seconds on the successful run.

Six staging-only `fork-regressions` fail on release, identically to 0.686;
their assertions and experimental runtime semantics are left unchanged.
