# Updating Fil-C sources and ports

Filnix tracks two revisions of the same upstream monorepo:

- `lib/filc-upstream.json`: `coreRev` selects the compiler, runtime, libc,
  libc++, compiler-rt, yolounwind and the SaRCAsm/minilute sources. `lib/filc-hashes.json` records
  their content hashes at that revision.
- `ports/upstream.json`: `portsRev` selects the Git history and tree used to
  extract application patches. Nix builds consume the checked-in patches and
  package archives. The native Projeny package uses the same revision and its
  separate `projenyHash`, fetching only `projects/projeny/`.

A ports update therefore does not change the compiler's derivation. The glibc
forks under upstream's `projects/` directory belong to the **core** pin: they
participate in its ABI and bootstrap. Directory location alone is not the
boundary. New application patches can still require a newer compiler/runtime
feature; test each updated port with the pinned toolchain before accepting it.

## Update application patches

Fetch the upstream clone, then update the ports pin and Projeny source hash
atomically. This reads the selected Git tree without changing the checkout:

```sh
git -C "$HOME/fil-c" fetch origin deluge
python3 scripts/update-ports-pin.py --repo "$HOME/fil-c" --rev origin/deluge
```

List the projects present at that revision:

```sh
make -C ports list REPO_DIR="$HOME/fil-c"
```

Regenerate selected patches (the targets run even when patches already exist):

```sh
make -C ports patch/gettext-0.22.5.patch REPO_DIR="$HOME/fil-c"
# Equivalent, with the revision read from ports/upstream.json:
ports/extract-patch.sh gettext-0.22.5 "$HOME/fil-c"
```

Use `nix develop -c make -C ports -j4` to regenerate all projects at the pin. Review the
resulting diffs and update package versions/hashes in `ports.nix` or
`ports/patches.nix` when necessary. The pin is the default for future extraction;
it does not claim that every existing, curated patch was extracted at that
revision, nor does changing it automatically upgrade all ports.

The extractor diffs the original import against the pinned tree. Other
branches, later commits, dirty files and untracked build artifacts do not
participate. An explicit fourth argument overrides the pin for investigating
an older project version that no longer exists at the default revision:

```sh
ports/extract-patch.sh PROJECT "$HOME/fil-c" /tmp/patch-review FULL_COMMIT_ID
```

## Projeny ports

`nix build .#projeny` builds the native C++ tool and runs its upstream test
suite. It is also available in `nix develop`. Its runtime archive helpers are
wrapped into PATH; it has no dependency on the Fil-C compiler or runtime.

The importer accepts `.projeny` descriptors alongside vendored directories:

```sh
nix develop -c make -C ports libffi.projeny
# Writes ports/patch/libffi-3.8.0.patch, using the descriptor's Origname.
nix develop -c ports/extract-patch.sh libffi.projeny "$HOME/fil-c" /tmp/patch-review
```

Fil-C’s own Projeny, minilute and SaRCAsm directories are excluded from
release-patch extraction.

The importer reads the descriptor and original archive from the pinned Git
tree, uses Projeny to reconstruct the port in a temporary directory, and compares that
with the original release through the same filters as other ports. Generated
Autotools files are omitted, so the libffi derivation runs autoreconf. Neither
a developer's Projeny worktree nor its status files participate in extraction.
Errors preserve the previous patch. Binary changes are rejected explicitly:
Projeny's binary encoding is not Git's, and Nix's ordinary patch phase cannot
apply binary diffs. Such a future port should consume materialized source.

Run importer regression tests with the packaged tool available:

```sh
nix develop -c python3 tests/upstream-sources.py
```

### Initial September 2026 ports refresh

The ports pin is `4867f1179f1c3dbe5484ec0f98c2fcc7d401e50c`. Existing checked-in
patches were regenerated for their existing versions; libffi moves from 3.4.6
to Projeny's 3.8.0 and uses upstream's closure allocation fix. Archived patches
for ports not currently enabled are retained, but regeneration alone does not
validate those packages. In particular, the OpenSSL 3.5.7 update is the async
context-switch fix; the separate 3.6.4 assembly port needed the subsequent
core and SaRCAsm update described below.

That initial refresh advanced the core only to
`2adb1051abf8a73778d8cb3cd94f4126363e5a08`:
upstream's fix for C++ exceptions crossing `zcall`. The first libffi run
passed 1,738 checks but failed both exception-unwinding cases with the old
runtime. This core update changes only two runtime files; the LLVM source
hash stays unchanged. `checks.x86_64-linux.libffi` covers calls, closures,
pointer capabilities, variadic arguments and C++ exception propagation.
With that fix, libffi's full suite reports 1,742 expected passes, no failures
and two unsupported tests. Projeny's native suite reports 996 passes; all six
source/import regression tests pass as well.

Ruby uses upstream's pthread coroutine backend: selecting native assembly
left `coroutine_transfer` unresolved and made extension probes falsely reject
Ruby APIs. Its derivation now uses `mkRuby`/`mkRubyVersion`, keeping the 3.3.10
source, soname and gem metadata consistent. The gem configuration importer
consumes the port list directly.

The refreshed active ports (libffi, Bison, Grep, M4, Tar, OpenSSL, libwebp and
Ruby) build with this core. Runtime checks cover parser generation, macro
expansion, matching, archive and lossless image roundtrips, OpenSSL async AES,
and Ruby Fiddle calls/closures, BigDecimal, io/console and 100 finalizers.

## SaRCAsm and the current core

The complete core now uses `4867f1179f1c3dbe5484ec0f98c2fcc7d401e50c`,
matching the ports pin. SaRCAsm and minilute have separate sparse source
components at the core revision: they implement the compiler/runtime ABI,
while changes to their sources do not invalidate LLVM's source component.
Minilute includes only its own tree and the vendored Luau subtree it needs.
Both tools build natively, avoiding a compiler bootstrap cycle.

The compiler wrapper pins the Fil-C resource directory containing SaRCAsm.
Its ccache check hashes wrapper contents, including the pinned runtime and assembler paths,
rather than relying on Nix-normalized timestamps and file sizes. SaRCAsm invokes
its pinned GNU assembler by absolute path after inserting Fil-C capability
checks. The loader is now named `ld-fil1-x86_64.so`, including its ELF soname
and the stdenv's dynamic-linker metadata. Bootstrap glibc explicitly uses
`-yolo-assembler`, as in upstream's bootstrap script.

OpenSSL 3.6.4 is an alternative package, leaving the existing 3.5.7 port as
the default. It is also exposed as `pkgsFilc.openssl-sarcasm` for dependency
overrides:

```sh
nix build -L .#openssl-sarcasm
nix run .#openssl-sarcasm -- version -a
```

Its perlasm generators run with `SARCASM=1`, assembly uses the compiler's
SaRCAsm default, and the unsupported VIA PadLock engine is disabled. The
3.5.7 port continues using its runtime forwarders and ordinary assembler.
The alternative runs the upstream OpenSSL test suite during its build.

```sh
nix build -L .#filcc .#sarcasm .#checks.x86_64-linux.sarcasm \
  .#checks.x86_64-linux.libffi .#checks.x86_64-linux.libtool-symbols \
  .#checks.x86_64-linux.openssl-sarcasm
```

The SaRCAsm integration check compiles annotated assembly through the final
compiler, verifies pointer-return capabilities, and requires an out-of-bounds
assembly load to report a Fil-C safety error. The OpenSSL check verifies an
AES known-answer vector and requires an invalid output pointer to trap inside
`AES_encrypt`. The full suite patches test-helper shebangs for the Nix
sandbox before execution.

At this revision the OpenSSL suite passes all 4,561 tests across 352 files.
The installed binary also passes SHA-256, an AES encryption/decryption
roundtrip, AES-GCM and asynchronous AES-CBC checks. The default OpenSSL
3.5.7 still builds and passes its SHA-256 smoke check with Fil-C 0.684.
Libffi reports 1,742 expected passes, no failures and two unsupported tests;
its C++ exception checks and the libtool symbol check also pass.

## Update the core

Use the local clone to compute all source hashes before recording the new pin:

```sh
scripts/update-filc-source-hashes.py --repo "$HOME/fil-c" --rev FULL_COMMIT_ID
```

Without `--rev`, this recomputes hashes at the existing core revision. The
script uses temporary detached worktrees and removes them afterwards; it does
not change the clone's checked-out branch or files. `--pull` explicitly opts
into pulling the clone first. A hashing failure leaves the existing pin and
hashes untouched. Empty component selections are rejected, so a renamed or
removed upstream directory must be addressed before recording the update.

`sourcePatterns` in `lib/filc-upstream.json` are Git **non-cone** sparse-checkout
patterns, shared by `fetchgit` and the hash updater. Anchored selections omit
unrelated ancestor files such as `README.md` and `build_*.sh`. The compiler,
C++ libraries and runtime have separate selections; `filc/tests` is excluded.
The C++ selection includes LLVM-libc, whose shared conversion utilities libc++
uses even when the target C library is glibc.
When a build needs another upstream file, extend its selection and regenerate
hashes at the same core revision.

Each fetch has a stable name (`filc0-src`, `libpas-src`, etc.). If an upstream
revision changes only unselected files, its source hash and store output path
stay the same, as do downstream output paths. Fetch and dependent `.drv`
files can change to describe the new revision without requiring those outputs
to rebuild. Switching existing installations to these names/selections causes
one rebuild; subsequent updates benefit from the finer dependency boundaries.

## Verify without rebuilding LLVM

```sh
python3 tests/upstream-sources.py
```

This uses small temporary Git repositories and the pinned nixpkgs to check
source hashes, Nix output reuse across revisions, component-specific changes,
pin-update failure handling, reproducible patch extraction, and the real
compiler derivation's independence from `portsRev`. It does not compile code.

For a core update, also build the toolchain and representative ports:

```sh
nix build -L --no-link .#filcc .#checks.x86_64-linux.libtool-symbols \
  .#legacyPackages.x86_64-linux.pkgsFilc.expat \
  .#legacyPackages.x86_64-linux.pkgsFilc.libffi \
  .#legacyPackages.x86_64-linux.pkgsFilc.gmp
```

With [Swash](https://github.com/lessrest/swash) installed, prefix that command
with `swash start --tag PROJECT=filnix --` to run it in the background. Swash
prints a session ID; `swash poll ID` retrieves saved output and
`swash follow ID` follows it through completion, returning the build's exit
status. Detaching a follower leaves the build running.
