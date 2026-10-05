# Updating Fil-C sources and ports

Filnix maintains two toolchain variants on `main`, plus an independent
application-patch extraction pin:

- **Release:** `lib/filc-upstream.json` selects an exact official release
  commit from `pizlonator/fil-c`; `lib/filc-hashes.json` records its sparse
  source hashes. This is `filcc`, `packages.default`, `pkgsFilc`, the ordinary
  apps/demos and the default NixOS modules.
- **Staging:** `lib/filc-staging.json` selects an experimental fork commit;
  `lib/filc-staging-hashes.json` records its hashes. This is `filcc-staging`
  and `legacyPackages.${system}.pkgsFilcStaging`. Campaigns can call
  `lib.${system}.mkPkgsFilc { staging = true; ... }` without a Filnix branch.
  It is opt-in, may be unsound, and is not a supported release.
- `ports/upstream.json`: `portsRev` selects the Git history and tree used to
  extract application patches. Nix builds consume the checked-in patches and
  package archives. The native Projeny package uses the same revision and its
  separate `projenyHash`, fetching only `projects/projeny/`.

A ports update therefore does not change the compiler's derivation. The glibc
forks under upstream's `projects/` directory belong to the **core** pin: they
participate in its ABI and bootstrap. Directory location alone is not the
boundary. New application patches can still require a newer compiler/runtime
feature; test each updated port with the chosen toolchain before accepting it.
Both toolchains share `sourcePatterns`, port declarations and Nix integration,
but each bootstrap consistently uses its selected compiler, runtime, libc,
libc++, compiler-rt, yolounwind and SaRCAsm/minilute. Do not mix their libraries
or silently fall back from release to staging.

## Fil-C 0.686 and the remaining fork delta

The release pin is [v0.686](https://github.com/pizlonator/fil-c/releases/tag/v0.686),
[163fae598eaf](https://github.com/pizlonator/fil-c/commit/163fae598eaf249b74065b0156f3a7e7ba8c0e5a),
published October 4, 2026. It includes many of our contributions: coroutine and
limited musttail support, setjmp with `-fno-builtin`, common linkage, union-record
capability handling, FP-state preservation/fenv, PI mutex and spinlock fixes,
mount/prctl compatibility and SaRCAsm improvements. It also fixes ARM64 ordering,
GC roots and fork-related deadlocks.

Staging preserves the latest reviewed comparison experiment,
[`simplify-union-storage` at e4427dbc5b77](https://github.com/mbrock/fil-c/commit/e4427dbc5b7715b8fc079fc60c412a755f9680b9).
It replaces the older Filnix `fix-quickjs-union-abi` pin, not the official release.
Its merged upstream base is
[e33a8e2c5376](https://github.com/pizlonator/fil-c/commit/e33a8e2c5376f476ad9ea72c0ca02265504f18bb),
before the release's final commits. The experiment remains a
[draft comparison PR](https://github.com/pizlonator/fil-c/pull/332), not a
merge-ready claim of soundness.

Residual work absent from v0.686, established by source comparison:

| Area | Staging change | Regression |
| --- | --- | --- |
| Function descriptors | Local implementation alias prevents wrong-module calls through `dlsym`/`RTLD_LOCAL` | `fork-regressions.tests.descriptors` |
| Exception unwinding | Save nested cleanup and per-fiber unwind state | `fork-regressions.tests.nested-cleanup`, `.fiber-unwind` |
| Pointer CAS | Revalidate shadow state after the primary load, with an ARM64 load-load fence | `fork-regressions.tests.cas-expected-cap` |
| ARM64 glibc | Obtain saved jump-buffer frame identity through `zget_jmp_buf_frame` | staging cancellation C++ cleanup |
| Cancellation | Local libpizlo, ARM64 gate and glibc patches | `staging-cancellation`, `staging-cancellation-native` (x86-only harness) |
| Unions/varargs | Complete aggregate-varargs transport, conservative alignment rejection, null-padding initialization and optimizer shadow-state guards | fork's union/varargs/copy/memset suites and QuickJS |

Filip's release independently lowers pointer-bearing unions to pointer storage.
The experiment now follows that general direction rather than its earlier
ABI-only carriers, but retains different initializer/layout handling and
SROA/InstCombine guards. Neither implementation should be mixed with a different
variant's by-value aggregate ABI without validation.

**Staging is not “0.686 plus fixes.”** In particular, it predates release commit
[45adc761aeee](https://github.com/pizlonator/fil-c/commit/45adc761aeee), which requires
`-yolo-assembler` to recognize `zunsafe_call` and related intrinsics. Preserving
this experimental snapshot does not give it the official release's tightened
unsafe-call boundary.

The release toolchain does not apply the local cancellation patches or the old
x86 inotify implementation substitution. It retains the Nix locale-archive
patch, installed locale, store paths and wrappers. Thus “release-backed” means
official compiler/runtime semantics with Nix packaging, not unmodified build
inputs. Selecting official also withdraws residual behavior previously provided
on Filnix main; packages needing it must explicitly use staging.

Fork regressions are separate derivations so one official failure does not hide
the remaining results. The aggregate checks remain strict; known upstream
failures are not converted into passing checks. For example:

```sh
nix build --no-link --keep-going .#checks.x86_64-linux.fork-regressions
nix build --no-link .#checks.x86_64-linux.staging-fork-regressions
nix build --no-link .#checks.x86_64-linux.fork-regressions.tests.descriptors
```

The known ARM64 binary128 directed-rounding limitation remains visible in
`fenv` and `staging-fenv`; this is not established to be a 0.686 regression.
ARM64 validation is limited to the native gates and representative ports below.

### Verification of the split

Both complete x86-64 toolchains were rebuilt without `FILC_DEV_LLVM`. All nine
staging gates passed: cancellation, native cancellation, the six-case fork
aggregate, coroutines, fenv, GC roots, link hygiene, wrapper roles and SaRCAsm.
Release passed coroutines, fenv, GC roots, link hygiene, wrapper roles, SaRCAsm,
UTF-8 locale, PI mutexes and spinlocks. Its unsafe-call boundary check passed
at O0/O2, distinguishing ordinary external calls from explicitly opted-in
intrinsics. The release fork aggregate failed in four independent cases:
descriptors, nested cleanup, fiber unwinding and CAS capability writeback.
The pointer-atomic and union-record cases passed in both variants.

The same 71 selected fork runtime cases were compiled and run at O0/O2/O3
with each rebuilt toolchain. Staging passed **213/213**; release passed
**205/213**. The differences were `byvalvaarg7` (overaligned aggregate varargs,
all three levels), `unionnullinit` (C++ member-pointer null initialization,
all three levels), and `unionshadowstate` (copy/zeroing capability semantics,
O2/O3). These are fork comparison tests, not a claim that the official
upstream suite fails or that staging has proved memory safety.

QuickJS, Expat and SQLite built from both package sets. The package-local
QuickJS worker/SAB repair from `fix-quickjs-worker-sab` is retained independently
of either compiler pin. Both QuickJS builds passed the upstream suite, SAB
reader/refcount/aliasing tests, worker sharing and regexp checks; the installed
worker test also passed five repeated runs per variant. Expat passed
incremental parsing, entity expansion and mismatched-tag error checks; SQLite
passed transaction rollback, row ordering and database-integrity smoke checks.

The earlier experiment's 84 Clang/LLVM tests used a development compiler with
existing runtime libraries. That evidence is separate from the fresh runtime
comparison above. All 18 pinned sparse sources were built and all 10
source/import policy tests passed, including component coherence and compiler
assignment checks for both architectures. On native ARM64, all 18 source
hashes were independently verified and all 10 policy tests passed, including
native Projeny coverage. Both complete ARM64 toolchains built without
`FILC_DEV_LLVM`; both LLVM and installed QuickJS binaries were verified as
AArch64 ELF executables. Both variants passed coroutines, GC roots, link
hygiene, wrapper roles, QuickJS's upstream/SAB/worker/qjsc/regexp checks and
zlib's static/shared/64-bit tests. The official unsafe-call boundary passed.

Staging passed all six native fork cases, their aggregate, and cancellation
(112 scenario results, each with 20 passes). Release passed pointer atomics,
union-record ABI and all ten CAS runs, but failed descriptors, nested cleanup
and fiber unwinding. The passing ARM64 CAS runs differ from x86's observed
bad writeback; they do not establish universal race freedom or that the
residual CAS issue is fixed on every platform.

The SaRCAsm integration harness now selects an architecture-specific assembly
fixture rather than attempting to compile x86 instructions on ARM64. The native
checks passed in both variants, preserving the unchanged load/identity
assertions and requiring the deliberate OOB load to trap with `asm_load` in
the diagnostic. Both x86 variants still pass. Both native fenv gates fail at
`fenv.c:27`, `lquotient(FE_UPWARD) > lquotient(FE_DOWNWARD)`; those failures
remain strict, and subsequent fenv assertions were not reached.

No requested native target remains pending. The x86-only
`staging-cancellation-native` harness was not run or counted as ARM64 coverage;
the broader 213-case runtime comparison was performed on x86, not rerun on
ARM64. These results validate the requested builds and gates, not all ports or
the soundness of the experimental compiler.

A full `nix flake check --no-build
--all-systems` remains blocked by a missing `dank-bashrc.drv`, reproduced at
the original Filnix main revision; targeted checks bypass that unrelated issue.

The older Filnix branches are historical checkpoints. Their toolchain choices
are now represented by these pins on `main`; keeping them does not require
switching branches. No fork or remote branch deletion is needed.

## Historical September 14 cancellation baseline

At this checkpoint, the core and ports pins selected
`b6dd63481f796f8bff8502165c7dfc61091dbbd6`. Both glibc source components move
from 2.40 to 2.44. The native Projeny build and all seven source/import tests pass.
All projects present at the new pin were passed through the patch importer;
existing-version changes include Mesa, Ruby, Tar and the OpenSSL 3.6.4 port.
New version patches are retained for subsequent package upgrades. Older curated
package versions remain explicit in `ports.nix`; extraction does not silently
change their source archives or claim that every new version builds.

The shared runtime/glibc cancellation patches and test evidence are described
in [the implementation checkpoint](pthread-cancellation-implementation.md).
LLVM build and install both honor `NIX_BUILD_CORES` through an explicit Ninja
job limit. The compiler bootstrap is rebuilt for this source update.

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
resulting diffs and update the active declarations in `ports.nix` or their
package files under `ports/` when necessary. `ports/patches.nix` is a historical
inventory and does not affect builds. The pin is the default for future extraction;
it does not claim that every existing, curated patch was extracted at that
revision, nor does changing it automatically upgrade all ports.

The extractor diffs the original import against the pinned tree. Other
branches, later commits, dirty files and untracked build artifacts do not
participate. An explicit fourth argument overrides the pin for investigating
an older project version that no longer exists at the default revision:

```sh
ports/extract-patch.sh PROJECT "$HOME/fil-c" /tmp/patch-review FULL_COMMIT_ID
```

## Patch ownership and standalone upstream patches

`ports/patch/` is generated upstream material; `patches/` is maintained locally.
Keep additions in a separate local patch applied after the upstream patch. See
[the local patch convention](../patches/README.md) for provenance headers and
refresh review. Importers reject the local directory as an output destination,
and `make clean` is restricted to the generated directory.

Some upstream ports already exist as standalone patches rather than vendored
project trees. `ports/patch-sources.json` maps an extraction name to its upstream
Git path. These files are copied byte-for-byte from `portsRev`, and are included
in `make -C ports` and `make -C ports list`:

```sh
ports/extract-patch.sh boost-filc "$HOME/fil-c"
# Imports pizlix/boost-filc.patch into ports/patch/boost-filc.patch.
```

The generated patch is an input, not a port declaration. Wire it into the actual
package attribute in `ports.nix`, check source-version compatibility and patch
order, and test the result. Merely adding a `ports/patches.nix` inventory entry
does not change a derivation. Use the [version audit](port-version-audit.md) to
compare the active declarations with Nixpkgs and the selected upstream tree.

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

A vendored directory may port the same release as a descriptor: at
`b6dd63481f79`, `projects/openssl-3.6.4/` is the SaRCAsm port and
`openssl.projeny` (Origname `openssl-3.6.4`) uses zunsafe forwarders into
ordinary assembly. The directory keeps `openssl-3.6.4.patch`; the descriptor
then writes `openssl-3.6.4-projeny.patch`. Previously the descriptor's patch
silently replaced the SaRCAsm one, breaking `openssl-sarcasm`.

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

## Historical SaRCAsm integration checkpoint

At this checkpoint, the core used `4867f1179f1c3dbe5484ec0f98c2fcc7d401e50c`,
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

## Update a toolchain pin

Use the local clone to compute all source hashes before recording the new pin:

```sh
# Ordinary updates follow official releases, not deluge HEAD or our fork.
git -C "$HOME/fil-c" fetch origin tag v0.686
scripts/update-filc-source-hashes.py --repo "$HOME/fil-c" \
  --rev v0.686 --release 0.686

# Experiment updates leave the official pin and its hashes untouched.
scripts/update-filc-source-hashes.py --repo "$HOME/fil-c" \
  --variant staging --rev FULL_FORK_COMMIT_ID
```

Review compiler/runtime soundness and run targeted regressions before adopting
either pin. Keep the staging URL pointed at the fork, and publish a fork commit
before pinning it for others. A package-build success is not a safety audit.

Without `--rev`, this recomputes hashes at the selected variant's existing revision. The
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

The Lute 1.0.0 extraction also contains roughly 492,000 lines of vendored
third-party source changes. It is not consumed by a Filnix port and is not
checked in as a release patch; the pinned upstream tree remains its source.
Other newly extracted version patches are retained as an archive, without
implicitly enabling those package versions.
