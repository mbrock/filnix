# Shared-library campaign repairs

## Re-enabling downstream evaluations

On 2026-09-14, campaign `eaaa75f8-2149-452d-8c0e-e76d6c584029` queued
4,261 previously failed evaluations against port revision
`35e3f40ca5173a8d72beec11f5becd5d0d48da96`. The selection matches the terminal
Nix diagnostic's “marked as broken” package, after discarding warning/trace
prefixes, and includes only candidates still in `evaluation-error`:

| Obsolete exclusion | Selected attributes |
| --- | ---: |
| GTK3 | 1,851 |
| GnuTLS | 1,675 |
| GObject introspection | 558 |
| GTK4 | 177 |

These exclusions were already removed in the repaired ports. No global
`allowBroken` override or additional port change was needed. The other 781
evaluation errors were left for separate diagnosis. Counts include aliases and
are retry inputs, not successful builds or predictions of success.

Runner 0.12.4's durable `queue-replan` request is
`c1487cb5-af84-410b-9bd1-68c9131a4fd6`. Its `replan-queued` event retains all
selected candidate IDs and the frozen source
`/nix/store/8fx8dj9af52hdbgxb1xpmlqw64y81vkz-filnix-campaign-source`.
The first planning attempt is `73778b3c-0099-406a-861b-2676a39db52d`.
DisnixWebService, MMA, OVMFFull, R and SDL passed its initial evaluations;
building and testing are separate subsequent observations.

The queue runs through ordinary bounded admission and persists across restarts.
The original campaign revision, old observations, kernel exclusions, CPU and
memory limits remain intact. The two active build workers continued during
deployment. All 117 runner tests passed, including queue recovery and atomic
admission; migration of a live database copy preserved every existing table's
row count and the active attempt specs and passed SQLite's quick check.

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

## Systemd and multimedia foundations

The systemd 256.4 upstream patch now applies to the common `systemd` package,
so `systemdMinimal` and `systemdLibs` inherit the same port. The existing
`systemdLibs` and compiler derivations remain unchanged. EFI images, BPF and
kexec payloads are outside the userspace compiler target; seccomp is still
unsupported by the runtime. The target-getent wrapper is deliberately allowed
as a runtime reference; other native build-tool references remain forbidden.

`systemdMinimal` builds, and installed systemd/udev version commands and
`systemd-escape` run successfully. This does not establish that Fil-C can boot
as PID 1 or run all systemd services. The full configuration currently reaches
TPM2-TSS, whose linker-based syscall mocks intercept native runtime symbols but
provide Fil-C functions. Its unresolved `__wrap_read`, `__wrap_write`,
`__wrap_socket` and `__wrap_connect` need a separate ABI-aware test adaptation.

Other verified dependency repairs:

- ALSA 1.2.13 omits ELF symbol version directives and deprecated-function warning
  sections, and expresses weak aliases in C. The installed-library check opens
  a null PCM device, configures stereo audio, writes and drains samples, and
  exercises a public weak alias. No physical audio device is needed.
- Libcbor uses its actual CMake options, disables incompatible automatic LTO,
  and drops a redundant generic-math include from a test. All 26 test groups
  pass; the old blanket test exclusion is removed.
- Libapparmor uses target Python and its configuration tool for its extension.
  The installed Fil-C Python binding imports and parses a profile/mode string.

GStreamer's upstream 1.24.7 patch applies to Nixpkgs' 1.26.3 release. Its optional
Rust PTP helper and native unwinding backends are disabled; leak tracking remains
enabled. Both Meson probes for `backtrace` must reject Fil-C's unsupported
`backtrace_symbols` backend. With two allocated CPUs, the package passes 110
Meson test groups and retains one upstream skip.

Those tests exposed a shared GLib problem: the upstream pointer CAS loops used
non-atomic loads. `glib-atomic-pointer-load.patch` uses atomic loads consistently.
A four-thread, 80,000-operation regression verifies pointer capabilities and
mutual exclusion; the same executable times out against the old GLib and passes
against the repaired library. GStreamer's contended TOC setter test also changes
from a timeout to a 1.5-second pass. GLib's existing GType checks still pass.

`toolchain/meson-check-cores.nix` bounds Meson's test concurrency, Fil-C collector
workers and test CPU affinity to `NIX_BUILD_CORES`. Merely limiting Meson jobs
left clock stress tests creating hundreds of threads from the machine's CPU
count. A six-CPU clock rescheduling stress run still timed out after that first atomic
repair. The follow-up below identifies and repairs a separate pointer-wait
problem; CPU limits remain useful for respecting the build allocation.

Run the focused installed-consumer checks with:

```sh
nix build .#checks.x86_64-linux.media-foundations \
  .#checks.x86_64-linux.glib-atomic .#checks.x86_64-linux.glib-gtype \
  --max-jobs 1 --cores 2
```

The default PipeWire package now requests `systemdLibs`, which supplies the API
it uses. Its larger default plugin graph still needs additional ports; this
change alone does not establish a successful full PipeWire build.

## PipeWire core experiment

`tests/pipewire-core.nix` is a standalone diagnostic profile rather than a
replacement for Nixpkgs' default PipeWire configuration. It keeps the core,
ALSA, D-Bus, libsystemd/logind, audio conversion/mixing and basic video plugins.
Optional dependency-heavy plugins are left out so failures in PipeWire itself
can be isolated. The default package still has its original plugin selection.

The local `patches/pipewire-*.patch` files are applied only by this profile:

- SPA log topics, built-in PulseAudio modules and test suites use C registration
  instead of enumerating linker sections. Log registration uses static nodes
  and a Fil-C-only enumeration field, with one hidden list per shared object.
  It avoids undefined weak function calls and constructor-priority dependencies.
- Pointer offset, container and alignment helpers preserve capabilities. Their
  native implementations remain unchanged, and C++ header checks still compile.
- The CPU probe spells `xgetbv` as an instruction instead of raw bytes, allowing
  Fil-C's existing safe lowering. SIMD feature detection and implementations
  remain enabled; their arithmetic/format tests pass.
- `NVALGRIND` selects the bundled Valgrind headers' existing opt-out. Fil-C cannot
  execute their native client-request assembly with pointer operands.
- Test cleanup uses `nftw` with one open descriptor. This preserves recursive
  cleanup while avoiding glibc's unported `__openat64_nocancel` path. Two tests
  of explicit `abort()` expect Fil-C's diagnostic SIGTRAP instead of SIGABRT.

The initial core checkpoint completed compilation/linking and passed 46 of 48
groups, with no skipped groups. It exposed two further problems:

1. `test-audioadapter` passes its follower node through a `pointer:%p` string.
   Parsing it in the plugin reconstructs an address without its capability.
   This needs a real pointer-preserving interface or shared pointer table;
   casting the parsed address cannot repair it.
2. `test-loop` passes its ordinary destruction, recursion and source-lifetime
   cases, but `cancel_thread_while_dispatching` aborts because glibc cannot load
   `libgcc_s.so.6661`. Fil-C has forced-unwind machinery, but the compatible
   unwind-library integration still needs to be established and tested.

Reproduce the current experiment, including its failures:

```sh
nix build --impure --file tests/pipewire-core.nix \
  --max-jobs 1 --cores 2 --keep-failed --no-link -L
```

Full systemd was also tested with optional TPM integration disabled. That
reached cryptsetup, whose checks fail when secure-allocation helpers apply
memory-mapping operations to malloc-backed memory. This is another distinct
blocker; TPM and cryptsetup tests have not been disabled in the main ports.


## Pointer properties and weak-reference contention

The PipeWire core profile now also applies `pipewire-pointer-properties.patch`.
Audio/video followers, DSP interfaces, JACK clients, Bluetooth transports and
custom thread creators use the same pointer-string helpers. Under Fil-C, one
shared library owns a weak exact-pointer table for both the application and
independently loaded plugins. It restores only registered capabilities, rejects
unknown/freed pointers and retains the original owner's lifetime responsibility.
Native builds keep `%p` serialization. The native resampler code generator uses
only SPA headers, so it does not link this target library in a cross build.

`pipewire-pointer-properties.c` loads two separate DSOs with `RTLD_LOCAL` and
checks concurrent first use, interior pointers, function pointers, null values,
malformed/unknown tokens and invalidation after `free()`. That check passes, as
does the original audio-adapter test. The profile now passes **47 of 48** groups,
with no skips; cancellation remains enabled and failing.

GStreamer's intermittent clock stress timeout was another GLib issue. A Fil-C
`zdump_stacks()` watchdog showed workers blocked in `g_weak_ref_get()`, including
pointer bit-lock waiters, with no thread making progress. Fil-C's atomic pointer
box is authoritative; the ordinary address bytes mirrored after exchanges can
lag concurrent operations. A kernel futex comparing those ordinary bytes can
therefore sleep even after the actual atomic pointer is unlocked.

`glib-pointer-bit-wait.patch` replaces pointer bit-lock futex predicates with
bucketed condition variables and atomic pointer rechecks. Unlock wakes the
bucket while holding its mutex; broadcasts handle unrelated addresses hashing
to the same bucket. Existing contention counters keep uncontended unlocks cheap.
Integer bit locks retain their ordinary futex implementation. The patch is local
and applied after the extracted upstream port and the earlier CAS-load repair.

The expanded GLib regression performs 192,000 weak-reference acquisitions across
48 threads, in addition to the existing 80,000 pointer-lock operations. The same
executable passes against the repaired library and times out against the previous
library. GStreamer's unchanged two clock stress cases pass ten consecutive runs
at six CPUs with six collector workers after the repair; before it, four of five
identical runs timed out. No GStreamer tests were removed or relaxed.
The full GStreamer build also passes at six CPUs: 110 test groups pass with
the one existing upstream skip. GObject introspection passes all 60 groups,
and the installed GStreamer fake-source/fake-sink pipeline runs to completion.

Cancellation investigation uses a separate libc derivation, leaving the shared
compiler/runtime graph unchanged. Three independent problems were exposed:

- The libc still preflighted `libgcc_s.so.6661`, although Fil-C supplies its own
  unwinder. The private derivation removes that obsolete check.
- Both the native libc underneath Fil-C and its user libc reserved signals 32
  and 33. The runtime correctly rejects user handlers and sends for these
  signals; `pthread_cancel()` returned `ENOSYS` when it needed to interrupt an
  asynchronous worker. Early deferred cancellation did not need a signal,
  explaining why diagnostic logging appeared to fix the test. The local
  `glibc-filc-cancellation-signals.patch` gives the user libc signals 34–36 and
  exposes `SIGRTMIN=37`; it also propagates handler-installation errors.
- `pause()` had lost its cancellation-point machinery. Restoring an async
  region alone exposed another boundary: Fil-C cannot force-unwind from a
  signal callback. `glibc-filc-pause-cancel.patch` gives the callback a temporary
  `siglongjmp` destination in libc and starts forced unwinding from that normal
  frame. It blocks cancellation during setup and uses `sigsuspend()` to
  atomically unblock and sleep. Pending cancellation takes the same path,
  restoring the signal mask before running cleanup.

This is deliberately a private fix for the `pause()` cancellation point, not
an implementation of arbitrary asynchronous cancellation across Fil-C poll
checks or all other blocking calls. The compiler and runtime safety checks are
unchanged. Both patches are maintained in `patches/`, outside the generated
upstream port patches.

### Isolating libc experiments from the campaign

`tests/pipewire-cancellation.nix` makes this a reproducible, opt-in experiment.
It derives a private libc from the existing compiler components, without
changing the compiler wrapper, sysroot or cross package set. PipeWire and its
dependencies still compile against the ordinary libc. Meson's per-test wrapper
then prepends the private libc to `LD_LIBRARY_PATH`, after Meson sets its own
build-tree library paths. The replacement applies to the test process and its
loaded libraries, rather than mixing two Fil-C libcs within one process.

This approach is for changes that preserve the libc ABI. Future cancellation
patches can be added to that private derivation without invalidating the
campaign's existing packages. Comparing recursive derivation closures confirmed
that all 1,560 existing dependencies are retained. The private libc, its two
patch sources and the runner are added; only the PipeWire leaf derivation is
replaced. No LLVM, runtime, compiler wrapper or shared-library dependency is
rebuilt.

```sh
# Check the selected libc, cancellation races, signal masks and C/C++ cleanup.
nix build --impure -f tests/pipewire-cancellation.nix probe \
  --max-jobs 1 --cores 2 --no-link -L

# Exercise the complete core-profile test suite against the private libc.
nix build --impure -f tests/pipewire-cancellation.nix pipewire \
  --max-jobs 1 --cores 2 --keep-failed --no-link -L

# Run an installed daemon and clients on a private socket, without hardware.
nix build --impure -f tests/pipewire-cancellation.nix runtime \
  --max-jobs 1 --cores 2 --no-link -L
```

The focused probe compiles with the ordinary toolchain and verifies the private
libc's path in `/proc/self/maps`. It covers cooperative cancellation, a request
pending before `pause()`, racing entry, cancellation during a confirmed blocked
syscall (both deferred and explicitly async callers), disabled cancellation,
and ordinary signal wakeups in both cancellation modes. It checks exactly-once
cleanup, `PTHREAD_CANCELED`, signal-mask restoration and preservation of the
caller's mode on ordinary wakeups. The cases also run through a C++ frame to
check destructor unwinding before the outer pthread cleanup handler. All 128
C cases and 128 C++ cases pass against the private libc.

The installed-runtime probe starts a daemon on a temporary socket, verifies its
loaded libc, creates and destroys a virtual audio adapter through `pw-cli`,
checks the registry with `pw-dump`, and requests a clean daemon shutdown. It
passes, using no sound hardware, session manager or host service. The core
profile now builds and installs successfully with **48/48 test groups passing
and no skips**. Its udev and systemd install directories are explicitly placed
under the Nix output rather than inherited from the host-style pkg-config
defaults.

These results apply to the opt-in core profile with the private libc. The main
campaign's full PipeWire package and the shared Fil-C libc are unchanged.
