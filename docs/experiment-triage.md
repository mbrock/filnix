# Experiment failure triage

These are follow-up observations from **The first Filnix inventory**
(`eaaa75f8-2149-452d-8c0e-e76d6c584029`), whose recipes are frozen at `b14a53e`.
The campaign continues with those recipes. Follow-up fixes below do not rewrite
its failures or claim that blocked downstream packages now pass.

## Verified fixes — 2026-09-13

### pycparser 2.22: supply the preprocessor used by its tests

The original Fil-C Python package ran 130 tests and reported four failures and
four errors because `cpp` was absent. The compiler wrapper exposes Clang but
has no `cpp` alias. All eight failures involved preprocessing fixtures/examples.

The Python port now adds the native compiler's tools to `PATH` in `preCheck`.
Only the fixture preprocessor is native; the test hook still invokes Fil-C
Python 3.12.5. No tests were disabled. The full **130 tests pass**.

- Original: `/nix/store/b8x301fqxfkd7s0ga0yj5hdmkaq3ysz1-python3.12-pycparser-2.22-x86_64-unknown-linux-gnufilc0.drv`
- Fixed: `/nix/store/5slg9j9c2fp4bqhszf9zkd94jabjaw4d-python3.12-pycparser-2.22-x86_64-unknown-linux-gnufilc0.drv`
- Original attempt: `509b1c36-3267-49b1-99fa-0fe50dec0d4d`

The failed dependency appears under `Fabric`. Fixing pycparser alone does not
establish that Fabric works: its recorded graph also has other failures.

### QuadProg++: declare the library's math dependency

`QuadProgpp` compiled its static library but failed to link its example with
unresolved `pizlonated_sqrt` and `pizlonated_sqrtf`. The CMake target now declares
`m` as a **PUBLIC** dependency. This fixes both the example and the installed
target's link interface for downstream consumers.

The package builds. A separate Fil-C C++ consumer imports the installed CMake
target, links without manually adding `-lm`, and verifies the unique solution
`(1, 2)` with objective value `12` for a constrained quadratic problem. CTest
passes. This is a focused consumer check, not an upstream test-suite claim.

- Original: `/nix/store/1cxlf9p26ynvm4cqp40b8g76fzimbq5i-quadprogpp-x86_64-unknown-linux-gnufilc0-unstable-2023-01-20.drv`
- Fixed: `/nix/store/hh785wgvq8p10x8s2c2pnzcy2pzwq0gm-quadprogpp-x86_64-unknown-linux-gnufilc0-unstable-2023-01-20.drv`
- Consumer output: `/nix/store/3hykddwyxmmizlh20q0kx2x60i9jz4l8-quadprogpp-consumer-check-x86_64-unknown-linux-gnufilc0-1`
- Original attempt: `509b1c36-3267-49b1-99fa-0fe50dec0d4d`

For each fixed package, comparing recursive store inputs against the failed
recipe found exactly one new derivation: the package itself. The existing
compiler, runtime, and other dependency derivations were reused.

Reproduce from the revision containing these fixes:

```sh
nix build .#legacyPackages.x86_64-linux.pkgsFilc.python312Packages.pycparser \
  --no-link --max-jobs 1 --cores 2 --timeout 600 -L
nix build --impure --file tests/quadprogpp.nix \
  --no-link --max-jobs 1 --cores 2 --timeout 600 -L
```

Build logs are retrievable with `nix log` on these derivations. The original
attempt logs remain in the experiment state. Additional local captures and
closure comparisons are in ignored `results/experiment-triage-20260913/`.

## Deferred findings from the first batches

### Initial targeted GTK follow-up, 2026-09-14

Plan `83b6d44e-5ce8-483c-80d6-5bffbdc047a4` evaluated only
`gobject-introspection-unwrapped`, `gnutls`, `gtk3` and `gtk4` from committed
revision `05ca9018d024e526347c98a29da09cd0afafeafe`. All four evaluations
succeeded. Introspection and GnuTLS entered the ready queue; GTK3 and GTK4
remain held by previously recorded dependency failures. The campaign's default
source and 4,216 other evaluation failures were verified unchanged.

GTK3's eight blockers all enter through `at-spi2-core` and its systemd dependency
(including kexec-tools, libapparmor, cryptsetup and libseccomp). GTK4's 32 blockers
enter through `gst-plugins-base` and `gst-plugins-bad`, including the existing
ALSA, Opus, codec and systemd failures. These are dependency results, not evidence
that the patched GTK sources failed to compile.

The next bounded investigation is the optional dependency configuration:
AT-SPI exposes `systemdSupport`, and GTK4's media backend pulls in the large
GStreamer plugin closure. Any such recipe changes need a fresh recorded
revision. This queue submission did not clear shared failures or disable tests.
Full explaining chains were saved in
`results/gtk-gnutls-ports/{gtk3,gtk4}-queue-blockers.json`.

### Shared GTK/TLS repairs, 2026-09-14

The subsequent investigation fixes the scanner/tool ABI boundary across the
Fil-C package scope, builds upstream-patched AT-SPI and PyGObject, and repairs
DConf and Duktape failures found through GTK's shared inputs. AT-SPI now links
the systemd libraries without the full tool closure; GTK4 omits its optional
GStreamer video backend. Both GTK versions build and pass the Broadway consumer
check; the original dependency blockers are
absent from the replacement toolkit graphs. See [gtk-ports.md](gtk-ports.md)
for version choices, limitations and reproducible consumer checks.

Observed checks include 60 introspection tests, 14 DConf tests, six libproxy
tests, six GLib networking test groups, and a PyGObject runtime probe. These
results belong to their exact new derivations; they do not erase the original
failed attempts. Separate TLS and GTK consumer checks are exposed by the flake.

Runner 0.12.2 accepts explicit source revisions when replanning queued, failed, blocked
or inconclusive candidates as well as evaluation failures. The new plan records
each candidate's previous recipe/result before replacing it; active and already
successful candidates cannot be replaced. This allows a bounded downstream
retry without changing the campaign's frozen default source or automatically
reopening every evaluation failure. The regression suite has 105 passing tests.

Plan `ef458359-6ce6-45f3-acb7-083c7849494f` evaluates 62 selected downstream
roots from `921eb54aa6366d1c71cd1cd10fcaad491e7671fd`: all 62 evaluations succeed,
30 recipes enter the ready queue, and 32 have other recorded dependency failures.
This is a follow-up result, not a reclassification of the original campaign.
GTK3 subsequently drops its disabled `devdoc` output. Plan
`a5bc20ac-fe95-42a7-802d-706a7b06c0fb` updates its 21 selected consumers from
`58f7bc9f8a3b8cae3339f07c903a08f7c489c1fc`, before their builds start.
Plan `e4c3ca39-ba4f-43e2-95c1-5ca1ecd0f434` adds 14 other selected GnuTLS
evaluation failures from that same revision: apcupsd, apt, apt-cacher-ng, atop,
bitlbee, chrony, conntrack-tools, corosync, coturn, dnsdist, gnupg, mailutils,
rdesktop and squid. This brings the explicit follow-up selection to 76 roots.

The final separate GnuTLS check passes 526 tests with 60 skips and no failures
across its TLS, certificate and slow suites. Libmicrohttpd 1.0.1 builds without
additional package changes. These local checks and builds reuse the unchanged
Fil-C compiler, GLib and Python derivations.

Two additional local probes identify further porting work. GtkSourceView 4.8.4
sets `GLIB_VERSION_MAX_ALLOWED` below 2.80, selecting the still-integer fallback
of GLib's `_g_type_once_init_type` macros. Libsoup 2.74.3 generates enum registration
code using `gsize` and integer once initialization; this blocks GSSDP as well.
These failures are retained in `results/gtk-unlock/downstream-1.log`. A future
GLib header correction should cover the old API branch without changing the
pointer ABI; libsoup also needs its enum template adapted. The working GTK
consumer checks do not imply these downstream packages pass.

### Earlier findings

These are diagnostic leads, not fixes or complete root-cause analyses. Use the
named original attempt to find its recorded derivations and logs.

| Package / dependency | Observed failure | Next investigation | Original attempt |
| --- | --- | --- | --- |
| wrapt 1.17.2 | Fil-C Python traps during `tests/test_copy.py` | Isolate the individual copy test and native comparison; retain all checks | `509b1c36-3267-49b1-99fa-0fe50dec0d4d` |
| Rust compiler dependency | No target specification for `x86_64-unknown-linux-gnufilc0` | Trace why a selected root needs target Rust; distinguish it from a native build tool | `509b1c36-3267-49b1-99fa-0fe50dec0d4d` |
| libtickit 0.4.5 | Cannot find `-lncurses` | Inspect pkg-config selection between unibilium and ncurses | `6e1ee130-399a-4f83-a98d-42ce24e8e28a` |
| 7zz 25.01 | GCC warning flags rejected by Clang under `-Werror` | Select upstream's Clang build settings, then see whether compilation proceeds | `ea14ba14-da7c-4ee1-8f13-429cdee27b62` |
| libmpg123 1.32.10 | SaRCAsm rejects labels outside functions in standalone assembly | Preserve the default assembly result; consider a separately labeled generic-C variant | `ea14ba14-da7c-4ee1-8f13-429cdee27b62` |
| FLAC 1.5.0 | Eight of ten checks fail; CPU detection traps on inline `.byte 0x0f, 0x01, 0xd0` | Investigate that instruction encoding or an explicit upstream CPU-detection alternative | `ea14ba14-da7c-4ee1-8f13-429cdee27b62` |
| libopus 1.5.2 | 12/14 tests pass; decode gets SIGTRAP, encode gets SIGSEGV | Recover full per-test diagnostics and reduce reproductions | `ea14ba14-da7c-4ee1-8f13-429cdee27b62` |
| Perl 5.40.0 dependency variant | `miniperl` traps on a pointer with no capability | Compare the dependency variant with the already available top-level Perl recipe | `ea14ba14-da7c-4ee1-8f13-429cdee27b62` |
| ALSA 1.2.13 | Compiler abort parsing module assembly with `.gnu.warning` and `.symver` | Separate symbol-version/warning metadata from executable assembly | `ea14ba14-da7c-4ee1-8f13-429cdee27b62` |
| dbus-glib 0.114 | Switches on Fil-C GLib's pointer-valued `GType` | Inspect upstream port patterns for fundamental type dispatch | `ea14ba14-da7c-4ee1-8f13-429cdee27b62` |
| Boehm GC 8.2.8 | Test executables fail to link `pizlonated__end` | Investigate compatibility of conservative heap/stack scanning before a superficial link fix | `6e1ee130-399a-4f83-a98d-42ce24e8e28a` |

Some candidates also stop at evaluation because Nixpkgs marks dependencies
broken (for example GTK, GnuTLS, and GObject Introspection), or rejects an
unfree package under the current policy. Those are evaluation refusals, not
evidence that Fil-C compilation failed. The original inventory remains intact.

## Scope correction — 2026-09-14

The hardened kernel variants escaped the original inventory's directory filter
because their metadata position points to `pkgs/top-level/linux-kernels.nix`.
They are excluded from the userspace experiment, including two variants whose
outputs were already realized; those outputs do not establish Fil-C kernel
compatibility. The inventory and runner now recognize kernel builders explicitly.
Kernel headers and userspace programs stay eligible.

Batch `02a8d98c-c9bf-4961-a74a-b4456c9ed61c` was cancelled while Linux 6.1.141
and 6.12.43 were compiling. Its history records the scope exclusion and preserves
the worker's cancellation result and raw logs. Unrelated interrupted roots from
that batch are explicitly requeued. Batch `81ce27c5-fd6d-45b8-a870-56eba8938dc8`
continued running independently. Local verification is retained in
`results/experiment-kernel-exclusions/`.
