# Fil-C port version audit

The October 6, 2026 audit evaluated all 290 declarations in `ports.nix` against
the locked Nixpkgs input, rather than reading the historical `ports/patches.nix`
inventory. Before this refresh, 36 packages were older than their Nixpkgs
counterparts; three custom packages had no comparable version. Most declarations
already followed Nixpkgs and only changed patches, flags or dependencies.

The refresh removes 17 version/source overrides: 12 upgrades and five exact
duplicates of Nixpkgs' version, archive URL and hash. The remaining declarations
evaluate to 263 matching versions, 24 older versions and three without a
comparable Nixpkgs version, on both x86-64 and ARM64. There are 28 explicit or
custom version selections left in the DSL. That count includes harmless choices
such as minizip's shared source and Ruby's version-aware constructor; version
comparison also catches indirect selections such as Perl.

These numbers cover the top-level DSL, not every nested Python, Perl, Ruby, Qt
or Nix component scope. Handcrafted package files and native build-tool overrides
also need review when their associated package families are updated.

## Repeat the audit

```sh
python3 scripts/audit-port-versions.py
python3 scripts/audit-port-versions.py --all --json > /tmp/port-versions.json
python3 scripts/audit-port-versions.py --system aarch64-linux

# Compare with a fetched upstream revision without changing any pins or checkout.
git -C "$HOME/fil-c" fetch origin deluge
python3 scripts/audit-port-versions.py --rev origin/deluge
```

The default upstream comparison is `ports/upstream.json`'s `portsRev`.
Directory names and Projeny `Origname` headers come from that exact Git tree;
dirty files and unrelated archive files do not participate. JSON includes all
records, source/version-selection flags, applied patch paths and upstream version
candidates. Candidates are available source versions, not tested upgrades.
Unversioned upstream projects and standalone patches cannot supply a version from
their names and may appear without a candidate.

## Completed upgrades

All these packages now inherit their source version and hash from locked Nixpkgs.
Their Fil-C patch selects the corresponding imported version; PCRE2's imported
patch changes only upstream tests and is not needed by its existing build.

| Package | Previous | Current |
| --- | --- | --- |
| OpenSSH | 10.3p1 | 10.5p1 |
| zlib | 1.3 | 1.3.2 |
| libevent | 2.1.12 | 2.1.13 |
| libuv | 1.51.0 | 1.52.1 |
| libxcrypt | 4.4.36 | 4.5.2 |
| PCRE2 | 10.44 | 10.48 |
| Diffutils | 3.10 | 3.12 |
| Grep | 3.11 | 3.12 |
| Sed | 4.9 | 4.10 |
| M4 | 1.4.19 | 1.4.21 |
| XZ | 5.6.2 | 5.8.4 |
| Kerberos | 1.21.3 | 1.22.2 |

The redundant pins removed were libffi 3.8.0, Make 4.4.1, Tar 1.35, Bison 3.8.2
and keyutils 1.6.3. XZ now runs `autoreconfHook`: the imported patch modifies
`Makefile.am`, while the old build supplied Automake 1.16 instead of the version
required by the new archive. Diffutils and Grep retain Nixpkgs' patches for their
new releases, instead of filtering them out for the older sources.

## Remaining selections and follow-up work

The following decisions describe this bounded refresh. An existing pin is not
evidence that the newer source cannot build; retained version differences remain
work to do.

| Package or family | Filnix version | Nixpkgs version | Decision / next verification |
| --- | --- | --- | --- |
| Git | 2.46.0 | 2.54.0 | Next batch: imported port is 2.55.0; select and test a source/patch pair. |
| Dash | 0.5.12 | 0.5.13.3 | Next batch: Projeny port is 0.5.13.5; reconcile the archive version. |
| libedit | 20240808-3.1 | 20251016-3.1 | Next batch: Projeny port is 20260512-3.1. |
| Binutils | 2.43.1 | 2.46 | Next batch: imported port is 2.47; verify local symbol/version-script patches. |
| zlib-ng | 2.2.4 | 2.3.3 | No rationale is recorded for this pin; try Nixpkgs with its runtime suite. |
| Expat | 2.7.1 | 2.8.4 | Upstream pin still ports 2.7.1; rebase its changes and test the newer source. |
| libpng | 1.6.43 | 1.6.58 | Reconcile the upstream port with Nixpkgs' APNG source/patch set. |
| libarchive | 3.7.4 | 3.8.9 | Rebase the port and review the patches currently filtered out. |
| libcap | 2.70 | 2.77 | Upstream pin still ports 2.70; validate newer C-only configuration. |
| libinput | 1.29.1 | 1.31.3 | Rebase source changes against the newer input stack. |
| libevdev | 1.11.0 | 1.13.6 | Rebase source changes and run input-event regressions. |
| GLib | 2.80.4 | 2.88.3 | Coordinated GLib/GI/GTK update, including native build-tool overrides. |
| GObject Introspection | 1.80.1 | 1.86.0 | Same coordinated update; preserve host/target tool and typelib handling. |
| Pango | 1.56.3 | 1.57.1 | Coordinate GLib requirements and existing source override. |
| GTK 4 | 4.14.5 | 4.22.4 | Rebase and test the GTK stack together. |
| glibmm | 2.80.1 | 2.88.1 | Follow the coordinated GLib update. |
| gtkmm4 | 4.14.0 | 4.22.0 | Follow the coordinated GTK update. |
| AT-SPI | 2.60.5 | 2.60.6 | Small candidate upgrade; verify current GTK accessibility integration. |
| Python 3.12 | 3.12.5 | 3.12.14 | Rebase Python patches and run extension/package regressions. |
| Perl | 5.40.0 | 5.42.0 | Selected indirectly; update ptrtable/XS changes and module scopes together. |
| Emacs 30 | 30.1 | 30.2 | Uses a local fork and additional patches; reconcile the fork first. |
| systemd | 256.4 | 260.4 | Broad package/configuration update; current local patches target 256. |
| OpenSSL default | 3.5.7 | 3.6.4 | Different assembly backend; keep separate from the existing SaRCAsm alternative. |
| Trealla | fork snapshot | 2.99.1 | Intentional source fork with FFI/tabling patches, not an archive-version replacement. |
| GTK 3 | 3.24.52 | 3.24.52 | Matching version; archive pin retained pending source-equivalence review. |
| Ruby 3.3 | 3.3.10 | 3.3.10 | Keep version-aware constructor and gem metadata; default 3.3 avoids Rust/YJIT. |
| minizip | 1.3.2 | 1.3.2 | Deliberately shares Nixpkgs' zlib source. |
| OpenSSL SaRCAsm | 3.6.4 | no equivalent | Separate custom derivation with its own assembly backend and suite. |
| kittydoom | Git source | no equivalent | Custom package. |
| libiconv | 1.19 | no equivalent | Native glibc has no separately versioned attribute; no DSL source/version override. |

At upstream `163fae598eaf` (October 4), several ports have moved again: Projeny
selects libuv 1.53.0, PCRE2 10.49, OpenSSL 3.6.5 and Coreutils 9.12. This refresh
uses already imported patches at `b6dd63481f79`; changing the application
extraction pin is a separate operation and does not upgrade packages by itself.

## Update policy and validation

Prefer Nixpkgs' source/version when a compatible Fil-C patch is available.
When a version override is required, record why next to the declaration and
keep its archive, hash and patch version consistent. Keep compiler/runtime pins
independent of application updates. `update-port-version.sh` remains a snippet
helper, not an automatic updater; failed prefetches now stop instead of printing
a fabricated hash.

All 17 changed package declarations built with the official release toolchain
on x86-64, and the runtime gate passed. The existing libffi suite reported 1,742
expected passes, no failures and two unsupported tests. The three audit helper
regressions passed. Both architecture audits evaluated all 290 declarations
without errors; ARM64 packages were not rebuilt as part of this refresh.

The refresh gate is:

```sh
python3 tests/test_port_version_audit.py
nix build --no-link .#checks.x86_64-linux.port-version-refresh
```

It compiles and runs a Fil-C consumer of zlib, libevent, libuv, libxcrypt, PCRE2
and Kerberos. It exercises compression, timers, a SHA-512 password-hash vector,
Unicode regex captures and principal parsing. OpenSSH generates Ed25519, RSA and
ECDSA keys and signs/verifies files; the text tools and XZ exercise actual data
transformations. Package builds retain their existing suite settings, including
zlib's enabled suite. This gate is focused coverage, not all upstream suites or
a network SSH login test. ARM64 version evaluation is separate from runtime
validation.
