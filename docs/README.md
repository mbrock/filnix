# Documentation

Notes on building software with [Fil-C](https://github.com/pizlonator/fil-c)
through Nix: how to use the results, how the toolchain is maintained, what
individual ports needed, and how the port campaigns run. The repository's
[README](../README.md) gives the overview.

## Using filnix

- [/opt/fil without Nix](optfil.md): a tarball of the Fil-C toolchain and
  memory-safe programs in upstream's `/opt/fil` layout.
- [A relocatable Fil-C root](filroot.md): the same toolchain and programs in
  a directory that works wherever it is unpacked.
- [Fil-C NixOS and finix](nixos.md): the module that makes a whole system's
  `pkgs` the Fil-C set, the base images, what stays native and what it
  costs, and how to check what runs Fil-C.
- [A Fil-C userland for NixOS: the record](nixos-userland.md): what it took,
  and what is still open.
- [The public AMI and its AWS account](aws.md): how releases register the
  AMI, the account's setup, and https://filc.less.rest.
- [A Fil-C userland for finix](finix.md): build a whole finix userland with
  Fil-C.
- [PHP on Fil-C](php.md): PHP 8.5, practical server performance, distributions
  and the experimental LLVM JIT.
- [PHP port notes](php-port-notes.md): implementation details, historical
  benchmarks and version-specific tests, including the early C-emitting JIT.
- [PHP extensions on Fil-C](php-extensions.md): PECL and bundled extensions
  beyond Nixpkgs' default set.
- [Determinate Nix under Fil-C](determinate-nix.md): Determinate Systems' Nix
  fork, with its test suites.

## Compiler and toolchain

- [Hacking on the Fil-C compiler without Nix rebuilds](llvm-dev.md): the
  incremental `filc-llvm` dev shell.
- [Updating Fil-C sources and ports](upstream-updates.md): the release and
  staging toolchain pins and how to move them.
- [Fil-C 0.687 port import](filc-0687-port-import.md): upstream changes,
  package-local integration fixes, and validation results.
- [Fil-C behaviour found while porting](filc-findings.md): compiler and
  runtime findings to report upstream, each with its filnix workaround.
- [Sealed closures](sealed-closures.md): a staging-only proof of concept
  for closures whose callers cannot read or replace their data.
- [zmark_shared: pointers inside shared mappings](zmark-shared.md): a
  staging-only rule, opted into with `-fzmark-shared`, that lets
  multi-process servers such as PostgreSQL keep pointers in shared memory.
- [Fil-C symbols and libtool](toolchain-symbols.md): why libtool's `nm` probe
  fails on Fil-C objects.
- [zstd with SaRCAsm](zstd-sarcasm.md): zstd's BMI2 assembly decoder loops
  through the SaRCAsm assembler.
- [Function-order shuffling (funkyenv) meets Fil-C](funkyenv.md): whether
  seeded per-deployment section shuffling fits Fil-C, why the upstream
  overlay silently breaks the Fil-C bintools, and a staged design for a
  filnix-native version.

## Notes on ports

- [Boehm GC on FUGC](boehm-on-fugc.md): the libgc API implemented on Fil-C's
  own garbage collector.
- [jemalloc on Fil-C's allocator](jemalloc-on-fugc.md): jemalloc's API on the
  garbage-collected heap.
- [Guile 3.0 on Fil-C](guile.md): GNU Guile on the libgc API above.
- [GTK, GObject introspection and GnuTLS](gtk-ports.md): GTK3, GTK4 and their
  GNOME and TLS dependencies.
- [TPM2-TSS on Fil-C](tpm2.md): the full upstream test suite.
- [Trealla with Fil-C](trealla.md): the Trealla Prolog interpreter.
- [QuickJS in place of Node.js](quickjs-for-node.md): which packages need
  Node on the Fil-C host and where QuickJS stands in.
- [PCRE2's JIT and the Fil-C LLVM JIT](pcre2-jit.md): why sljit cannot run,
  and a prototype that lowers its LIR to LLVM IR for Fil-C's JIT.
- [Data race in Determinate Nix's parallel evaluation](determinate-nix-addtrace-race.md):
  a failed thunk's shared exception mutated across threads.
- [Gem porting workflow](gem-porting.md) and
  [Ruby porting patterns](ruby-filc-porting-patterns.txt) (plain text): Ruby
  and its native gems.

## Thread cancellation

- [Thread cancellation: what Fil-C needs to get right](pthread-cancellation.md):
  the explanation; start here.
- Its design, implementation checkpoint, research notes and raw results
  are in the [archive](#archive).

## Port campaigns

- [What campaigns mean](campaigns.md): a frozen, bounded observation of
  named roots at one revision, with its expected compatibility baseline.
- [The campaign service](campaign-service.md): queued campaigns of
  survey-style builds (port campaigns, the nanofil survey, benchmarks),
  `campaignctl`, and the campaign list at <https://nix.swa.sh/>.
- [Native Fil-C port campaigns](port-campaign-operations.md): operating
  port campaigns and the cache publishers.
- [Publishing campaign builds](binary-caches.md): the two public binary
  caches.
- [Shared-library campaign repairs](shared-library-unblocks.md)

## Archive

Records of finished or retired work, kept as written at their old
addresses. What still holds has moved into the documents above.

- Thread cancellation, September 2026:
  [proposed semantics for Fil-C glibc](archive/pthread-cancellation-design.md),
  the [implementation checkpoint](archive/pthread-cancellation-implementation.md),
  the [research notes](archive/pthread-cancellation-notes.md) (source audit
  and experiments), and raw results for the
  [glibc comparison](archive/pthread-cancellation-results.txt) and the
  [implementation](archive/pthread-cancellation-implementation-results.txt).
- Port campaigns, September and October 2026:
  [selecting packages to try](archive/package-inventory.md), the
  [port version audit](archive/port-version-audit.md),
  [focused repairs after the shared-cancellation campaign](archive/campaign-repairs-20260915.md)
  and the [campaign failure review of October 6](archive/campaign-failure-review.md).
- The Python experiment runner, retired for the
  [campaign service](campaign-service.md):
  [its architecture](archive/experiment-architecture.md),
  [operations](archive/experiment-operations.md),
  [failure triage](archive/experiment-triage.md),
  [the Tagflow viewer](archive/dashboard-architecture.md) and
  [the monitor's design tightening](archive/dashboard-design-tightening.md).
