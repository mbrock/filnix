# Documentation

Notes on building software with [Fil-C](https://github.com/pizlonator/fil-c)
through Nix: how to use the results, how the toolchain is maintained, what
individual ports needed, and how the port campaigns run. The repository's
[README](../README.md) gives the overview. These pages are also published at
<https://mbrock.github.io/filnix/docs/>.

## Using filnix

- [/opt/fil without Nix](optfil.md): a tarball of the Fil-C toolchain and
  memory-safe programs in upstream's `/opt/fil` layout.
- [A relocatable Fil-C root](filroot.md): the same toolchain and programs in
  a directory that works wherever it is unpacked.
- [Fil-C services on NixOS](nixos.md): swap chosen NixOS services for their
  Fil-C builds and leave the rest of the system alone.
- [A Fil-C userland for finix](finix.md): build a whole finix userland with
  Fil-C.
- [PHP on Fil-C](php.md): PHP 7.4, 8.4 and 8.5, distribution tarballs, the
  Docker image, and the experimental opcache JIT compiled through C.
- [PHP extensions on Fil-C](php-extensions.md): PECL and bundled extensions
  beyond Nixpkgs' default set.
- [Determinate Nix under Fil-C](determinate-nix.md): Determinate Systems' Nix
  fork, with its test suites.

## Compiler and toolchain

- [Hacking on the Fil-C compiler without Nix rebuilds](llvm-dev.md): the
  incremental `filc-llvm` dev shell.
- [Updating Fil-C sources and ports](upstream-updates.md): the release and
  staging toolchain pins and how to move them.
- [Fil-C behaviour found while porting](filc-findings.md): compiler and
  runtime findings to report upstream, each with its filnix workaround.
- [Fil-C symbols and libtool](toolchain-symbols.md): why libtool's `nm` probe
  fails on Fil-C objects.
- [zstd with SaRCAsm](zstd-sarcasm.md): zstd's BMI2 assembly decoder loops
  through the SaRCAsm assembler.

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
- [Data race in Determinate Nix's parallel evaluation](determinate-nix-addtrace-race.md):
  a failed thunk's shared exception mutated across threads.
- [Gem porting workflow](gem-porting.md) and
  [Ruby porting patterns](ruby-filc-porting-patterns.txt) (plain text): Ruby
  and its native gems.

## Thread cancellation

- [Thread cancellation: what Fil-C needs to get right](pthread-cancellation.md):
  the explanation; start here.
- [Proposed cancellation semantics for Fil-C glibc](pthread-cancellation-design.md)
- [Fil-C cancellation implementation checkpoint](pthread-cancellation-implementation.md)
- [Thread cancellation: research notes](pthread-cancellation-notes.md): the
  source audit and experiment record.
- Raw results: [glibc comparison](pthread-cancellation-results.txt) and
  [implementation](pthread-cancellation-implementation-results.txt) (plain
  text).

## Port campaigns

- [Native Fil-C port campaigns](port-campaign-operations.md): the runner and
  the dashboard at <https://nix.swa.sh/>.
- [Publishing campaign builds](binary-caches.md): the two public binary
  caches.
- [Selecting packages to try with Fil-C](package-inventory.md)
- [Fil-C port version audit](port-version-audit.md)
- [Shared-library campaign repairs](shared-library-unblocks.md)
- [Focused repairs after the shared-cancellation campaign](campaign-repairs-20260915.md)
- [Campaign failure review, October 6, 2026](campaign-failure-review.md)

### Earlier experiment runner

- [Filnix experiment runner and dashboard](experiment-architecture.md)
- [Archived Python campaign operations](experiment-operations.md)
- [Experiment failure triage](experiment-triage.md)
- [The Tagflow campaign viewer](dashboard-architecture.md)
- [Campaign monitor: design tightening](dashboard-design-tightening.md)
