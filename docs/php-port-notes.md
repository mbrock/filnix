# PHP port: implementation and measurement notes

Start with [PHP on Fil-C](php.md) for installation, server performance
and choosing a build. This page keeps the detailed porting record,
historical benchmark configurations and test counts. Numbers below belong
to the builds and workloads named alongside them, not to every current
PHP package. The C-emitting JIT is an early experiment, superseded for
new evaluations by the staging LLVM backend described below.

PHP 8.5 builds with Fil-C, along with its bundled extensions and the common
PECL ones. A memory error anywhere in PHP or a library it loads stops the
process with a Fil-C panic instead of corrupting memory. There are three ways
to get it:

```sh
nix build .#pkgsFilc.php     # the Nix package, with Nixpkgs' default extensions
nix build .#php-dist         # php-8.5.12-filc-x86_64-linux.tar.xz, runs without Nix
nix build .#php-docker       # an OCI image of the same tree
```

`pkgsFilc.php` follows PHP's 8.5 releases, now 8.5.12, which fixes
CVE-2026-109618 and CVE-2026-109619. `pkgsFilc.php84_25` keeps the
vulnerable 8.4.25 with the same Fil-C patches, for reproducing those bugs
and comparing them with their fixes (see
[Vulnerable PHP under Fil-C](#vulnerable-php-under-fil-c)). It is marked
insecure, so Nix refuses it unless asked:

```sh
NIXPKGS_ALLOW_INSECURE=1 nix build --impure .#pkgsFilc.php84_25
```

For isolated reproductions, the explicitly named distribution outputs opt in
to this version only, without allowing insecure packages globally:

```sh
nix build .#php84_25          # cached Nix package, default extensions
nix build .#php84_25-dist     # php-8.4.25-filc-x86_64-linux.tar.xz
nix build .#php84_25-docker   # the same distribution as an OCI image
docker pull ghcr.io/mbrock/filnix-php:8.4.25
```

Configure a [binary cache](binary-caches.md) to substitute the Nix outputs.
The tarball and image use the same distribution machinery as the default
build, with the extensions supported by 8.4. CI keeps both tarballs as
workflow artifacts; releases include both tarballs and image archives.
**8.4.25 is vulnerable, for reproductions only,
not production.** It never replaces `pkgsFilc.php`, `php-dist`, `php-docker`
or the container's `latest` tag.

`pkgsFilc.php.withExtensions` and `pkgsFilc.php.buildEnv` work as in
Nixpkgs; see [php-extensions.md](php-extensions.md) for which extensions are
ported and how they are tested. PHP 8.5 is the default, also named
`pkgsFilc.php85`; see [PHP 8.5](#php-85). PHP 7.4, which no longer gets
regular security fixes, builds too; see [PHP 7.4](#php-74).

## The tarball

`php-dist` is a relocatable directory with `php`, `php-fpm`, `php-cgi` and
`phpdbg`, its own glibc, libc++ and Fil-C runtime, and every library its
extensions load. Unpack it anywhere on x86-64 Linux; it needs nothing from
Nix or the host's C library. Its [README](../packages/php-dist/README.md) is
the user documentation and ships inside the tarball.

It loads Nixpkgs' default extensions plus apcu, ast, bz2, decimal, ds,
event, imagick, mailparse, maxminddb, memcached, mongodb, msgpack,
protobuf, redis, shmop, sysvmsg, sysvshm, tidy, uuid, xsl, yaml and zstd
(`packages/php-dist/default.nix`). Imagick brings ImageMagick with its
image libraries: libjpeg-turbo, libtiff, libpng, libwebp, OpenJPEG, OpenEXR,
LibRaw and lcms2, all built with Fil-C. Debuggers and profilers (xdebug,
pcov, spx) are ported but not loaded, since they slow every request.
The CA bundle is the Fil-C package set's `cacert`.

`packages/php-dist/test/run.sh TARBALL IMAGE...` unpacks it in containers
without `/nix` and checks the extensions, the built-in server and FPM with
opcache, as root and unprivileged. The default **PHP 8.5.12** distribution
passed on `debian:13` and `alpine:3` (Alpine 3.24), under both UIDs, on
November 5, 2026. The OCI image also loads OPcache, Imagick, MongoDB, Redis
and PDO SQLite and reports PHP 8.5.12. The original 8.4 distribution passed
on `debian:12`, `debian:13`, `ubuntu:22.04` and `alpine:3`; those additional
platform results are historical.

## The container image

Without Nix, pull it from the GitHub container registry, where CI publishes
each cached revision of `main`:

```sh
docker pull ghcr.io/mbrock/filnix-php:8.5.12    # after a release publishes this tag
```

The same CI run keeps the tarball as a workflow artifact; see
[binary-caches.md](binary-caches.md#continuous-integration). With Nix:

```sh
nix build .#php-docker && docker load < result
docker run --rm -it filnix-php:8.5.12                       # php -a
docker run --rm -p 8000:8000 -v $PWD:/var/www/html \
  filnix-php:8.5.12 php -S 0.0.0.0:8000                     # built-in server
docker run --rm -p 9000:9000 -v $PWD:/var/www/html \
  filnix-php:8.5.12 php-fpm                                 # FastCGI on 9000
```

The layout follows the official `php` images: programs in `/usr/local/bin`,
the tree in `/opt/php`, the document root in `/var/www/html`. FPM stays in
the foreground, listens on port 9000, logs to the container's stderr and
runs its workers as `nobody`. Mount a web server such as nginx or Caddy in
front of it as with `php:fpm`. The configuration is `/opt/php/etc`;
`PHP_INI_SCAN_DIR` and `PHPRC` work as usual.

The image's stop signal is SIGQUIT, FPM's graceful shutdown. PHP's CLI has
no handler for it, and PID 1 ignores signals it does not handle, so
`php -S` and scripts need `docker run --init` to stop promptly.

## Differences from other PHP builds

- PHP uses the system allocator by default, not Zend's. Zend's allocator
  hands out request memory from 2 MiB chunks, so Fil-C would bound a PHP
  value only by its chunk, and a freed value's memory is reused within it:
  use after free and overflows between values would go unnoticed. The
  `var_destroy` use after free in `unserialize()` (see
  [the reproduction](https://ampcode.com/threads/T-01a15e04-a3b6-7208-bdf5-680581ab02f5))
  runs silently to completion on Zend's allocator and stops with a Fil-C
  panic on the system allocator. The default is PHP's *tracked* system
  allocator, the one its ASan CI uses, so `memory_limit` and
  `memory_get_usage()` and `memory_get_peak_usage()` still work.
  It is about twice as slow as Zend's on allocation-heavy code.
  `USE_TRACKED_ALLOC=0` uses untracked malloc, about a third faster, without
  `memory_limit`; `USE_ZEND_ALLOC=1` restores Zend's allocator and gives up
  that protection. See `patches/php-8.4-alloc-filc.patch`.
- No JIT by default. Opcache's native JIT and PCRE's JIT are off. The
  experimental staging build uses Fil-C's in-process LLVM JIT; see
  [PHP 8.5 through the LLVM JIT](#php-85-through-the-llvm-jit). The older
  C-emitting backend below is retained as an experiment.
- Opcache maps its shared memory privately, because capabilities do not
  cross processes. Each FPM worker therefore has its own cache. Workers share
  what the master compiled before forking, and `opcache_reset()` affects only
  the worker that calls it.
- PHP uses more CPU and memory than an ordinary build. See the
  [server measurements](php.md#the-jit-on-real-applications) for latency,
  throughput and limits of the comparison, rather than a universal slowdown.
- Native extensions must be built with Fil-C as well, so binary PECL
  packages from elsewhere do not load.

## Test results

The Nix build runs the bundled extensions' suites (pcntl skips a
CPU-pinning test). On 8.4.27, filter passes 118 tests and OPcache 864, with
no unexpected failures. The separate core/standard-library sweep passes
13345 tests, with four expected failures and three failures in ZipArchive
encryption, since Nixpkgs builds libzip without it; 816 tests skip.
The sweep uses a directory containing the shared modules as `extension_dir`
so subprocess tests can find them, and `--set-timeout 300` for the new OOM
tests under instrumentation.
`USE_ZEND_ALLOC=0` runs, which give each PHP value its own bounds, are
described in [php-extensions.md](php-extensions.md).

Not yet ported: memprof, enchant and swoole.

## Opcache JIT through C

**Historical experiment.** This was the first checked JIT backend, not the
recommended starting point for a new service. The staging LLVM API backend
below replaces the external compiler with in-process compilation and links
side traces. These notes explain how the experiment worked and retain its
measurements for comparison.

`pkgsFilc.php84-jit` (also `.#php-jit`) is PHP 8.4 whose opcache has the
JIT enabled. It is experimental and not the default: everything else,
including `php-dist` and `php-docker`, uses `pkgsFilc.php`.

```sh
nix build .#php-jit
result/bin/php -d opcache.enable_cli=1 -d opcache.jit=function \
  -d opcache.jit_buffer_size=32M script.php
```

Opcache's JIT builds each hot PHP function into an IR and normally turns
that into machine code, which Fil-C cannot run. This build prints the IR as
C instead, compiles it with the Fil-C compiler, and loads the result with
`dlopen` (`patches/php-8.4-opcache-jit-c-filc.patch`). The generated code is
instrumented like any other Fil-C code, so a JIT bug gives a wrong result or
a Fil-C panic, not memory corruption. Emacs' Comphack backend does the same
for Emacs Lisp.

The JIT turns pointers into integers, which lose their Fil-C capability.
The backend records every pointer the JIT embeds as a constant and the
generated code reads it back from a table the loader fills in; address
values are `char *` in the C, and the fixed VM registers are C variables.
A guard that fails in a trace writes the snapshot's values into a buffer
laid out like the native exit's register dump and calls the usual
`zend_jit_trace_exit()`.

What works and what does not:

- Opcache's JIT test suite (475 tests) passes with `opcache.jit=function`,
  `opcache.jit=tracing`, and hot-function triggering
  (`opcache.jit=1235`), and the Nix build runs the extension's 866 tests.
- Every compile runs the Fil-C compiler, about 0.1 to 1 second per
  function, synchronously in the request that made the function hot.
  `opcache.jit=function` compiles every function of a script when it is
  loaded, which suits small CPU-bound scripts and not applications with
  thousands of functions; `opcache.jit=1235` compiles only functions
  called often. `PHP_JIT_CC="ccache …"` reuses compiled objects across
  processes.
- Tracing works but is slower than the interpreter: generated code cannot
  be patched, so side traces are never linked and their exits always fall
  back to the interpreter. (The LLVM backend below links them.)
- Each process compiles its own code; FPM workers do not share it.

On `Zend/bench.php`, function mode ran the CPU-bound benchmarks 4 to 60
times faster than the interpreter (mandel 0.198 s to 0.005 s, fibo(30)
0.367 s to 0.096 s), not counting compile time.

DokuWiki (the Nixpkgs copy, served with `php -S`) works with
`opcache.jit=1235`: page views, raw export, index, search, the editor,
recent changes, the CSS and JS bundles and the RSS feed produce the same
output as the interpreter, and the error log stays empty. The first
requests are slow because they compile what becomes hot (the first page took
about 9 minutes on a loaded machine, and the CSS bundle about 2.5 minutes).
After a few requests nothing new compiles, and rendering all ten pages with an
empty page cache takes about 2.1 s, the same as the interpreter. The JIT
does not speed up this kind of string- and I/O-bound code.
`opcache.jit=function` is impractical for DokuWiki because it compiles
every function of each included file on first load.

Environment variables: `PHP_JIT_CC` (compiler, default the Fil-C clang the
package was built with), `PHP_JIT_CFLAGS` (default `-O1`), `PHP_JIT_C_DIR`
(parent of the per-process work directory, default `/tmp`),
`PHP_JIT_C_KEEP=1` (keep the generated C), `PHP_JIT_C_VERBOSE=1`.

### PHP 8.5 and the persistent cache

`.#php85-jit` (`pkgsFilcStaging.php85-jit`) is PHP 8.5 with the same JIT,
built with the staging toolchain, whose compiler the JIT also runs. 8.5's CALL VM passes
`opline` to handlers and returns the next one tagged with
`ZEND_VM_ENTER_BIT`, and the backend follows that
(`patches/php-8.5-opcache-jit-c-filc.patch`). Plain `php85` uses a HYBRID
VM, which the JIT cannot use; it is selected only without the JIT. In a
development build the JIT suite passes 488/488 in function, tracing and 1235
modes; the Nix build runs the OPcache suite (with the JIT off, its default)
and a small script with it on, through each backend (see the LLVM section
below, which is the default on staging).

Compiled code can be shared between processes. `PHP_JIT_C_CACHE` names
colon-separated directories of compiled objects; new ones go to the first.
The generated C refers to every pointer through the `zjc_K` table that the
loader fills, so its text determines the code. The key hashes that text with
PHP's `zend_system_id`, the compiler and its flags, so it covers the PHP
build, the source and the JIT settings. To keep the text the same across
processes, addresses derived from embedded pointers are written relative to
pointers of the same function, opline comparisons use whole pointers, and
jump tables' bucket addresses are loaded rather than embedded. A second
process then hits on every function of the JIT suite and of DokuWiki.

A hit skips clang, but the JIT still builds the IR and prints the C. On 25
DokuWiki files (304 functions, `opcache.jit=function`) that was 0.9 s with
everything cached against 983 s cold (of which clang 973 s) and 0.03 s
without the JIT, about 3 ms per function. The emitter turns off stdio
locking on its private streams: Fil-C's libc made two `sigprocmask` calls
per locked `fprintf`, which more than doubled that.

`PHP_JIT_C_CACHE_ONLY=1` leaves functions that miss to the interpreter
instead of compiling them, so a server with a prefilled cache never compiles.
`PHP_JIT_C_MAX_SIZE` (default 512 KiB of C) leaves larger functions
interpreted: one 650-line PHP function made 1.8 to 3.3 MB of C, and the
1.8 MB version took 3 minutes and 7 GB to compile at `-O0`.
`PHP_JIT_C_STATS=1` prints counts and times at exit and `PHP_JIT_C_LOG=file`
logs one line per function. The settings are read once,
so FPM workers use the master's even with `clear_env`.

### PHP 8.5 through the LLVM JIT

The staging toolchain has Fil-C's in-process LLVM JIT (`filc_llvm_jit.h`,
see [upstream updates](upstream-updates.md#llvm-jit)), and there
`.#php85-jit` compiles with it by default instead of printing C
(`ext/opcache/jit/zend_jit_llvm.c` in the same patch). Each IR function
becomes an LLVM module built in memory and compiled by
`FilLLVMJIT_CompileModule`, which always runs KillUB and FilPizlonator, so
the code is checked like compiled C. Nothing is written to disk and no
compiler process runs. The package links PHP with `-enable-filc-jit`, which
the JIT API requires.

The backend reuses the C backend's analysis: addresses that are integers
stay `i64`, the others are LLVM pointers and arithmetic on them is a GEP. A
registered pointer becomes an external global bound to that pointer with
`FilLLVMJIT_SetGlobalMapping`, so the code gets its capability. Every IR
value gets a stack slot of its own and PHIs become IR's de-SSA moves, as
variables do in the C; LLVM's SROA turns the slots back into SSA values. Trace
exits, stubs and the fixed VM registers work as in the C backend.

Unlike the C backend, the LLVM backend links side traces. Each trace has an
exit table, a global array bound with `FilLLVMJIT_SetGlobalMapping`; a
failed guard writes its snapshot's values to an exit buffer laid out like
the native exit's register dump and, if `zend_jit_link_side_trace` has
filled its slot, tail-calls the side trace (`musttail`), which reads its
parent's registers (`RLOAD`) from that buffer. Unlinked exits deoptimize
through the C exit stub. Only one kind of exit still fails to compile (the
`trace_exit` stub's `EXITCALL`, which nothing needs); an earlier count of
171 "EXITCALL" failures was side traces reading non-VM registers, which now
work. Linking made no measurable difference on `Zend/bench.php`, where the
bigger win was allocating the 1 KiB area for the IR's `SP` only in functions
that use it: Fil-C zeroes stack allocations, and every trace paid for it.
A branchy loop went from 1.07 s to 0.38 s in tracing mode (interpreter
0.86 s, function mode 0.12 s).

Both backends stop PHP's execution timer while compiling, so compile time
does not count against `max_execution_time`. Without that, the first
requests to a WordPress or MediaWiki FPM worker, which compile hundreds of
traces, failed with "Maximum execution time of 30 seconds exceeded" where
the interpreter served them.

Two bugs that the JIT suite missed showed up in the applications, in both
backends. Function JIT adds each `RECV` or OSR entry as an `ENTRY` block
whose fake input is the preceding `END`, and the backends let that `END`
jump into the entry, which resets FP and IP to the function's parameters.
That is harmless until IR turns a direct recursive call into a loop: then
the "call" restarted the caller's frame. Under `opcache.jit=1235` WordPress
served truncated pages with status 200 and a clean log, and MediaWiki
recursed until it ran out of memory and panicked in `FE_FETCH_R`. Both
backends now skip `ENTRY` successors, as IR's own emitters do. And a trace
exit into a `__call` trampoline frame read `EG(trampoline)`'s reserved
slot, which property hooks and FFI reuse for other data, as a trace
extension; Fil-C stopped the C backend on MediaWiki.

Compiled functions are named after their PHP code (`jit:Class::method@file`,
`jit:TRACE-$Class::method$34`, without the trace number so that workers
build identical modules), so a Fil-C panic in JIT code says which code it
was. `PHP_JIT_LLVM_DUMP=text` prints the IR and the LLVM module of
the functions whose name contains `text`. `PHP_JIT_LLVM_MAX_INSNS` (default
10000) leaves larger IR functions to the interpreter: LLVM's time grows
faster than the function (49000 IR instructions took 20 to 35 s, most of it
in FilPizlonator's check scheduling), and it is spent in the request that
made the code hot. `PHP_JIT_LLVM_OPTIONS=key=value,...` passes further
`FilLLVMJIT_SetOption` options. At staging `18b6663`, only `opt-level` is
consumed from that per-session map. O1 reduced compilation time in the
early experiments without a clear warm-runtime result, so O2 remains the
default. The earlier `filc-inline=0` and `verify=0` experiments used this
map too: those options were ignored, so their timing differences do not
demonstrate an inlining or verification benefit. The separate global
`FILC_LLVM_OPTIONS` parser is available only with the testing runtime.

`PHP_JIT_BACKEND=c` selects the C backend (with its persistent cache, which
the LLVM backend does not use; it shares code between workers instead, see
below), `PHP_JIT_LLVM_OPT` sets LLVM's opt-level
(default 2) and `PHP_JIT_LLVM_DUMP=1` prints each module. `PHP_JIT_C_STATS`,
`PHP_JIT_C_LOG` and `PHP_JIT_C_VERBOSE` cover both backends.

In a development build the JIT suite passes 488/488 with the LLVM backend in
function, tracing and 1235 modes, in 24 to 26 s per mode with 24 jobs.
Compile times on `Zend/bench.php` (`opcache.jit=function`, C backend without
ccache):

| | units | C backend | LLVM |
| --- | --- | --- | --- |
| stubs | 25 | 2.36 s (94 ms each) | 0.25 s (10 ms each) |
| functions | 31 | 11.4 s (368 ms each) | 6.65 s (214 ms each) |

The largest function (the script body, 4166 IR instructions) took 2.3 s
through C and 2.0 s through LLVM. Across the JIT suite's 1224 functions and
traces the LLVM backend averaged 130 ms; the slowest, a 19089-instruction
script body, took 8.7 s.

The code is as fast or faster (seconds, `opcache.jit=function`, run time
only):

| | interpreter | C backend | LLVM |
| --- | --- | --- | --- |
| mandel | 0.109 | 0.004 | 0.004 |
| ackermann(7) | 0.073 | 0.024 | 0.017 |
| fibo(30) | 0.234 | 0.081 | 0.061 |
| heapsort(20000) | 0.067 | 0.015 | 0.012 |
| matrix(20) | 0.061 | 0.017 | 0.013 |
| bench.php total | 8.9 | 8.520 | 8.523 |

These numbers come from a development build whose `strcat` is slow; the
packaged build's are in [the next section](#the-jit-on-real-applications). `strcat` (over 8 s) dominates the totals in every configuration. In tracing mode,
where traces compile while the benchmark runs, the total was 16.2 s
through C and 10.6 s through LLVM, and with `opcache.jit=1235` 15.5 s and
12.1 s. LLVM's opt-level matters little here: `-O1` compiled bench.php's
functions in 5.5 s and ran them within a few percent of `-O2`.

### The JIT on real applications

Measured with `php-bench` (`bench/php/README.md`) on the packaged
`pkgsFilcStaging.php85-jit`, `php -S` with one worker, the fixtures'
request mixes, three rounds of `php-bench quiet`. Short version: the JIT
runs WordPress, MediaWiki and DokuWiki correctly in every mode tried. On
CPU-bound PHP the LLVM tracing JIT is several times faster than Fil-C's
interpreter and on `Zend/bench.php` slightly faster than the native
interpreter. The applications gain at most 16% in wall time, because their time goes to
string handling, arrays, PCRE, the database and the runtime, not to PHP
opcodes. Each worker pays about two minutes of compiling and 350 to 400 MB
of memory to get there.

**Compatibility.** `php-bench check` serves each mix after warm-up and
compares it with the interpreter (`filc-staging`): status, size and body,
with numbers, hashes and nonces masked, and the error and server logs.

| app | `jit=tracing` LLVM | `jit=tracing` C | `jit=1235` LLVM |
| --- | --- | --- | --- |
| DokuWiki (12 requests) | same, 110 compiles, 22 s | same, 92 compiles, 18 s | same, 44 compiles, 12 s |
| MediaWiki (12) | same, 1188 compiles, 131 s | same, 811 compiles, 233 s | same, 1664 compiles, 768 s |
| WordPress (11) | same, 1330 compiles, 114 s | same, 920 compiles, 236 s | same, 678 compiles, 344 s |

Every response matched and every log stayed empty. Before the fixes above,
WordPress under 1235 served truncated pages with status 200 and a clean
log, which only the body comparison caught, and MediaWiki crashed under 1235
and, through C, under tracing. `opcache.jit=1235` compiles whole functions,
which costs far more than traces in big applications (13 minutes for
MediaWiki); `function` mode would compile every function of every file
loaded. Use tracing.

**Steady state.** User cycles of all threads, and wall time, for one pass
over the mix after ten warm-up passes (medians of three rounds):

| app | native | native JIT | Fil-C interpreter | Fil-C LLVM JIT | Fil-C C JIT |
| --- | --- | --- | --- | --- | --- |
| DokuWiki Gcycles | 0.049 | 0.043 | 0.252 | 0.324 | 0.364 |
| DokuWiki wall ms | 22 | 21 | 68 | 57 | 77 |
| MediaWiki Gcycles | 1.29 | 1.21 | 6.50 | 6.80 | 8.03 |
| MediaWiki wall ms | 299 | 282 | 1287 | 1339 | 1591 |
| WordPress Gcycles | 1.54 | 1.26 | 9.93 | 8.59 | 11.53 |
| WordPress wall ms | 331 | 276 | 1920 | 1654 | 2179 |

Against the Fil-C interpreter the LLVM JIT takes 0.87× the cycles and wall
time on WordPress, 1.05× and 1.04× on MediaWiki, and on DokuWiki 1.29× the
cycles but 0.84× the wall time (more of the work lands on Fil-C's GC
threads). Against native it stays where the interpreter is: 5.3 to 6.6×
the cycles and 2.6 to 5.0× the wall time, or 5.6 to 7.5× and 2.7 to 6.0×
against native with its JIT. Native's JIT gains only 4 to 18% on these
applications too. The C backend is slower than the interpreter everywhere:
it cannot link side traces, so every side exit deoptimizes.

**Warm-up.** A fresh server's first pass compiles almost everything:

| app | LLVM: compiles, compile s, first pass s | C, cold: compiles, first pass s | C, with its cache: first pass s |
| --- | --- | --- | --- |
| DokuWiki | 109, 12.8 s, 8.2 s | 92, 10.1 s | 0.34 s |
| MediaWiki | 1170, 130 s, 132 s | 811, 235 s | 179 s |
| WordPress | 1330, 114 s, 117 s | 920, 241 s | 8.7 s |

Steady state follows from the third pass on. MediaWiki's traces mostly miss
the C backend's cache from one process to the next (543 compiles even with
a filled cache), WordPress's and DokuWiki's hit. Compiling runs in the
request that made the code hot, with the execution timer stopped, so the
first visitors to each worker wait.

**Memory (FPM).** One static FPM worker, the mix repeated, RSS of the
worker: the LLVM JIT reached 742 MB after WordPress's first pass and stayed
between 745 and 790 MB through 1617 requests; MediaWiki stayed between 816
and 864 MB through 360 requests (850 to 910 MB through 1200 in an earlier
run). The interpreter held about 390 MB (WordPress) and 490 MB (MediaWiki),
the C backend about 520 MB on WordPress. Compiled code is never freed, but
nothing new compiles after warm-up, so this is a one-time 350 to 400 MB per
worker, not a leak. A pass took 1.7 s with the LLVM JIT against 1.9 s for
the interpreter on WordPress, and 1.4 s on MediaWiki for both. With the C
backend WordPress's passes slowed from 2.2 s to 7.7 s over 330 requests,
which we have not explained.

**Sharing code between workers.** Every FPM worker traces and compiles on
its own, and opcache's shared-memory lock serializes JIT compiles across
workers, so with four static workers the first pass of the request mix
spent 625 s compiling WordPress (4952 units) and 730 s compiling MediaWiki
(4407 units) before steady state. `PHP_JIT_LLVM_CACHE_SIZE=256M` turns on
Fil-C's shared object cache (`FilLLVMJIT_EnableSharedObjectCache`, see
[upstream updates](upstream-updates.md#llvm-jit)): the master maps a
region before forking, and a worker whose module and mappings match one
another worker compiled links that object (about 1 ms) instead of
compiling it (tens of ms). For modules to match across workers, the
backend keeps per-process values out of the IR: pointers into opcache's
memory (private to each process under Fil-C), each exit's link target and
the trace number are read from module globals filled in after compiling.
Four static workers, `opcache.jit=tracing`, the mix repeated:

| | units | hits | compile seconds | first pass | steady pass |
| --- | --- | --- | --- | --- | --- |
| WordPress, no cache | 4952 | 0 | 624 s | 625 s | 2.1 s |
| WordPress, cache | 4945 | 2138 (43%) | 332 s | 333 s | 2.1 s |
| MediaWiki, no cache | 4407 | 0 | 730 s | 729 s | 1.8 s |
| MediaWiki, cache | 4452 | 976 (22%) | 602 s | 602 s | 1.8 s |

Worker RSS stays at 750 to 840 MB (WordPress) and 820 to 1030 MB
(MediaWiki) either way. The hit rate is bounded by tracing itself: most
misses are traces that only one worker built, because each worker's
traces follow its own profile, and MediaWiki's vary more. About 10% of
misses are the same trace in several workers with identical LLVM modules,
so what differs is a mapped pointer: an object each worker allocated after
forking (which ones is not yet known; classes linked at run time are a
guess), bound as a constant. Reading every pointer from a global instead
cost 60% on `Zend/bench.php`. The cache is off by default: Fil-C code gets no
capability to the region, but the runtime's refusal of writable
`/proc/self/mem` opens can be raced by a second thread, and code that
escaped that way could plant code for every worker instead of only its
own.

**CPU-bound scripts.** `Zend/bench.php` and `bench/php/micro.php`, served
warm (seconds; three requests to warm up, median of three):

| | native | native JIT | Fil-C interpreter | Fil-C JIT tracing | Fil-C JIT function | Fil-C C JIT |
| --- | --- | --- | --- | --- | --- | --- |
| bench.php | 0.151 | 0.041 | 0.620 | 0.133 | 0.190 | 0.372 |
| mandel | 0.016 | 0.004 | 0.049 | 0.004 | 0.004 | 0.005 |
| fibo(30) | 0.026 | 0.011 | 0.149 | 0.045 | 0.072 | 0.193 |
| heapsort(20000) | 0.010 | 0.003 | 0.042 | 0.008 | 0.012 | 0.035 |
| strcat(200000) | 0.002 | 0.001 | 0.014 | 0.011 | 0.011 | 0.011 |
| micro.php | 0.238 | 0.162 | 1.126 | 0.686 | 0.692 | 1.308 |
| fib(27) | 0.005 | 0.003 | 0.037 | 0.010 | 0.017 | 0.070 |
| nbody | 0.081 | 0.019 | 0.358 | 0.065 | 0.087 | 0.159 |
| usort | 0.103 | 0.109 | 0.503 | 0.454 | 0.452 | 0.641 |
| strings | 0.027 | 0.023 | 0.153 | 0.128 | 0.129 | 0.131 |

On bench.php the LLVM tracing JIT is 4.7× faster than Fil-C's interpreter
and 0.88× the native interpreter's time, 3.2× native's JIT. Loops over
numbers run as fast as native's JIT (mandel) or faster than native's
interpreter (nbody); recursion and arrays take 3 to 4× native's JIT; `usort` and string
building gain 10 to 20%, since their time is in the runtime. Compiling
costs more than these scripts run: bench.php's 94 traces took 3.8 s, so a
single cold run from the command line takes 3.7 s with the JIT against 0.72 s
without, and `opcache.jit=function` compiles its 56 functions in 7 s before
it starts.

So the JIT pays for itself in long-running workers with numeric or
algorithmic PHP, and does little for page rendering, which is what most
PHP servers do. Fil-C's cost there is the runtime (checked string, array
and allocator code), which the JIT does not touch.

## HTTP service measurements

Measured November 5, 2026 on Chapel, a bare-metal Core i7-10700K with
16 logical CPUs. PHP workers could use CPUs `0-15`. Native nginx 1.30.5
fronted two static FPM workers; each load completed 120 HTTP responses
over loopback. Three rounds reversed variant order within each application.
The guide reports the median of the three round-level p50s, p95s and
throughputs, not pooled percentiles. Article views use one client; mixed
loads use one or four. Four clients have at most four requests in flight,
so this is closed-loop capacity, not an open-loop arrival-rate test.

The cached PHP 8.5.12 builds are exactly those evaluated at
[the November 2 snapshot](https://github.com/mbrock/filnix/commit/37e529c96b9d0bc305170e667bd048cd95a078e9):
native Nixpkgs PHP, `pkgsFilcStaging.php85` and
`pkgsFilcStaging.php85-jit`. They are not the newly rebuilt ordinary
released-toolchain default. Both Fil-C builds use the tracked system
allocator. Native PHP keeps its PCRE JIT but not its PHP JIT. LLVM uses
`opcache.jit=tracing`, a 64 MiB JIT buffer and no shared object cache.

Fixtures: MediaWiki 1.45.4 (30 generated articles, templates and categories)
and WordPress 6.9.8 (20 posts, Twenty Twenty-Five 1.5,
sqlite-database-integration 3.0.1). There is no web-server full-page cache;
normal application and filesystem caches are warmed. OPcache has 256 MiB
and 32 MiB for interned strings; PHP's `memory_limit` is 512 MiB and its
execution timer is disabled. The reverse proxy allows 1200 seconds for
cold compilation. These are deliberately small SQLite sites, not MySQL,
TLS, browser asset loading or a VM benchmark.

Each round starts fresh FPM workers, not a fresh database or filesystem
cache. Warm-up makes three passes of the mix per worker, ten for LLVM,
with two concurrent clients. Warm bodies are compared across variants
using the existing volatility mask; HTTP failures and error logs are
checked. A few mixed-load traces can still compile after warm-up; their
cost remains in latency and throughput. One article load compiled one
new trace; mixed loads compiled zero to ten. The JIT log records those
counts rather than assuming warm-up means compilation has stopped forever.

Round-to-round ranges, not confidence intervals:

| Site / runtime | Article median, ms | Mixed req/s | First mixed pass, s | Worker RSS after mixed load, MiB |
| --- | ---: | ---: | ---: | ---: |
| MediaWiki — native | 49.2–73.4 | 46.1–49.0 | 0.9 | 76–78 |
| MediaWiki — Fil-C interpreter | 179.0–185.6 | 10.5–11.2 | 3.6–3.7 | 551–616 |
| MediaWiki — Fil-C LLVM JIT | 203.9–215.7 | 8.4–8.5 | 533.8–568.3 | 1004–1228 |
| WordPress — native | 46.0–46.9 | 45.5–47.3 | 0.8 | 56–58 |
| WordPress — Fil-C interpreter | 276.1–284.8 | 7.1–7.2 | 4.0–4.2 | 518–532 |
| WordPress — Fil-C LLVM JIT | 264.3–268.6 | 7.0–7.2 | 451.3–464.1 | 976–1040 |

Host CPU busy share sampled just before each load ranged from 0.9% to
10.2%, mostly around 1–2%; the machine was lightly loaded, not exclusively
reserved. Worker RSS includes shared pages and is not unique pool memory
or a measured peak. All 54 loads completed (6480 measured responses).

The [service command](../bench/php/README.md#http-service-latency-and-throughput)
records every latency, elapsed time, warm-up pass, worker RSS and build
path in `service.jsonl` and `service-meta.json`. The latency quantiles and
throughputs were independently recalculated from those raw samples.
An initial Igloo run encountered unrelated heavy load and is not used for
the capacity figures. Replay your own traffic before sizing a deployment.

## Vulnerable PHP under Fil-C

PHP 8.4.27 (with 8.3.36, 8.2.35 and 8.5.12) fixed two memory-safety CVEs
in request handling:

- **CVE-2026-109618.** An out-of-memory error unwound the request with
  `longjmp` and could leave objects half built. Request shutdown then
  freed or used them. The fix makes allocation failures soft and checks
  for them.
- **CVE-2026-109619.** Request-owned globals survived an aborted request
  and were used again before the next request started. The case found was
  the session upload-progress handler, which runs during multipart
  parsing. The fix resets them early and clears them at shutdown.

We ran the regression tests PHP added with these fixes (the OOM,
multipart, session and next-request tests: 235 in all) against Fil-C
8.4.25, before the fixes, and Fil-C 8.4.27, both on the default system
allocator ([thread](https://ampcode.com/threads/T-01a15f5c-79eb-70bb-b41f-3eff4075aa4b)).
On 8.4.25, Fil-C stopped two of them at an invalid access, where native
PHP keeps going:

- `ext/xml/tests/oom_xml_parse_into_struct.phpt` (CVE-2026-109618). The
  OOM leaves an XML parser half built, and request shutdown frees it:

  ```text
  filc safety error: cannot read pointer with null object.
      pointer: (nil),<null>
      expected 8 bytes.
  semantic origin:
      (php) Zend/zend_alloc.c:3006:16: tracked_free
  ...
      (php) ext/xml/xml.c:327:4: xml_parser_free_ltags
      (php) ext/xml/xml.c:341:2: xml_parser_free_obj
      (php) Zend/zend_execute_API.c:423:2: zend_shutdown_executor_values
      (php) main/main.c:1952:2: php_request_shutdown
  filc panic: thwarted a futile attempt to violate memory safety.
  ```

  Native PHP 8.4.26 passes this test without noticing.
- `ext/session/tests/user_session_module/session_create_id_create_sid_throws.phpt`
  (the CVE-2026-109619 session fixes). A `create_sid` handler that throws
  leaves the session half set up, and validation reads through it:

  ```text
  filc safety error: cannot read pointer with null object.
      pointer: 0x4,<null>
      expected 4 bytes.
  semantic origin:
      (session.so) mod_user.c:264:3: ps_validate_sid_user
  ...
      (session.so) session.c:2515:9: zif_session_create_id
  filc panic: thwarted a futile attempt to violate memory safety.
  ```

  Native 8.4.26 fails the test's expected output but does not crash.

On 8.4.27 none of the 235 tests panics. Its eight failures come from the
test setup: CGI subprocesses without some extensions, no network for curl,
and multipart memory limits tuned to Zend's allocator.

So Fil-C turned bugs in the class these CVEs belong to into a stopped
process before PHP knew about them, and it did so without knowing what the
bugs were. That is the case for running PHP on Fil-C. But the evidence
has limits:

- The OOM stage of the exploit below runs in the CLI server. The startup
  OOM routes to CVE-2026-109618 that need mod_php or FrankenPHP, which
  have no Fil-C build, were not tested.
- A trap is still a crash, and an attacker who can trigger one at will can
  take workers down. Logic bugs in the same code are unaffected.

So run patched releases. `php84_25` is marked insecure for that reason
and exists only to reproduce the bugs and compare them with their fixes.

### The StealMyBitcoin exploit against 8.4.25

[StealMyBitcoin](https://github.com/KillaBoi/StealMyBitcoin-PoC) is a
public exploit chain for these two CVEs. A multipart request walks a
worker into its memory limit during startup parsing; the abort skips the
session deactivate and leaves stale request state behind. Consumers then
race for that worker: a fresh session-id string lands on the freed slot,
later multipart fields corrupt its length, and the corrupted read leaks
neighbouring heap bytes — the Zend chunk base, then `zval_ptr_dtor`,
which locates the code image. A final request plants a forged HashTable
whose pDestructor is `zif_system`, and PHP's cleanup path runs the
attacker's command.

We adapted the PoC's address constants to the builds this flake ships and
run it as a differential check
(`nix build .#checks.x86_64-linux.php-stealmybitcoin`,
[tests/php-stealmybitcoin.nix](../tests/php-stealmybitcoin.nix)): the same
exploit, against the Nixpkgs PHP 8.4.25 built the same way without Fil-C,
and against `pkgsFilc.php84_25`, each behind nginx. On the native build
the exploit succeeds: both leaks land, the forged callback fires, and the
response carries the execution evidence. On the Fil-C build the producer
still OOMs — the vulnerability is real and gets exercised — but the first
consumer's corrupted read stops at the capability trap, every single run
(three runs, all at the same source line):

```text
filc safety error: cannot read pointer with null object.
    pointer: (nil),<null>
    expected 8 bytes.
semantic origin:
    (php) Zend/zend_alloc.c:3006:16: tracked_free
...
    (session.so) session.c:3378:5: php_session_rfc1867_callback
    (php) main/php_variables.c:498:3: php_default_treat_data
    (php) main/php_variables.c:788:2: php_hash_environment
    (php) main/main.c:1873:3: php_request_startup
filc panic: thwarted a futile attempt to violate memory safety.
```

No heap bytes, no code pointer, no callback: the stages after the trap
cannot even start. The check writes both arms' raw HTTP, the PoC's
attempt records and the server logs to `$out/evidence`. The PoC's
calibrated constants (the `zif_system` offset, the heap carrier delta)
are build-specific; the defaults match the unstripped Nixpkgs baseline,
and `SMB_*` environment variables override each one while re-measuring
([thread](https://ampcode.com/threads/T-01a1783f-2a3f-71c0-9ae7-db5c801ce9c0)).

The `var_destroy` use after free in `unserialize()`
([php-src#21824](https://github.com/php/php-src/issues/21824), fix in
[#21828](https://github.com/php/php-src/pull/21828)) is a separate bug
that is not fixed in 8.4.27. Fil-C 8.4.27 still traps on it with the
default allocator, and it still runs to completion on Zend's allocator
(see [above](#differences-from-other-php-builds)).

## PHP 7.4

PHP 7.4 reached its end of life in November 2022 and gets no regular
security fixes. For CVE-2026-109618 and CVE-2026-109619 PHP published a
minimal mitigation on branch `PHP-7.4-CVE-2026-109618-109619`, which this
build applies (`patches/php-7.4-cve-2026-109618-109619.patch` and, for the
session extension, `php-7.4-session-cve-2026-109619.patch`). It is cruder
than the 8.4 fix: running past `memory_limit`, running out of memory, or
overflowing an allocation size prints the fatal error and exits the
process immediately, without shutdown functions or the rest of request
shutdown (an FPM worker that does so exits, and the master starts another),
and `session.upload_progress` does nothing.

Other PHP 7.4 bugs stay unfixed. Fil-C does not fix them, but it stops the
memory-corruption ones from being exploited: an out-of-bounds access or
use after free in PHP 7.4 or a library it loads panics instead of handing
an attacker memory. For example, the `var_destroy` use after free in `unserialize()` (see
[above](#differences-from-other-php-builds)) is present in 7.4.33:
ordinary 7.4 runs the reproduction to completion, reading freed memory, and
this build stops with a Fil-C panic (exit 133) at the freed read.

It does nothing for logic bugs. SQL injection, path traversal,
authentication bypasses, type juggling, object injection through
`unserialize()` gadget chains made of ordinary PHP code, and any CVE that
is not a memory error work exactly as in ordinary PHP 7.4. Treat it as a
mitigation while moving to PHP 8, not as a supported PHP.

```sh
nix build .#pkgsFilc.php74   # Nix package with the PHP 7.4 default extensions
nix build .#php74-dist       # php-7.4.33-filc-x86_64-linux.tar.xz, as php-dist
```

The package comes from [fossar/nix-phps](https://github.com/fossar/nix-phps),
which keeps Nixpkgs' PHP builder working for PHP 7.4 (pinned in the
`php74` block of `ports/overlay.nix`). Like nix-phps, it builds against
libxml2 2.12 and ICU 64; OpenSSL is the default OpenSSL 3. `php74-dist`
adds bz2, shmop, sysvmsg and sysvshm to the defaults and passes
`packages/php-dist/test/run.sh` (with `smoke74.php`) on `debian:12`,
`debian:13`, `ubuntu:22.04` and `alpine:3`.

It differs from PHP 8.4 on Fil-C in these ways:

- The allocator default is the same (`patches/php-7.4-alloc-filc.patch`),
  but PHP 7.4's tracked allocator kept no sizes, so it had no
  `memory_limit` and reported no memory usage. The patch gives it PHP 8's
  size tracking, so `memory_limit`, `memory_get_usage()` and
  `memory_get_peak_usage()` work as they do on 8.4.
- PHP 7.4 keeps type declarations in an integer that holds a tagged pointer
  to the class name or class entry; under Fil-C it is a pointer
  (`patches/php-7.4-filc.patch`).
- Opcache works as on 8.4 (private shared memory, no JIT).
- No PECL extensions are ported for 7.4, and there is no xsl: nix-phps
  builds PHP 7.4 against libxml2 2.12, and libxslt 1.1.45 needs 2.15.
- phpdbg watchpoints do not work: they `mprotect()` pages of PHP's heap,
  which Fil-C refuses, and phpdbg cannot install its SIGBUS handler.
  phpdbg otherwise works.

Every default extension's own test suite passes during the build. PHP's
whole test suite, run from the 7.4.33 source tree with all the default
extensions loaded (`run-tests.php -j24` with `SKIP_SLOW_TESTS`,
`SKIP_ONLINE_TESTS` and `SKIP_PERF_SENSITIVE`):

| PHP 7.4.33 | Passed | Failed |
| --- | --- | --- |
| x86-64, no Fil-C (nix-phps) | 13157 | 85 |
| Fil-C, tracked system allocator (default; `SKIP_ASAN=1`) | 13135 | 85 |
| Fil-C, Zend's allocator (`USE_ZEND_ALLOC=1`) | 13142 | 91 |

The ordinary build's 85 failures come from PHP 7.4's age against current
libraries (OpenSSL 3, libgd, libxml2, curl) and from tests that want a
terminal or the network; the same tests fail on Fil-C. Fil-C fails four
tests that pass without it: `pcntl_unshare_01`, because
`unshare(CLONE_NEWUSER)` needs a single-threaded process and the Fil-C
runtime runs its own threads, phpdbg's `info_001` (the SIGBUS handler
above), and `bug61371` and `bug61371-unix`, which expect
`memory_get_usage(true)` to stay level and see the first sockets' few
bytes of lazily created state once allocations are counted exactly.
On Zend's allocator the `bug61371` tests pass, and phpdbg's seven
watchpoint tests, which skip on the system allocator, fail, as does
opcache's `log_verbosity_bug`, which expects mapping 1 GB of shared memory
to fail; the private mapping succeeds.
It passes three that fail without it: `bug78272`, whose forked child
crashes in PCRE's JIT, and two libgd image-scaling tests. Tests of PCRE's
JIT skip, and `SKIP_ASAN` skips the tests PHP marks as needing Zend's
allocator, as in its ASan CI.

These counts predate the CVE backport. With it, the default Fil-C run
passes 13126 and fails 94: the same failures plus nine the backport causes
on purpose. Eight are the `rfc1867*` session upload-progress tests, which
now see no progress data, and `bug45392` gets an extra blank line before
the fatal error, which the backport now prints itself. The `var_destroy`
reproduction still stops with a Fil-C panic.

## PHP 8.5

`pkgsFilc.php85` is PHP 8.5.12, the current 8.5 security release, which
fixes CVE-2026-109618 and CVE-2026-109619. It is also `pkgsFilc.php`,
the default used by `php-dist` and `php-docker`.

```sh
nix build .#pkgsFilc.php85
nix build --impure --expr '(builtins.getFlake (toString ./.)).legacyPackages.x86_64-linux.pkgsFilc.php85.withExtensions ({ all, enabled }: enabled ++ [ all.apcu all.redis ])'
```

It has the 8.4 port's patches and allocator default (`mkFilcPhp` in
`ports/overlay.nix`), and the differences from other PHP builds above apply
to it too. PHP 8.5 builds Lexbor and OPcache into PHP itself, so their
patches and `--disable-opcache-jit` are applied to the PHP build, not to
shared extensions; `php-8.5-dom-filc.patch` is the Lexbor patch at its new
path. These changes are specific to 8.5:

- `--disable-huge-code-pages`: OPcache, now always built, finds PHP's
  machine code with `dl_iterate_phdr()` to copy it into huge pages. Fil-C's
  libc lacks the function, so PHP did not link.
- `php-8.5-deepbind-filc.patch`: PHP 8.5 stopped loading extensions with
  `RTLD_DEEPBIND`. Fil-C exports functions that libraries built with
  `-fvisibility=hidden` keep internal natively, so libsodium's BLAKE2b then
  called libargon2's `blake2b_update()`, which PHP links, with libsodium's
  state. `sodium_crypto_generichash()`, the KDF, key exchange and Argon2i
  returned the hash of the empty string whatever their input. The patch
  restores 8.4's loading under Fil-C. The visibility gap itself is in the
  toolchain and is not fixed here.
- `php-8.5-realloc-filc.patch`: Fil-C's `realloc()` always moves the
  object, and `zend_string_extend()` asks for the exact new length, so each
  `$s .= ...` on the system allocator copied the whole string and building
  a string took quadratic time. `__zend_realloc()` now grows past 1 KiB by
  half again and reuses the capacity `zgetupper()` reports. Zend/bench.php's
  `strcat` went from 11 s to 0.02 s, the whole of bench.php from 9.9 s to
  1.1 s, and in the PHP application benchmark (staging, three rounds) best
  user cycles fell 7% on WordPress and 5% on MediaWiki, with DokuWiki
  unchanged ([thread](https://ampcode.com/threads/T-01a1634e-c1c9-7582-9f19-79f3956e749f)).
  8.4 does not have this patch yet.
- `pcre2-10.48-filc-match.patch`, on the PCRE2 that PHP 8.5 links (other
  packages keep the shared `pcre2`): PCRE's JIT cannot run under Fil-C, and
  its interpreter spent half its time in Fil-C's capability-aware
  `memmove()`, copying the tail of a backtracking frame (pointers and the
  ovector) at every backtracking point. `pcre2_match()` also allocated its
  match block and callout block on the heap at every call, because their
  addresses escape. Under Fil-C the patch copies frames field by field and
  keeps those blocks with the match data. This PCRE2 is built without its
  JIT and runs its own test suite.

  Measured by replaying every `pcre2_match()` call of a warm pass of the PHP
  application benchmark (DokuWiki: 2,545 calls; WordPress: 331,164 calls
  over 206 patterns), checked against native results. In user cycles
  against native PCRE2 without its JIT, DokuWiki's calls went from 8.9× to
  4.5× and WordPress's from 7.9× to 5.3× on a busy machine, or about 3.7×
  on a quiet one. In the application benchmark (release toolchain,
  fixture version 2, five interleaved rounds, against the same build with
  Nixpkgs' PCRE2), instructions and best user cycles fell 0.9% and 3.3% on
  DokuWiki, 1.3% and 3.1% on MediaWiki, and 3.8% and 5.8% on WordPress,
  where cycles were lower in every round
  ([thread](https://ampcode.com/threads/T-01a163ac-9b72-7219-821f-9a8993781dc3)).
  DokuWiki's PCRE time is now small; with the first fixtures, whose pages
  were all lorem ipsum, its search highlighter backtracked over every page.

The `unserialize()` use-after-free reproduction above stops with a Fil-C
panic on 8.5.12 with the default allocator and completes on Zend's.

### Tests

The PHP build runs the suites of the extensions built into it: OPcache
passes 895 tests and URI 327, with one expected failure and 43 skipped.
Every shared extension runs its own suite as on 8.4, the PECL ones on both
allocators ([php-extensions.md](php-extensions.md#how-they-are-tested)).
The default extensions' suites pass (Nixpkgs leaves a few, such as curl's,
off), as do bz2, dba, ffi, shmop, snmp, sysvmsg, sysvshm, tidy, xsl and
zend_test.

These PECL extensions build and pass on 8.5, with the same test removals
as on 8.4 and those below: amqp, apcu, ast, decimal, ds, event, excimer,
gnupg, grpc, imagick, imap, inotify, luasandbox, mailparse, maxminddb,
memcached, meminfo, mongodb, msgpack, opentelemetry, pcov, pinba, rdkafka,
redis, snuffleupagus, spx, uuid, uv, vld, wikidiff2, xdebug, yaml and zstd.
protobuf and systemd build and ship no tests; pspell and ssh2 build and
skip all of theirs, as on 8.4.

Tests removed on 8.5 only, none of them Fil-C failures:

- decimal (7) and yaml (3) were written before PHP 8.5's warning for NAN
  coerced to a string and its deprecation of null array offsets.
- zstd's `streams_3` reads two copies of `PHP_BINARY` under a 128 MB
  `memory_limit`. Fil-C's PHP 8.5 binary is 82 MB (8.4's is 65 MB; an
  ordinary build's 16 MB).
- meminfo's `dump-memory_leak` runs on Zend's allocator only: on PHP 8.5's
  tracked allocator `memory_get_usage()` ends 426 bytes lower after the
  dump, natively too.

igbinary 3.2.14, memcache 8.2 and phalcon 5.10.0 do not build on PHP 8.5,
natively either: they include `ext/standard/php_smart_string.h`, which 8.5
removed, and Nixpkgs marks them broken. They need newer releases. The
extensions not ported to 8.4 are not ported to 8.5 either.

### Interpreter dispatch

PHP picks one of three VM kinds. CALL calls each opcode handler through a
function pointer from a loop. HYBRID jumps between handlers inside one big
`execute_ex` with computed `goto`. TAILCALL, new in 8.5, has handlers
tail-call each other. Upstream uses HYBRID only with GCC's global register
variables and TAILCALL only with `preserve_none`, and Fil-C's clang has
neither. That made Fil-C's 8.5 build fall back to CALL, which costs a call,
a Fil-C frame push and pop, and a return per opcode.

TAILCALL stays out of reach. Fil-C keeps a `musttail` call as a tail call
only when the pointers it passes are the caller's own incoming arguments.
PHP's handlers pass a new `opline`, so their tail calls become ordinary
calls. An unmerged upstream ABI change (branch
`fil/callee_arg_roots_abi_change`) would lift that restriction, but it was
not evaluated.

`php-8.5-hybrid-vm-filc.patch` adds a Fil-C HYBRID mode to
`zend_vm_gen.php`, and the build regenerates `zend_vm_execute.h` with a
native PHP. The mode differs from upstream HYBRID in three ways:

- No global registers. `execute_data` and `opline` are locals of
  `execute_ex`, and out-of-line handlers keep CALL's protocol: they take
  `(execute_data, opline)` and return the next opline.
- Only a hot set is inlined into `execute_ex`: arithmetic, comparisons,
  increments and decrements, `QM_ASSIGN`, the jumps, `FETCH_DIM_R_INDEX`,
  bitwise ops, `TYPE_CHECK`, `ISSET_ISEMPTY_CV` and `NOP`, which is 136
  specialized handlers. Every other handler stays out of line and is
  reached through the same computed `goto` table. Inlining all of them made
  `execute_ex` slower than CALL: FilPizlonator re-records pointer roots at
  the dispatch loop's header, and the huge function spills.
- The JIT red zone is reserved only with global registers.

The mode is chosen with `defined(__FILC__) && !defined(HAVE_JIT)`.
`php85-jit` is configured with the JIT, so it keeps CALL, which its C
backend relies on. PHP 8.4 is unchanged.

Gains over CALL, measured as minimum cycles on a loaded machine with
interleaved runs. `Zend/bench.php` totals leave out `strcat`, which is
dominated by string allocation:

| | release | staging |
|---|---|---|
| bench.php total | −11.4% | −16.1% |
| mandel / mandel2 | −10.5% / −12.9% | −14.5% / −18.1% |
| fibo(30) | −14.7% | −18% |
| simple | −37% | −39% |
| micro: `for` loop | −35% | −34% |
| micro: arithmetic | −26% | −23% |
| micro: user function call | −18% | −20% |
| micro: array reads | −15% | −11% |
| micro: internal function call | −1% | −6% |

In the PHP application benchmark (five interleaved rounds), HYBRID ran
2.3% fewer user instructions on DokuWiki and 3.3% fewer on MediaWiki and
WordPress. Cycle deltas there were within the noise of a loaded machine.

Compiling `zend_execute.c` takes 139 s and 1.7 GB instead of 115 s and
1.2 GB. The binary is 0.7 MB larger.

On release, the store binaries pass the same 6145 `Zend/tests` and OPcache
tests under both VMs, with 2 expected failures and 185 skipped. A local
staging build with `zend_test` also gives identical results under both VMs.
These problems occur under both VMs, so the VM choice does not cause them:

- `gh10370_2`, `_3` and `_4` (`copy_file_range`) fail.
- `revalidate_path_01` is flaky, because `posix_spawn` sometimes fails with
  `ENOENT` when it starts the CLI server.
- `stack_limit_009` hangs, recursing in C through `zend_test`.
- With `-j12`, `run-tests.php` sometimes hangs at its last tests, leaving
  defunct workers.

## Upstream

The port is also in upstream Fil-C's Projeny format, on branch
[`php-8.4`](https://github.com/mbrock/fil-c/tree/php-8.4) of mbrock/fil-c
(`projects/php.projeny` and `build_php.sh`). It has the same allocator default. It is built against glibc only:
Fil-C's `ucontext`, which PHP fibers need, exists only in its glibc.
The 8.4.27 build and smoke test pass; its OPcache suite passes 868 tests
with the existing `gh9164` failure, which depends on shared opcache memory.
The last full core run, on 8.4.25, passed 15027 tests; `pcntl_unshare_02`
failed because the Fil-C runtime panics creating a thread after
`unshare(CLONE_NEWPID)`.

`ports/extract-projeny.py` imports it, like upstream's other `URL:`
descriptors:

```sh
nix develop -c ports/extract-patch.sh php.projeny ~/fil-c /tmp/review php-8.4
```
