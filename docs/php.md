# PHP on Fil-C

PHP 8.4 builds with Fil-C, along with its bundled extensions and the common
PECL ones. A memory error anywhere in PHP or a library it loads stops the
process with a Fil-C panic instead of corrupting memory. There are three ways
to get it:

```sh
nix build .#pkgsFilc.php     # the Nix package, with Nixpkgs' default extensions
nix build .#php-dist         # php-8.4.27-filc-x86_64-linux.tar.xz, runs without Nix
nix build .#php-docker       # an OCI image of the same tree
```

`pkgsFilc.php` follows PHP's 8.4 releases, now 8.4.27, which fixes
CVE-2026-109618 and CVE-2026-109619. `pkgsFilc.php84_25` keeps the
vulnerable 8.4.25 with the same Fil-C patches, for reproducing those bugs
and comparing them with their fixes (see
[Vulnerable PHP under Fil-C](#vulnerable-php-under-fil-c)). It is marked
insecure, so Nix refuses it unless asked:

```sh
NIXPKGS_ALLOW_INSECURE=1 nix build --impure .#pkgsFilc.php84_25
```

`pkgsFilc.php.withExtensions` and `pkgsFilc.php.buildEnv` work as in
Nixpkgs; see [php-extensions.md](php-extensions.md) for which extensions are
ported and how they are tested. PHP 8.5 is an opt-in package,
`pkgsFilc.php85`; see [PHP 8.5](#php-85). PHP 7.4, which no longer gets
regular security fixes, builds too; see [PHP 7.4](#php-74).

## The tarball

`php-dist` is a relocatable directory with `php`, `php-fpm`, `php-cgi` and
`phpdbg`, its own glibc, libc++ and Fil-C runtime, and every library its
extensions load. Unpack it anywhere on x86-64 Linux; it needs nothing from
Nix or the host's C library. Its [README](../packages/php-dist/README.md) is
the user documentation and ships inside the tarball.

It loads Nixpkgs' default extensions plus apcu, ast, bz2, decimal, ds,
event, igbinary, imagick, mailparse, maxminddb, memcached, mongodb, msgpack,
protobuf, redis, shmop, sysvmsg, sysvshm, tidy, uuid, xsl, yaml and zstd
(`packages/php-dist/default.nix`). Imagick brings ImageMagick with its
image libraries: libjpeg-turbo, libtiff, libpng, libwebp, OpenJPEG, OpenEXR,
LibRaw and lcms2, all built with Fil-C. Debuggers and profilers (xdebug,
pcov, spx) are ported but not loaded, since they slow every request.
The CA bundle is the Fil-C package set's `cacert`.

`packages/php-dist/test/run.sh TARBALL IMAGE...` unpacks it in containers
without `/nix` and checks the extensions, the built-in server and FPM with
opcache, as root and unprivileged. It passes on `debian:12`, `debian:13`,
`ubuntu:22.04` and `alpine:3`.

## The container image

Without Nix, pull it from the GitHub container registry, where CI publishes
each cached revision of `main`:

```sh
docker pull ghcr.io/mbrock/filnix-php:8.4.27    # or :latest
```

The same CI run keeps the tarball as a workflow artifact; see
[binary-caches.md](binary-caches.md#continuous-integration). With Nix:

```sh
nix build .#php-docker && docker load < result
docker run --rm -it filnix-php:8.4.27                       # php -a
docker run --rm -p 8000:8000 -v $PWD:/var/www/html \
  filnix-php:8.4.27 php -S 0.0.0.0:8000                     # built-in server
docker run --rm -p 9000:9000 -v $PWD:/var/www/html \
  filnix-php:8.4.27 php-fpm                                 # FastCGI on 9000
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
- No JIT by default. Fil-C cannot run generated machine code, so opcache's
  native JIT and PCRE's JIT are off. An experimental build compiles
  opcache's JIT through C instead; see [Opcache JIT through C](#opcache-jit-through-c).
- Opcache maps its shared memory privately, because capabilities do not
  cross processes. Each FPM worker therefore has its own cache. Workers share
  what the master compiled before forking, and `opcache_reset()` affects only
  the worker that calls it.
- PHP runs 1.5 to 4 times slower than an ordinary build and uses more memory.
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
  back to the interpreter.
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
and a small script with it on.

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

- These are PHP's regression tests, not exploits. Exploiting
  CVE-2026-109619 across requests takes heap grooming to reach a dangling
  reference. We showed the corrupted state it starts from (on 8.4.25,
  `rfc1867_no_user_code.phpt` runs user code from the upload-progress
  handler before the request has started) but not a groomed dereference.
- The startup OOM route to CVE-2026-109618 needs mod_php or FrankenPHP,
  which have no Fil-C build. It was not tested.
- A trap is still a crash, and an attacker who can trigger one at will can
  take workers down. Logic bugs in the same code are unaffected.

So run patched releases. `php84_25` is marked insecure for that reason
and exists only to reproduce the bugs and compare them with their fixes.

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
fixes CVE-2026-109618 and CVE-2026-109619. It is opt-in: `pkgsFilc.php`
stays on 8.4, and `php-dist` and `php-docker` are 8.4 builds.

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
