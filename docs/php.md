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
ported and how they are tested. PHP 7.4, which no longer gets regular
security fixes, builds too; see [PHP 7.4](#php-74).

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
- No JIT. Fil-C cannot run generated machine code, so opcache's JIT and
  PCRE's JIT are off.
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

## PHP 8.5 investigation

[PHP 8.5.12](https://www.php.net/releases/8_5_12.php) is the current 8.5
security release (21 October 2026), but is not yet a supported Fil-C port.
The inherited `pkgsFilc.php85` definition does not include the 8.4 port's
patches; its presence is not a support claim.

Source-level checks found that the core, allocator, shmop and OPcache
patches apply to 8.5.12. The Lexbor patches apply after changing their paths
from `ext/dom/lexbor/lexbor` to `ext/lexbor/lexbor`. Both Lexbor and OPcache
are now built into PHP itself, so their patches and `--disable-opcache-jit`
must move into the core derivation rather than shared-extension overrides.
The module ABI changes from 20240924 to 20250925; PECL extensions need a
fresh compatibility/build/test pass. These patch checks are not a build or
runtime verification. Add 8.5 as a separate opt-in port before considering
a change to the default; this update keeps `php` on 8.4.

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
