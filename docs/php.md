# PHP on Fil-C

PHP 8.4 builds with Fil-C, along with its bundled extensions and the common
PECL ones. A memory error anywhere in PHP or a library it loads stops the
process with a Fil-C panic instead of corrupting memory. There are three ways
to get it:

```sh
nix build .#pkgsFilc.php     # the Nix package, with Nixpkgs' default extensions
nix build .#php-dist         # php-8.4.25-filc-x86_64-linux.tar.xz, runs without Nix
nix build .#php-docker       # an OCI image of the same tree
```

`pkgsFilc.php.withExtensions` and `pkgsFilc.php.buildEnv` work as in
Nixpkgs; see [php-extensions.md](php-extensions.md) for which extensions are
ported and how they are tested. PHP 7.4, which no longer gets security
fixes, builds too; see [PHP 7.4](#php-74).

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
docker pull ghcr.io/mbrock/filnix-php:8.4.25    # or :latest
```

The same CI run keeps the tarball as a workflow artifact; see
[binary-caches.md](binary-caches.md#continuous-integration). With Nix:

```sh
nix build .#php-docker && docker load < result
docker run --rm -it filnix-php:8.4.25                       # php -a
docker run --rm -p 8000:8000 -v $PWD:/var/www/html \
  filnix-php:8.4.25 php -S 0.0.0.0:8000                     # built-in server
docker run --rm -p 9000:9000 -v $PWD:/var/www/html \
  filnix-php:8.4.25 php-fpm                                 # FastCGI on 9000
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

The Nix build runs PHP's test suite. Every bundled extension's suite passes
(pcntl skips a CPU-pinning test), and the core run passes 13084 of 13087; the
failures are ZipArchive encryption, since Nixpkgs builds libzip without it.
`USE_ZEND_ALLOC=0` runs, which give each PHP value its own bounds, are
described in [php-extensions.md](php-extensions.md).

Not yet ported: memprof, enchant and swoole.

## PHP 7.4

PHP 7.4 reached its end of life in November 2022 and gets no security
fixes; the fixes for current PHP CVEs exist only for PHP 8. Fil-C does not
fix those bugs, but it stops the memory-corruption ones from being
exploited: an out-of-bounds access or use after free in PHP 7.4 or a
library it loads panics instead of handing an attacker memory. For example,
the `var_destroy` use after free in `unserialize()` (see
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

## Upstream

The port is also in upstream Fil-C's Projeny format, on branch
[`php-8.4`](https://github.com/mbrock/fil-c/tree/php-8.4) of mbrock/fil-c
(`projects/php.projeny` and `build_php.sh`). It has the same allocator default. It is built against glibc only:
Fil-C's `ucontext`, which PHP fibers need, exists only in its glibc. That
build passes 15027 core tests of about 16000. It fails `pcntl_unshare_01`
and `02`, because the Fil-C runtime panics creating a thread after
`unshare(CLONE_NEWPID)`, and opcache's `gh9164`, which depends on shared
opcache memory.

`ports/extract-projeny.py` imports it, like upstream's other `URL:`
descriptors:

```sh
nix develop -c ports/extract-patch.sh php.projeny ~/fil-c /tmp/review php-8.4
```
