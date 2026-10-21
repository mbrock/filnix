# PHP built with Fil-C

PHP 8.4 compiled with [Fil-C](https://github.com/pizlonator/fil-c), a
memory-safe implementation of C. It covers PHP and every library it uses:
out-of-bounds accesses, use-after-free and other memory errors stop the
process with a Fil-C panic instead of corrupting memory.

This directory is self-contained and relocatable. It carries its own C
runtime and libraries, so it runs on x86-64 Linux whatever its C library
(tested on Debian 12 and 13, Ubuntu 22.04 and Alpine 3.24) and needs nothing
from Nix. Put it anywhere and run the programs in `bin/`:

    bin/php -v
    bin/php -S 127.0.0.1:8000 -t public/
    bin/php-fpm --nodaemonize          # listens on 127.0.0.1:9000
    bin/php-cgi
    bin/phpdbg

Symlinks to these programs work too, for example
`ln -s $PWD/bin/php /usr/local/bin/php`.

## Configuration

- `etc/php.ini` is PHP's production configuration. `PHPRC` overrides it.
- `etc/php.d/extensions.ini` loads the extensions; remove lines to disable
  them. `PHP_INI_SCAN_DIR` overrides the directory.
- `etc/php-fpm.conf` and `etc/php-fpm.d/www.conf` configure FPM. Paths in
  them are relative to this directory unless `php-fpm --prefix DIR` is given;
  `var/` must be writable for the default pid and log files.
- TLS uses the host's CA certificates when it finds them and
  `etc/ssl/cert.pem` otherwise. Set `SSL_CERT_FILE` to choose.
  `etc/ssl/openssl.cnf` is the OpenSSL configuration (`OPENSSL_CONF`).

The programs in `bin/` set these variables when they are unset and start
the real programs in `libexec/` with the bundled loader in `lib/`. The
bundled glibc reads `FILC_GCONV` and `FILCLOC` where glibc normally reads
`GCONV_PATH` and `LOCPATH`, so that host programs started from PHP keep
using their own character sets and locales.

## Differences from other PHP builds

- No JIT: Fil-C cannot run generated machine code, so the opcache JIT and
  PCRE's JIT are disabled. Opcache itself works.
- Each FPM worker has a private opcache. Workers share what the master
  cached before forking; `opcache_reset()` affects only the calling worker.
- Code runs 1.5 to 4 times slower than ordinary PHP and uses more memory.
- Only the C and C.UTF-8 locales are available.
- Native code loaded at run time must be built with Fil-C too, so `dl()`
  and PECL extensions from elsewhere do not work.
