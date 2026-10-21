# Fil-C in /opt/fil

[Fil-C](https://github.com/pizlonator/fil-c) is a memory-safe implementation
of C and C++. This directory holds the Fil-C compiler and runtime and a set of
programs and libraries compiled with it, built by
[Filnix](https://github.com/mbrock/filnix) in the layout of upstream's
`/opt/fil` distribution. It runs on x86-64 Linux whatever its C library and
needs nothing from Nix or from the host's libraries.

It must be installed at `/opt/fil`, where the programs find their libraries
and files:

    sudo tar -C /opt -xJf optfil-*.tar.xz
    export PATH=/opt/fil/bin:$PATH

## Compiling

`filcc` and `fil++` compile C and C++ against the Fil-C glibc and libc++ in
`/opt/fil/lib` and `/opt/fil/include`:

    filcc -O2 -o hello hello.c
    fil++ -O2 -o hello hello.cc
    filcc -o get get.c $(pkg-config --cflags --libs libcurl)

The programs they make load `/opt/fil/lib/ld-fil1-x86_64.so` and the
libraries in `/opt/fil/lib`. Out-of-bounds accesses, use-after-free and other
memory errors stop them with a Fil-C panic. Every library a program uses must
be built with Fil-C too. These are in `/opt/fil/lib`, with headers and
pkg-config files: zlib, bzip2, xz, zstd, brotli, OpenSSL, curl, nghttp2,
ngtcp2, nghttp3, libidn2, libpsl, krb5, ncurses, readline, SQLite, libffi,
Lua and Python.

The compiler, the linker and the assembler are ordinary programs, not Fil-C.

## Programs

`/opt/fil/bin` has bash, coreutils, grep, sed, gawk, find, diff, tar, gzip,
xz, zstd, bzip2, less, file, which, jq, make, m4, bison, flex, pkg-config,
git, curl, openssl, ssh, rsync, sqlite3, lua, python3, perl, nano and tmux,
all compiled with Fil-C.

`/opt/fil/s` holds the rest of what these need, under the Nix store names
they were built with.

## Certificates

OpenSSL, curl and git read the Mozilla root certificates in
`/opt/fil/etc/ssl/cert.pem` and the host's hashed certificates through
`/opt/fil/etc/ssl/certs`, a link to `/etc/ssl/certs`. Set `SSL_CERT_FILE` to
use another bundle, for example
`/etc/pki/tls/certs/ca-bundle.crt` on Fedora.
