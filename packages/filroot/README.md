# A relocatable Fil-C root

[Fil-C](https://github.com/pizlonator/fil-c) is a memory-safe implementation
of C and C++. This directory holds the Fil-C compiler and runtime and a set of
programs and libraries compiled with it, built by
[Filnix](https://github.com/mbrock/filnix). It runs on x86-64 Linux whatever
its C library and needs nothing from Nix or from the host's libraries.

It works wherever it is unpacked, also read-only or at a path with spaces.
Use it through `bin/`:

    tar -xJf filroot-*.tar.xz
    export PATH=$PWD/filroot-0.686-filnix-x86_64-linux/bin:$PATH

Symlinks to programs in `bin/` work too. Copies and hard links do not.

## How it finds itself

Every program in `bin/` is a small launcher. It opens this directory as file
descriptor 987, which the program and its children inherit, and runs the
real program from `libexec/filroot/bin` with the same arguments. Inside the
root, paths are written as `/proc/self/fd/987/...`: the Fil-C loader and
libraries, script interpreters, glibc's character sets and locales,
OpenSSL's directory, terminfo, Python's and Perl's libraries. No environment
variables are set, so programs started from here see the host as usual.

A program in the root that closes all inherited descriptors and then needs
one of those paths cannot find it; `ssh`, for example, closes them at
startup. `/proc` must be mounted.

## Compiling

`filcc` and `fil++` compile C and C++ against the Fil-C glibc and libc++:

    filcc -O2 -o hello hello.c
    fil++ -O2 -o hello hello.cc
    filcc -o get get.c $(pkg-config --cflags --libs libcurl)

The programs they make load `/proc/self/fd/987/lib/ld-fil1-x86_64.so` and
libraries from `/proc/self/fd/987/lib`, so they run where descriptor 987 is
a Fil-C root:

    fil-run ./hello            # from any shell
    bash                       # or from a program of the root,
    ./hello                    # such as its bash or make

Run directly from a host shell, they fail as if the file did not exist.
They are not tied to this directory: they run with any root of the same
Fil-C version, wherever it is.

Out-of-bounds accesses, use-after-free and other memory errors stop them with
a Fil-C panic. Every library a program uses must be built with Fil-C too.
These are in `lib/`, with headers in `include/` and pkg-config files: zlib,
bzip2, xz, zstd, brotli, OpenSSL, curl, nghttp2, ngtcp2, nghttp3, libidn2,
libpsl, krb5, ncurses, readline, SQLite, libffi, Lua and Python.

The compiler, the linker and the assembler are ordinary programs, not Fil-C.

## Programs

`bin/` has bash, coreutils, grep, sed, gawk, find, diff, tar, gzip, xz,
zstd, bzip2, less, file, which, jq, make, m4, bison, flex, pkg-config, git,
curl, openssl, ssh, rsync, sqlite3, lua, python3, perl, nano and tmux, all
compiled with Fil-C. `s/` holds the rest of what they need.

## Certificates

OpenSSL, curl and git read the Mozilla root certificates in
`etc/ssl/cert.pem` and the host's hashed certificates through
`etc/ssl/certs`, a link to `/etc/ssl/certs`. Set `SSL_CERT_FILE` to use
another bundle.
