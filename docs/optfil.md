# /opt/fil without Nix

`nix build .#optfil` makes `optfil-0.686-filnix-x86_64-linux.tar.xz`, a
tarball of `/opt/fil` in the layout of upstream Fil-C's binary
distribution. It holds the Fil-C compiler, its runtime, glibc, libc++ and
headers, and memory-safe builds of common programs and libraries. It runs on
x86-64 Linux whatever the host's C library, without Nix:

    sudo tar -C /opt -xJf optfil-0.686-filnix-x86_64-linux.tar.xz
    export PATH=/opt/fil/bin:$PATH
    filcc -O2 -o hello hello.c && ./hello

The tree must be at `/opt/fil`. [packages/optfil/README.md](../packages/optfil/README.md)
is the user documentation shipped in the tarball.

## Upstream's /opt/fil

Upstream builds `/opt/fil` with `optfil/build_opt.sh` and ships it as
`fil.tar.xz` together with an installer, `setup.sh`, that extracts it to
`/opt` and can set up the Fil-C sshd. Its layout:

- `bin/filcc-clang-20` is the Fil-C Clang, linked against a renamed
  ("yolo") glibc and started by `lib/ld-fil1-x86_64.so`; `filcc`, `fil++`
  and `filcpp` link to it. When Clang's executable is in `/opt/fil/bin`,
  its driver uses `/opt/fil/include` and `/opt/fil/lib`, links with
  `/opt/fil/lib/ld-fil1-x86_64.so` as the interpreter, and runs `ld` and
  `sarcasm` from `/opt/fil/bin`.
- `lib` has the loader, the yolo glibc (`libyolocimpl.so`), `libpizlo.so`
  and the crt objects, the Fil-C glibc installed with `--prefix=/opt/fil`,
  and libc++.
- `include` has the kernel headers, the Fil-C (`stdfil`) headers, glibc's
  headers and libc++'s in `include/c++/v1`.
- Around 65 packages built with `filcc` and `--prefix=/opt/fil`: binutils,
  bash, zsh, coreutils, OpenSSL, OpenSSH, sudo, PAM, krb5, curl, wget, git,
  rsync, tmux, ICU, libxml2, libpq and others, about 1.3 GB.

Pizlix, in `pizlix/`, is the other packaging: a Linux From Scratch system in
which `/usr` is built with Fil-C. It is a whole OS image, not a directory to
add to a host.

## This tree

The Filnix tree has the same layout for the toolchain, so the driver's
`/opt/fil` mode does the work that the Nix compiler wrapper does with flags.
The rest is the Nix closure of the toolchain and the packages listed in
[packages/optfil/default.nix](../packages/optfil/default.nix):

| Path | Contents |
| --- | --- |
| `bin`, `lib`, `include`, `libexec`, `share`, `etc` | the toolchain and the listed packages, all outputs except documentation, merged |
| `lib/clang/20` | Clang's resource directory |
| `s/HASH-NAME` | every other store path of the closure |
| `etc/ssl/cert.pem` | Mozilla's root certificates; `etc/ssl/certs` links to the host's `/etc/ssl/certs` |

Programs from the listed packages are in `/opt/fil/bin`; the other programs
in the closure are still runnable from `/opt/fil/s`.

### How it is made

[mkprefix.py](../packages/optfil/mkprefix.py) copies the closure and then
rewrites every reference to a store path, in the bytes of every file:

- `/nix/store/HASH-NAME` of a path in `/opt/fil/s` becomes
  `/opt/fil/s/HASH-NAME`. `/opt/fil/s/` has as many characters as
  `/nix/store/`.
- A merged path, or one of the toolchain components whose files the merged
  toolchain provides (the Fil-C glibc, the yolo glibc, libpizlo, libc++,
  the kernel headers), becomes `/opt/fil` followed by as many slashes as it
  takes to keep the length, which names the same directory.

Because no length changes, this is safe in ELF files: the interpreters and
RUNPATHs of the programs point into `/opt/fil` without patchelf, and so do
compiled-in paths such as glibc's character set modules and locales, the
loader's default library directory, OpenSSL's directory, terminfo, shebangs
and pkg-config files. The merge keeps the first of two files at one path
and warns when they differ; with the current package list there are no
such conflicts. Files with the same bytes become hard links.

### Why a fixed prefix

A program's interpreter is an absolute path, so programs compiled with
`filcc` name the loader's location. A relocatable compiler would make
programs that break when the tree moves, or that differ from machine to
machine. A fixed `/opt/fil` makes compiled programs portable between machines
that have the tree, like upstream's.

[php-dist](php.md) is relocatable instead: it starts each program with a
small launcher that runs it through the bundled loader, and sets variables
for the paths that glibc and PHP otherwise take from `/nix`. That fits one
application, not a compiler whose output has to run on its own.

### What is not Fil-C

- Clang, binutils (`ld`, `as`, `nm`, ...), and the minilute interpreter that
  runs `sarcasm` are ordinary programs, and use the Nix glibc in
  `/opt/fil/s`. Upstream builds binutils with Fil-C.
- Some scripts of the Fil-C glibc (`ldd`, `tzselect`, `mtrace`, `xtrace`) and
  of ncurses and curl (`*-config`) name the Nix build platform's bash, and
  bison and flex run the build platform's m4. These come from the Fil-C
  packages and are in `/opt/fil/s` as well.

## Adding packages

Add the package to `packages` in `packages/optfil/default.nix`. Its
dependencies come along in `/opt/fil/s`. Look for `warning:` lines in the
build log of `.#optfil.tree`: two packages that install the same file, or
references that mkprefix.py could not map.

## Testing

[packages/optfil/test/run.sh](../packages/optfil/test/run.sh) unpacks the
tarball and runs [inside.sh](../packages/optfil/test/inside.sh) in podman
containers without Nix, as root and as an unprivileged user, with the tree
mounted read-only at `/opt/fil`:

    nix build .#optfil
    packages/optfil/test/run.sh result debian:12 debian:13 ubuntu:22.04 alpine:3

It compiles and runs C and C++ programs, shared libraries, programs that use
zlib, OpenSSL, iconv and locales, builds with `make` and `pkg-config`, checks
that an out-of-bounds write and a use-after-free stop with a Fil-C panic,
and runs the bundled programs. `OPTFIL_TEST_NET=1` adds HTTPS fetches with
curl and git.
