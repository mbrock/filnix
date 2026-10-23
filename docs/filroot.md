# A relocatable Fil-C root

`nix build .#filroot` makes `filroot-0.687-filnix-x86_64-linux.tar.xz`, the
toolchain and programs of [optfil](optfil.md) in a directory that works
wherever it is unpacked: at any path, including one with spaces, and
read-only. It needs nothing from Nix or from the host's libraries:

    tar -xJf filroot-0.687-filnix-x86_64-linux.tar.xz
    export PATH=$PWD/filroot-0.687-filnix-x86_64-linux/bin:$PATH
    filcc -O2 -o hello hello.c && fil-run ./hello

[packages/filroot/README.md](../packages/filroot/README.md) is the user
documentation shipped in the tarball.

## Descriptor 987

A relocatable tree has to resolve its own paths without knowing where it
is. ELF interpreters must be absolute paths, and so are most of the paths
compiled into the programs and libraries: glibc's character set modules and
locales, the loader's library directories, OpenSSL's directory, terminfo,
Python's prefix, Perl's `@INC`, shebangs, pkg-config files.

The root writes all of them as `/proc/self/fd/987/...`, and arranges for
descriptor 987 to be the root's directory in every process that needs it:

- [mkprefix.py](../packages/optfil/mkprefix.py), which also builds optfil,
  rewrites the store paths in place with the prefix `/proc/self/fd/987`.
  Merged packages become `/proc/self/fd/987` padded with slashes, the rest
  of the closure `/proc/self/fd/987/s/HASH-NAME` with the hash shortened by
  nine characters to keep the length. Symlinks into the store become
  relative links (`--relative-links`).
- [launchers.py](../packages/filroot/launchers.py) moves every ELF program
  with an interpreter and every script in `bin/` and `sbin/` to
  `libexec/filroot/bin` (or `sbin`) and puts a hard link to one static
  launcher, [launcher.c](../packages/filroot/launcher.c), in its place.
  Links between entries of `bin/` stay links.
- The launcher finds the root from `/proc/self/exe` (`ROOT/bin/NAME`),
  opens it with `O_PATH`, moves it to descriptor 987 without close-on-exec,
  and execs `ROOT/libexec/filroot/bin/NAME` with the same `argv`, `argv[0]`
  included. `bin/fil-run PROGRAM ARGS...` runs any program that way.

The kernel resolves an interpreter or a `#!` line in the process that calls
`execve`, so a program started by a program of the root finds its loader
through the inherited descriptor. Within the process, the loader, libc and
the rest open their files through it. Host programs started from the root
inherit the descriptor and nothing else; no environment variables are set,
so unlike [php-dist](php.md) the root needs no renamed variables in glibc
and does not leak settings into host programs.

The costs:

- A program that closes inherited descriptors and later opens a path of
  the root fails to find it. OpenSSH's `ssh` and `sshd` call `closefrom` at
  startup. Programs that start others usually do it after `fork`, which
  does not matter when the child is a launcher in `bin/`.
- `/proc` must be mounted, and descriptor 987 must fit under the descriptor
  limit; the launcher raises the soft limit when the hard limit allows.
- Compiled-in paths look like `/proc/self/fd/987//////libexec/git-core`,
  for example in `git --exec-path`.
- `/proc/self/exe` of a real program is in `libexec/filroot/bin`, not in
  `bin/`.

## The compiler

`bin/filcc`, `bin/fil++` and `bin/filcpp` are links to `bin/clang-20`, a
launcher for `libexec/filroot/bin/clang-20`. Clang computes its directory
from `/proc/self/exe`, so it reads `clang.cfg` (`clang++.cfg`,
`clang-cpp.cfg`) from `libexec/filroot/bin` and finds its resource
directory and libc++'s headers through the links `libexec/filroot/lib` and
`libexec/filroot/include`. The configuration puts the driver into its
`pizfix` mode with these options:

    --filc-resource-dir=<CFGDIR>/..
    --filc-stdfil-include=<CFGDIR>/../include
    --filc-os-include=<CFGDIR>/../include
    --filc-include=<CFGDIR>/../include
    --filc-crt-path=/proc/self/fd/987/lib
    --filc-dynamic-linker=/proc/self/fd/987/lib/ld-fil1-x86_64.so

Headers come from the root's real path, so diagnostics and dependency files
name real files. Linking uses the crt files and libraries through the
descriptor, which the compiler has because it was started by a launcher, and
records `/proc/self/fd/987/lib` as the interpreter's directory and the
RUNPATH. `ld`, `as` and `sarcasm` are found next to Clang.

### What compiled programs need

A program built with the root's `filcc` has the interpreter
`/proc/self/fd/987/lib/ld-fil1-x86_64.so` and the RUNPATH
`/proc/self/fd/987/lib`, like the programs in the root. It runs in any
process where descriptor 987 is a Fil-C root of the same version:

- started by a program of the root, such as its `bash`, `make` or
  `python3`;
- through `ROOT/bin/fil-run ./program` from anywhere else.

Started from a host shell, `execve` fails with `ENOENT`. Nothing ties a
compiled program to the directory that built it, so it runs with the root
moved, or with another copy of it. The alternative, recording the root's
absolute path as the interpreter, would let programs start directly, but
they would break when the root moves, and glibc's data paths in the root
would still need the descriptor.

## Testing

[packages/filroot/test/run.sh](../packages/filroot/test/run.sh) unpacks the
tarball and runs [inside.sh](../packages/filroot/test/inside.sh) in podman
containers without Nix, as root and as an unprivileged user. The tree is
mounted read-only at `/srv/my fil root/filroot-...` and again at
`/elsewhere`:

    nix build .#filroot
    packages/filroot/test/run.sh result debian:12 debian:13 ubuntu:22.04 alpine:3

It runs optfil's checks through `fil-run` and also checks that compiled
programs run from the root's `bash` and `make` and with the root at the
other path, that they do not start without the descriptor, that programs
work with an empty environment, and that Python, Perl, git and scripts in
`bin/` find their files. `FILROOT_TEST_NET=1` adds HTTPS fetches with curl
and git.
