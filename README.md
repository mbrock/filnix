# filnix

A Nix flake that wraps [Fil-C](https://fil-c.org) as a Nix stdenv.

## What is this?

This flake packages Fil-C 0.673 for Nix and provides a custom stdenv (`filenv`) that replaces the standard C compiler with Fil-C. This means you can compile existing C/C++ software with memory safety guarantees using familiar Nix workflows.

## Quick Start

```bash
# Try building a simple package with Fil-C
nix build .#gnuawk
nix build .#sqlite # takes a while

# Try running a program that doesn't work for some reason
nix run .#bash

# Enter a shell with Fil-C clang
nix develop
```

## What's Included

- **filenv**: A custom stdenv using Fil-C instead of gcc/clang
- **withFilC**: Helper function to rebuild any nixpkgs package with Fil-C
- **filpkgs**: Experimental full nixpkgs with Fil-C as the default compiler
- **Pre-tested packages**: Several packages confirmed to build and work with Fil-C

## Confirmed Working Packages

These packages build successfully:

- `gawk`, `gnused`, `gnutar`, `bzip2` - Core Unix utilities
- `sqlite` - Database engine
- `ncurses`, `readline` - Terminal libraries

These packages build but have runtime issues:

- `bash` - Builds with 1-line alignment patch, but crashes with termios syscall error (tcgetwinsize). No idea why!
- `lua` - Same termios/syscall issue as bash

```
filc user error: src/termios/tcgetwinsize.c:7: int tcgetwinsize(int, struct winsize *): bad syscall: 16, fd, 0x5413, wsz
    <runtime>: zerror
    ../filc/src/snprintf.c:1336:2: zerrorf
    src/termios/tcgetwinsize.c:7:9: tcgetwinsize
    winsize.c:98:20: get_new_window_size
    jobs.c:2648:2: get_tty_state (inlined)
    jobs.c:4872:5: initialize_job_control
    shell.c:1969:3: shell_initialize (inlined)
    shell.c:580:3: main
    src/env/__libc_start_main.c:79:7: __libc_start_main
    <runtime>: start_program
[4117445] filc panic: user thwarted themselves.
Trace/breakpoint trap (core dumped)
```

If anyone knows how I can stop thwarting myself, don't hesitate to leave a comment.

## How It Works

The flake:

1. Downloads the official Fil-C 0.673 prebuilt binaries
2. Patches ELF executables with correct interpreter and rpath
3. Wraps Fil-C's clang in Nix's stdenv wrapper
4. Provides a drop-in replacement for nixpkgs' stdenv

## Status

This is an early experimental attempt. There are some problems!

- Linking issues with mixed Fil-C/non-Fil-C code
- Build system incompatibilities
- Runtime issues with certain syscalls

## Learn More

- [Fil-C Website](https://fil-c.org)
- [Fil-C Documentation](https://fil-c.org/documentation.html)

## License

MIT.
