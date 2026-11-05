# Fil-C NixOS and finix

filnix's product is a whole system whose `pkgs` is the Fil-C package set.
NixOS and finix modules take their programs from `pkgs`, so systemd or finit,
PAM, D-Bus, OpenSSH, the shell and every service you enable are memory-safe
Fil-C builds without being named anywhere. The kernel, the bootloader and a
short list of exceptions stay native, and you can add your own.

One module does it for both operating systems: `nixosModules.default` and
`finixModules.default` are thin wrappers ([nixos/default.nix](../nixos/default.nix),
[finix/default.nix](../finix/default.nix)) around one core,
[lib/filc-system.nix](../lib/filc-system.nix).

## Using it

```nix
{
  inputs.filnix.url = "github:mbrock/filnix";

  outputs = { filnix, ... }: {
    nixosConfigurations.host = filnix.lib.nixosSystem {
      modules = [
        {
          # Packages to keep native, picked from the native package set.
          filc.native = native: { inherit (native) tailscale ripgrep; };
        }
        ./configuration.nix
      ];
    };
  };
}
```

`filnix.lib.nixosSystem` is Nixpkgs' `nixosSystem` with the module imported
and `filc.enable = true`, using the NixOS modules of filnix's pinned Nixpkgs.
The Fil-C packages are built and tested against that pin (systemd's port
above all), so take the modules from it too. To use the module in another
evaluation, import `filnix.nixosModules.default` and set `filc.enable`.

Add the binary cache, or the first build compiles the Fil-C world:

```ini
extra-substituters = https://filc.cachix.org
extra-trusted-public-keys = filc.cachix.org-1:8rA7kXyu1HaJuMTsAKfA9fU/+r8YtLv5KiZ5hfDNZMk=
```

| Option | Meaning |
| --- | --- |
| `filc.enable` | `pkgs` becomes the Fil-C package set |
| `filc.system` | `x86_64-linux` (default) or `aarch64-linux` |
| `filc.native` | a function from the native package set to the packages to keep native, such as `native: { inherit (native) tailscale; }`; a name the native set lacks fails evaluation |
| `filc.nativePackages` | the native package set; default filnix's Nixpkgs, imported natively. Your own Nixpkgs works too, with its cache hits |
| `filc.nativeNix` | whether Nix is the native build (default `true`); the Fil-C Nix cannot sandbox builds |
| `filc.packages` | the resulting package set, which is also `pkgs` (read only) |

There are no per-service or per-tool switches. If a service needs a fix to
work as Fil-C, the fix goes in its port, where every system gets it.

## What stays native

A process is either all Fil-C or all native: a Fil-C program can't load a
native library, and a native program can't load a Fil-C one. So every
exception is a whole package, taken from native Nixpkgs. These are built in,
from [lib/native-exceptions.nix](../lib/native-exceptions.nix):

<!-- native-exceptions -->
| Package | NixOS | finix | Why |
| --- | --- | --- | --- |
| `glibc` | ✓ | ✓ | Only the setuid wrappers use it, for a header from its source. Fil-C programs get their libc from the Fil-C sysroot. |
| `linuxKernel` | ✓ | ✓ | Fil-C cannot build the kernel. |
| `linuxPackages` | ✓ | ✓ | The kernel and its modules. |
| `linuxPackages_latest` | ✓ | ✓ | The kernel and its modules. |
| `nix` | ✓ | ✓ | Unless `filc.nativeNix = false`. The Fil-C Nix works but cannot sandbox builds: Fil-C has no namespaces or seccomp. |
| `pkgsStatic` | ✓ | ✓ | The setuid wrappers are small static programs. Fil-C does not link statically, and a static set derived from the Fil-C one recurses. |
| `fish` | ✓ |  | Rust (fish 4). users-groups.nix compares every user's shell with `pkgs.fish`, so it must evaluate; a user who picks fish gets the native one. |
| `grub2` | ✓ |  | The bootloader runs before any userland, and its package holds the boot images as well as the tools that install them. |
| `kexec-tools` | ✓ |  | kexec loads a kernel together with its purgatory, freestanding code that runs between the two kernels. |
| `makeInitrdNGTool` | ✓ |  | Rust: builds the initrd, and generate-shutdown-ramfs runs it on the machine. |
| `nixos-init` | ✓ |  | Rust: the initrd's initrd-find-nixos-closure and, with `system.nixos-init`, stage 2's init and activation. |
| `switch-to-configuration-ng` | ✓ |  | Rust: switch-to-configuration, which talks to systemd over D-Bus. |
| `efibootmgr` |  | ✓ | limine's install hook uses it to manage EFI boot entries. |
| `limine` |  | ✓ | The bootloader runs before any userland. |
| `sbctl` |  | ✓ | Go; limine's install hook uses it for secure boot. |
| `userborn` |  | ✓ | Rust; finix creates users and groups with it during activation. |
<!-- /native-exceptions -->

The table is generated; `checks.x86_64-linux.native-exceptions-table` fails
when it and the data differ. The module asserts that every built-in name
exists in the native set, so a rename in Nixpkgs fails evaluation instead of
silently building the Fil-C package.

Rust and Go cannot slip in unnoticed. The package set refuses them at
evaluation time ([lib/block-rust-go.nix](../lib/block-rust-go.nix)), and the
error says how to keep one native:

```
error: Refusing to evaluate package 'ripgrep-15.1.0' … because it has problems:
- filc (kind "broken"): Rust has no Fil-C target. Take the native build instead, with filc.native = native: { inherit (native) ripgrep; }; in your system's configuration, or leave it out.
```

The adapter only touches `meta`, so derivations hash the same as in plain
`pkgsFilc`. Haskell (cachix, pandoc) and Zig (ghostty) are not detected;
name them in `filc.native` too.

## What is Fil-C here?

`filc-ps`, installed by the module, checks the negative: every running
process must map libpizlo, the Fil-C runtime, unless its program is in the
closure of an allowed native exception (or is a setuid wrapper). It prints
each process and exits 1 if any other native process runs. Run it as root:
other users' memory maps are unreadable otherwise, and it exits 2.

```
$ sudo filc-ps
Fil-C         1  /nix/store/…-systemd-x86_64-unknown-linux-gnufilc0-260.4/lib/systemd/systemd
Fil-C      1215  /nix/store/…-systemd-x86_64-unknown-linux-gnufilc0-260.4/lib/systemd/systemd-journald
Fil-C      2808  /nix/store/…-dbus-x86_64-unknown-linux-gnufilc0-1.16.2/bin/dbus-daemon
Fil-C      4063  /nix/store/…-openssh-x86_64-unknown-linux-gnufilc0-10.5p1/bin/sshd
native     4204  /nix/store/…-nix-2.34.8/bin/nix
15 Fil-C, 1 allowed native, 0 not allowed, 0 unreadable
```

`filc-audit` ([lib/filc-audit.sh](../lib/filc-audit.sh), also
`packages.<system>.filc-audit`) looks at files instead of processes: it
classifies every ELF file in a closure by its program headers and dynamic
section. A Fil-C executable names the Fil-C loader (`ld-fil1-*.so`) as its
interpreter, and a Fil-C executable or library needs `libpizlo.so`. That is
what the loader acts on, so a native program that merely contains those names
is not counted as Fil-C. The runtime underneath (libpizlo, the loader and its
yolo glibc) is counted apart, as are kernel modules.

```sh
nix run .#filc-audit -- /run/current-system
nix run .#filc-audit -- --paths store-paths --allow expected-native-paths
```

With `--allow`, native files outside the listed store paths are marked
`UNEXPECTED` and the exit status is 1. The audit also catches packages built
by the Fil-C stdenv that came out native: filcc has no target prefix, so a
build that runs plain `cc` can pick up the build platform's compiler.

## What you give up

| Where | Cost | Why |
| --- | --- | --- |
| everywhere | CPU time is 1.5× to 4× that of the native build, and memory use is higher | bounds checks and the garbage collector |
| memory | give a machine at least 2 GiB (t3.small or larger on EC2) | the Fil-C userland with systemd needs it |
| Rust and Go | no Fil-C build; keep them native with `filc.native` | Fil-C compiles C and C++ |
| Nix | the default native Nix sandboxes builds; the Fil-C one cannot | Fil-C has no namespaces or seccomp |
| NSS | names resolve from `/etc` files only: no nscd, nss-systemd or myhostname, so DynamicUser names show as numbers, and activation prints a harmless nscd error | the Fil-C glibc has no nscd, and nsncd is Rust |
| D-Bus | dbus-daemon instead of dbus-broker | dbus-broker's port is not done |
| QEMU guest agent | none | the full QEMU does not build with Fil-C yet |
| PHP-FPM | each worker grows to about 150-250 MB | the garbage collector keeps more memory alive |
| nginx | no Fil-C build; use lighttpd | nginx's processes share pointers through shared memory, which capabilities don't survive |
| updates | packages follow filnix's Nixpkgs pin, not your channel | they are built and cached against that pin |

[docs/nixos-userland.md](nixos-userland.md) is the running record of what it
took to get here and of what is still open.

## One Fil-C daemon on a stock NixOS

The module makes the whole system Fil-C; there is no module support for
mixing. A single service's package option can still point at a Fil-C build:

```nix
services.tor.package = filnix.legacyPackages.x86_64-linux.pkgsFilc.tor;
```

That works for daemons that load no plugins from the rest of the system. A
Fil-C program can't load the native system's PAM or NSS modules, so this is
not for sshd, login or anything that authenticates users through PAM, and
user and host lookups see `/etc` files only. Nothing checks it for you.

## finix

[finix](finix.md) is the same module on a smaller, systemd-free distribution:
finit as PID 1, and the same option names.

## VM tests

`nixosTests.userland` ([tests/nixos/userland.nix](../tests/nixos/userland.nix))
boots a whole Fil-C NixOS, logs in on the console through the Fil-C PAM,
checks that PID 1, journald, udevd, logind, D-Bus, sshd and the login shell map
libpizlo, and runs `filc-ps`, which must pass and must fail once a native
program outside the exceptions runs.

`nixosTests` ([tests/nixos](../tests/nixos/default.nix)) also runs Nixpkgs'
own tests of services with the module on every node, then `filc-ps` on every
machine still up, so a test passes only when no native process outside the
exceptions ran.

```sh
nix build .#nixosTests.userland -L          # needs the kvm system feature
nix build .#nixosTests.lighttpd.driver       # or run the driver yourself:
mkdir out && ./result/bin/nixos-test-driver -o out
```

Without KVM, the driver falls back to QEMU's emulation, which works but is
slow.
