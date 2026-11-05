# A Fil-C finix

`finixModules.default` ([finix/default.nix](../finix/default.nix), around the
shared core [lib/filc-system.nix](../lib/filc-system.nix)) builds a
[finix](https://github.com/finix-community/finix) system's whole userland
with Fil-C. finix modules take their packages from `pkgs`, which is just
`config.nixpkgs.pkgs`; the module sets that to the Fil-C package set, so
finit, busybox, bash, coreutils, util-linux, OpenSSH, sudo, Linux-PAM, D-Bus,
dhcpcd, mdevd, sysklogd, Python, Perl, git and the rest become Fil-C builds
without a per-service override.

It is the same module as NixOS's `nixosModules.default`, with the same
options; [docs/nixos.md](nixos.md) describes them, the table of built-in
native exceptions (finix adds limine, sbctl, efibootmgr and userborn), how
Rust and Go are refused, and `filc-ps` and `filc-audit`.

```nix
finixConfigurations.host = finix.lib.finixSystem {
  inherit (nixpkgs) lib;
  modules = [
    filnix.finixModules.default
    {
      filc.enable = true;
      filc.system = "aarch64-linux";
      # Your own Nixpkgs: native packages come from its binary cache.
      filc.nativePackages = import nixpkgs { system = "aarch64-linux"; };
      filc.native = native: { inherit (native) tailscale; };
    }
    ./configuration.nix
  ];
};
```

## Example machine

[finix/demo.nix](../finix/demo.nix) is a small finix machine with this
userland: finit as
PID 1, mdevd, sysklogd, dhcpcd, OpenSSH, sudo, the Nix daemon (native, as
above), Bash and the usual tools. It boots the kernel directly in QEMU, with a
tmpfs root and the host's Nix store over 9p:

```sh
nix run .#finixConfigurations.filc-demo.config.system.build.vm
```

Log in as root on the serial console (no password), or
`ssh -p 2222 demo@localhost` with password `demo` once dhcpcd has its lease
from QEMU. Ctrl-a x quits QEMU. It needs KVM to be usable; the first boot of
a fresh store builds the whole Fil-C userland.

The flake pins finix (the `finix` input) to the last revision before it
required finit 5; filnix's Nixpkgs has finit 4.17.

Booting it found these, now fixed:

- Fil-C's glibc stopped the program in `nftw`, `scandirat` and `fts`, which
  finit (switch_root, tmpfiles), libmount, agetty and login use, and in
  `sbrk`, `sched_setattr` and `pidfd_spawn`
  ([filc-findings.md](filc-findings.md));
- finit's `clone3` call stopped PID 1; the port uses its fork fallback;
- finit's keventd wrote one byte past its uevent buffer, which Fil-C stopped
  during coldplug;
- dhcpcd's vendored rbtree kept its parent pointer in an integer; the
  upstream Fil-C port had not followed the file to `vendor/`;
- the busybox port had no applet links, so the initrd had no `sh`;
- libbsd, which ifupdown-ng (finix's test network) needs, did not build;
  its port is in [filc-findings.md](filc-findings.md).

## The check

`checks.x86_64-linux.finix-filc-demo` ([finix/test.nix](../finix/test.nix))
boots the same machine with finix's own VM test driver (its `tests/lib`, the
NixOS driver with finit support) and checks, from inside the machine:

- no finit service crashed, and dhcpcd, keventd, sshd and syslogd run;
- ifupdown-ng gave eth0 its test-network address;
- PID 1 (finit), the test shell and sshd map libpizlo, the Fil-C runtime;
- an ssh login as root gets a Bash that maps libpizlo;
- `filc-ps` finds no native process outside the exceptions (the native Nix
  daemon is the one there is);

and, from the host, with `filc-audit`, that every native ELF file in the
system closure belongs to an expected exception: the native Nix and its
closure, userborn, the static setuid wrappers, and the native Bash that
Fil-C's glibc names in the shebangs of its scripts (ldd and friends)
together with its glibc.

```sh
nix build -L .#checks.x86_64-linux.finix-filc-demo
```

The audit also finds packages built by the Fil-C stdenv that came out native.
filcc has no target prefix, so a build that runs plain `cc` or `gcc` can pick
up the build platform's compiler from `depsBuildBuild`. busybox did, until its
port named the compiler; any Fil-C-named package in the native list deserves a
look.

## Nixpkgs revisions

`filc.nativePackages` defaults to filnix's own Nixpkgs, imported natively. Not
`buildPackages`: its target platform is Fil-C, which matters for any package
that is itself a compiler (Emacs' native compilation pulled in a
Fil-C-targeted libgccjit that way). Not `pkgsBuildBuild` either: it carries
the Fil-C set's `replaceCrossStdenv`, so its `pkgsStatic`, which finix's
setuid wrappers use, built with filcc and failed to link. Passing your own
Nixpkgs, as above, keeps the kernel and the other native packages identical to
the rest of your machines.
