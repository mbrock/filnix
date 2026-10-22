# Fil-C services on NixOS

`nixosModules.filc` ([nixos/filc.nix](../nixos/filc.nix)) swaps chosen NixOS
services and programs for their Fil-C builds and leaves the rest of the system
alone. systemd, glibc, the kernel and every other package stay the ordinary
NixOS builds, so memory-safe daemons run next to native ones.

```nix
{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";
  inputs.filnix.url = "github:mbrock/filnix/next";

  outputs = { nixpkgs, filnix, ... }: {
    nixosConfigurations.host = nixpkgs.lib.nixosSystem {
      system = "x86_64-linux";
      modules = [ filnix.nixosModules.filc ./configuration.nix ];
    };
  };
}
```

The Fil-C packages come from filnix's own pinned Nixpkgs (and its binary
cache); the rest of the system comes from yours.

In a configuration:

```nix
{
  imports = [ filnix.nixosModules.filc ];

  filc.enable = true;        # turns on every switch below
  filc.nix.enable = false;   # ...each can be turned off again
  filc.tools = [ "coreutils" "curl" "git" ];

  services.openssh.enable = true;   # now the Fil-C sshd
}
```

| Option | Effect |
| --- | --- |
| `filc.openssh.enable` | `services.openssh.package` |
| `filc.shell.enable` | Bash as the login shell of root and normal users |
| `filc.tor.enable` | `services.tor.package` |
| `filc.unbound.enable` | `services.unbound.package` |
| `filc.lighttpd.enable` | `services.lighttpd.package` |
| `filc.redis.enable` | `services.redis.package` |
| `filc.phpfpm.enable` | `services.phpfpm.phpPackage`, for pools without their own `phpPackage` |
| `filc.bind.enable` | `services.bind.package` |
| `filc.nix.enable` | `nix.package` (daemon and CLI), with the build sandbox off: Fil-C has no namespaces or seccomp |
| `filc.tools` | attributes of `filc.packages` on PATH, ahead of native programs of the same name |
| `filc.packages` | the package set replacements come from (default: this flake's `pkgsFilc`) |
| `filc.units` | (read-only) the running services the switches made Fil-C programs |

The switches only choose packages; enable the services as usual. A switch sets
the package at normal priority, so a configuration that also sets the package
itself gets a conflict rather than a silent choice. To add a service, give it
an entry in the `services` table of `nixos/filc.nix`: its package option and
the systemd units whose main process it becomes.

There is no nginx switch. nginx's processes share pointer-containing memory
(shared zones), which Fil-C capabilities don't survive, so the php-fpm test
runs Fil-C PHP-FPM behind native nginx. Use lighttpd for a Fil-C web server.

## Example machines

- `nixosConfigurations.filc-demo` ([nixos/demo.nix](../nixos/demo.nix)): a
  QEMU VM with the Fil-C sshd, Bash, Unbound, lighttpd, Nix and a set of tools.
  `filc-status` shows which programs are Fil-C builds.

  ```sh
  nix run .#nixosConfigurations.filc-demo.config.system.build.vm
  ssh -p 2222 demo@localhost        # password "demo"
  curl localhost:8080
  ```

- `nixosConfigurations.ec2-filc` ([nixos/ec2.nix](../nixos/ec2.nix)): the
  former `mbrock/ec2filc` repository, an Amazon image using the module plus
  Tor. Replace its SSH key first.

  ```sh
  nixos-rebuild switch --flake .#ec2-filc --target-host root@HOST
  nix build .#nixosConfigurations.ec2-filc.config.system.build.amazonImage
  ```

## VM tests

`nixosTests` ([tests/nixos](../tests/nixos/default.nix)) runs NixOS VM tests
with the module on every node: mostly Nixpkgs' own tests of each service
(openssh, lighttpd, php-fpm, unbound, tor, bind), unchanged, plus
`demo`, which boots the demo machine, logs in through the Fil-C sshd to the
Fil-C shell and has the Fil-C Nix build a derivation, and a Redis test.

After a test's own script passes, every unit in `filc.units` that is still
running must map the Fil-C runtime, so a test can't pass with a native build,
and the log ends with a table of which services were Fil-C builds:

```
Fil-C server       lighttpd         /nix/store/…-lighttpd-x86_64-unknown-linux-gnufilc0-1.4.85/bin/lighttpd
```

```sh
nix build .#nixosTests.lighttpd -L           # needs the kvm system feature
nix build .#nixosTests.lighttpd.driver       # or run the driver yourself:
mkdir out && ./result/bin/nixos-test-driver -o out
nix run .#nixosTests.lighttpd.driverInteractive   # Python REPL with the VMs
```

Without KVM, running the driver directly falls back to QEMU's emulation. It
works but is slow: the lighttpd test takes about five minutes in an orb.

A test builds only once all its Fil-C packages do.

To add a test, add Nixpkgs' test file (or a test module of our own) to the
list in `tests/nixos/default.nix`. When the Nixpkgs test chooses a variant of
the package, force the same variant of the Fil-C build on those nodes, as the
openssh and unbound entries do.

Use the binary cache to skip most of the build:

```ini
extra-substituters = https://filc.cachix.org
extra-trusted-public-keys = filc.cachix.org-1:8rA7kXyu1HaJuMTsAKfA9fU/+r8YtLv5KiZ5hfDNZMk=
```
