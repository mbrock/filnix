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
| `filc.nix.enable` | `nix.package` (daemon and CLI), with the build sandbox off: Fil-C has no namespaces or seccomp |
| `filc.tools` | attributes of `filc.packages` on PATH, ahead of native programs of the same name |
| `filc.packages` | the package set replacements come from (default: this flake's `pkgsFilc`) |

The switches only choose packages; enable the services as usual. The same
pattern extends to any NixOS service with a `package` option: set it to the
attribute from `config.filc.packages`.

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

`checks.nixos-filc` ([tests/nixos-filc.nix](../tests/nixos-filc.nix)) boots the
demo machine, checks that the service processes map the Fil-C runtime, logs in
through the Fil-C sshd to the Fil-C shell, fetches a page from lighttpd, and has
the Fil-C Nix evaluate and build a derivation. It needs a builder with the `kvm`
system feature.

Use the binary cache to skip most of the build:

```ini
extra-substituters = https://filc.cachix.org
extra-trusted-public-keys = filc.cachix.org-1:8rA7kXyu1HaJuMTsAKfA9fU/+r8YtLv5KiZ5hfDNZMk=
```
