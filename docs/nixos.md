# Fil-C on NixOS

filnix's NixOS support is a small, curated flavor of NixOS. The services you
choose run as Fil-C builds: memory-safe programs from the same Nixpkgs sources
and NixOS modules, checked by Nixpkgs' own VM tests. Everything else stays
ordinary NixOS. `nixosModules.filc` ([nixos/filc.nix](../nixos/filc.nix))
makes the swap, and [finix](finix.md) carries it further, to the whole
userland.

## How far to go

A process is either all Fil-C or all native: a Fil-C program can't load a
native library, and a native program can't load a Fil-C one. So the unit of
choice is a whole program, and a system moves along this scale one program
at a time:

| Step | What is Fil-C | How | Example |
| --- | --- | --- | --- |
| 0. Native | nothing | plain NixOS | |
| 1. Some services | the daemons you choose | `filc.openssh.enable` and the other switches, or any service's package option set to `config.filc.packages.X` | `ec2-filc`: sshd and Tor |
| 2. Services, shell and tools | also the login shell, Nix and the programs on PATH | `filc.enable = true`, `filc.tools = [ … ]` | `filc-demo` |
| 3. Whole userland | everything except the kernel, the bootloader and a short exception list | `nixosModules.filc-userland` on NixOS, or [finix](finix.md)'s `finixModules.filc-userland`; `filc.userland.native` names the exceptions | |

Steps 1 and 2 add Fil-C programs to an otherwise native NixOS: `pkgs`
stays your Nixpkgs, and the options name what becomes Fil-C. At step 3 the
whole of `pkgs` is Fil-C and the options name the exceptions instead.

On NixOS, `nixosModules.filc-userland` (`filc.userland.enable = true`,
[nixos/userland.nix](../nixos/userland.nix)) makes the system's `pkgs` the
Fil-C package set. systemd 260 (PID 1, journald, udevd, logind), D-Bus,
util-linux, Linux-PAM, coreutils, OpenSSH and every service a module starts
are then Fil-C builds, including the initrd's userland. Only the kernel, GRUB,
kexec-tools, the static setuid wrappers, Nix and NixOS 26.05's Rust boot tools
(nixos-init, the initrd builder, switch-to-configuration, fish) stay native,
and [docs/nixos-userland.md](nixos-userland.md) says why for each. The VM test
`nixosTests.userland` logs in on the console and checks that PID 1 and the
main services map libpizlo. Open gaps: no NSS modules or nscd, dbus-daemon
instead of dbus-broker, and no QEMU guest agent.

## Using it

```nix
{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";
  inputs.filnix.url = "github:mbrock/filnix";

  outputs = { nixpkgs, filnix, ... }: {
    nixosConfigurations.host = nixpkgs.lib.nixosSystem {
      system = "x86_64-linux";
      modules = [ filnix.nixosModules.filc ./configuration.nix ];
    };
  };
}
```

The Fil-C packages come from filnix's own pinned Nixpkgs; the rest of the
system comes from yours. Add the binary cache to skip most of the build:

```ini
extra-substituters = https://filc.cachix.org
extra-trusted-public-keys = filc.cachix.org-1:8rA7kXyu1HaJuMTsAKfA9fU/+r8YtLv5KiZ5hfDNZMk=
```

In a configuration:

```nix
{
  filc.enable = true;        # turns on every switch below
  filc.nix.enable = false;   # ...each can be turned off again
  filc.tools = [ "coreutils" "curl" "git" ];

  services.openssh.enable = true;   # now the Fil-C sshd
}
```

| Option | Effect |
| --- | --- |
| `filc.openssh.enable` | `services.openssh.package`, with `UsePAM = false` |
| `filc.tor.enable` | `services.tor.package` |
| `filc.unbound.enable` | `services.unbound.package` |
| `filc.lighttpd.enable` | `services.lighttpd.package` |
| `filc.redis.enable` | `services.redis.package` |
| `filc.phpfpm.enable` | `services.phpfpm.phpPackage`, and the PHP of MediaWiki, DokuWiki and Nextcloud; see below |
| `filc.bind.enable` | `services.bind.package` |
| `filc.shell.enable` | Bash as the login shell of root and normal users |
| `filc.nix.enable` | `nix.package` (daemon and CLI), with the build sandbox off |
| `filc.tools` | attributes of `filc.packages` on PATH, ahead of native programs of the same name |
| `filc.packages` | the package set replacements come from (default: this flake's `pkgsFilc`) |
| `filc.units` | the systemd services that should run Fil-C programs; the switches add theirs |

The switches only choose packages; enable the services as usual. A switch sets
the package at normal priority, so a configuration that also sets the package
itself gets a conflict rather than a silent choice.

## Any other service

The switches are the services filnix tests on every change, not the limit.
Any NixOS service with a package option can run a Fil-C build:

```nix
{ config, ... }:
{
  services.mosquitto.enable = true;
  services.mosquitto.package = config.filc.packages.mosquitto;
  filc.units = [ "mosquitto" ];
}
```

Listing the unit in `filc.units` makes `filc-status` and the VM tests check
that it really runs Fil-C. The [`mosquitto` test](../tests/nixos/default.nix)
runs Nixpkgs' test of the MQTT broker this way, with no switch. Whether a package builds
with Fil-C, and whether its tests pass, is on the campaign dashboard at
<https://nix.swa.sh/>. To make a service a switch, give it an entry in the
`services` table of `nixos/filc.nix` (its package option and its units) and
a VM test.

The same goes for programs: `filc.tools` takes any attribute of
`filc.packages`, and `environment.systemPackages = [ config.filc.packages.X ]`
works too.

## What you give up

| Where | Cost | Why |
| --- | --- | --- |
| everywhere | CPU time is 1.5× to 4× that of the native build, and memory use is higher | bounds checks and the garbage collector |
| sshd (steps 1 and 2) | no PAM: sshd checks passwords and keys itself, so an SSH login gets no logind session (no `XDG_RUNTIME_DIR`, no `loginctl` entry) and no other PAM module, such as `pam_limits` or two-factor login. A `!` password doesn't lock an account against keys, as on stock NixOS: to lock one on purpose, use `users.users.<name>.openssh.authorizedKeys.keys = [ ]` or a nologin shell | a Fil-C sshd can't load the native PAM modules; with the whole userland, PAM is Fil-C too and sshd keeps it |
| sshd without OpenSSL | no Fil-C build (`openssh.override { linkOpenssl = false; }`) | the Fil-C OpenSSH patch set does its ML-KEM key exchange through OpenSSL |
| Nix | no build sandbox | Fil-C has no namespaces or seccomp |
| PHP-FPM | each worker grows to about 150-250 MB, so a pool needs several GB | the garbage collector keeps more memory alive |
| nginx | no Fil-C build; use lighttpd | nginx's processes share pointers through shared memory zones, which capabilities don't survive |
| PHP web apps | apps whose module hard-codes its PHP (privatebin, dolibarr, icingaweb2, …) stay native unless you force their pool's `phpPackage` | the switch can only set the options NixOS has |
| updates | Fil-C packages follow filnix's Nixpkgs pin, not your channel, so their security fixes arrive when filnix updates | they are built and cached against that pin |

Without PAM, sshd also refuses every account whose password starts with `!`
as locked, and NixOS gives that password to every user who has none, so
key-only users couldn't log in. The switch's sshd leaves that check out
([nixos/openssh-nixos-unlocked.patch](../nixos/openssh-nixos-unlocked.patch)),
as NixOS's own sshd does by using PAM.

`filc.phpfpm` sets `services.phpfpm.phpPackage`, which pools use unless they
choose their own PHP. MediaWiki, DokuWiki and Nextcloud have a PHP option of
their own, which the switch sets too. A pool that keeps a native PHP gets an
evaluation warning and is left out of `filc.units`, so it is never counted as
Fil-C. To move it, set its `services.phpfpm.pools.<name>.phpPackage` with
`mkForce`.

## What is Fil-C here?

`filc-status`, installed whenever the module changes something, lists each
unit in `filc.units` with the program it runs, then the login shell, Nix and
each tool, as found on PATH:

```
Fil-C   lighttpd       /nix/store/…-lighttpd-x86_64-unknown-linux-gnufilc0-1.4.85/bin/lighttpd
Fil-C   sshd           /nix/store/…-openssh-x86_64-unknown-linux-gnufilc0-10.5p1/bin/sshd
Fil-C   unbound        /nix/store/…-unbound-x86_64-unknown-linux-gnufilc0-1.26.0/bin/unbound
Fil-C   login shell    /nix/store/…-bash-interactive-x86_64-unknown-linux-gnufilc0-5.3p9/bin/bash
Fil-C   curl           /nix/store/…-curl-x86_64-unknown-linux-gnufilc0-8.22.0-bin/bin/curl
```

A running process is Fil-C if it maps the Fil-C runtime, libpizlo, which the
VM tests check too. A program is Fil-C if its ELF headers name the Fil-C
loader as its interpreter or libpizlo as a needed library, the rule
[finix/filc-audit.sh](../finix/filc-audit.sh) applies to a whole closure. A normal user can't read the processes of root's services, so
it shows `?` for them; run it as root. It exits with status 1 if a listed unit
runs a native program.

## Example machines

- `nixosConfigurations.filc-demo` ([nixos/demo.nix](../nixos/demo.nix)): a
  QEMU VM at step 2, with the Fil-C sshd, Bash, Unbound, lighttpd, Nix and a
  set of tools.

  ```sh
  nix run .#nixosConfigurations.filc-demo.config.system.build.vm
  ssh -p 2222 demo@localhost        # password "demo"
  curl localhost:8080
  ```

- `nixosConfigurations.ec2-filc` ([nixos/ec2.nix](../nixos/ec2.nix)): the
  former `mbrock/ec2filc` repository, an Amazon image at step 1 with sshd and
  Tor. Replace its SSH key first.

  ```sh
  nixos-rebuild switch --flake .#ec2-filc --target-host root@HOST
  nix build .#nixosConfigurations.ec2-filc.config.system.build.amazonImage
  ```

## VM tests

`nixosTests` ([tests/nixos](../tests/nixos/default.nix)) runs NixOS VM tests
with the module on every node. Most are Nixpkgs' own tests of each service, so
the Fil-C services are held to the tests NixOS holds the native ones to, and
follow them as Nixpkgs updates.

| Test | What runs Fil-C | Changes to Nixpkgs' test |
| --- | --- | --- |
| `lighttpd`, `bind`, `tor` | the server; for Tor, all 13 nodes of a private Tor network with a hidden service | none |
| `unbound` | three resolvers | `unbound-full` without its Python plugin, which the test doesn't use |
| `openssh` | sshd on 9 of its nodes | `server-no-openssl` keeps the native sshd; two checks of `pam_limits` instead check that the limit is absent |
| `mosquitto` | the broker, through the general pattern above | none |
| `php-fpm` | PHP-FPM, behind native nginx | Fil-C PHP with APCu as the test's `php` |
| `wordpress`, `dokuwiki`, `mediawiki-*` (5), `nextcloud-*` (3) | the apps' PHP-FPM pools, and Redis for `nextcloud-with-postgresql-and-redis` | more memory |
| `redis`, `php-lighttpd` | Redis; lighttpd serving PHP-FPM over FastCGI | our own tests |
| `demo` | the demo machine: sshd, Bash, Unbound, lighttpd, the tools and Nix, which builds a derivation | our own test |
| `userland` | the whole NixOS userland under `nixosModules.filc-userland` | our own test; see [docs/nixos-userland.md](nixos-userland.md) |

All of them pass.

WordPress runs five releases behind httpd, nginx and Caddy; MediaWiki with
MySQL, PostgreSQL, SQLite, nginx and no web server; Nextcloud 35, 35 with MySQL
and memcached, and 34 with PostgreSQL and Redis (Nixpkgs ships its
notify_push app only up to 34). These VMs get more memory than the default
1 GB, which a Fil-C pool exhausts: 2 GB for WordPress and DokuWiki, 4 GB for
Nextcloud, which starts 12 workers.

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
