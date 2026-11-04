# NixOS module: run chosen services and programs as Fil-C builds.
#
# Only the selected packages change. The rest of the system, including
# systemd, glibc and the kernel, stays the ordinary NixOS build, so the
# Fil-C programs sit alongside native ones.
#
#   imports = [ filnix.nixosModules.filc ];
#   filc.enable = true;                      # every switch below
#   filc.nix.enable = false;                 # ...except this one
#   filc.tools = [ "coreutils" "curl" ];     # programs on PATH
#
# A service switch sets the service's package option to its Fil-C build.
# Any other service works the same way by hand:
#
#   services.mosquitto.package = config.filc.packages.mosquitto;
#   filc.units = [ "mosquitto" ];
#
# `filc.units` lists the systemd units that should run Fil-C programs. The
# NixOS tests in tests/nixos check that each one maps the Fil-C runtime, and
# so does `filc-status` on the machine.
{ filnix }:
{
  config,
  lib,
  pkgs,
  ...
}:
let
  cfg = config.filc;
  fp = cfg.packages;
  inherit (lib)
    mkDefault
    mkEnableOption
    mkIf
    mkMerge
    mkOption
    types
    ;

  # Each service: what the switch describes, the systemd units whose main
  # process becomes a Fil-C program, and the configuration that does it.
  # To add one, find the service's package option and its units.
  services = with config.services; {
    openssh = {
      what = "the OpenSSH daemon (services.openssh)";
      units = lib.optional (openssh.enable && !openssh.startWhenNeeded) "sshd";
      config = {
        # A Fil-C program can't dlopen the system's native PAM modules, so
        # sshd checks passwords and keys itself (no logind session). The
        # patch lets it in users whose password NixOS sets to "!".
        services.openssh.package = fp.openssh.overrideAttrs (old: {
          patches = old.patches ++ [ ./openssh-nixos-unlocked.patch ];
        });
        services.openssh.settings.UsePAM = mkDefault false;
      };
    };
    tor = {
      what = "Tor (services.tor)";
      units = lib.optional tor.enable "tor";
      config.services.tor.package = fp.tor;
    };
    unbound = {
      what = "the Unbound resolver (services.unbound)";
      units = lib.optional unbound.enable "unbound";
      # The service is Type=notify, so it needs the systemd-enabled build.
      config.services.unbound.package = fp.unbound-with-systemd;
    };
    lighttpd = {
      what = "lighttpd (services.lighttpd)";
      units = lib.optional lighttpd.enable "lighttpd";
      config.services.lighttpd.package = fp.lighttpd;
    };
    redis = {
      what = "Redis (services.redis)";
      units = lib.mapAttrsToList (n: _: if n == "" then "redis" else "redis-${n}") (
        lib.filterAttrs (_: s: s.enable) redis.servers
      );
      config.services.redis.package = fp.redis;
    };
    phpfpm = {
      what = "PHP for PHP-FPM pools (services.phpfpm) and the web apps that choose their own";
      # Only pools that really run Fil-C PHP; the rest get a warning below.
      units = map (n: "phpfpm-${n}") (lib.attrNames filcPools);
      config = {
        services.phpfpm.phpPackage = fp.php;
        # Web apps whose pool uses the app's own phpPackage option. Each
        # gets Fil-C PHP 8.4 with the extensions its default adds.
        services.mediawiki.phpPackage = fp.php.buildEnv {
          extensions = { all, enabled }: enabled ++ [ all.apcu ];
        };
        services.nextcloud.phpPackage = fp.php;
        # services.dokuwiki.sites.*.phpPackage is set in options below.
        warnings = lib.mapAttrsToList (
          n: p:
          "filc.phpfpm: the PHP-FPM pool ${n} runs ${p.phpPackage.name}, not a Fil-C build: "
          + "its module chooses its own PHP. Set services.phpfpm.pools.${n}.phpPackage "
          + "(with mkForce) to a PHP from filc.packages, or set filc.phpfpm.enable = false."
        ) (lib.filterAttrs (n: _: !filcPools ? ${n}) phpfpm.pools);
      };
    };
    bind = {
      what = "the BIND DNS server (services.bind)";
      units = lib.optional bind.enable "bind";
      config.services.bind.package = fp.bind;
    };
  };

  filcPools = lib.filterAttrs (
    _: p: p.phpPackage.stdenv.hostPlatform.isFilc or false
  ) config.services.phpfpm.pools;

  # `filc-status` answers "what here is Fil-C?" the way the VM tests do: a
  # running unit is Fil-C if its process maps the runtime, libpizlo, and a
  # program if its ELF interpreter is the Fil-C loader or it needs libpizlo
  # (the rule of finix/filc-audit.sh). It fails if a listed unit runs native.
  status = pkgs.writeShellScriptBin "filc-status" ''
    row() { printf '%-7s %-14s %s\n' "$@"; }
    program() {
      f=$(type -P "$2") || { row - "$1" "not on PATH"; return; }
      f=$(readlink -f "$f")
      if ${lib.getBin pkgs.binutils-unwrapped}/bin/readelf -l -d "$f" 2>/dev/null |
        grep -qE 'interpreter: [^]]*/ld-fil1-|\(NEEDED\).*\[libpizlo\.so\]'; then
        row Fil-C "$1" "$f"
      else
        row native "$1" "$f"
      fi
    }
    bad=0
    for u in ${lib.escapeShellArgs cfg.units}; do
      pid=$(systemctl show -p MainPID --value "$u")
      if [ "$pid" = 0 ]; then
        row - "$u" "not running"
      elif ! maps=$(cat /proc/$pid/maps 2>/dev/null); then
        row '?' "$u" "run as root to check"
      elif grep -q libpizlo <<<"$maps"; then
        row Fil-C "$u" "$(readlink -f /proc/$pid/exe)"
      else
        row native "$u" "$(readlink -f /proc/$pid/exe)"
        bad=1
      fi
    done
    ${lib.optionalString cfg.shell.enable ''program "login shell" "$(getent passwd root | cut -d: -f7)"''}
    ${lib.optionalString cfg.nix.enable "program nix nix"}
    ${lib.concatMapStrings (
      name:
      let
        p = fp.${name};
      in
      # The tool's main program, or else the first one it has.
      "program ${name} ${
        p.meta.mainProgram or ''"$(ls ${lib.getBin p}/bin | head -1)"''
      }\n"
    ) cfg.tools}
    exit $bad
  '';

  # A switch that follows filc.enable unless set explicitly.
  switch =
    what:
    mkOption {
      type = types.bool;
      default = cfg.enable;
      defaultText = lib.literalExpression "config.filc.enable";
      description = "Whether to use the Fil-C build of ${what}.";
    };
in
{
  # DokuWiki chooses PHP per site.
  options.services.dokuwiki.sites = mkOption {
    type = types.attrsOf (
      types.submodule {
        config.phpPackage = mkIf cfg.phpfpm.enable fp.php;
      }
    );
  };

  options.filc = lib.mapAttrs (_: s: { enable = switch s.what; }) services // {
    enable = mkEnableOption "the Fil-C builds of every service and program below";

    packages = mkOption {
      type = types.raw;
      default = filnix.legacyPackages.${pkgs.stdenv.hostPlatform.system}.pkgsFilc;
      defaultText = lib.literalExpression "filnix.legacyPackages.\${system}.pkgsFilc";
      description = "The Fil-C package set that replacements come from.";
    };

    shell.enable = switch "Bash as the login shell of root and normal users";

    nix.enable = switch ''
      Nix itself (the daemon and the CLI). Fil-C has no namespaces or
      seccomp, so this also turns off the build sandbox'';

    tools = mkOption {
      type = types.listOf types.str;
      default = [ ];
      example = [
        "coreutils"
        "curl"
        "git"
      ];
      description = ''
        Attributes of filc.packages to put on the system PATH, ahead of the
        native programs of the same name.
      '';
    };

    units = mkOption {
      type = types.listOf types.str;
      default = [ ];
      example = [ "mosquitto" ];
      description = ''
        The systemd services whose main process should be a Fil-C program.
        The switches add their enabled services. Add the services you point
        at `filc.packages` yourself, and `filc-status` and the VM tests check
        those too.
      '';
    };
  };

  config = mkMerge (
    lib.mapAttrsToList (name: s: mkIf cfg.${name}.enable s.config) services
    ++ [
      {
        filc.units = lib.concatLists (
          lib.mapAttrsToList (
            name: s: lib.optionals cfg.${name}.enable s.units
          ) services
          ++ [ (lib.optional (cfg.nix.enable && config.nix.enable) "nix-daemon") ]
        );
      }

      (mkIf cfg.shell.enable {
        users.defaultUserShell = fp.bashInteractive;
        users.users.root.shell = fp.bashInteractive;
        environment.shells = [ fp.bashInteractive ];
      })

      (mkIf cfg.nix.enable {
        nix.package = fp.nix;
        nix.settings.sandbox = false;
      })

      {
        environment.systemPackages = map (name: lib.hiPrio fp.${name}) cfg.tools;
      }

      (mkIf
        (cfg.units != [ ] || cfg.tools != [ ] || cfg.shell.enable || cfg.nix.enable)
        {
          environment.systemPackages = [ status ];
        }
      )
    ]
  );
}
