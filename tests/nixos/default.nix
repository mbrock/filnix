# NixOS VM tests of Fil-C services: Nixpkgs' own tests of each service, run
# with nixosModules.filc on every node, plus tests of our own.
#
#   nix build .#nixosTests.lighttpd           # one test
#   nix build .#nixosTests.lighttpd.driver    # just the driver, to run by hand
#
# After a test's own script passes, every unit the module switched
# (filc.units) that is still running must map the Fil-C runtime, so a test
# can't pass on a native build by accident. The log ends with a table of
# which services ran Fil-C builds.
#
# The tests want a builder with KVM; see docs/nixos.md for running them
# elsewhere.
{
  pkgs,
  pkgsFilc,
  filcModule,
}:
let
  inherit (pkgs) lib;
  upstream = "${pkgs.path}/nixos/tests";

  # The Fil-C switches the tests turn on unless a test says otherwise. Nix
  # isn't one of them: the Nixpkgs tests that use it want its sandbox.
  filcDefaults = {
    imports = [ filcModule ];
    filc.enable = true;
    filc.nix.enable = lib.mkDefault false;
  };

  proof = nodes: ''

    with subtest("Fil-C: the switched services run Fil-C builds"):
        expected = ${builtins.toJSON (lib.mapAttrs (_: n: n.filc.units) nodes)}
        proven = []
        for m in machines:
            if not m.is_up():
                continue
            for unit in expected.get(m.name, []):
                pid = m.succeed(f"systemctl show -p MainPID --value {unit}").strip()
                if pid == "0":
                    m.log(f"{unit} is not running; not checked")
                    continue
                exe = m.succeed(f"readlink -f /proc/{pid}/exe").strip()
                m.succeed(f"grep -q libpizlo /proc/{pid}/maps")
                proven.append((m.name, unit, exe))
        assert proven, f"no Fil-C unit was running at the end: {expected}"
        for p in proven:
            print("Fil-C %-12s %-16s %s" % p, flush=True)
  '';

  # Run `test` with the Fil-C module on every node, then check its units.
  withFilc =
    test:
    let
      base = pkgs.testers.runNixOSTest {
        imports = [ test ];
        defaults = filcDefaults;
      };
      script = base.config.testScript;
    in
    base.extend {
      modules = [
        {
          name = lib.mkForce "filc-${base.config.name}";
          testScript = lib.mkForce (
            { nodes, ... }@args:
            (if lib.isFunction script then script args else script) + proof nodes
          );
        }
      ];
    };
in
lib.mapAttrs (_: withFilc) {
  # Boots nixos/demo.nix and logs in through the Fil-C sshd.
  demo = ./demo.nix;

  lighttpd = "${upstream}/lighttpd.nix";
  tor = "${upstream}/tor.nix";
  bind = "${upstream}/bind.nix";

  # Where a Nixpkgs test picks a variant of the package, use the same
  # variant of the Fil-C build.
  openssh = {
    imports = [ "${upstream}/openssh.nix" ];
    nodes =
      let
        variant = args: {
          services.openssh.package = lib.mkForce (pkgsFilc.openssh.override args);
        };
      in
      {
        server-no-openssl = variant { linkOpenssl = false; };
        server-no-pam = variant { withPAM = false; };
        server-null-pam = variant { withPAM = false; };
      };
  };
  unbound = {
    imports = [ "${upstream}/unbound.nix" ];
    defaults.services.unbound.package = lib.mkForce pkgsFilc.unbound-full;
  };
  redis = ./redis.nix;

  # Nixpkgs runs this with PHP and APCu behind nginx. Only PHP-FPM is
  # Fil-C; nginx shares pointers between processes in shared memory, which
  # Fil-C capabilities don't survive, so the module has no nginx switch.
  php-fpm = {
    imports = [ "${upstream}/php/fpm.nix" ];
    _module.args.php = pkgsFilc.php.buildEnv {
      extensions = { enabled, all }: enabled ++ [ all.apcu ];
    };
  };
}
