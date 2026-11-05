# NixOS VM tests of Fil-C systems: Nixpkgs' own tests of each service, run
# with nixosModules.default on every node, plus tests of our own.
#
#   nix build .#nixosTests.lighttpd           # one test
#   nix build .#nixosTests.lighttpd.driver    # just the driver, to run by hand
#
# Every node's `pkgs` is the Fil-C package set, so the services, their
# clients, systemd and PAM are Fil-C builds. After a test's own script
# passes, `filc-ps` runs on every machine still up and fails the test if a
# process is native without being an allowed exception; its table ends the
# log.
#
# The tests want a builder with KVM, and about 2 GiB of memory per node.
{
  pkgs,
  pkgsFilc,
  filcModule,
}:
let
  inherit (pkgs) lib;
  upstream = "${pkgs.path}/nixos/tests";

  # Keyed, so the module is imported once however many times it is listed.
  filc = {
    key = "filnix-tests-filc-module";
    imports = [ filcModule ];
  };

  filcDefaults = {
    imports = [ filc ];
    filc.enable = true;
    # Fil-C programs need more memory than the default 1 GiB.
    virtualisation.memorySize = lib.mkOverride 900 2048;
    # The test driver talks to the VM over its backdoor, not the guest
    # agent, and the agent comes from a QEMU build Fil-C cannot do yet.
    services.qemuGuest.enable = lib.mkForce false;
  };

  proof = ''

    with subtest("Fil-C: every process is Fil-C or an allowed exception"):
        for m in machines:
            if not m.is_up():
                continue
            m.succeed("grep -q libpizlo /proc/1/maps")
            print(m.succeed("filc-ps"), flush=True)
  '';

  # A Fil-C php-fpm worker grows to about 150-250 MB, and these apps run
  # several (Nextcloud starts 12).
  phpApp =
    memorySize: test:
    let
      memory.defaults.virtualisation = { inherit memorySize; };
    in
    if test ? extend then
      test.extend { modules = [ memory ]; }
    else
      {
        imports = [
          test
          memory
        ];
      };

  # Tests whose nodes use Rust or Go programs keep those native.
  native =
    f: test:
    let
      m.defaults = {
        imports = [ filc ];
        filc.native = f;
      };
    in
    if test ? extend then
      test.extend { modules = [ m ]; }
    else
      {
        imports = [
          test
          m
        ];
      };

  # Run `test` (a test module, or a test Nixpkgs already built with runTest)
  # with the Fil-C module on every node, then check its processes.
  withFilc =
    test:
    let
      base = if test ? extend then test else pkgs.testers.runNixOSTest test;
      script = base.config.testScript;
    in
    base.extend {
      modules = [
        {
          # The module chooses the package set.
          node.pkgsReadOnly = false;
          defaults = filcDefaults;
          name = lib.mkForce "filc-${base.config.name}";
          testScript = lib.mkForce (
            { nodes, ... }@args:
            (if lib.isFunction script then script args else script) + proof
          );
        }
      ];
    };
in
lib.mapAttrs (_: withFilc) {
  lighttpd = "${upstream}/lighttpd.nix";
  # Its hidden service is served by Caddy, which is Go.
  tor = native (n: { inherit (n) caddy; }) "${upstream}/tor.nix";
  bind = "${upstream}/bind.nix";
  openssh = "${upstream}/openssh.nix";
  unbound = {
    imports = [ "${upstream}/unbound.nix" ];
    # Without the Python plugin, which the test doesn't use: its configure
    # runs the host's python, which a cross build can't.
    defaults =
      { pkgs, ... }:
      {
        services.unbound.package = lib.mkForce (
          pkgs.unbound-full.override { withPythonModule = false; }
        );
      };
  };
  mosquitto = "${upstream}/mosquitto.nix";
  redis = ./redis.nix;
  php-lighttpd = ./php-lighttpd.nix;

  # Nixpkgs runs this with PHP and APCu behind nginx.
  php-fpm = {
    imports = [ "${upstream}/php/fpm.nix" ];
    _module.args.php = pkgsFilc.php.buildEnv {
      extensions = { enabled, all }: enabled ++ [ all.apcu ];
    };
  };

  # Both also run behind Caddy, which is Go.
  wordpress = native (n: { inherit (n) caddy; }) (
    phpApp 2048 "${upstream}/wordpress.nix"
  );
  dokuwiki = native (n: { inherit (n) caddy; }) (
    phpApp 2048 "${upstream}/dokuwiki.nix"
  );
}
# mediawiki-mysql, -postgresql, -sqlite, -nohttpd and -nginx.
// lib.mapAttrs' (n: t: lib.nameValuePair "mediawiki-${n}" (withFilc t)) (
  import "${upstream}/mediawiki.nix" {
    inherit lib;
    runTest = t: t;
  }
)
# Nextcloud's own tests: nextcloud-basic, with Redis and PostgreSQL, and with
# MySQL and memcached. The Redis one is on 34 because Nixpkgs' notify_push
# app supports Nextcloud only up to 34, so its 35 test fails on any PHP; its
# notify_push daemon is Rust, so it stays native.
//
  lib.mapAttrs'
    (
      n: t:
      lib.nameValuePair
        "nextcloud-${lib.removeSuffix "34" (lib.removeSuffix "35" n)}"
        (
          withFilc (native (n: { inherit (n) nextcloud-notify_push; }) (phpApp 4096 t))
        )
    )
    (
      lib.getAttrs
        [ "basic35" "with-postgresql-and-redis34" "with-mysql-and-memcached35" ]
        (
          import "${upstream}/nextcloud" {
            inherit pkgs;
            inherit (pkgs.stdenv.hostPlatform) system;
          }
        )
    )
// {
  # A whole Fil-C NixOS boots and logs a user in; see userland.nix.
  userland = import ./userland.nix { inherit pkgs filcModule; };
}
