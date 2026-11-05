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
  filnix,
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

  mediawikiPhp =
    { pkgs, ... }:
    {
      services.mediawiki.phpPackage = pkgs.php84.buildEnv {
        extensions = { all, enabled }: enabled ++ [ all.apcu ];
      };
    };

  # Tests whose nodes use Rust or Go programs, or nginx, keep those native.
  # nginx's processes share pointers through shared memory, which Fil-C
  # capabilities do not survive; on a Fil-C system the web server is lighttpd.
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
  # Its hidden service is served by Caddy, which is Go, and its client
  # side runs arti, the Rust Tor.
  tor = native (n: { inherit (n) caddy arti; }) "${upstream}/tor.nix";
  bind = "${upstream}/bind.nix";
  openssh = {
    imports = [ "${upstream}/openssh.nix" ];
    # Its OpenSSH without OpenSSL can't use the Fil-C PAM: pam_unix's
    # crypt_r from libxcrypt doesn't resolve in that sshd (an open issue).
    # The node runs the regular Fil-C OpenSSH instead.
    nodes.server-no-openssl =
      { pkgs, lib, ... }:
      {
        services.openssh.package = lib.mkForce pkgs.openssh;
      };
  };
  # Its DNS client is knot-dns's kdig; the Fil-C knot-dns stops in its own
  # test suite (open, docs/nixos-userland.md).
  unbound = native (n: { inherit (n) knot-dns; }) {
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
  apache = ./apache.nix;
  demo-wiki = import ./demo-wiki.nix { inherit filnix; };
  first-switch = import ./first-switch.nix { inherit filnix; };
  php-lighttpd = ./php-lighttpd.nix;

  # Nixpkgs runs this with PHP and APCu behind nginx, here native.
  php-fpm = native (n: { inherit (n) nginxStable; }) {
    imports = [ "${upstream}/php/fpm.nix" ];
    _module.args.php = pkgsFilc.php.buildEnv {
      extensions = { enabled, all }: enabled ++ [ all.apcu ];
    };
  };

  # Both also run behind Caddy, which is Go, and nginx; WordPress also
  # behind Fil-C Apache. Each talks to Fil-C PHP-FPM.
  wordpress = native (n: {
    inherit (n)
      caddy
      nginxStable
      mariadb
      ;
  }) (phpApp 2048 "${upstream}/wordpress.nix");
  dokuwiki = native (n: { inherit (n) caddy nginxStable; }) (
    phpApp 2048 "${upstream}/dokuwiki.nix"
  );
}
# mediawiki-mysql, -postgresql, -sqlite, -nohttpd and -nginx, on Fil-C PHP
# 8.4: the module's default is 8.3, which is not ported. Apache is Fil-C;
# nginx, in front of PHP-FPM in one of them, is native.
//
  lib.mapAttrs'
    (
      n': t:
      lib.nameValuePair "mediawiki-${n'}" (
        withFilc (
          let
            t' = {
              imports = [ t ];
              defaults = mediawikiPhp;
            };
          in
          # MariaDB, the default database, is not ported yet; nginx can't be.
          native (
            n:
            {
              inherit (n) mariadb;
            }
            // lib.optionalAttrs (n' == "nginx") { inherit (n) nginxStable; }
            // lib.optionalAttrs (n' == "postgresql") { inherit (n) postgresql_17; }
          ) t'
        )
      )
    )
    (
      import "${upstream}/mediawiki.nix" {
        inherit lib;
        runTest = t: t;
      }
    )
# Nextcloud's own tests: nextcloud-basic, with Redis and PostgreSQL, and with
# MySQL and memcached. The Redis one is on 34 because Nixpkgs' notify_push
# app supports Nextcloud only up to 34, so its 35 test fails on any PHP; its
# notify_push daemon is Rust, so it stays native, and so does the nginx
# in front of Nextcloud.
//
  lib.mapAttrs'
    (
      test: t:
      lib.nameValuePair
        "nextcloud-${lib.removeSuffix "34" (lib.removeSuffix "35" test)}"
        (
          withFilc (
            native (
              n:
              {
                inherit (n) nginxStable nextcloud-notify_push;
                # The test's WebDAV client: the Fil-C mount.davfs daemon
                # stops after it forks (open, docs/nixos-userland.md).
                inherit (n) davfs2;
              }
              # MariaDB is not ported yet.
              // lib.optionalAttrs (lib.hasInfix "mysql" test) { inherit (n) mariadb; }
              # This one also runs notify_push's (Rust) test client.
              // lib.optionalAttrs (lib.hasInfix "postgresql" test) {
                inherit (n) postgresql_17;
                notify_push-test_client = n.nextcloud-notify_push.passthru.test_client;
              }
            ) (phpApp 4096 t)
          )
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
