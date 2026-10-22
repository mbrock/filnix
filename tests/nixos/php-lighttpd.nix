# PHP-FPM behind lighttpd over FastCGI, both Fil-C builds: the web stack the
# module offers, since it has no nginx switch.
{ ... }:
{
  name = "php-lighttpd";
  nodes.machine =
    { config, pkgs, ... }:
    {
      services.phpfpm.pools.web = {
        user = "lighttpd";
        settings = {
          "listen.owner" = "lighttpd";
          "listen.mode" = "0600";
          "pm" = "static";
          "pm.max_children" = 2;
        };
      };

      services.lighttpd = {
        enable = true;
        document-root = pkgs.writeTextDir "index.php" ''
          <?php
          header("Content-Type: application/json");
          echo json_encode([
              "version" => PHP_VERSION,
              "method" => $_SERVER["REQUEST_METHOD"],
              "name" => $_POST["name"] ?? null,
              "sum" => array_sum(range(1, 100)),
          ]);
        '';
        enableModules = [ "mod_fastcgi" ];
        extraConfig = ''
          index-file.names += ( "index.php" )
          fastcgi.server = ( ".php" => ((
            "socket" => "${config.services.phpfpm.pools.web.socket}",
          )))
        '';
      };
    };

  testScript =
    { nodes, ... }:
    ''
      import json

      machine.wait_for_unit("phpfpm-web")
      machine.wait_for_unit("lighttpd")
      machine.wait_for_open_port(80)

      got = json.loads(machine.succeed("curl -fsS http://127.0.0.1/"))
      assert got == {
          "version": "${nodes.machine.services.phpfpm.phpPackage.version}",
          "method": "GET",
          "name": None,
          "sum": 5050,
      }, got

      got = json.loads(machine.succeed("curl -fsS -d name=fil-c http://127.0.0.1/index.php"))
      assert got["method"] == "POST" and got["name"] == "fil-c", got
    '';
}
