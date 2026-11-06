# https://filc.less.rest: a public Fil-C server on EC2, booted from the
# filnix AMI (nixos/amazon.nix). MediaWiki runs on Fil-C PHP-FPM behind Fil-C
# lighttpd, with SQLite; TLS comes from Let's Encrypt over HTTP-01 on the
# machine itself. scripts/launch-demo-wiki launches it.
#
# It is meant to survive being broken into without cost: no IAM instance
# profile, IMDSv2 with a hop limit of 1, no tokens or private keys but its
# own TLS key, a read-only wiki without account creation, and updates
# pulled from the latest filnix release, with nothing that could push to it.
# /status/ shows what filc-ps finds running.
{ filnix }:
{
  config,
  lib,
  pkgs,
  ...
}:
let
  domain = "filc.less.rest";
  wiki = config.services.mediawiki;
  status = "/var/lib/filc-status";
in
{
  imports = [ (import ./amazon.nix { inherit filnix; }) ];

  filnix.configuration = "demo-wiki";
  networking.hostName = lib.mkForce "filc-wiki";

  # lego (ACME) and minica (its bootstrap certificate) are Go.
  filc.native = native: { inherit (native) lego minica; };

  # A public server: no console autologin; root logs in with the key pair.
  services.getty.autologinUser = lib.mkForce null;
  users.motd = lib.mkForce ''

    filc.less.rest: MediaWiki on Fil-C PHP-FPM and lighttpd, on a Fil-C
    NixOS (nixos/demo-wiki.nix in github:mbrock/filnix). It updates itself
    from the latest filnix release (filnix-update.timer).

  '';

  networking.firewall.allowedTCPPorts = [
    80
    443
  ];

  services.mediawiki = {
    enable = true;
    name = "Fil-C wiki";
    url = "https://${domain}";
    webserver = "none";
    database.type = "sqlite";
    # The module's default is PHP 8.3, which is not ported.
    phpPackage = pkgs.php84.buildEnv {
      extensions = { all, enabled }: enabled ++ [ all.apcu ];
    };
    # Nobody logs in, so nobody needs to know it.
    passwordFile = "/var/lib/mediawiki/admin-password";
    # A Fil-C php-fpm worker grows to 150-250 MB; t3.medium has 4 GiB.
    poolConfig = {
      "pm" = "static";
      "pm.max_children" = 4;
      "pm.max_requests" = 500;
      "listen.mode" = "0660";
    };
    extraConfig = ''
      # Read-only to the world.
      $wgGroupPermissions['*']['edit'] = false;
      $wgGroupPermissions['*']['createaccount'] = false;
      $wgGroupPermissions['*']['createpage'] = false;
      $wgGroupPermissions['user']['edit'] = false;
      $wgEnableUploads = false;
      $wgMainCacheType = CACHE_NONE;
    '';
  };

  systemd.services.mediawiki-admin-password = {
    description = "Generate the MediaWiki admin password";
    wantedBy = [ "mediawiki-init.service" ];
    before = [ "mediawiki-init.service" ];
    serviceConfig.Type = "oneshot";
    script = ''
      f=${wiki.passwordFile}
      if [ ! -s "$f" ]; then
        install -d -m 0750 -o mediawiki -g mediawiki "$(dirname "$f")"
        (umask 077; head -c 24 /dev/urandom | base64 > "$f")
        chown mediawiki "$f"
      fi
    '';
  };

  # lighttpd reaches PHP-FPM through the pool's socket, owned by mediawiki.
  users.users.lighttpd.extraGroups = [ "mediawiki" ];

  services.lighttpd = {
    enable = true;
    document-root = "${wiki.finalPackage}/share/mediawiki";
    enableModules = [
      "mod_access"
      "mod_alias"
      "mod_fastcgi"
      "mod_openssl"
      "mod_redirect"
      "mod_setenv"
    ];
    extraConfig = ''
      index-file.names += ( "index.php" )
      url.access-deny = ( "~", ".inc" )
      fastcgi.server = ( ".php" => ((
        "socket" => "${config.services.phpfpm.pools.mediawiki.socket}",
        "check-local" => "enable",
      )))
      alias.url += (
        "/.well-known/acme-challenge/" => "/var/lib/acme/acme-challenge/.well-known/acme-challenge/",
        "/status/" => "${status}/",
      )
      $HTTP["url"] =~ "^/status/" {
        index-file.names = ( "index.txt" )
        setenv.add-response-header = ( "Content-Type" => "text/plain; charset=utf-8" )
      }

      $SERVER["socket"] == ":443" {
        ssl.engine = "enable"
        ssl.pemfile = "/var/lib/acme/${domain}/full.pem"
      }
      $SERVER["socket"] == "[::]:443" {
        ssl.engine = "enable"
        ssl.pemfile = "/var/lib/acme/${domain}/full.pem"
      }
      $SERVER["socket"] == "[::]:80" { }
      $HTTP["scheme"] == "http" {
        $HTTP["url"] !~ "^/.well-known/acme-challenge/" {
          url.redirect = ( "" => "https://${domain}''${url.path}''${qsa}" )
        }
      }
    '';
  };

  security.acme = {
    acceptTerms = true;
    certs.${domain} = {
      webroot = "/var/lib/acme/acme-challenge";
      group = "lighttpd";
      reloadServices = [ "lighttpd" ];
    };
  };
  # lighttpd starts with the self-signed certificate that the acme unit
  # makes first, and reloads when Let's Encrypt's arrives.
  systemd.services.lighttpd = {
    wants = [ "acme-${domain}.service" ];
    after = [ "acme-${domain}.service" ];
  };

  # What runs here, every 5 minutes, at https://filc.less.rest/status/.
  systemd.services.filc-status = {
    description = "Write the filc-ps status page";
    path = [ "/run/current-system/sw" ];
    serviceConfig.Type = "oneshot";
    script = ''
      install -d -m 0755 ${status}
      {
        echo "filc.less.rest at $(date -u '+%Y-%m-%d %H:%M UTC'), up $(awk '{ printf "%d days %d hours", $1 / 86400, $1 % 86400 / 3600 }' /proc/uptime)"
        echo "system: $(readlink /run/current-system)"
        # The revision this system was built from, not the updater's tag
        # file, which lags when a switch fails before writing it.
        echo "filnix: ${filnix.rev or "local"}$(tag=$(cat /var/lib/filnix-update/tag 2>/dev/null) && echo " (filnix-update: $tag)")"
        echo "kernel: $(uname -r)"
        echo
        echo "Every running process, by whether it maps libpizlo, the Fil-C runtime."
        echo "Native ones must be in the closure of an allowed exception"
        echo "(lib/native-exceptions.nix, or this machine's filc.native: lego, minica)."
        echo
        filc-ps || echo "filc-ps exited $?"
      } > ${status}/index.txt.new
      mv ${status}/index.txt.new ${status}/index.txt
    '';
  };
  systemd.timers.filc-status = {
    wantedBy = [ "timers.target" ];
    timerConfig = {
      OnBootSec = "2min";
      OnUnitActiveSec = "5min";
    };
  };

  # Pull updates: switch to this configuration at the newest filnix
  # release, substituting everything (max-jobs 0 refuses to build here).
  systemd.services.filnix-update = {
    description = "Switch to demo-wiki at the latest filnix release";
    path = with pkgs; [
      config.nix.package
      config.system.build.nixos-rebuild
      curl
      jq
      coreutils
      config.systemd.package
    ];
    serviceConfig.Type = "oneshot";
    serviceConfig.StateDirectory = "filnix-update";
    # The switch changes this unit too; restarting it would kill the switch's
    # caller before it writes the tag, and the rerun collides with the switch.
    restartIfChanged = false;
    script = ''
      tag=$(curl -fsS https://api.github.com/repos/mbrock/filnix/releases/latest | jq -er .tag_name)
      case $tag in v*) ;; *) echo "unexpected tag: $tag"; exit 1 ;; esac
      if [ "$tag" = "$(cat /var/lib/filnix-update/tag 2>/dev/null)" ]; then
        echo "at $tag already"
        exit 0
      fi
      echo "switching to $tag"
      nixos-rebuild switch --flake "github:mbrock/filnix/$tag#demo-wiki" \
        --option max-jobs 0 --option builders ""
      echo "$tag" > /var/lib/filnix-update/tag
      systemctl start --no-block filc-status.service
    '';
  };
  systemd.timers.filnix-update = {
    wantedBy = [ "timers.target" ];
    timerConfig = {
      OnBootSec = "15min";
      OnUnitActiveSec = "6h";
      RandomizedDelaySec = "30min";
    };
  };
}
