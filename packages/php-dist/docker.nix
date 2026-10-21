# An OCI image of the php-dist tree, laid out like the official php images:
# PHP in /usr/local/bin, the document root in /var/www/html, and `php -a`
# by default. FPM listens on port 9000 and logs to the container's stderr.
#
#   nix build .#php-docker && docker load < result
#   docker run --rm -it filnix-php:8.4.25
#   docker run --rm -p 9000:9000 filnix-php:8.4.25 php-fpm
{
  pkgs,
  dist,
}:

let
  version = dist.passthru.php.version;
  root =
    pkgs.runCommand "php-docker-root" { nativeBuildInputs = [ pkgs.xz ]; }
      ''
        mkdir -p $out/opt $out/usr/local/bin $out/var/www/html
        tar -xJf ${dist} -C $out/opt
        mv $out/opt/php-*-filc-x86_64-linux $out/opt/php
        for prog in php php-cgi php-fpm phpdbg; do
          ln -s /opt/php/bin/$prog $out/usr/local/bin/$prog
        done
        # The FPM master runs as root and its workers as nobody; listen beyond
        # loopback, keep the environment, and send logs to the container's stderr.
        cat > $out/opt/php/etc/php-fpm.d/zz-docker.conf <<'EOF'
        [global]
        daemonize = no
        error_log = /proc/self/fd/2
        log_limit = 8192

        [www]
        listen = 9000
        access.log = /proc/self/fd/2
        clear_env = no
        catch_workers_output = yes
        decorate_workers_output = no
        EOF
      '';
in
pkgs.dockerTools.buildLayeredImage {
  name = "filnix-php";
  tag = version;
  contents = [
    root
    pkgs.dockerTools.fakeNss
  ];
  # Sessions and uploads use /tmp; FPM writes its pid under var/run.
  extraCommands = ''
    mkdir -m 1777 tmp
    chmod -R u+w opt/php/var
  '';
  config = {
    Cmd = [
      "php"
      "-a"
    ];
    WorkingDir = "/var/www/html";
    Env = [ "PATH=/usr/local/bin:/opt/php/bin" ];
    ExposedPorts."9000/tcp" = { };
    # Links the image to the repository when published to ghcr.io.
    Labels."org.opencontainers.image.source" = "https://github.com/mbrock/filnix";
    StopSignal = "SIGQUIT";
  };
}
