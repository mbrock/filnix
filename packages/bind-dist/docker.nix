# An OCI image of the bind-dist tree, laid out like ISC's official
# internetsystemsconsortium/bind9 images: programs in /usr/bin and
# /usr/sbin, the configuration in /etc/bind, the working directory
# /var/cache/bind, secondary zones in /var/lib/bind, and named running as
# the bind user (53:53) with the same entrypoint and default command. The
# default named.conf is ISC's, without the DoT and DoH listeners, which
# need certificates.
#
#   nix build .#bind-docker && docker load < result
#   docker run --rm -p 53:53/udp -p 53:53/tcp filnix-bind:9.20.30
{
  pkgs,
  dist,
}:

let
  version = dist.passthru.bind.version;
  sbin = [
    "named"
    "rndc"
    "rndc-confgen"
    "tsig-keygen"
    "ddns-confgen"
  ];
  root =
    pkgs.runCommand "bind-docker-root" { nativeBuildInputs = [ pkgs.xz ]; }
      ''
        mkdir -p $out/opt $out/usr/bin $out/usr/sbin $out/etc/bind
        tar -xJf ${dist} -C $out/opt
        mv $out/opt/bind-*-filc-x86_64-linux $out/opt/bind
        for prog in $out/opt/bind/bin/*; do
          prog=$(basename $prog)
          case " ${pkgs.lib.concatStringsSep " " sbin} " in
            *" $prog "*) dir=sbin ;;
            *) dir=bin ;;
          esac
          ln -s /opt/bind/bin/$prog $out/usr/$dir/$prog
        done
        cat > $out/etc/bind/named.conf <<'EOF'
        options {
                directory "/var/cache/bind";

                listen-on { any; };
                listen-on-v6 { any; };
        };
        EOF
        cat > $out/etc/passwd <<'EOF'
        root:x:0:0:root:/root:/bin/false
        bind:x:53:53:bind:/var/cache/bind:/bin/false
        nobody:x:65534:65534:nobody:/nonexistent:/bin/false
        EOF
        cat > $out/etc/group <<'EOF'
        root:x:0:
        bind:x:53:
        nobody:x:65534:
        EOF
      '';
in
pkgs.dockerTools.buildLayeredImage {
  name = "filnix-bind";
  tag = version;
  contents = [ root ];
  fakeRootCommands = ''
    mkdir -m 1777 tmp
    mkdir -p var/cache/bind var/lib/bind var/log/bind run/named
    ln -s /run var/run
    chown 53:53 var/cache/bind var/lib/bind var/log/bind run/named
  '';
  config = {
    Entrypoint = [
      "/usr/sbin/named"
      "-u"
      "bind"
    ];
    Cmd = [
      "-f"
      "-c"
      "/etc/bind/named.conf"
      "-L"
      "/var/log/bind/default.log"
    ];
    Env = [ "PATH=/usr/bin:/usr/sbin" ];
    ExposedPorts = {
      "53/udp" = { };
      "53/tcp" = { };
      "953/tcp" = { };
      "853/tcp" = { };
      "443/tcp" = { };
    };
    Volumes = {
      "/etc/bind" = { };
      "/var/cache/bind" = { };
      "/var/lib/bind" = { };
      "/var/log" = { };
    };
    # Links the image to the repository when published to ghcr.io.
    Labels."org.opencontainers.image.source" = "https://github.com/mbrock/filnix";
  };
}
