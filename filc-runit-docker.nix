{
  base,
  ports,
  filc-sysroot,
}:

let
  runit = ports.runit;
  busybox = ports.busybox;
  bash = ports.bash;
  runtimeLibs = filc-sysroot;

  bannerService = ''
        mkdir -p etc/service/banner
        cat > etc/service/banner/run <<'EOF'
    #!/bin/sh
    PATH=/bin
    export PATH
    /bin/busybox echo "[banner] Fil-C runit container alive"
    while true; do
      /bin/busybox sleep 30
      /bin/busybox printf '[banner] heartbeat %s\n' "$(/bin/busybox date -Iseconds)"
    done
    EOF
        chmod +x etc/service/banner/run
  '';
in
base.dockerTools.streamLayeredImage {
  name = "filc-runit-2";
  tag = "latest";
  architecture = "amd64";

  contents = [
    runit
    busybox
    bash
    runtimeLibs
  ];

  config = {
    Entrypoint = [ "/bin/runit-init" ];
    Env = [
      "PATH=/bin"
    ];
    WorkingDir = "/root";
  };

  extraCommands = ''
        set -euo pipefail

        mkdir -p bin sbin etc/runit var/log run tmp root dev

        for exe in runit runit-init runsv runsvdir runsvchdir chpst sv svlogd utmpset; do
          ln -sf ${runit}/bin/$exe bin/$exe
        done

        ln -sf ${busybox}/bin/busybox bin/busybox
        ln -sf ${bash}/bin/bash bin/bash
        for applet in sh ls cat echo printf sleep ps top dmesg env uname id hostname true false pwd tail head; do
          ln -sf busybox bin/$applet || true
        done

        ln -sf ../bin/runit sbin/runit

        cat > etc/runit/1 <<'EOF'
    #!/bin/sh
    PATH=/bin
    export PATH
    echo "[stage1] Fil-C runit container bootstrap"
    mkdir -p /etc/service /var/log /run
    exit 0
    EOF

        cat > etc/runit/2 <<'EOF'
    #!/bin/sh
    PATH=/bin
    export PATH
    echo "[stage2] launching runsvdir on /etc/service"
    exec /bin/runsvdir -P /etc/service
    EOF

        cat > etc/runit/3 <<'EOF'
    #!/bin/sh
    PATH=/bin
    export PATH
    echo "[stage3] shutdown hooks running"
    exit 0
    EOF

        chmod +x etc/runit/{1,2,3}

        ${bannerService}

        mkdir -p etc/service/shell
        cat > etc/service/shell/run <<'EOF'
    #!/bin/sh
    PATH=/bin
    export PATH
    exec /bin/busybox setsid -w /bin/bash -l </dev/console >/dev/console 2>&1
    EOF
        chmod +x etc/service/shell/run
  '';
}
