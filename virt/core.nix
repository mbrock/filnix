{
  base,
  ports,
  world-pkgs,
  dank-bashrc,
  ghostty-terminfo,
}:

{
  # Platform-specific configuration
  consoleDevice ? "/dev/console",
  mountFilesystems ? false,
}:

let
  runit = ports.runit;

   runit-config = base.runCommand "runit-config" { } ''
    mkdir -p $out/etc/runit $out/etc/service/banner $out/etc/service/shell $out/sbin

    cp ${runit-stage1} $out/etc/runit/1
    cp ${runit-stage2} $out/etc/runit/2
    cp ${runit-stage3} $out/etc/runit/3
    chmod +x $out/etc/runit/{1,2,3}

    # Create stopit file so SIGCONT triggers shutdown
    touch $out/etc/runit/stopit
    chmod +x $out/etc/runit/stopit

    cp ${banner-service} $out/etc/service/banner/run
    chmod +x $out/etc/service/banner/run

    cp ${shell-service} $out/etc/service/shell/run
    chmod +x $out/etc/service/shell/run

    ln -s ../bin/runit $out/sbin/runit
  '';

  env = base.buildEnv {
    name = "filc-world-env";
    paths = [
      runit
      ghostty-terminfo
      runit-config
    ]
    ++ world-pkgs;
  };

  closure = base.closureInfo { rootPaths = [ env ]; };

  # Configuration files
  os-release = base.writeText "os-release" ''
    NAME="Fil-C Runit"
    ID=filc
    PRETTY_NAME="Fil-C Runit Container"
    VERSION="latest"
  '';

  bashrc = base.writeText "bashrc" ''
    export PATH=${env}/bin
    export TERMINFO_DIRS=/usr/share/terminfo
    export PS1='\[\033[1;32m\][filc]\[\033[0m\] \w \$ '
    export CC=clang
    export CXX=clang++
    eval $(dircolors)
    alias ls='ls --color=auto'
    ${builtins.readFile dank-bashrc}
  '';

  bash_profile = base.writeText "bash_profile" ''
    [ -f ~/.bashrc ] && source ~/.bashrc
  '';

  runit-stage1 = base.writeShellScript "runit-stage1" (
    ''
      PATH=/bin
      export PATH
      export TERMINFO_DIRS=/usr/share/terminfo

      if ! touch /.test 2>/dev/null; then
        mount -o remount,rw / || true
        rm -f /.test
      fi
    ''
    + (
      if mountFilesystems then
        ''
          mkdir -p /proc /sys /run /dev /var/service /var/log
          mount -t proc proc /proc
          mount -t sysfs sysfs /sys
          mount -t devtmpfs devtmpfs /dev
          mount -t tmpfs tmpfs /run
          hostname filux
        ''
      else
        ''
          mkdir -p /var/service /var/log /run
        ''
    )
    + ''
      # Symlink services from /etc/service to writable /var/service
      for svc in /etc/service/*; do
        if [ -d "$svc" ]; then
          ln -sf "$svc" /var/service/
        fi
      done

      exit 0
    ''
  );

  runit-stage2 = base.writeShellScript "runit-stage2" ''
    PATH=/bin
    export PATH
    echo "[stage2] supervising services"
    runsvdir -P /var/service
  '';

  runit-stage3 = base.writeShellScript "runit-stage3" (
    ''
      PATH=/bin
      export PATH
      echo "[stage3] shutdown"
    ''
    + (
      if mountFilesystems then
        ''
          for target in /run /proc /sys /dev; do
            umount "$target" 2>/dev/null || true
          done
        ''
      else
        ""
    )
    + ''
      echo "[stage3] stopping services..."
      sv -w5 force-stop /var/service/*
      sv exit /var/service/*
    ''
  );

  banner-service = base.writeShellScript "banner-run" ''
    PATH=/bin
    export PATH
    trap 'echo "[banner] shutting down"; exit 0' TERM INT KILL
    while true; do
      sleep 5
      uptime=$(cat /proc/uptime | cut -d' ' -f1)
      printf '[uptime] %.0fs\n' "$uptime"
    done
  '';

  shell-service = base.writeShellScript "shell-run" ''
    PATH=/bin
    export PATH
    export HOME=/root
    export SHELL=/bin/bash
    cd "$HOME"
    exec setsid bash +m -l <${consoleDevice} >${consoleDevice} 2>&1
  '';

  mkRootfsScript = targetDir: ''
    mkdir -p ${targetDir}/{var/log,var/service,run,tmp,root,dev,nix/store,usr/share/terminfo,proc,sys}

    # Copy entire closure into /nix/store
    for path in $(cat ${closure}/store-paths); do
      dst="${targetDir}$path"
      mkdir -p "$(dirname "$dst")"
      cp -a --no-preserve=ownership "$path" "$dst"
    done

    # Symlink env structure into rootfs (includes runit-config merged in)
    for item in ${env}/*; do
      ln -s $item "${targetDir}/$(basename $item)"
    done

    # Install ghostty terminfo
    ${ports.ncurses}/bin/tic -x -o "${targetDir}/usr/share/terminfo" ${../ghostty.terminfo}

    # Install user configuration files
    cp ${bashrc} "${targetDir}/root/.bashrc"
    cp ${bash_profile} "${targetDir}/root/.bash_profile"
  '';

  mkDockerExtraCommands = ''
    mkdir -p var/log var/service run tmp root dev usr/share/terminfo

    # Install ghostty terminfo (can't be in nix store symlink)
    ${ports.ncurses}/bin/tic -x -o usr/share/terminfo ${../ghostty.terminfo}

    # Install user configuration files (need writable /root)
    cp ${bashrc} root/.bashrc
    cp ${bash_profile} root/.bash_profile
  '';

in
{
  inherit
    env
    closure
    runit-config
    os-release
    bashrc
    bash_profile
    runit-stage1
    runit-stage2
    runit-stage3
    banner-service
    shell-service
    mkRootfsScript
    mkDockerExtraCommands
    ;
}
