{
  pkgs,
  ports,
  world-pkgs,
  dank-bashrc,
  ghostty-terminfo,
  lighttpd-demo,
}:

{
  # Platform-specific configuration
  consoleDevice ? "/dev/console",
  mountFilesystems ? false,
}:

let
  runit = ports.runit;

  passwd = pkgs.writeText "passwd" ''
    root:x:0:0:root:/root:/bin/bash
    sshd:x:74:74:Privilege-separated SSH:/var/empty/sshd:/bin/false
    nobody:x:65534:65534:nobody:/:/bin/false
  '';

  shadow = pkgs.writeText "shadow" ''
    root:*:19659:0:99999:7:::
    sshd:*:19659:0:99999:7:::
    nobody:*:19659:0:99999:7:::
  '';

  group = pkgs.writeText "group" ''
    root:x:0:
    sshd:x:74:
    nogroup:x:65534:
  '';

  nsswitch = pkgs.writeText "nsswitch.conf" ''
    passwd: files
    group: files
    shadow: files
    hosts: files dns
    networks: files
    protocols: files
    services: files
    ethers: files
    rpc: files
  '';

  sshd-config = pkgs.writeText "sshd_config" ''
    Port 22
    ListenAddress 0.0.0.0
    HostKey /var/ssh/ssh_host_ed25519_key
    HostKey /var/ssh/ssh_host_rsa_key
    PermitRootLogin yes
    PasswordAuthentication no
    ChallengeResponseAuthentication no
    UsePAM no
    AuthorizedKeysFile .ssh/authorized_keys
    Subsystem sftp ${ports.openssh}/libexec/sftp-server
    PrintMotd no
    ClientAliveInterval 30
    ClientAliveCountMax 5
    ModuliFile ${ports.openssh}/etc/ssh/moduli
  '';

  sshd-service = pkgs.writeShellScript "sshd-run" ''
    PATH=/bin:${ports.openssh}/bin
    export PATH

    mkdir -p /var/run/sshd /var/ssh /root/.ssh
    chmod 700 /root/.ssh

    if [ ! -f /var/ssh/ssh_host_ed25519_key ]; then
      echo "[sshd] generating ed25519 host key"
      ${ports.openssh}/bin/ssh-keygen -t ed25519 -N "" -f /var/ssh/ssh_host_ed25519_key
    fi

    if [ ! -f /var/ssh/ssh_host_rsa_key ]; then
      echo "[sshd] generating RSA host key"
      ${ports.openssh}/bin/ssh-keygen -t rsa -b 4096 -N "" -f /var/ssh/ssh_host_rsa_key
    fi

    chmod 600 /var/ssh/ssh_host_*_key

    mkdir -p /var/empty/sshd
    chown sshd:sshd /var/empty/sshd
    chmod 755 /var/empty
    chmod 755 /var/empty/sshd

    echo "[sshd] starting ssh daemon..."
    exec ${ports.openssh}/bin/sshd -D -e -f /etc/ssh/filnix_sshd_config
  '';

  runit-config = pkgs.runCommand "runit-config" { } ''
    mkdir -p $out/etc/runit $out/etc/service/shell $out/etc/service/lighttpd $out/etc/service/sshd $out/etc/ssh $out/sbin

    cp ${runit-stage1} $out/etc/runit/1
    cp ${runit-stage2} $out/etc/runit/2
    cp ${runit-stage3} $out/etc/runit/3
    chmod +x $out/etc/runit/{1,2,3}

    # Create stopit file so SIGCONT triggers shutdown
    touch $out/etc/runit/stopit
    chmod +x $out/etc/runit/stopit

    cp ${shell-service} $out/etc/service/shell/run
    chmod +x $out/etc/service/shell/run

    cp ${lighttpd-service} $out/etc/service/lighttpd/run
    chmod +x $out/etc/service/lighttpd/run

    cp ${sshd-service} $out/etc/service/sshd/run
    chmod +x $out/etc/service/sshd/run

    cp ${passwd} $out/etc/passwd
    cp ${shadow} $out/etc/shadow
    cp ${group} $out/etc/group
    cp ${nsswitch} $out/etc/nsswitch.conf
    cp ${sshd-config} $out/etc/ssh/filnix_sshd_config
    chmod 600 $out/etc/shadow

    ln -s ../bin/runit $out/sbin/runit
  '';

  env = pkgs.buildEnv {
    name = "filc-world-env";
    paths = [
      runit
      ghostty-terminfo
      runit-config
      lighttpd-demo
    ]
    ++ world-pkgs;
  };

  closure = pkgs.closureInfo { rootPaths = [ env ]; };

  # Configuration files
  os-release = pkgs.writeText "os-release" ''
    NAME="Fil-C Runit"
    ID=filc
    PRETTY_NAME="Fil-C Runit Container"
    VERSION="latest"
  '';

  bashrc = pkgs.writeText "bashrc" ''
    export PATH=${env}/bin
    export TERMINFO_DIRS=/usr/share/terminfo
    export PS1='\[\033[1;32m\][filc]\[\033[0m\] \w \$ '
    export CC=clang
    export CXX=clang++
    eval $(dircolors)
    alias ls='ls --color=auto'
    ${builtins.readFile dank-bashrc}
  '';

  bash_profile = pkgs.writeText "bash_profile" ''
    [ -f ~/.bashrc ] && source ~/.bashrc
  '';

  runit-stage1 = pkgs.writeShellScript "runit-stage1" (
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
                    mkdir -p /proc /sys /run /dev /var/service /var/log /var/tmp
                    mount -t proc proc /proc
                    mount -t sysfs sysfs /sys
                    mount -t devtmpfs devtmpfs /dev
                    mount -t tmpfs tmpfs /run
                    hostname filux
                    if command -v ifconfig >/dev/null 2>&1; then
                      ifconfig lo 127.0.0.1 up || true
                      ifconfig eth0 10.0.2.15 netmask 255.255.255.0 up || true
                      if command -v route >/dev/null 2>&1; then
                        route add default gw 10.0.2.2 || true
                      fi
                    fi
                    if [ ! -f /etc/resolv.conf ]; then
                      cat <<'EOF' >/etc/resolv.conf
          nameserver 10.0.2.3
          EOF
                    fi
        ''
      else
        ''
          mkdir -p /var/service /var/log /var/tmp /run
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

  runit-stage2 = pkgs.writeShellScript "runit-stage2" ''
    PATH=/bin
    export PATH
    echo "[stage2] supervising services"
    runsvdir -P /var/service
  '';

  runit-stage3 = pkgs.writeShellScript "runit-stage3" (
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

  shell-service = pkgs.writeShellScript "shell-run" ''
    PATH=/bin
    export PATH
    export HOME=/root
    export SHELL=/bin/bash
    cd "$HOME"
    exec setsid bash +m -l <${consoleDevice} >${consoleDevice} 2>&1
  '';

  lighttpd-service = pkgs.writeShellScript "lighttpd-run" ''
    PATH=/bin
    export PATH
    export HOME=/root

    # Create runtime directory for lighttpd
    RUNDIR=/var/log/lighttpd
    mkdir -p "$RUNDIR"

    echo "[lighttpd] starting web server..."

    # Run lighttpd-demo (redirects to log file)
    exec ${lighttpd-demo}/bin/lighttpd-demo 2>&1
  '';

  mkRootfsScript = targetDir: ''
    mkdir -p ${targetDir}/{var/log,var/service,var/tmp,run,tmp,root,dev,nix/store,usr/share/terminfo,proc,sys}

    # Copy entire closure into /nix/store
    for path in $(cat ${closure}/store-paths); do
      dst="${targetDir}$path"
      mkdir -p "$(dirname "$dst")"
      ${pkgs.coreutils}/bin/cp -a --no-preserve=ownership "$path" "$dst"
    done

    # Symlink env structure into rootfs (includes runit-config merged in)
    for item in ${env}/*; do
      name=$(basename "$item")
      if [ "$name" = "etc" ]; then
        mkdir -p "${targetDir}/etc"
        ${pkgs.coreutils}/bin/cp -a --no-preserve=ownership "$item/." "${targetDir}/etc/"
      else
        ln -s $item "${targetDir}/$name"
      fi
    done

    # Install ghostty terminfo
    ${ports.ncurses}/bin/tic -x -o "${targetDir}/usr/share/terminfo" ${../ghostty.terminfo}

    # Install user configuration files
    cp ${bashrc} "${targetDir}/root/.bashrc"
    cp ${bash_profile} "${targetDir}/root/.bash_profile"
  '';

  mkDockerExtraCommands = ''
    mkdir -p var/log var/service var/tmp run tmp root dev usr/share/terminfo

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
    shell-service
    lighttpd-service
    sshd-service
    mkRootfsScript
    mkDockerExtraCommands
    ;
}
