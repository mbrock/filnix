{
  base,
  toolchain,
  ports,
}:

let
  inherit (toolchain) filcc filc-aliases;

  ghostty-terminfo = base.runCommand "ghostty-terminfo" { } ''
    mkdir -p $out/share/terminfo
    ${base.ncurses}/bin/tic -x -o $out/share/terminfo ${../ghostty.terminfo}
  '';

  dank-bashrc = base.writeText "dank-bashrc" ''
    echo
    tput bold
    figlet -f fender "Fil-C" | sed 's/^/   /' | clolcat -f | head -n-1
    tput sgr0; tput dim
    echo -n '    '; clang 2>&1 -v | grep Fil-C
    tput sgr0
    echo; echo '  You feel an uncanny sense of safety...'
    tput sgr0
    echo

    export CC=filc
    export CXX=filc++
    export PKG_CONFIG=pkgconf
  '';

  shutdown-tools =
    let
      shutdown-bin = base.writeShellScriptBin "shutdown" ''
        sync
        kill -CONT 1
      '';
    in
    base.runCommand "shutdown-tools" {} ''
      mkdir -p $out/bin
      ln -s ${shutdown-bin}/bin/shutdown $out/bin/poweroff
      ln -s ${shutdown-bin}/bin/shutdown $out/bin/halt
      ln -s ${shutdown-bin}/bin/shutdown $out/bin/reboot
    '';

  world-pkgs = with ports; [
    bash
    coreutils
    gnumake
    gnum4
    bison
    gawk
    gnused
    gnugrep
    lesspipe
    flex
    bc
    ed
    which
    file
    diffutils
    gnutar
    bzip2
    zstd
    xz
    tmux
    nano
    nethack
    ncurses
    figlet
    clolcat
    ncurses
    sqlite
    lua
    perl
    tcl
    filcc
    filc-aliases
    openssl
    curl
    git
    pkgconf
    autoconf
    automake
    libtool
    depizloing-nm
    ghostty-terminfo
    util-linux
    wasm3
    kittydoom
    procps
    inetutils
    elfutils
    strace
    shutdown-tools
    lighttpd
    trealla # prolog
  ];

in
rec {
  filc-world = base.mkShellNoCC {
    name = "filc-world";
    buildInputs = world-pkgs;
    shellHook = ''
      source ${dank-bashrc}
    '';
  };

  # This shell gives you a pure PATH with nothing from your system!
  filc-world-shell =
    let
      env = base.buildEnv {
        name = "filc-world";
        paths = world-pkgs;
      };
      pure-dank-bashrc = base.writeText "pure-dank-bashrc" ''
        export PATH="${env}/bin"
        export TERMINFO_DIRS="${ghostty-terminfo}/share/terminfo"
        export PS1='\[\033[1;32m\][filc]\[\033[0m\] \w \$ '
        eval $(dircolors)
        alias ls='ls --color=auto'
        source ${dank-bashrc}
      '';
    in
    base.writeShellScriptBin "filc-world-shell" ''
      exec ${ports.bash}/bin/bash --rcfile ${pure-dank-bashrc} --noprofile
    '';

  # Legacy alias
  pure = filc-world;

  inherit world-pkgs;
}
