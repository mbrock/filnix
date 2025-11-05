{
  base,
  toolchain,
  portset,
  ghostty-terminfo,
  dank-bashrc,
}:

let
  inherit (toolchain) filcc filc-aliases;

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

  world-pkgs = with portset; [
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
      exec ${portset.bash}/bin/bash --rcfile ${pure-dank-bashrc} --noprofile
    '';

  # Legacy alias
  pure = filc-world;

  inherit world-pkgs;
}
