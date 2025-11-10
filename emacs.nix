{
  pkgs,
  pkgsFilc,
}:

let
  emacsPackages = pkgsFilc.emacs30Packages;

  baseEmacs = emacsPackages.withPackages (
    epkgs: with epkgs; [
      cmake-mode
      consult
      embark
      embark-consult
      envrc
      htmlize
      llvm-mode
      magit
      marginalia
      meson-mode
      nix-mode
      orderless
      paredit
      treesit-grammars.with-all-grammars
      use-package
      vertico
      vterm
    ]
  );

  languageServers = with pkgs; [
    llvmPackages_21.clang-tools
    nixd
    cmake-language-server
    mesonlsp
    llvmPackages_21.mlir
  ];

  languageServerBinPath = pkgs.lib.makeBinPath languageServers;

  configDir = pkgs.lib.cleanSourceWith {
    name = "filc-emacs-config";
    src = ./emacs;
    filter = pkgs.lib.cleanSourceFilter;
  };

  launcher = pkgs.writeShellScriptBin "filc-emacs" ''
    export PATH="${languageServerBinPath}:$PATH"
    exec ${baseEmacs}/bin/emacs --init-directory ${configDir} "$@"
  '';

  filcEmacs = pkgs.symlinkJoin {
    name = "filc-emacs";
    paths = [
      baseEmacs
      launcher
    ]
    ++ languageServers;
    postBuild = ''
      rm $out/bin/emacs
      cp ${launcher}/bin/filc-emacs $out/bin/emacs
      ln -sf emacs $out/bin/filc-emacs
      mkdir -p $out/share
      ln -s ${configDir} $out/share/filc-emacs-config
    '';
    meta = (baseEmacs.meta or { }) // {
      description = "Fil-C Emacs with a ready-to-hack configuration";
      longDescription = ''
        Fil-C Emacs wraps ${baseEmacs.name or "emacs"} and ships a curated init.el,
        early-init.el, and Org notebook so you can iterate from Nix.
      '';
    };
  };
in
{
  inherit
    emacsPackages
    baseEmacs
    configDir
    launcher
    ;
  filc-emacs = filcEmacs;
}
