{
  pkgs,
  pkgsFilc,
}:

let
  inherit (pkgsFilc) emacsPackages;

  baseEmacs = emacsPackages.withPackages (
    epkgs: with epkgs; [
      cmake-mode
      company
      consult
      diff-hl
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
      rainbow-delimiters
      (treesit-grammars.with-grammars (
        gs: with gs; [
          tree-sitter-bash
          tree-sitter-c
          tree-sitter-cpp
          tree-sitter-cmake
          tree-sitter-go
          tree-sitter-javascript
          tree-sitter-json
          tree-sitter-lua
          tree-sitter-markdown
          tree-sitter-nix
          tree-sitter-python
          tree-sitter-rust
          tree-sitter-toml
          tree-sitter-typescript
          tree-sitter-yaml
          tree-sitter-zig
        ]
      ))
      use-package
      vertico
      vterm
      which-key
      eat
    ]
  );

  languageServers = with pkgs; [
    llvmPackages_21.clang-tools
    cmake-language-server
    mesonlsp
    llvmPackages_21.mlir
    nixd
  ];

  languageServerBinPath = pkgs.lib.makeBinPath languageServers;

  configDir = pkgs.lib.cleanSourceWith {
    name = "filc-emacs-config";
    src = ./.;
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
