{ pkgs, pkgsFilc }:
let
  grammars = pkgsFilc.emacsPackages.treesit-grammars.with-grammars (g: [
    g.tree-sitter-c
  ]);
in
pkgs.runCommand "filc-emacs-treesit-check" { } ''
  ${pkgsFilc.emacs30}/bin/emacs --batch \
    --eval '(setq treesit-extra-load-path (list "${grammars}/lib"))' \
    -l ${./emacs-treesit.el} > "$out"
  cat "$out"
''
