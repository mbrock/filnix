# tree-sitter's CLI is Rust, which has no Fil-C target. Consumers such as
# Emacs only link the C runtime library, which the Makefile builds on its own.
# Nixpkgs' passthru stays, so the grammar set and its builders are unchanged.
{
  stdenv,
  tree-sitter,
}:

stdenv.mkDerivation {
  pname = "tree-sitter";
  inherit (tree-sitter) version src passthru;

  makeFlags = [ "PREFIX=${placeholder "out"}" ];

  meta = removeAttrs tree-sitter.meta [
    "mainProgram"
    "broken"
    "badPlatforms"
  ];
}
