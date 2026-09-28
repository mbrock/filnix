# tree-sitter's CLI is Rust, which has no Fil-C target. Consumers such as
# Emacs only link the C runtime library, which the Makefile builds on its own.
# Nixpkgs' passthru stays, so the grammar set and its builders are unchanged.
{
  lib,
  stdenv,
  tree-sitter,
}:

stdenv.mkDerivation {
  pname = "tree-sitter";
  inherit (tree-sitter) version src passthru;

  makeFlags = [ "PREFIX=${placeholder "out"}" ];

  # Only the descriptive fields: the rest of the CLI's meta is computed from
  # the Rust build (problems, availability) and does not apply here.
  meta = lib.filterAttrs (
    name: _:
    lib.elem name [
      "description"
      "longDescription"
      "homepage"
      "changelog"
      "license"
      "maintainers"
      "teams"
      "platforms"
    ]
  ) tree-sitter.meta;
}
