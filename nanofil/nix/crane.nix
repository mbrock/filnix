# Crane (https://github.com/bloomberg/crane), Bloomberg's extraction of
# Rocq to C++, for the Gallina backend (rocq/backend/crane,
# docs/gallina-backend.md, M6). Pinned to one commit and patched
# (crane-nanofil.patch, whose parts the doc lists): Crane's own tree
# builds against Rocq 9.0, the backend against 9.1.
#
# Only the plugin and the four theory files the backend's extraction
# imports are built. $out/lib/coq/9.1/user-contrib/Crane goes on
# ROCQPATH and $out/lib/ocaml/site-lib on OCAMLPATH; the headers the
# extracted C++ includes are in $out/include.
{ pkgs }:
let
  coq = pkgs.coqPackages_9_1;
  ocamlPackages = coq.coq.ocamlPackages;
in
pkgs.stdenv.mkDerivation {
  pname = "rocq-crane";
  version = "0-unstable-c2aadd9";
  src = pkgs.fetchFromGitHub {
    owner = "bloomberg";
    repo = "crane";
    rev = "c2aadd996f86425a486a1343d9cf2a1f5c4ed334";
    sha256 = "13a9n608hjknbqkwzi4imwc4kv50z95f5d4l58p9813hazsyqf6w";
  };
  patches = [ ./crane-nanofil.patch ];
  nativeBuildInputs = [
    coq.coq
    ocamlPackages.ocaml
    ocamlPackages.findlib
    ocamlPackages.dune_3
  ];
  buildInputs = [ coq.stdlib ];
  # The theory's dune stanza names ITree, ExtLib and Paco, for files
  # that are not built here.
  postPatch = ''
    substituteInPlace theories/dune \
      --replace-fail "(theories Stdlib ITree ExtLib Paco)" "(theories Stdlib)"
  '';
  buildPhase = ''
    runHook preBuild
    dune build -j "$NIX_BUILD_CORES" src \
      theories/Extraction.vo theories/Mapping/Shared.vo theories/Mapping/Std.vo \
      theories/Mapping/NatIntStd.vo theories/Mapping/AsciiChar.vo
    runHook postBuild
  '';
  installPhase = ''
    runHook preInstall
    mkdir -p $out/lib/ocaml/site-lib $out/lib/coq/9.1/user-contrib/Crane $out/include
    cp -rL _build/install/default/lib/rocq-crane $out/lib/ocaml/site-lib/
    (cd _build/default/theories && find . -name '*.vo' -exec cp --parents {} $out/lib/coq/9.1/user-contrib/Crane/ \;)
    cp theories/cpp/*.h $out/include/
    runHook postInstall
  '';
  passthru = { inherit coq ocamlPackages; };
}
