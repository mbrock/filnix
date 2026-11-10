# Native Trealla at the revision filnix builds under Fil-C (ports.nix), for
# fast development runs. nixpkgs' Trealla predates native tabling.
{ pkgs }:
pkgs.trealla.overrideAttrs (old: {
  version = "unstable-2026-11-10";
  src = pkgs.fetchFromGitHub {
    owner = "trealla-prolog";
    repo = "trealla";
    rev = "98a821db66715618e358c36c7d7164213c0f6820";
    hash = "sha256-kU3Vgtk7Ni7nYVJ/ii++EForHclMh1WrQpyNYKgpqmQ=";
  };
  patches = (old.patches or [ ]) ++ [
    ../../patches/trealla-filc-tabling-cursors.patch
    ../../patches/trealla-goal-expansion-share-cells.patch
    ../../patches/trealla-heap-page-mark.patch
  ];
  postPatch = builtins.replaceStrings [ "Makefile" ] [ "GNUmakefile" ] (
    old.postPatch or ""
  );
  makeFlags = (old.makeFlags or [ ]) ++ [
    "LIBDIR=$(out)/share/trealla"
  ];
  postInstall = (old.postInstall or "") + ''
    mkdir -p $out/share/trealla/library
    find library -name '*.pl' -exec cp --parents -t $out/share/trealla {} +
  '';
  doCheck = false;
})
