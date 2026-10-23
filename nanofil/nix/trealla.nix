# Native Trealla at the revision filnix builds under Fil-C (ports.nix), for
# fast development runs. nixpkgs' Trealla predates native tabling.
{ pkgs }:
pkgs.trealla.overrideAttrs (old: {
  version = "unstable-2026-09-05";
  src = pkgs.fetchFromGitHub {
    owner = "trealla-prolog";
    repo = "trealla";
    rev = "12f4cbd7fc2269265e7306775ded2f6410671499";
    hash = "sha256-PL5RyiakGDyFLnoSiOS5/b2AoRNwqoG7W+ShYsNl5a4=";
  };
  patches = (old.patches or [ ]) ++ [
    ../../patches/trealla-filc-tabling-cursors.patch
    ../../patches/trealla-goal-expansion-share-cells.patch
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
