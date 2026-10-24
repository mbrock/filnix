# Native SWI-Prolog at the revision swipl-wasm is built from, so the
# playground's build (the frozen profile, the page's Prolog) and the
# browser run one SWI. Nixpkgs has 9.2.9; 10.1 is a development release,
# so it comes from swipl-devel.
{ pkgs }:
(pkgs.swi-prolog.override {
  withJava = false;
  withOdbc = false;
  withPython = false;
}).overrideAttrs
  (old: rec {
    version = "10.1.19";
    src = pkgs.fetchFromGitHub {
      owner = "SWI-Prolog";
      repo = "swipl-devel";
      tag = "V${version}";
      hash = "sha256-ngiyG61P9WxJfNF+CWIfG+pVTHOlXpOJV9zrlmGzYIY=";
      fetchSubmodules = true;
    };
    # 10.x's utf8proc package finds its library with pkg-config.
    nativeBuildInputs = old.nativeBuildInputs ++ [ pkgs.pkg-config ];
    buildInputs = old.buildInputs ++ [ pkgs.utf8proc ];
    # The 10.1 manual's doc2tex step fails here; the playground needs no manual.
    cmakeFlags = (old.cmakeFlags or [ ]) ++ [ "-DINSTALL_DOCUMENTATION=OFF" ];
  })
