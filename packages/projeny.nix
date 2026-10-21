{
  lib,
  stdenv,
  fetchgit,
  makeWrapper,
  coreutils,
  gnutar,
  gzip,
  bzip2,
  xz,
  zstd,
  curl,
  git,
  patch,
  python3,
}:
let
  upstream = builtins.fromJSON (builtins.readFile ../ports/upstream.json);
in
stdenv.mkDerivation {
  pname = "projeny";
  version = "0-unstable-${builtins.substring 0 12 upstream.projenyRev}";
  src = fetchgit {
    name = "projeny-src";
    url = "https://github.com/pizlonator/fil-c";
    rev = upstream.projenyRev;
    sparseCheckout = [ "/projects/projeny/" ];
    nonConeMode = true;
    hash = upstream.projenyHash;
  };
  sourceRoot = "projeny-src/projects/projeny";
  nativeBuildInputs = [ makeWrapper ];
  # URL: headers are downloaded with libcurl.
  buildInputs = [ curl ];
  nativeCheckInputs = [
    git
    patch
    gnutar
    gzip
    bzip2
    xz
    zstd
    python3
  ];
  enableParallelBuilding = true;
  # The test harness keeps command output in a shell variable named `out`;
  # exported, as Nix exports it, a large diff overflowed every child's
  # environment (E2BIG).
  preCheck = ''
    patchShebangs tests
    export -n out
  '';
  postCheck = "export out";
  doCheck = true;
  checkTarget = "test";
  installPhase = ''
    runHook preInstall
    install -Dm755 projeny $out/bin/projeny
    wrapProgram $out/bin/projeny --prefix PATH : ${
      lib.makeBinPath [
        coreutils
        gnutar
        gzip
        bzip2
        xz
        zstd
      ]
    }
    runHook postInstall
  '';
  meta = {
    description = "Project tarball and patch manager from Fil-C";
    homepage = "https://github.com/pizlonator/fil-c/tree/deluge/projects/projeny";
    license = lib.licenses.bsd2;
    mainProgram = "projeny";
    platforms = lib.platforms.unix;
  };
}
