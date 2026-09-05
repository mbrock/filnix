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
  git,
  patch,
  python3,
}:
let
  upstream = builtins.fromJSON (builtins.readFile ../ports/upstream.json);
in
stdenv.mkDerivation {
  pname = "projeny";
  version = "0-unstable-${builtins.substring 0 12 upstream.portsRev}";
  src = fetchgit {
    name = "projeny-src";
    url = "https://github.com/pizlonator/fil-c";
    rev = upstream.portsRev;
    sparseCheckout = [ "/projects/projeny/" ];
    nonConeMode = true;
    hash = upstream.projenyHash;
  };
  sourceRoot = "projeny-src/projects/projeny";
  nativeBuildInputs = [ makeWrapper ];
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
  preCheck = "patchShebangs tests";
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
