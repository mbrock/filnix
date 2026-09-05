{ pkgs }:
let
  sources = import ../lib/sources.nix { inherit pkgs; };
in
pkgs.stdenv.mkDerivation {
  pname = "minilute";
  version = "0-unstable-${builtins.substring 0 12 sources.coreRev}";
  src = sources.minilute-src;
  sourceRoot = "minilute-src/projects/minilute";
  # Luau is a sibling of sourceRoot and builds in place.
  postUnpack = "chmod -R u+w minilute-src/projects/lute-1.0.0";
  enableParallelBuilding = true;
  doCheck = true;
  checkPhase = ''
    runHook preCheck
    ./minilute tests/smoke.luau
    runHook postCheck
  '';
  installPhase = ''
    runHook preInstall
    install -Dm755 minilute $out/bin/minilute
    runHook postInstall
  '';
  meta = {
    description = "Minimal Luau runtime for the Fil-C assembler";
    homepage = "https://github.com/pizlonator/fil-c/tree/deluge/projects/minilute";
    license = with pkgs.lib.licenses; [
      bsd2
      mit
    ];
    mainProgram = "minilute";
    platforms = [ "x86_64-linux" ];
  };
}
