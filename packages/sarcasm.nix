{ pkgs }:
let
  sources = import ../lib/sources.nix { inherit pkgs; };
  minilute = import ./minilute.nix { inherit pkgs; };
in
pkgs.stdenvNoCC.mkDerivation {
  pname = "sarcasm";
  version = "0-unstable-${builtins.substring 0 12 sources.coreRev}";
  src = sources.sarcasm-src;
  sourceRoot = "sarcasm-src/projects/sarcasm";
  nativeBuildInputs = [ pkgs.makeWrapper ];
  dontBuild = true;
  installPhase = ''
    runHook preInstall
    mkdir -p $out/bin $out/lib
    ln -s ${minilute}/bin/minilute $out/bin/minilute
    sh install.sh $out
    wrapProgram $out/bin/sarcasm --add-flags "--as ${pkgs.binutils-unwrapped}/bin/as"
    $out/bin/sarcasm --version
    runHook postInstall
  '';
  passthru = { inherit minilute; };
  meta = {
    description = "Fil-C capability-enforced assembler";
    homepage = "https://github.com/pizlonator/fil-c/tree/deluge/projects/sarcasm";
    license = pkgs.lib.licenses.bsd2;
    mainProgram = "sarcasm";
    platforms = [ "x86_64-linux" ];
  };
}
