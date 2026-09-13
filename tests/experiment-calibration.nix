{ pkgs, nonce }:
let
  mk =
    name: attrs:
    pkgs.stdenvNoCC.mkDerivation (
      {
        name = "filnix-calibration-${name}-${nonce}";
        dontUnpack = true;
        phases = [
          "configurePhase"
          "buildPhase"
          "checkPhase"
          "installPhase"
        ];
        configurePhase = "true";
        buildPhase = "echo calibration > proof";
        doCheck = true;
        checkPhase = "test -s proof";
        installPhase = "mkdir -p $out; cp proof $out/proof";
      }
      // attrs
    );
  bad = mk "bad-library" {
    configurePhase = "echo deliberate-calibration-failure >&2; exit 17";
  };
in
{
  good = mk "good" { buildPhase = "sleep 25; echo calibration > proof"; };
  inherit bad;
  dependent = mk "dependent" { buildInputs = [ bad ]; };
  sibling = mk "sibling" { buildInputs = [ bad ]; };
  slow = mk "slow" { buildPhase = "sleep 90; echo calibration > proof"; };
}
