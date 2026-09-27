# glibmm runtime check for both API series (2.4 and 2.68): a derived
# object type with a property and signal, GValue boxing, variants, wrap()
# and a Gio list model, exercising glibmm over pointer-valued GTypes.
{ pkgs, pkgsFilc }:
let
  check =
    glibmm: module:
    pkgsFilc.stdenv.mkDerivation {
      name = "filc-${module}-runtime-check";
      dontUnpack = true;
      nativeBuildInputs = [ pkgs.pkg-config ];
      buildInputs = [ glibmm ];
      buildPhase = ''
        $CXX -std=c++17 ${./glibmm/glibmm-runtime.cc} \
          $(pkg-config --cflags --libs ${module}) -o glibmm-check
        ./glibmm-check | tee result
      '';
      installPhase = ''cp result "$out"'';
    };
in
{
  glibmm = check pkgsFilc.glibmm "giomm-2.4";
  glibmm_2_68 = check pkgsFilc.glibmm_2_68 "giomm-2.68";
}
