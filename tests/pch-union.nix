# Records that contain a union keep Fil-C's union handling when they come from
# a precompiled header. Clang did not serialize RecordDecl's HasUnion bit, so
# std::string temporaries lost their zhas_union markers under a PCH; SROA
# then split a literal copy into a misaligned pointer load that trapped
# (Nix's unit tests, which build with a PCH). The C case writes a plain C
# record with a union through the PCH record abbreviation.
{ pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-pch-union-check";
  dontUnpack = true;
  buildPhase = ''
    cp ${./pch-union}/* .
    $CXX -std=c++23 -O3 -x c++-header loc.hh -o loc.hh.pch
    $CXX -std=c++23 -O3 -include-pch loc.hh.pch loc.cc -o loc
    ./loc | tee loc.log
    grep -qx 'BuildResultJSON ../build-result.cc:41' loc.log

    $CC -O2 -x c-header rep.h -o rep.h.pch
    $CC -O2 -include-pch rep.h.pch rep.c -o rep
    ./rep | grep -qx '../build-result.cc'
  '';
  installPhase = ''
    touch "$out"
  '';
}
