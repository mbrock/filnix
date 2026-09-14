{ pkgs, pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-glib-gtype-check";
  dontUnpack = true;
  nativeBuildInputs = [ pkgs.pkg-config ];
  buildInputs = [ pkgsFilc.glib ];
  buildPhase = ''
    for version in 38 56 74 80; do
      for language in c c++; do
        compiler="$CC"
        if [ "$language" = c++ ]; then compiler="$CXX"; fi
        $compiler -x "$language" -Werror \
          -DGLIB_VERSION_MIN_REQUIRED=GLIB_VERSION_2_$version \
          -DGLIB_VERSION_MAX_ALLOWED=GLIB_VERSION_2_$version \
          ${./glib-gtype.c} $(pkg-config --cflags --libs gobject-2.0) -o check
        ./check
      done
    done
  '';
  installPhase = ''touch "$out"'';
}
