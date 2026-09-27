# The Fil-C compiler and bintools wrappers must not share a role salt with
# the native ones. When they did, both wrappers accepted both roles' flags:
# a native zlib in nativeBuildInputs came first in Fil-C links (undefined
# pizlonated_deflate), and Fil-C's zlib reached native links.
{ pkgsFilc }:
pkgsFilc.callPackage (
  {
    stdenv,
    buildPackages,
    zlib,
  }:
  stdenv.mkDerivation {
    name = "filc-wrapper-roles-check";
    dontUnpack = true;
    depsBuildBuild = [ buildPackages.stdenv.cc ];
    # Spliced: the build platform's zlib here, Fil-C's in buildInputs.
    nativeBuildInputs = [ zlib ];
    buildInputs = [ zlib ];
    buildPhase = ''
      [ "${stdenv.cc.suffixSalt}" != "${buildPackages.stdenv.cc.suffixSalt}" ]
      [ "${stdenv.cc.suffixSalt}" = "${stdenv.cc.bintools.suffixSalt}" ]
      cat > z.c <<'C'
      #include <stdio.h>
      #include <zlib.h>
      int main(void) {
        unsigned char out[64];
        unsigned long len = sizeof out;
        if (compress(out, &len, (const unsigned char *)"hello", 5) != Z_OK)
          return 1;
        printf("%s %lu\n", zlibVersion(), len);
        return 0;
      }
      C
      $CC z.c -lz -o z-filc
      ./z-filc
      $CC_FOR_BUILD z.c -lz -o z-native
      ./z-native
      # Each program must load its own platform's zlib.
      readelf -d z-filc | grep -q 'libc.so.6666'
      ! readelf -d z-native | grep -q 'libc.so.6666'
    '';
    installPhase = ''
      touch "$out"
    '';
  }
) { }
