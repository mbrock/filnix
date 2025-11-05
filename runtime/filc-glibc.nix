{
  pkgs,
  filc,
  libpizlo,
}:

let
  sources = import ../lib/sources.nix { inherit pkgs; };
in

{
  # Memory-safe glibc compiled with Fil-C
  filc-glibc = pkgs.stdenv.mkDerivation {
    pname = "filc-glibc";
    version = "2.40";
    src = "${sources.user-glibc-src}/projects/user-glibc-2.40";
    outputs = [ "out" ];

    enableParallelBuilding = true;

    nativeBuildInputs = with pkgs; [
      gnumake
      autoconf
      bison
      python3
      binutils
      glibc.dev
    ];

    preConfigure = ''
      # Fil-C compiler flags from build script
      FILCXXFLAGS="-nostdlibinc -Wno-ignored-attributes -Wno-pointer-sign"
      FILCFLAGS="$FILCXXFLAGS -Wno-unused-command-line-argument -Wno-macro-redefined"

      export CC="${filc}/bin/clang $FILCFLAGS -isystem ${libpizlo}/include"
      export CXX="${filc}/bin/clang++ $FILCXXFLAGS -isystem ${libpizlo}/include"

      # glibc requires out-of-tree build
      autoconf
      cd ..
      mkdir -p build
      cd build
      configureScript=$PWD/../$sourceRoot/configure

      # Set these in shell so $out actually expands
      configureFlagsArray+=(
        "libc_cv_slibdir=$out/lib"
      )
    '';

    configureFlags = [
      "--disable-mathvec"
      "--disable-nscd"
      "--disable-werror"
      "--with-headers=${pkgs.linuxHeaders}/include"
    ];

    meta.description = "Memory-safe glibc compiled with Fil-C";
  };
}
