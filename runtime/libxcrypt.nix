{ base, sources, filc2, libpizlo, libmojo }:

{
  filc-xcrypt = base.stdenv.mkDerivation {
    pname = "filc-xcrypt";
    version = "4.4.36";
    src = "${sources.libxcrypt-src}/projects/libxcrypt-4.4.36";
    enableParallelBuilding = true;

    nativeBuildInputs = with base; [
      gnumake automake116x autoconf libtool binutils perl python3
    ];

    preConfigure = ''
      export CC="${filc2}/bin/clang -isystem ${libpizlo}/include -L${libmojo}/lib -I${libmojo}/include"

      rm -f aclocal.m4
      libtoolize --copy --force
      autoreconf -vfi -I build-aux/m4
    '';

    meta.description = "libxcrypt compiled with Fil-C";
  };
}
