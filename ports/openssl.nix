{
  lib,
  fetchurl,
  perl,
  stdenv,
  zlib,
  withSafeAssembly ? false,
  ...
}:

stdenv.mkDerivation rec {
  pname = "openssl";
  version = "3.5.7";

  src = fetchurl {
    url = "https://www.openssl.org/source/openssl-${version}.tar.gz";
    hash = "sha256-qMDSilKcpID582z1eS4s0hmEVSo8jkqhGiSqMa6smOg=";
  };

  patches = [
    ./patch/openssl-3.5.7.patch
  ];

  outputs = [
    "out"
    "dev"
    "bin"
    # "man"
  ];
  setOutputFlags = false; # Don't let stdenv add --bindir/--libdir flags

  nativeBuildInputs = [ perl ];
  buildInputs = [ zlib ];

  postPatch = ''
    patchShebangs Configure config
  '';

  configurePlatforms = [ ];
  dontAddStaticConfigureFlags = true;
  configureScript = "./config";

  # The older port uses runtime forwarders into ordinary assembly.
  configureFlags = lib.optional (!withSafeAssembly) "-yolo-assembler" ++ [
    "shared"
    "zlib"
    "--prefix=${placeholder "out"}"
    "--openssldir=etc/ssl"
    "--libdir=lib"
    "--with-zlib-lib=${zlib}/lib"
    "--with-zlib-include=${zlib}/include"
  ];

  # makeFlags = [
  #   "MANDIR=$(man)/share/man"
  #   "MANSUFFIX=ssl"
  # ];

  enableParallelBuilding = true;

  doCheck = false;

  # skip man pages, takes a long time and you already have them
  installTargets = [
    "install_sw"
    "install_ssldirs"
  ];

  postInstall = ''
    mkdir -p $bin
    mv $out/bin $bin/bin

    mkdir -p $dev
    mv $out/include $dev/

    rm -rf $out/etc/ssl/misc
    rmdir $out/etc/ssl/{certs,private}
    rm -rf $dev/lib/cmake
  '';

  meta = with lib; {
    description = "Cryptographic library (SSL/TLS) - Fil-C build";
    homepage = "https://www.openssl.org/";
    license = licenses.asl20;
    mainProgram = "openssl";
    platforms = platforms.unix;
  };
}
