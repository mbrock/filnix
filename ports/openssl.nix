# Simple OpenSSL build for Fil-C
# Based on the upstream fil-c build script, avoiding nixpkgs complexity
{ lib, fetchurl, perl, stdenv, zlib }:

stdenv.mkDerivation rec {
  pname = "openssl";
  version = "3.3.1";

  src = fetchurl {
    url = "https://www.openssl.org/source/openssl-${version}.tar.gz";
    hash = "sha256-d3zVlihMiDN1oqehG/XSeG/FQTJV76sgxQ1v/m0CC34=";
  };

  patches = [ ./patch/openssl-3.3.1.patch ];

  outputs = [ "out" "dev" "bin" ];
  setOutputFlags = false;  # Don't let stdenv add --bindir/--libdir flags

  nativeBuildInputs = [perl];
  buildInputs = [zlib];

  postPatch = ''
    patchShebangs Configure config
  '';

  # OpenSSL uses a custom configure system, not autotools
  # Disable automatic platform flag generation
  configurePlatforms = [];
  dontAddStaticConfigureFlags = true;

  # OpenSSL's config script does platform detection
  configureScript = "./config";

  configureFlags = [
    "zlib"
    "--prefix=${placeholder "out"}"
    "--libdir=lib"
  ];

  enableParallelBuilding = true;

  doCheck = false;

  # Use install_sw (software only, no docs) and install_ssldirs
  installTargets = [ "install_sw" "install_ssldirs" ];

  postInstall = ''
    # Move binaries to separate output
    mkdir -p $bin
    mv $out/bin $bin/bin

    # Move headers to dev output
    mkdir -p $dev
    mv $out/include $dev/

    # Remove perl scripts we don't need
    rm -rf $out/etc/ssl/misc
  '';

  meta = with lib; {
    description = "Cryptographic library (SSL/TLS) - Fil-C build";
    homepage = "https://www.openssl.org/";
    license = licenses.openssl;
    platforms = platforms.unix;
  };
}
