{
  stdenv,
  curl,
  fetchurl,
}:
stdenv.mkDerivation {
  pname = "libmicrohttpd";
  version = "1.0.2";
  src = fetchurl {
    url = "mirror://gnu/libmicrohttpd/libmicrohttpd-1.0.2.tar.gz";
    hash = "sha256-3zJPzQg0F12rB0gxM5Atl3SmBb+imAJfaYgyiP0gqMc=";
  };
}
