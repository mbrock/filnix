# The Murrine GTK 2 theme engine as Nixpkgs 26.05 packaged it; 26.11 removed
# it with GTK 2's other consumers. tests/gtk2-runtime.nix loads it as a module.
{
  lib,
  stdenv,
  fetchurl,
  pkg-config,
  intltool,
  gtk2,
}:

stdenv.mkDerivation (finalAttrs: {
  pname = "gtk-engine-murrine";
  version = "0.98.2";

  src = fetchurl {
    url = "mirror://gnome/sources/gtk-engine-murrine/${lib.versions.majorMinor finalAttrs.version}/gtk-engine-murrine-${finalAttrs.version}.tar.xz";
    sha256 = "129cs5bqw23i76h3nmc29c9mqkm9460iwc8vkl7hs4xr07h8mip9";
  };

  patches = [
    # add prototypes to fix gcc-14 implicit-function-declaration errors
    ./missing-prototypes.diff
  ];

  strictDeps = true;
  nativeBuildInputs = [
    pkg-config
    intltool
  ];
  buildInputs = [ gtk2 ];

  meta = {
    description = "Very flexible theme engine";
    homepage = "https://gitlab.gnome.org/Archive/murrine";
    license = lib.licenses.lgpl3;
    platforms = lib.platforms.linux;
  };
})
