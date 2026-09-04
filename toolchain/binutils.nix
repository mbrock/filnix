{ pkgs }:

# Fil-C binutils includes djb's BFD demangler change from:
# https://cr.yp.to/2025/20251030-filian-install-compiler.sh
# It strips pizlonated_ during demangling (e.g. nm -C), unless
# FILC_PRESERVE_PREFIX is set. Plain nm still reports the real ELF names;
# libtool's ABI adaptation lives in the compiler setup hook instead.
#
# Version scripts are passed through Fil-C's Clang driver by wrappers.nix.
# The separate binutils-version-script-depizlonation.patch is not applied.

pkgs.binutils-unwrapped.overrideAttrs (old: rec {
  version = "2.43.1";
  src = pkgs.fetchurl {
    url = "mirror://gnu/binutils/binutils-${version}.tar.bz2";
    hash = "sha256-vsqsXSleA3WHtjpC+tV/49nXuD9HjrJLZ/nuxdDxhy8=";
  };
  patches = (old.patches or [ ]) ++ [
    # I split this up into two patches just for clarity
    # and for testing various things, but we just apply both
    # now anyway.
    ../patches/binutils-version-script.patch
    ../patches/binutils-other-fixes.patch
    ../patches/binutils-pizlonated-demangle.patch

  ];

  nativeBuildInputs =
    old.nativeBuildInputs
    ++ (with pkgs; [
      texinfo
      autoconf269
      automake
      libtool
      gettext
    ]);

  # The patch changes some .am files so we need to autoreconf.
  # I do it just in the affected directories cuz I had some issues
  # autoreconfing everything.
  preConfigure = ''
    for i in libctf libsframe; do
      pushd $(dirname $i)
      autoreconf -vfi
      popd
    done
    for i in {binutils,gas,ld,gold}/Makefile.in; do
      sed -i "$i" -e 's|ln |ln -s |'
    done
    configureScript="$PWD/configure"
    mkdir $NIX_BUILD_TOP/build
    cd $NIX_BUILD_TOP/build
  '';

  configureFlags = old.configureFlags ++ [
    "--enable-gold=default"
  ];
})
