{ pkgs }:

# Patched binutils that strips pizlonated_ prefix from symbols
#
# Fil-C mangles all symbols by prepending "pizlonated_" for memory safety.
# This causes issues with version scripts in shared libraries:
#
# Version scripts declare symbols like "malloc" and "free", but at link
# time the actual symbols are "pizlonated_malloc" and "pizlonated_free",
# causing version script matching to fail.
#
# Two solutions exist:
# 1. Filip's approach: Add --version-script= to clang driver to mangle
#    version scripts automatically (requires patching build systems)
# 2. djb's approach: Patch binutils to strip "pizlonated_" when demangling
#    symbols (transparent, works with unmodified version scripts)
#
# djb's patch from: https://cr.yp.to/2025/20251030-filian-install-compiler.sh
#
# We use Filip's approach for now.

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
    ../binutils-version-script.patch
    ../binutils-other-fixes.patch
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
