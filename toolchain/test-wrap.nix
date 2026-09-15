# A package-local compiler adapter; the shared compiler derivation is unchanged.
{ pkgs }:
old: {
  preConfigure = (old.preConfigure or "") + ''
    export FILNIX_WRAP_CC="$CC"
    export FILNIX_WRAP_NM=${pkgs.binutils}/bin/nm
    export FILNIX_WRAP_OBJCOPY=${pkgs.binutils}/bin/objcopy
    export CC="${pkgs.python3}/bin/python3 ${./filc-test-wrap.py}"
  '';
}
