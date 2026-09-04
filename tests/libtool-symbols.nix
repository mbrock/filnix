# Exercise the installed compiler setup hook and real libtool probes, including
# configure generated in preConfigure rather than shipped in a source archive.
{ pkgs, filcc }:

(pkgs.overrideCC pkgs.stdenv filcc).mkDerivation {
  name = "filc-libtool-symbols-test";
  dontUnpack = true;
  nativeBuildInputs = [
    pkgs.autoconf
    pkgs.automake
    pkgs.libtool
  ];
  configureFlags = [ "--enable-static" ];

  preConfigure = ''
    cat > configure.ac <<'ACEOF'
    AC_INIT([filc-symbol-test], [1])
    AC_CONFIG_SRCDIR([probe.c])
    AC_PROG_CC
    LT_INIT([dlopen])
    AC_OUTPUT
    ACEOF
    cat > probe.c <<'CEOF'
    int nm_test_var = 42;
    int nm_test_func(void) { return nm_test_var; }
    CEOF
    cat > main.c <<'CEOF'
    int nm_test_func(void);
    int main(void) { return nm_test_func() != 42; }
    CEOF
    autoreconf -vfi
    cp -p configure configure.pristine
    # Also exercise discovery of bundled configure scripts and mtime retention.
    mkdir nested
    cp -p configure nested/configure
    touch -r configure configure.timestamp
  '';

  buildPhase = ''
    runHook preBuild
    test "$(stat -c %Y configure)" = "$(stat -c %Y configure.timestamp)"
    grep 'for ac_symprfx in "pizlonated_"; do' nested/configure
    # The hook is inert when this compiler is only a build-time dependency.
    mkdir native
    cp configure.pristine native/configure
    (cd native; NIX_CC=${pkgs.stdenv.cc} filcFixLibtoolSymbols)
    cmp configure.pristine native/configure
    # Honor configureScript when preConfigure has left the source directory.
    mkdir separate-build
    (cd separate-build; configureScript=../native/configure filcFixLibtoolSymbols)
    grep 'for ac_symprfx in "pizlonated_"; do' native/configure
    sha256sum native/configure > before.sha256
    (cd separate-build; configureScript=../native/configure filcFixLibtoolSymbols)
    sha256sum -c before.sha256
    ./libtool --config > libtool.config
    source libtool.config
    test -n "$global_symbol_pipe"
    $CC -c probe.c -o probe.o
    $NM probe.o > raw-symbols
    grep ' pizlonated_nm_test_func$' raw-symbols
    grep ' pizlonatedFI[0-9]*_nm_test_func$' raw-symbols
    eval "$NM probe.o | $global_symbol_pipe" > symbols
    grep ' pizlonated_nm_test_func nm_test_func$' symbols
    grep ' pizlonated_nm_test_var nm_test_var$' symbols
    ! grep -E 'pizlonated(FI|FIP|[12]ET)' symbols
    eval "$global_symbol_to_cdecl < symbols" > declarations.c
    grep 'extern int nm_test_func();' declarations.c
    ! grep pizlonated declarations.c
    $CC -c declarations.c

    ./libtool --mode=compile $CC -c probe.c -o probe.lo
    ./libtool --mode=link $CC -o libprobe.la probe.lo -rpath "$out/lib"
    ./libtool --mode=link $CC -o probe main.c -dlpreopen libprobe.la
    ./probe
    ./libtool --mode=link $CC -o libexport.la probe.lo \
      -rpath "$out/lib" -export-symbols-regex '^nm_test_'
    $NM -D .libs/libexport.so | grep ' pizlonated_nm_test_func$'
    ./libtool --mode=link $CC -o exported-probe main.c libexport.la
    ./exported-probe
    # Raw nm retains its CLI semantics, including failures.
    if $NM missing.o; then
      echo 'nm accepted a missing object' >&2
      exit 1
    fi
    runHook postBuild
  '';

  installPhase = ''
    mkdir -p $out
    cp config.log libtool.config raw-symbols symbols declarations.c $out/
  '';
}
