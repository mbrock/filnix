# These regression checks keep the Fil-C glibc source fixes honest; the
# fixes are the three patches in patches/
# (string/filc-glibc-string-pointers.patch and the two locale
# validation patches).  docs/zsys.md keeps the campaign notes.
#
#   nix build -L -f nanofil/survey/glibc/regress.nix units
#   nix build -L -f nanofil/survey/glibc/regress.nix locarch-stock
#   nix build -L -f nanofil/survey/glibc/regress.nix locarch
#
# units compiles string/memcmp.c and string/wordcopy.c out of the
# source tree, standalone, and links them into regress/driver.c: the
# units the stock glibc builds with trap under filcc at -O0 (the
# pointer-cast-to-long pattern loses the capability), the patched
# units pass.  The check is cheap, so CI runs it
# (.github/workflows/nanofil-glibc.yml).
#
# locarch-stock and locarch run regress/locarch.c against a glibc's
# own libc.so.  Each mode feeds the locale loader a crafted archive
# or category file; a patched loader refuses the corrupt ones cleanly
# while the stock one faults on them (or spins, on the full hash
# table).  locarch-stock runs against the staging toolchain's stock
# glibc, which the cache already has, so it is cheap and records the
# unpatched behaviour; locarch runs against the patched glibc that
# mixed.nix builds, which takes a while and stays by hand.  Pass
# glibc to point locarch at another patched build.
{
  repo ? ../../..,
  pkgs ? import (builtins.getFlake (toString repo)).inputs.nixpkgs {
    system = "x86_64-linux";
  },
  filcc ?
    (builtins.getFlake (toString repo)).packages.x86_64-linux.filcc-staging,
  # A patched glibc for locarch; the default is mixed.nix's build.
  glibc ? null,
}:
let
  # The stock glibc derivation's own source and patches (runtime/
  # filc-glibc.nix): take them from the derivation rather than
  # restating them, so the trees below are the toolchain's source and
  # differ from the stock build only by the three in patches/.
  stock = filcc.components.filc-glibc;
  src = stock.src;
  stockPatches = stock.patches;
  glibcPatches = [
    ./patches/filc-glibc-string-pointers.patch
    ./patches/filc-glibc-loadarchive-validate.patch
    ./patches/filc-glibc-loadlocale-validate.patch
  ];
  pristine = pkgs.applyPatches {
    name = "user-glibc-stock-patches";
    inherit src;
    patches = stockPatches;
  };
  patched = pkgs.applyPatches {
    name = "user-glibc-stock-plus-filc-patches";
    inherit src;
    patches = stockPatches ++ glibcPatches;
  };
  cc = "${filcc}/bin/clang";
  units = pkgs.runCommand "glibc-string-units-regression" { } ''
    cc=${filcc}/bin/clang
    mkdir -p $out
    # wordcopy.c includes glibc's internal memcopy.h (and its chain);
    # these five headers beside the unit are all it needs beyond the
    # installation headers, so <sys/cdefs.h> and friends resolve in
    # the filcc sysroot.
    mkinc() {
      rm -rf $2 && mkdir -p $2
      cp $1/include/libc-diag.h $1/sysdeps/generic/memcopy.h \
         $1/sysdeps/generic/pagecopy.h $1/sysdeps/generic/string-opthr.h \
         $1/sysdeps/generic/string-optype.h $2/
    }
    mkinc ${pristine} inc0
    mkinc ${patched} inc1
    memdefs=(-DHAVE_STRING_H -D__THROW= '-Dop_t=unsigned long int' -DOP_T_THRES=16
             '-Dlibc_hidden_builtin_def(x)=' '-Dlibc_hidden_def(x)='
             '-Dweak_alias(a,b)=' '-Dstrong_alias(a,b)=' -Wno-pointer-sign)
    wcdefs=(-D__THROW= '-Dlibc_hidden_builtin_def(x)=' '-Dlibc_hidden_def(x)='
            '-Dweak_alias(a,b)=' '-Dstrong_alias(a,b)=' '-Dattribute_hidden='
            -Wno-pointer-sign)
    build() { # inc tree tag optlevel
      $cc "''${memdefs[@]}" -O$4 -c $2/string/memcmp.c -o memcmp-$3.o
      $cc "''${wcdefs[@]}" -I$1 -O$4 -c $2/string/wordcopy.c -o wordcopy-$3.o
    }
    build inc0 ${pristine} pristine 0
    build inc1 ${patched} patched 0
    build inc1 ${patched} patched-o2 2
    $cc -O1 -fno-builtin -c ${./regress/driver.c} -o driver.o
    $cc driver.o memcmp-pristine.o wordcopy-pristine.o -o test-pristine
    $cc driver.o memcmp-patched.o wordcopy-patched.o -o test-patched
    $cc driver.o memcmp-patched-o2.o wordcopy-patched-o2.o -o test-patched-o2
    : >$out/matrix
    echo "### stock units at -O0: must fail filc's checks" | tee -a $out/report
    status=0
    ./test-pristine >pristine.out 2>&1 || status=$?
    printf 'stock -O0: exit %s\n' "$status" | tee -a $out/matrix
    if [ "$status" -eq 0 ]; then
      echo "stock units passed; the check no longer catches the bug" >&2
      exit 1
    fi
    grep -q "filc safety error" pristine.out || {
      echo "stock units failed without a filc check:" >&2; cat pristine.out >&2; exit 1; }
    for t in test-patched test-patched-o2; do
      ./$t >$t.out 2>&1
      grep -q "all checks passed" $t.out || { cat $t.out >&2; exit 1; }
      printf 'patched %s: exit 0, all checks passed\n' \
        "''${t#test-patched}" | tee -a $out/matrix
    done
    cp pristine.out test-patched.out test-patched-o2.out $out/
  '';
  # locarch.c's modes, run one per process against one glibc's own
  # libc.so.  The binary links against the stock toolchain, so the run
  # must swap in the library under test: LD_LIBRARY_PATH points the
  # loader at it before the binary's RUNPATH (mixed.nix's check does
  # the same), and the check verifies with LD_DEBUG that the intended
  # libc.so was really mapped, so it can never silently test the
  # stock one (which is what passing the locale dir alone would do:
  # locarch's arguments choose the crafted files, but the loader
  # comes from whichever libc.so the process runs).  For the stock
  # glibc the corrupt modes must not exit zero (its loader traps or
  # spins on them, or loads one wrongly, which the harness reports
  # as exit 1); for a patched glibc every mode must exit zero, the
  # corrupt ones by refusing the load.  The two valid modes must agree
  # on the monetary values under either.
  locarchModes = "control archive-valid archive-loop archive-nonul archive-name-oob archive-locrec-oob archive-record-wrap file-idx-eof file-nonul";
  runLocarch = libdir: lib: corruptExpect: ''
    mkdir -p $out work
    ${cc} -O1 -fno-builtin -o locarch ${./regress/locarch.c}
    LD_LIBRARY_PATH=${lib} LD_DEBUG=libs ./locarch ${libdir} x control \
      >/dev/null 2>loaded.log || true
    grep -q '${lib}/libc.so' loaded.log || {
      echo "the loader did not map ${lib}/libc.so:" >&2
      grep 'libc.so' loaded.log >&2
      exit 1; }
    corrupt="archive-loop archive-nonul archive-name-oob archive-locrec-oob archive-record-wrap file-idx-eof file-nonul"
    : >$out/matrix
    for m in ${locarchModes}; do
      rm -rf work/$m && mkdir -p work/$m
      status=0
      LD_LIBRARY_PATH=${lib} timeout 30 ./locarch ${libdir} work/$m $m >$out/$m.out 2>&1 || status=$?
      case " $corrupt " in *" $m "*) expect=${corruptExpect} ;; *) expect=ok ;; esac
      verdict=ok
      if { [ "$expect" = ok ] && [ "$status" -ne 0 ]; } ||
         { [ "$expect" = fail ] && [ "$status" -eq 0 ]; }; then
        verdict=BAD
      fi
      printf '%-22s expected %-4s exit %-3s %s\n' "$m" "$expect" "$status" "$verdict" \
        | tee -a $out/matrix
      [ "$verdict" = ok ] || echo "$m" >>$out/failed
    done
    test ! -s $out/failed || { echo "modes failed: $(cat $out/failed)"; exit 1; }
    # The valid archive and the control tree must agree on the values.
    c=$(grep -o 'monetary: .*' $out/control.out || true)
    a=$(grep -o 'monetary: .*' $out/archive-valid.out || true)
    test -n "$c" -a "$c" = "$a" || {
      echo "valid archive loaded different values: '$c' vs '$a'"; exit 1; }
  '';
  patchedGlibc =
    if glibc != null then glibc else (import ./mixed.nix { inherit pkgs filcc; }).glibc;
in
{
  inherit units;
  locarch-stock = pkgs.runCommand "glibc-locarch-stock" { }
    (runLocarch "${stock}/lib/locale" "${stock}/lib" "fail");
  locarch = pkgs.runCommand "glibc-locarch-patched" { }
    (runLocarch "${patchedGlibc}/lib/locale" "${patchedGlibc}/lib" "ok");
}
