# This check builds GNU Hello and the user glibc it reaches with
# nanofil -O, together.  The mixed builder falls back to filcc on
# failure; this check forbids that, checks the exact unit set
# (including libc_nonshared's atexit), and verifies which libc the
# loader actually maps. The glibc it builds
# carries the Fil-C source fixes (mixed.nix's glibcPatches), so the
# regression programs run against it too: mem16 for the string units,
# locarch for the locale loader.
{
  pkgs,
  filcc,
}:
let
  # The 305 survey units plus atexit.oS and all 15 shared-libc siblings.
  # There are 321 distinct units, not 320: the sibling list has 15 entries.
  units = pkgs.writeText "hello-glibc-units.txt" (
    builtins.readFile ../survey/glibc/run/units.txt
    + ''
      io/fcntl_nocancel.os
      libio/iofgets_u.os
      libio/iofputws_u.os
      misc/mremap.os
      nptl/alloca_cutoff.os
      posix/sched_cpucount.os
      stdio-common/printf_buffer_puts_1.os
      stdlib/abs.os
      stdlib/atexit.oS
      stdlib/dbl2mpn.os
      stdlib/divrem.os
      stdlib/ldbl2mpn.os
      wcsmbs/mbsrtowcs.os
      wcsmbs/mbsrtowcs_l.os
      wcsmbs/wcsrtombs.os
      wcsmbs/wmemmove.os
    ''
  );
  inherit
    (import ../survey/glibc/mixed.nix {
      inherit units pkgs filcc;
      opt = "-O";
    })
    glibc
    ;
  nanofilSrc = pkgs.lib.fileset.toSource {
    root = ../.;
    fileset = pkgs.lib.fileset.unions [
      ../bin
      ../src
    ];
  };
  cc = import ./nanofil-cc.nix {
    inherit pkgs filcc;
    src = nanofilSrc;
  };
  src = pkgs.hello.src;
  runAll = ''
    invocations=(
      "" "-g x" "-t" "--version" "--help" "--bogus" "extra" "-g"
      "-g Grüße,_мир_→_世界" "--greeting=$(printf 'a%.0s' {1..300})"
      "-t -g ignored" "--traditional"
    )
    run_all() {
      for a in "''${invocations[@]}"; do
        echo "### hello $a"
        LC_ALL=C.UTF-8 ./hello $a 2>&1 && status=0 || status=$?
        echo "### exit $status"
      done
    }
  '';
  reference =
    pkgs.runCommandCC "nanofil-hello-glibc-reference" { inherit src; }
      ''
        ${runAll}
        mkdir ref $out
        tar -xf $src -C ref --strip-components=1
        cd ref
        CC=${filcc}/bin/clang ./configure --disable-nls >configure.log 2>&1 ||
          { cat configure.log; exit 1; }
        make -j$NIX_BUILD_CORES >make.log 2>&1 || { cat make.log; exit 1; }
        run_all >$out/ref.out
      '';
in
pkgs.runCommandCC "nanofil-hello-glibc" { inherit src; } ''
  mkdir $out
  cp ${glibc}/nanofil/compiled ${glibc}/nanofil/failed $out/
  sort -u ${units} >$out/units.txt
  sort -u $out/compiled >$out/compiled-unique
  diff -u $out/units.txt $out/compiled-unique
  test ! -s $out/failed || { cat $out/failed; exit 1; }
  test "$(wc -l <$out/compiled)" -eq 321
  test "$(wc -l <$out/units.txt)" -eq 321
  grep -qxF stdlib/atexit.oS $out/compiled
  echo "nanofil -O compiled all 321 glibc units, 0 failures"

  ${runAll}
  mkdir hello
  tar -xf $src -C hello --strip-components=1
  cd hello
  CC=${filcc}/bin/clang ./configure --disable-nls >configure.log 2>&1 ||
    { cat configure.log; exit 1; }
  export NANOFIL_OPT=-O NANOFIL_LOG=$PWD/nanofil.log
  # The wrapper's sysroot still finds the stock libc linker script.
  # Resolve atexit from the nanofil archive explicitly before that script.
  make -j$NIX_BUILD_CORES CC=${cc} LDFLAGS="-L${glibc}/lib -Wl,-t" \
    LIBS=${glibc}/lib/libc_nonshared.a >make.log 2>&1 ||
    { cat make.log; exit 1; }
  grep -F '${glibc}/lib/libc_nonshared.a(atexit.oS)' make.log | tee $out/nonshared-loaded ||
    { tail -80 make.log; exit 1; }
  objects=$(find . -name '*.o' | wc -l)
  compiled=$(sort -u nanofil.log | wc -l)
  echo "nanofil -O compiled $compiled of $objects Hello objects" | tee $out/hello-counts
  test "$objects" -gt 0 && test "$compiled" -eq "$objects"
  cp nanofil.log $out/hello-compiled

  export LD_LIBRARY_PATH=${glibc}/lib
  LD_DEBUG=libs ./hello >/dev/null 2>$out/loader.log
  grep -F '${glibc}/lib/libc.so' $out/loader.log | tee $out/loaded
  run_all >$out/nanofil.out
  diff -u ${reference}/ref.out $out/nanofil.out
  FUGC_SCRIBBLE=1 FUGC_VERIFY=1 run_all >$out/nanofil-gc.out
  diff -u ${reference}/ref.out $out/nanofil-gc.out
  echo "matches filcc on ''${#invocations[@]} invocations, plain and GC-verified"

  # The Fil-C source fixes, through this glibc's own libc.so: the
  # 16-byte string calls (its memcmp unit is nanofil's), and the locale
  # loader's harness, whose nine modes must all load or refuse cleanly
  # (regress.nix's locarch-stock holds the unpatched picture).
  ${filcc}/bin/clang -O1 -fno-builtin -o mem16 ${../survey/glibc/run/mem16.c}
  ${filcc}/bin/clang -O1 -fno-builtin -o locarch ${../survey/glibc/regress/locarch.c}
  ./mem16 >$out/mem16.out
  grep -q '^eq: 1 1 1$' $out/mem16.out && grep -q '^copies: 12 1 1 1$' $out/mem16.out ||
    { cat $out/mem16.out; exit 1; }
  modes="control archive-valid archive-loop archive-nonul archive-name-oob archive-locrec-oob archive-record-wrap file-idx-eof file-nonul"
  for m in $modes; do
    mkdir -p work/$m
    timeout 30 ./locarch ${glibc}/lib/locale work/$m $m >$out/locarch-$m.out 2>&1 ||
      { echo "locarch mode $m failed:"; cat $out/locarch-$m.out; exit 1; }
  done
  echo "mem16 and all 9 locarch modes clean against this glibc"
  make check CC=${cc} >$out/check.log 2>&1 ||
    { cat $out/check.log test-suite.log; exit 1; }
  FUGC_SCRIBBLE=1 FUGC_VERIFY=1 make check CC=${cc} >$out/check-gc.log 2>&1 ||
    { cat $out/check-gc.log test-suite.log; exit 1; }
  cat $out/check.log $out/check-gc.log
  echo "321 glibc units, $compiled/$objects Hello objects, 0 failures; 24 invocations, both make checks, mem16 and 9 locarch modes agree" |
    tee $out/verdict
''
