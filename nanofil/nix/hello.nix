# GNU hello built entirely by nanofil, then its own test suite.
#
# configure runs with filcc, so feature detection is clang's. make then
# runs with CC=nanofil-cc: every `-c` compile is preprocessed by filcc
# with make's flags, compiled by nanofil and assembled by GNU as; only
# the final link uses filcc. The check fails unless every object came
# from nanofil, and runs `make check` plainly and under FUGC_SCRIBBLE
# and FUGC_VERIFY, once with nanofil's middle end off and once with -O.
{ pkgs, filcc }:
pkgs.runCommandCC "nanofil-hello"
  {
    nativeBuildInputs = [ pkgs.swi-prolog ];
    src = pkgs.hello.src;
  }
  ''
    cp -r ${../.} nanofil
    chmod -R u+w nanofil
    patchShebangs nanofil/bin
    nanofil=$PWD/nanofil/bin/nanofil

    cat >nanofil-cc <<EOF
    #!${pkgs.runtimeShell}
    # A compile (-c of one .c file) goes through nanofil; anything else
    # (linking) goes to filcc unchanged.
    set -eu
    out= src= compile= args=()
    while [ \$# -gt 0 ]; do
      case \$1 in
        -c) compile=1 ;;
        -o) out=\$2; shift ;;
        *.c) src=\$1; args+=("\$1") ;;
        *) args+=("\$1") ;;
      esac
      shift
    done
    if [ -z "\$compile" ] || [ -z "\$src" ]; then
      exec ${filcc}/bin/clang "\''${args[@]}" \''${out:+-o "\$out"}
    fi
    : "\''${out:=\''${src%.c}.o}"
    ${filcc}/bin/clang "\''${args[@]}" -E -o "\$out.i"
    $nanofil \''${NANOFIL_OPT:-} cc "\$out.i" </dev/null >"\$out.s"
    as -o "\$out" "\$out.s"
    rm "\$out.i" "\$out.s"
    echo "\$out" >>"\$NANOFIL_LOG"
    EOF
    chmod +x nanofil-cc

    # The reference: the same hello built by filcc alone. Its test suite
    # is small, so every build is also compared with the reference on
    # these invocations (stdout, stderr and exit status).
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
    mkdir ref
    tar -xf $src -C ref --strip-components=1
    (
      cd ref
      CC=${filcc}/bin/clang ./configure --disable-nls >configure.log 2>&1 ||
        { cat configure.log; exit 1; }
      make -j$NIX_BUILD_CORES >make.log 2>&1 || { cat make.log; exit 1; }
      run_all >../ref.out
    )

    for opt in "" -O; do
      echo "== GNU hello, nanofil $opt"
      rm -rf hello && mkdir hello
      tar -xf $src -C hello --strip-components=1
      (
        cd hello
        CC=${filcc}/bin/clang ./configure --disable-nls >configure.log 2>&1 ||
          { cat configure.log; exit 1; }
        export NANOFIL_OPT=$opt NANOFIL_LOG=$PWD/nanofil.log
        make -j$NIX_BUILD_CORES CC=$PWD/../nanofil-cc
        objects=$(find . -name '*.o' | wc -l)
        compiled=$(sort -u nanofil.log | wc -l)
        echo "nanofil compiled $compiled of $objects objects"
        [ "$objects" -gt 0 ] && [ "$compiled" -eq "$objects" ]
        run_all >../nanofil.out
        diff -u ../ref.out ../nanofil.out
        FUGC_SCRIBBLE=1 FUGC_VERIFY=1 run_all >../nanofil-gc.out
        diff -u ../ref.out ../nanofil-gc.out
        echo "matches the filcc build on ''${#invocations[@]} invocations"
        make check CC=$PWD/../nanofil-cc || { cat test-suite.log; exit 1; }
        FUGC_SCRIBBLE=1 FUGC_VERIFY=1 make check CC=$PWD/../nanofil-cc ||
          { cat test-suite.log; exit 1; }
      )
    done
    touch $out
  ''
