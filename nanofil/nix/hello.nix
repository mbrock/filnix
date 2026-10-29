# GNU hello built entirely by nanofil, then its own test suite.
#
# configure runs with filcc, so feature detection is clang's. make then
# runs with CC=nanofil-cc: every `-c` compile is preprocessed by filcc
# with make's flags, compiled by nanofil and assembled by GNU as; only
# the final link uses filcc. The check fails unless every object came
# from nanofil, and runs `make check` plainly and under FUGC_SCRIBBLE
# and FUGC_VERIFY, once per middle-end, register and check-reuse
# choice, each in its own derivation (configurations.nix).
{ pkgs, filcc }:
let
  src = pkgs.hello.src;
  # The reference: the same hello built by filcc alone. Its test suite
  # is small, so every build is also compared with the reference on
  # these invocations (stdout, stderr and exit status).
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
  reference = pkgs.runCommandCC "nanofil-hello-reference" { inherit src; } ''
    ${runAll}
    mkdir ref $out
    tar -xf $src -C ref --strip-components=1
    cd ref
    CC=${filcc}/bin/clang ./configure --disable-nls >configure.log 2>&1 ||
      { cat configure.log; exit 1; }
    make -j$NIX_BUILD_CORES >make.log 2>&1 || { cat make.log; exit 1; }
    run_all >$out/ref.out
  '';
  # Middle end and target cache are independent choices.
  configurations = {
    plain = "";
    O = "-O";
    O-stack = "-O --registers=stack";
    reuse = "--checks=reuse";
    O-reuse = "-O --checks=reuse";
    O-renew = "-O --checks=renew";
  };
in
import ./configurations.nix { inherit pkgs; } "nanofil-hello" configurations (
  label: opt:
  pkgs.runCommandCC "nanofil-hello-${label}" { inherit src; } ''
    cc=${import ./nanofil-cc.nix { inherit pkgs filcc; }}
    ${runAll}
    echo "== GNU hello, nanofil ${opt}"
    mkdir hello
    tar -xf $src -C hello --strip-components=1
    cd hello
    CC=${filcc}/bin/clang ./configure --disable-nls >configure.log 2>&1 ||
      { cat configure.log; exit 1; }
    export NANOFIL_OPT="${opt}" NANOFIL_LOG=$PWD/nanofil.log
    make -j$NIX_BUILD_CORES CC=$cc
    objects=$(find . -name '*.o' | wc -l)
    compiled=$(sort -u nanofil.log | wc -l)
    echo "nanofil compiled $compiled of $objects objects"
    [ "$objects" -gt 0 ] && [ "$compiled" -eq "$objects" ]
    run_all >../nanofil.out
    diff -u ${reference}/ref.out ../nanofil.out
    FUGC_SCRIBBLE=1 FUGC_VERIFY=1 run_all >../nanofil-gc.out
    diff -u ${reference}/ref.out ../nanofil-gc.out
    echo "matches the filcc build on ''${#invocations[@]} invocations"
    make check CC=$cc || { cat test-suite.log; exit 1; }
    FUGC_SCRIBBLE=1 FUGC_VERIFY=1 make check CC=$cc ||
      { cat test-suite.log; exit 1; }
    touch $out
  ''
)
