# zlib built entirely by nanofil. libz.a, example and minigzip are
# compiled through nanofil-cc (all 17 objects must come from nanofil),
# zlib's own `make test` runs, and minigzip's output must be byte for
# byte the same as a filcc-built zlib's, at levels 1, 6 and 9 on text
# and on random data, with each build inflating the other's output.
# Once per middle-end, register and check-reuse choice, each in its own
# derivation (configurations.nix); the tests also run under
# FUGC_SCRIBBLE and FUGC_VERIFY.
{ pkgs, filcc }:
let
  src = pkgs.zlib.src;
  unpack = ''
    unpack() {
      mkdir $1
      tar -xf $src -C $1 --strip-components=1
      (cd $1 && CC=${filcc}/bin/clang ./configure --static >configure.log)
    }
  '';
  reference = pkgs.runCommandCC "nanofil-zlib-reference" { inherit src; } ''
    ${unpack}
    unpack ref
    make -C ref -j$NIX_BUILD_CORES libz.a example minigzip >/dev/null
    mkdir -p $out/bin
    cp ref/minigzip $out/bin/
  '';
  # Middle end and target cache are independent choices.
  configurations = {
    plain = "";
    O = "-O";
    O-branches-reference = "-O --branches=reference";
    O-stack = "-O --registers=stack";
    reuse = "--checks=reuse";
    O-reuse = "-O --checks=reuse";
    O-renew = "-O --checks=renew";
  };
in
import ./configurations.nix { inherit pkgs; } "nanofil-zlib" configurations (
  label: opt:
  pkgs.runCommandCC "nanofil-zlib-${label}" { inherit src; } ''
    cc=${import ./nanofil-cc.nix { inherit pkgs filcc; }}
    ref=${reference}/bin/minigzip
    ${unpack}
    cat ${../.}/src/*.pl ${../.}/docs/*.md > text
    head -c 2000000 /dev/urandom > random

    echo "== zlib, nanofil ${opt}"
    unpack nf
    export NANOFIL_OPT="${opt}" NANOFIL_LOG=$PWD/nanofil.log
    make -C nf -j$NIX_BUILD_CORES CC=$cc libz.a example minigzip
    objects=$(find nf -name '*.o' | wc -l)
    compiled=$(sort -u nanofil.log | wc -l)
    echo "nanofil compiled $compiled of $objects objects"
    [ "$objects" -gt 0 ] && [ "$compiled" -eq "$objects" ]
    for env in "" "FUGC_SCRIBBLE=1 FUGC_VERIFY=1"; do
      env $env make -C nf CC=$cc test | tee test.log
      grep -q '\*\*\* zlib test OK \*\*\*' test.log
      for f in text random; do
        for level in 1 6 9; do
          $ref -$level <$f >$f.ref.gz
          env $env nf/minigzip -$level <$f >$f.nf.gz
          cmp $f.ref.gz $f.nf.gz
          env $env nf/minigzip -d <$f.ref.gz | cmp - $f
          $ref -d <$f.nf.gz | cmp - $f
        done
      done
      echo "minigzip matches filcc's zlib byte for byte ($env)"
    done
    touch $out
  ''
)
