# zlib built entirely by nanofil. libz.a, example and minigzip are
# compiled through nanofil-cc (all 17 objects must come from nanofil),
# zlib's own `make test` runs, and minigzip's output must be byte for
# byte the same as a filcc-built zlib's, at levels 1, 6 and 9 on text
# and on random data, with each build inflating the other's output.
# Once with nanofil's middle end off and once with -O; the tests also
# run under FUGC_SCRIBBLE and FUGC_VERIFY.
{ pkgs, filcc }:
pkgs.runCommandCC "nanofil-zlib" { src = pkgs.zlib.src; } ''
  cc=${import ./nanofil-cc.nix { inherit pkgs filcc; }}
  unpack() {
    mkdir $1
    tar -xf $src -C $1 --strip-components=1
    (cd $1 && CC=${filcc}/bin/clang ./configure --static >configure.log)
  }

  unpack ref
  make -C ref -j$NIX_BUILD_CORES libz.a example minigzip >/dev/null
  cat ${../.}/src/*.pl ${../.}/docs/*.md > text
  head -c 2000000 /dev/urandom > random

  # Middle end and target cache are independent choices.
  for opt in "" -O "--registers=local" "-O --registers=local"; do
    echo "== zlib, nanofil $opt"
    rm -rf nf
    unpack nf
    export NANOFIL_OPT=$opt NANOFIL_LOG=$PWD/nanofil.log
    rm -f nanofil.log
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
          ref/minigzip -$level <$f >$f.ref.gz
          env $env nf/minigzip -$level <$f >$f.nf.gz
          cmp $f.ref.gz $f.nf.gz
          env $env nf/minigzip -d <$f.ref.gz | cmp - $f
          ref/minigzip -d <$f.nf.gz | cmp - $f
        done
      done
      echo "minigzip matches filcc's zlib byte for byte ($env)"
    done
  done
  touch $out
''
