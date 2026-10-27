# bzip2 1.0.8 built entirely by nanofil. Every object of bzip2 and
# bzip2recover (libbz2 included) is compiled through nanofil-cc, bzip2's
# own `make test` round-trips its three samples, and bzip2's output must
# be byte for byte the same as a filcc-built bzip2's at block sizes 1, 5
# and 9, on text and on random data, with each build decompressing the
# other's output. Repeated with each middle-end and register choice; the
# comparisons also run under FUGC_SCRIBBLE and FUGC_VERIFY.
{ pkgs, filcc }:
assert pkgs.bzip2.version == "1.0.8";
pkgs.runCommandCC "nanofil-bzip2" { src = pkgs.bzip2.src; } ''
  cc=${import ./nanofil-cc.nix { inherit pkgs filcc; }}
  unpack() {
    mkdir $1
    tar -xf $src -C $1 --strip-components=1
  }

  unpack ref
  make -C ref -j$NIX_BUILD_CORES CC=${filcc}/bin/clang bzip2 bzip2recover >/dev/null
  cat ${../.}/src/*.pl ${../.}/docs/*.md > text
  head -c 1000000 /dev/urandom > random

  for opt in "" -O "--registers=local" "-O --registers=local"; do
    echo "== bzip2, nanofil $opt"
    rm -rf nf
    unpack nf
    export NANOFIL_OPT=$opt NANOFIL_LOG=$PWD/nanofil.log
    rm -f nanofil.log
    make -C nf -j$NIX_BUILD_CORES CC=$cc bzip2 bzip2recover
    # Compare names, not just counts: no object may come from clang.
    find nf -name '*.o' -printf '%f\n' | sort >objects
    sed 's|.*/||' nanofil.log | sort -u >compiled
    test -s objects
    diff -u objects compiled
    echo "nanofil compiled every one of $(wc -l <objects) bzip2 objects"
    make -C nf CC=$cc test >test.log 2>&1 || { cat test.log; exit 1; }
    ! grep -q differ test.log
    for env in "" "FUGC_SCRIBBLE=1 FUGC_VERIFY=1"; do
      for f in text random; do
        for level in 1 5 9; do
          ref/bzip2 -$level <$f >$f.ref.bz2
          env $env nf/bzip2 -$level <$f >$f.nf.bz2
          cmp $f.ref.bz2 $f.nf.bz2
          env $env nf/bzip2 -d <$f.ref.bz2 | cmp - $f
          ref/bzip2 -d <$f.nf.bz2 | cmp - $f
        done
      done
      # bzip2recover splits a damaged-free file into its blocks the same way.
      rm -rf rec.ref rec.nf && mkdir rec.ref rec.nf
      cp text.ref.bz2 rec.ref/t.bz2 && cp text.ref.bz2 rec.nf/t.bz2
      (cd rec.ref && ../ref/bzip2recover t.bz2 >/dev/null 2>&1)
      (cd rec.nf && env $env ../nf/bzip2recover t.bz2 >/dev/null 2>&1)
      diff -r rec.ref rec.nf
      echo "bzip2 matches filcc's bzip2 byte for byte ($env)"
    done
  done
  touch $out
''
