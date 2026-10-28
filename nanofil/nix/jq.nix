# jq 1.8.2 built entirely by nanofil, with its bundled oniguruma (regular
# expressions) and decNumber (number literals). oniguruma carries
# filnix's port patch (its hash tables hold pointers). Every object of
# jq, libjq, oniguruma and decNumber must come from nanofil; oniguruma
# dispatches its bytecode with GNU computed gotos. A deterministic
# workload (workloads/jq.sh) must print byte for byte what a filcc-built
# jq prints, plainly and under FUGC_SCRIBBLE and FUGC_VERIFY, and the test
# suites of jq and oniguruma (whose test programs nanofil compiles too)
# must pass, with nanofil's middle end off and with -O, each in its own
# derivation (configurations.nix).
{ pkgs, filcc }:
assert pkgs.jq.version == "1.8.2";
let
  src = pkgs.jq.src;
  workload = ./workloads/jq.sh;
  # The suites print dates in named zones and recurse deeply; Fil-C
  # frames are larger than native ones (as filnix's jq port says).
  unpack = ''
    export TZDIR=${pkgs.tzdata}/share/zoneinfo
    ulimit -s 65536
    mkdir jq
    tar -xf $src -C jq --strip-components=1
    cd jq
    (cd vendor/oniguruma && patch -p1 <${../../patches/oniguruma-pointer-data.patch})
    CC=${filcc}/bin/clang ./configure --disable-shared --with-oniguruma=builtin \
      --disable-docs --disable-maintainer-mode >configure.log 2>&1 ||
      { cat configure.log; exit 1; }
  '';
  reference = pkgs.runCommandCC "nanofil-jq-reference" { inherit src; } ''
    ${unpack}
    make -j$NIX_BUILD_CORES >make.log 2>&1 || { cat make.log; exit 1; }
    cp jq ../jq.ref
    mkdir $out
    (mkdir ../w.ref && cd ../w.ref && bash ${workload} ../jq.ref >$out/ref.out)
  '';
in
import ./configurations.nix { inherit pkgs; } "nanofil-jq"
  {
    plain = "";
    O = "-O";
  }
  (
    label: opt:
    pkgs.runCommandCC "nanofil-jq-${label}" { inherit src; } ''
      cc=${import ./nanofil-cc.nix { inherit pkgs filcc; }}
      ref=${reference}/ref.out
      ${unpack}
      echo "== jq, nanofil ${opt}"
      export NANOFIL_OPT="${opt}" NANOFIL_LOG=$PWD/nanofil.log
      make -j$NIX_BUILD_CORES CC=$cc
      # Compare names, not just counts: no object may come from clang.
      # oniguruma builds in its own directory, so log paths are relative to
      # either; compare file names, which are unique here.
      find . -name '*.o' -printf '%f\n' | sort >../objects
      sed 's|.*/||' nanofil.log | sort -u >../compiled
      test -s ../objects
      diff -u ../objects ../compiled
      echo "nanofil compiled every one of $(wc -l <../objects) jq objects"
      for env in "" "FUGC_SCRIBBLE=1 FUGC_VERIFY=1"; do
        rm -rf ../w.nf && mkdir ../w.nf
        (cd ../w.nf && env $env bash ${workload} ../jq/jq >../nf.out)
        diff -u $ref ../nf.out
        echo "jq matches filcc's jq on $(grep -c '^### jq' $ref) commands ($env)"
      done
      make check CC=$cc >check.log 2>&1 || { cat check.log; exit 1; }
      grep -E '^# (TOTAL|PASS|SKIP|FAIL|ERROR)' check.log
      touch $out
    ''
  )
