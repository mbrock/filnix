# xz-utils 5.8.4 built entirely by nanofil, with filnix's xz port patch
# (its C changes; the Makefile.am one only matters for shared liblzma).
#
# configure runs with filcc; make then runs with CC=nanofil-cc, and every
# object of xz, xzdec, lzmainfo, liblzma and xz's tests must come from
# nanofil. Two SIMD paths are configured out of both builds, since
# nanofil refuses vector types (docs/m4.md): the CLMUL CRC
# (--disable-clmul-crc) and the SSE2 copy in the LZ decoder
# (LZMA_LZ_DECODER_CONFIG=1, its memcpy variant). A deterministic
# workload (workloads/xz.sh) must print byte for byte what a filcc-built
# xz prints, plainly and under FUGC_SCRIBBLE and FUGC_VERIFY: liblzma's
# threaded encoder and decoder at 1 to 8 threads, the single-threaded
# coders and filters, --list and errors. xz's own test suite must pass,
# with nanofil's middle end off and with -O, each in its own derivation
# (configurations.nix).
{ pkgs, filcc }:
assert pkgs.xz.version == "5.8.4";
let
  src = pkgs.xz.src;
  workload = ./workloads/xz.sh;
  unpack = ''
    mkdir xz
    tar -xf $src -C xz --strip-components=1
    cd xz
    ${pkgs.patchutils}/bin/filterdiff -x '*/Makefile.am' \
      ${../../ports/patch/xz-5.8.4.patch} | patch -p1
    CC=${filcc}/bin/clang CPPFLAGS=-DLZMA_LZ_DECODER_CONFIG=1 ./configure \
      --disable-shared --disable-nls --disable-doc --disable-scripts \
      --disable-clmul-crc >configure.log 2>&1 ||
      { cat configure.log; exit 1; }
  '';
  reference = pkgs.runCommandCC "nanofil-xz-reference" { inherit src; } ''
    ${unpack}
    make -j$NIX_BUILD_CORES >make.log 2>&1 || { cat make.log; exit 1; }
    cp src/xz/xz ../xz.ref
    mkdir $out
    (mkdir ../w.ref && cd ../w.ref && bash ${workload} ../xz.ref >$out/ref.out)
  '';
in
import ./configurations.nix { inherit pkgs; } "nanofil-xz"
  {
    plain = "";
    O = "-O";
  }
  (
    label: opt:
    pkgs.runCommandCC "nanofil-xz-${label}" { inherit src; } ''
      cc=${import ./nanofil-cc.nix { inherit pkgs filcc; }}
      ref=${reference}/ref.out
      ${unpack}
      echo "== xz, nanofil ${opt}"
      export NANOFIL_OPT="${opt}" NANOFIL_LOG=$PWD/nanofil.log
      make -j$NIX_BUILD_CORES CC=$cc
      for env in "" "FUGC_SCRIBBLE=1 FUGC_VERIFY=1"; do
        rm -rf ../w.nf && mkdir ../w.nf
        (cd ../w.nf && env $env bash ${workload} ../xz/src/xz/xz >../nf.out)
        diff -u $ref ../nf.out
        echo "xz matches filcc's xz on $(grep -c '^### xz' $ref) commands ($env)"
      done
      make check CC=$cc >check.log 2>&1 || { cat check.log tests/test-suite.log; exit 1; }
      grep -E '^# (TOTAL|PASS|SKIP|FAIL|ERROR)' check.log
      # Compare names, not just counts: no object, the tests' included,
      # may come from clang. Objects of different directories have
      # distinct names here.
      find . -name '*.o' -printf '%f\n' | sort >../objects
      sed 's|.*/||' nanofil.log | sort -u >../compiled
      test -s ../objects
      diff -u ../objects ../compiled
      echo "nanofil compiled every one of $(wc -l <../objects) xz objects"
      touch $out
    ''
  )
