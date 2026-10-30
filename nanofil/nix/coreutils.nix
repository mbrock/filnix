# GNU coreutils 9.11 built entirely by nanofil, with nixpkgs' source
# patches and filnix's coreutils port patch (without its tests/local.mk
# hunk, which would need automake; it only registers the port's new
# multibyte sort tests).
#
# configure runs with filcc; make then runs with CC=nanofil-cc (with
# configure's -std=gnu23), and every object of the 107 programs and
# libcoreutils must come from nanofil. Configured out of both builds:
# the AVX2, AVX-512 and PCLMUL paths of wc and cksum, since nanofil
# refuses vector types; _Float16 and __bf16 in od (refused too); and
# factor's longlong.h inline asm (USE_LONGLONG_H=0, its portable
# multiply).
#
# The reference derivation builds the filcc tree. Each configuration's
# derivation (configurations.nix) runs, beside its own build and on the
# same builder, both builds' deterministic workload (workloads/
# coreutils.sh, nanofil's also under FUGC_SCRIBBLE and FUGC_VERIFY),
# which must match byte for byte, and both builds' coreutils test
# suite, whose per-test results must be equal: some of the suite's
# results depend on the builder's file system and limits.
{ pkgs, filcc }:
assert pkgs.coreutils.version == "9.11";
let
  src = pkgs.coreutils.src;
  workload = ./workloads/coreutils.sh;
  unpack = dir: ''
    cd $NIX_BUILD_TOP
    mkdir ${dir}
    tar -xf $src -C ${dir} --strip-components=1
    cd ${dir}
    for p in ${
      pkgs.lib.concatMapStringsSep " " (p: "${p}") pkgs.coreutils.patches
    }; do
      patch -p1 <$p
    done
    ${pkgs.patchutils}/bin/filterdiff -x '*/tests/local.mk' \
      ${../../ports/patch/coreutils-9.11.patch} | patch -p1
    export utils_cv_ieee_16_bit_supported=no utils_cv_brain_16_bit_supported=no \
      utils_cv_avx2_intrinsic_exists=no utils_cv_avx2_pclmul_intrinsic_exists=no \
      utils_cv_avx512_intrinsic_exists=no utils_cv_avx512_pclmul_intrinsic_exists=no \
      utils_cv_pclmul_intrinsic_exists=no gl_cv_crc_pclmul=no
    CC=${filcc}/bin/clang CPPFLAGS=-DUSE_LONGLONG_H=0 ./configure \
      --disable-nls --without-selinux --without-openssl --disable-libcap \
      --without-libgmp >configure.log 2>&1 || { cat configure.log; exit 1; }
  '';
  # The suite's per-test results; its own exit status is not the
  # comparison (filcc's build fails some tests too). timeout.sh and
  # seq-epipe.sh measure time (a sleep against a deadline): on a loaded
  # builder filcc's run failed one and skipped the other while nanofil's
  # passed both, so they are not compared.
  testSuite = out: ''
    make check -j$NIX_BUILD_CORES >check.log 2>&1 || true
    grep -E '^(PASS|FAIL|SKIP|XFAIL|XPASS|ERROR): tests/.*\.(sh|pl|xpl)$' check.log \
      | grep -vE ' tests/(timeout/timeout|seq/seq-epipe)\.sh$' \
      | sort -k2 >${out}
    test -s ${out}
  '';
  # perl too, or configure records it missing and the suite skips its
  # Perl tests in the reference tree only.
  reference =
    pkgs.runCommandCC "nanofil-coreutils-reference"
      {
        inherit src;
        nativeBuildInputs = [ pkgs.perl ];
      }
      ''
        ${unpack "ref"}
        make -j$NIX_BUILD_CORES >make.log 2>&1 || { cat make.log; exit 1; }
        cd $NIX_BUILD_TOP
        mkdir $out
        tar -cf $out/ref.tar ref
      '';
in
import ./configurations.nix { inherit pkgs; } "nanofil-coreutils"
  {
    plain = "";
    O = "-O";
  }
  (
    label: opt:
    pkgs.runCommandCC "nanofil-coreutils-${label}"
      {
        inherit src;
        nativeBuildInputs = [ pkgs.perl ];
      }
      ''
        cc=${import ./nanofil-cc.nix { inherit pkgs filcc; }}
        (cd $NIX_BUILD_TOP && tar -xf ${reference}/ref.tar)
        ${unpack "coreutils"}
        echo "== coreutils, nanofil ${opt}"
        export NANOFIL_OPT="${opt}" NANOFIL_LOG=$PWD/nanofil.log
        make -j$NIX_BUILD_CORES CC="$cc$(sed -n 's/^CC = [^ ]*//p' Makefile)"
        w=$NIX_BUILD_TOP/w
        rm -rf $w && mkdir $w
        (cd $w && bash ${workload} $NIX_BUILD_TOP/ref/src >../ref.out)
        for env in "" "FUGC_SCRIBBLE=1 FUGC_VERIFY=1"; do
          rm -rf $w && mkdir $w
          (cd $w && env $env bash ${workload} $NIX_BUILD_TOP/coreutils/src >../nf.out)
          diff -u $NIX_BUILD_TOP/ref.out $NIX_BUILD_TOP/nf.out
          echo "coreutils matches filcc's on $(grep -c '^### exit' $NIX_BUILD_TOP/ref.out) commands ($env)"
        done
        (cd $NIX_BUILD_TOP/ref && ${testSuite "$NIX_BUILD_TOP/ref.results"})
        ${testSuite "$NIX_BUILD_TOP/nf.results"}
        # The same tests, and none worse in nanofil's build: FAIL, ERROR,
        # XPASS or SKIP where filcc's had another result. Under load,
        # filcc's run fails or skips a test now and then that nanofil's
        # passes (pwd-long.sh, tail/pipe-f.sh); that is not a difference.
        awk 'NR == FNR { r[$2] = $1; next } { n[$2] = $1 }
          END {
            for (t in r) if (!(t in n)) { print "only in filcc results: " t; bad = 1 }
            for (t in n) {
              if (!(t in r)) { print "only in nanofil results: " t; bad = 1 }
              else if (n[t] != r[t] && n[t] ~ /^(FAIL|ERROR|XPASS|SKIP):$/) { print "nanofil " n[t] " " t ", filcc " r[t]; bad = 1 }
              else if (n[t] != r[t]) print "filcc " r[t] " " t ", nanofil " n[t] " (not counted)"
            }
            exit bad
          }' $NIX_BUILD_TOP/ref.results $NIX_BUILD_TOP/nf.results
        echo "coreutils' test suite: $(awk '{print $1}' $NIX_BUILD_TOP/nf.results | sort | uniq -c | tr -s ' \n' ' '), none worse than filcc's"
        # Compare names, not just counts: no object may come from clang.
        find . -name '*.o' -printf '%f\n' | sort >../objects
        sed 's|.*/||' nanofil.log | sort -u >../compiled
        test -s ../objects
        diff -u ../objects ../compiled
        echo "nanofil compiled every one of $(wc -l <../objects) coreutils objects"
        touch $out
      ''
  )
