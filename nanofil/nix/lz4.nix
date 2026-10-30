# lz4 1.10.0 built entirely by nanofil. Every object of the lz4 program
# (liblz4, lz4frame, lz4hc and xxhash included) is compiled through
# nanofil-cc, and its output must be byte for byte the same as a
# filcc-built lz4's at several levels and modes, on text and on random
# data, with each build decompressing the other's output. Once per
# middle-end, register and check-reuse choice, each in its own
# derivation (configurations.nix); the comparisons also run under
# FUGC_SCRIBBLE and FUGC_VERIFY. The source is unpatched: --list shows
# file sizes through lz4io's x87 long double LZ4IO_toHuman.
{ pkgs, filcc }:
assert pkgs.lz4.version == "1.10.0";
let
  src = pkgs.lz4.src;
  unpack = ''
    unpack() {
      cp -r $src $1
      chmod -R u+w $1
    }
  '';
  reference = pkgs.runCommandCC "nanofil-lz4-reference" { inherit src; } ''
    ${unpack}
    unpack ref
    make -C ref/programs -j$NIX_BUILD_CORES CC=${filcc}/bin/clang lz4 >/dev/null
    mkdir -p $out/bin
    cp ref/programs/lz4 $out/bin/
  '';
  configurations = {
    plain = "";
    O = "-O";
    O-branches-reference = "-O --branches=reference";
    O-stack = "-O --registers=stack";
    reuse = "--checks=reuse";
    O-reuse = "-O --checks=reuse";
    O-refchecks = "-O --checks=reference";
  };
in
import ./configurations.nix { inherit pkgs; } "nanofil-lz4" configurations (
  label: opt:
  pkgs.runCommandCC "nanofil-lz4-${label}" { inherit src; } ''
    cc=${import ./nanofil-cc.nix { inherit pkgs filcc; }}
    ref=${reference}/bin/lz4
    ${unpack}
    cat ${../.}/src/*.pl ${../.}/docs/*.md > text
    head -c 1000000 /dev/urandom > random
    cat text random text > mixed

    echo "== lz4, nanofil ${opt}"
    unpack nf
    export NANOFIL_OPT="${opt}" NANOFIL_LOG=$PWD/nanofil.log
    make -C nf/programs -j$NIX_BUILD_CORES CC=$cc lz4
    # Compare names, not just counts: no object may come from clang.
    find nf -name '*.o' -printf '%f\n' | sort >objects
    sed 's|.*/||' nanofil.log | sort -u >compiled
    test -s objects
    diff -u objects compiled
    echo "nanofil compiled every one of $(wc -l <objects) lz4 objects"
    for env in "" "FUGC_SCRIBBLE=1 FUGC_VERIFY=1"; do
      for f in text random mixed; do
        for mode in -1 -9 -12 --fast=3 -BD --favor-decSpeed; do
          $ref -q $mode <$f >$f.ref.lz4
          env $env nf/programs/lz4 -q $mode <$f >$f.nf.lz4
          cmp $f.ref.lz4 $f.nf.lz4
          env $env nf/programs/lz4 -q -d <$f.ref.lz4 | cmp - $f
          $ref -q -d <$f.nf.lz4 | cmp - $f
        done
      done
      # A frame listing reads headers through lz4frame's by-value structs
      # and shows sizes as long double.
      $ref -q -f -9 text t.lz4
      $ref --list t.lz4 >list.ref
      env $env nf/programs/lz4 --list t.lz4 >list.nf
      diff -u list.ref list.nf
      echo "lz4 matches filcc's lz4 byte for byte ($env)"
    done
    touch $out
  ''
)
