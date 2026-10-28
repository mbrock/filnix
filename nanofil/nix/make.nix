# GNU make 4.4.1 built entirely by nanofil, with filnix's make port
# patch and nixpkgs' source patches (those that need no autoreconf).
#
# configure runs with filcc; make then runs with CC=nanofil-cc, and every
# object of make and its gnulib must come from nanofil. A deterministic
# workload (workloads/make.sh) must print byte for byte what a
# filcc-built make prints, plainly and under FUGC_SCRIBBLE and
# FUGC_VERIFY: recipes forked and exec'd, pattern, static and archive
# rules, functions, remade makefiles, errors, -j1 to -j8 through the
# fifo and pipe jobservers to recursive makes, -O output sync, and
# signals deleting targets. make's own test suite must give the filcc
# build's per-category results, with nanofil's middle end off and with
# -O, each in its own derivation (configurations.nix).
{ pkgs, filcc }:
assert pkgs.gnumake.version == "4.4.1";
let
  src = pkgs.gnumake.src;
  workload = ./workloads/make.sh;
  nixpkgsPatches = builtins.filter (
    p: !(pkgs.lib.hasInfix "Do-not-search-for-a-C-compiler" (toString p))
  ) pkgs.gnumake.patches;
  unpack = ''
    mkdir make
    tar -xf $src -C make --strip-components=1
    cd make
    for p in ${
      pkgs.lib.concatMapStringsSep " " (p: "${p}") nixpkgsPatches
    } ${../../ports/patch/make-4.4.1.patch}; do
      patch -p1 <$p
    done
    CC=${filcc}/bin/clang ./configure --disable-nls --without-guile \
      >configure.log 2>&1 || { cat configure.log; exit 1; }
  '';
  # make's test suite, one line per category with its result; the
  # suite's own exit status is not the comparison. In the build sandbox
  # filcc's make, like nanofil's, passes 102 of 107 categories:
  # features/targetvars and misc/general4 fail to run, functions/shell
  # passes 19 of 21, and two are N/A.
  testSuite = ''
    make check >check.log 2>&1 || true
    grep -E '^[a-z_0-9/-]+ \.+ ' check.log | sed 's/ *$//' >../check.summary
    grep -E 'ok|N/A|FAILED' ../check.summary >/dev/null
  '';
  reference =
    pkgs.runCommandCC "nanofil-make-reference"
      {
        inherit src;
        nativeBuildInputs = [ pkgs.perl ];
      }
      ''
        ${unpack}
        make -j$NIX_BUILD_CORES >make.log 2>&1 || { cat make.log; exit 1; }
        mkdir ../ref && cp make ../ref/make  # make names itself by argv[0]
        ${testSuite}
        mkdir $out
        cp ../check.summary $out/check.summary
        (mkdir ../w.ref && cd ../w.ref && bash ${workload} ../ref/make >$out/ref.out)
      '';
in
import ./configurations.nix { inherit pkgs; } "nanofil-make"
  {
    plain = "";
    O = "-O";
  }
  (
    label: opt:
    pkgs.runCommandCC "nanofil-make-${label}"
      {
        inherit src;
        nativeBuildInputs = [ pkgs.perl ];
      }
      ''
        cc=${import ./nanofil-cc.nix { inherit pkgs filcc; }}
        ref=${reference}
        ${unpack}
        echo "== make, nanofil ${opt}"
        export NANOFIL_OPT="${opt}" NANOFIL_LOG=$PWD/nanofil.log
        make -j$NIX_BUILD_CORES CC=$cc
        for env in "" "FUGC_SCRIBBLE=1 FUGC_VERIFY=1"; do
          rm -rf ../w.nf && mkdir ../w.nf
          (cd ../w.nf && env $env bash ${workload} ../make/make >../nf.out)
          diff -u $ref/ref.out ../nf.out
          echo "make matches filcc's make on $(grep -c '^### make' $ref/ref.out) commands ($env)"
        done
        ${testSuite}
        diff -u $ref/check.summary ../check.summary
        echo "make's test suite: $(grep -c ' ok ' ../check.summary) categories ok, as filcc's make"
        grep -v ' ok \| N/A' ../check.summary || true
        find . -name '*.o' -printf '%f\n' | sort >../objects
        sed 's|.*/||' nanofil.log | sort -u >../compiled
        test -s ../objects
        diff -u ../objects ../compiled
        echo "nanofil compiled every one of $(wc -l <../objects) make objects"
        touch $out
      ''
  )
