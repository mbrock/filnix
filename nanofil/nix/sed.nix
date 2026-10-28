# GNU sed 4.10 built entirely by nanofil, with filnix's sed port patch.
#
# configure runs with filcc (it picks -std=gnu23, so nanofil-cc reads
# C23 keywords) and gnulib's config.h turns on _FORTIFY_SOURCE; make
# then runs with CC=nanofil-cc, and every object of sed and its gnulib
# (regex, locale and multibyte support included) must come from nanofil.
# A deterministic workload (workloads/sed.sh) must print byte for byte
# what a filcc-built sed prints, plainly and under FUGC_SCRIBBLE and
# FUGC_VERIFY, and sed's own test suite must pass, with nanofil's middle
# end off and with -O.
{ pkgs, filcc }:
assert pkgs.gnused.version == "4.10";
pkgs.runCommandCC "nanofil-sed" { src = pkgs.gnused.src; } ''
  cc=${import ./nanofil-cc.nix { inherit pkgs filcc; }}
  workload=${./workloads/sed.sh}
  mkdir sed
  tar -xf $src -C sed --strip-components=1
  cd sed
  patch -p1 <${../../ports/patch/sed-4.10.patch}
  CC=${filcc}/bin/clang ./configure --disable-nls >configure.log 2>&1 ||
    { cat configure.log; exit 1; }
  # make's CC keeps configure's flags (-std=gnu23) after the compiler.
  flags=$(sed -n 's|^CC = ${filcc}/bin/clang||p' Makefile)
  make -j$NIX_BUILD_CORES >make.log 2>&1 || { cat make.log; exit 1; }
  cp sed/sed ../sed.ref
  (mkdir ../w.ref && cd ../w.ref && bash $workload ../sed.ref >../ref.out)

  for opt in "" -O; do
    echo "== GNU sed, nanofil $opt"
    make clean >/dev/null
    export NANOFIL_OPT=$opt NANOFIL_LOG=$PWD/nanofil.log
    rm -f nanofil.log
    make -j$NIX_BUILD_CORES CC="$cc$flags"
    # Compare names, not just counts: no object may come from clang.
    # gnulib-tests builds in its own directory, so log paths are relative
    # to either; compare file names, which are unique here.
    find . -name '*.o' -printf '%f\n' | sort >../objects
    sed 's|.*/||' nanofil.log | sort -u >../compiled
    test -s ../objects
    diff -u ../objects ../compiled
    echo "nanofil compiled every one of $(wc -l <../objects) sed objects"
    for env in "" "FUGC_SCRIBBLE=1 FUGC_VERIFY=1"; do
      rm -rf ../w.nf && mkdir ../w.nf
      (cd ../w.nf && env $env bash $workload ../sed/sed/sed >../nf.out)
      diff -u ../ref.out ../nf.out
      echo "sed matches filcc's sed on $(grep -c '^### sed' ../ref.out) commands ($env)"
    done
    # sed's own suite; gnulib's tests (SUBDIRS gnulib-tests) are left out.
    make check SUBDIRS=. CC="$cc$flags" >check.log 2>&1 ||
      { cat check.log test-suite.log; exit 1; }
    grep -E '^# (TOTAL|PASS|SKIP|FAIL|ERROR)' check.log
  done
  touch $out
''
