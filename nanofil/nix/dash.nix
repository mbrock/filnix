# dash 0.5.13.3 built entirely by nanofil, with filnix's dash port patch
# (fork for vfork: a vforked child would share the collector's heap).
# Every object of dash must come from nanofil (its build-time generators
# are compiled straight to executables by configure's CC_FOR_BUILD,
# filcc, and leave no objects). A deterministic workload of shell scripts (workloads/dash.sh:
# fork and exec, pipelines, signals and traps, redirections, here-
# documents, builtins, file operations and errors) must print byte for
# byte what a filcc-built dash prints, plainly and under FUGC_SCRIBBLE and
# FUGC_VERIFY, with nanofil's middle end off and with -O.
{ pkgs, filcc }:
assert pkgs.dash.version == "0.5.13.3";
pkgs.runCommandCC "nanofil-dash" { src = pkgs.dash.src; } ''
  cc=${import ./nanofil-cc.nix { inherit pkgs filcc; }}
  workload=${./workloads/dash.sh}
  mkdir dash
  tar -xf $src -C dash --strip-components=1
  cd dash
  patch -p1 <${../../ports/patch/dash-0.5.13.5.patch}
  CC=${filcc}/bin/clang ./configure >configure.log 2>&1 ||
    { cat configure.log; exit 1; }
  make -j$NIX_BUILD_CORES >make.log 2>&1 || { cat make.log; exit 1; }
  cp src/dash ../dash.ref
  (mkdir ../w.ref && cd ../w.ref && bash $workload ../dash.ref >../ref.out)

  for opt in "" -O; do
    echo "== dash, nanofil $opt"
    make clean >/dev/null
    export NANOFIL_OPT=$opt NANOFIL_LOG=$PWD/nanofil.log
    rm -f nanofil.log
    make -j$NIX_BUILD_CORES CC=$cc
    # Compare names, not just counts: no object may come from clang.
    find . -name '*.o' -printf '%f\n' | sort >../objects
    sed 's|.*/||' nanofil.log | sort -u >../compiled
    test -s ../objects
    diff -u ../objects ../compiled
    echo "nanofil compiled every one of $(wc -l <../objects) dash objects"
    for env in "" "FUGC_SCRIBBLE=1 FUGC_VERIFY=1"; do
      rm -rf ../w.nf && mkdir ../w.nf
      (cd ../w.nf && env $env bash $workload ../dash/src/dash >../nf.out)
      diff -u ../ref.out ../nf.out
      echo "dash matches filcc's dash on $(grep -c '^### script' ../ref.out) scripts ($env)"
    done
  done
  touch $out
''
