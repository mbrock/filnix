# GNU bash 5.3 (patch level 9, as nixpkgs pins it) built entirely by
# nanofil, with nixpkgs' patches and filnix's bash port patch (the
# unwind_prot buffer that saves jmp_bufs, aligned for their capabilities)
# and the port's configure flags (--without-bash-malloc). Readline,
# history, glob, tilde, termcap and the builtins are bash's bundled
# copies, so they are nanofil's too.
#
# configure runs with filcc; make then runs with CC=nanofil-cc, and every
# object must come from nanofil (the build-time generators are compiled
# straight to executables and leave no objects). A deterministic
# workload (workloads/bash.sh) must print byte for byte what a
# filcc-built bash prints, plainly and under FUGC_SCRIBBLE and
# FUGC_VERIFY, and each of bash's own tests/run-* scripts
# (workloads/bash-tests.sh) must pass or differ as it does with filcc's
# bash in the same sandbox (some need a terminal or locales it lacks),
# with nanofil's middle end off and with -O,
# each in its own derivation (configurations.nix).
{ pkgs, filcc }:
assert pkgs.bash.version == "5.3p9";
let
  src = pkgs.bash.src;
  workload = ./workloads/bash.sh;
  tests = ./workloads/bash-tests.sh;
  unpack = ''
    mkdir bash
    tar -xf $src -C bash --strip-components=1
    cd bash
    for p in ${pkgs.lib.concatMapStringsSep " " (p: "${p}") pkgs.bash.patches}; do
      patch -p0 <$p
    done
    patch -p1 <${../../ports/patch/bash-5.3.patch}
    CC=${filcc}/bin/clang ./configure --without-bash-malloc --disable-nls \
      bash_cv_job_control_missing=nomissing bash_cv_sys_named_pipes=nomissing \
      bash_cv_getcwd_malloc=yes bash_cv_getenv_redef=yes \
      >configure.log 2>&1 || { cat configure.log; exit 1; }
  '';
  reference = pkgs.runCommandCC "nanofil-bash-reference" { inherit src; } ''
    ${unpack}
    make -j$NIX_BUILD_CORES >make.log 2>&1 || { cat make.log; exit 1; }
    mkdir $out
    (mkdir ../w.ref && cd ../w.ref && bash ${workload} ../bash/bash >$out/ref.out)
    bash ${tests} . >$out/tests.log
    grep -v '^    |' $out/tests.log >$out/tests
  '';
in
import ./configurations.nix { inherit pkgs; } "nanofil-bash"
  {
    plain = "";
    O = "-O";
  }
  (
    label: opt:
    pkgs.runCommandCC "nanofil-bash-${label}" { inherit src; } ''
      cc=${import ./nanofil-cc.nix { inherit pkgs filcc; }}
      ref=${reference}
      ${unpack}
      echo "== bash, nanofil ${opt}"
      export NANOFIL_OPT="${opt}" NANOFIL_LOG=$PWD/nanofil.log
      make -j$NIX_BUILD_CORES CC=$cc
      # Compare names, not just counts: no object may come from clang.
      find . -name '*.o' -printf '%f\n' | sort >../objects
      sed 's|.*/||' nanofil.log | sort >../compiled
      test -s ../objects
      diff -u ../objects ../compiled
      echo "nanofil compiled every one of $(wc -l <../objects) bash objects"
      for env in "" "FUGC_SCRIBBLE=1 FUGC_VERIFY=1"; do
        rm -rf ../w.nf && mkdir ../w.nf
        (cd ../w.nf && env $env bash ${workload} ../bash/bash >../nf.out)
        diff -u $ref/ref.out ../nf.out
        echo "bash matches filcc's bash on $(grep -c '^### script' $ref/ref.out) scripts ($env)"
      done
      bash ${tests} . >../tests.log
      grep -v '^    |' ../tests.log >../tests
      diff -u $ref/tests ../tests || { cat $ref/tests.log ../tests.log; exit 1; }
      echo "bash's test suite: $(grep -c ' ok$' ../tests) of $(wc -l <../tests) scripts pass, as with filcc's bash"
      touch $out
    ''
  )
