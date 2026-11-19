# Rocq orders the glibc proofs and Make compiles them in one Nix build.
# The push check uses the sealed interpreter. The scheduled check builds
# a second tree against the abstract runtime signature.
{
  pkgs,
  filcc,
  model,
}:
let
  inherit (pkgs) lib;
  inherit (model) rocqInputs;
  watch = ../tests/watch.py;
  glibc = ../rocq/glibc;
  glibcSrc = lib.fileset.toSource {
    root = glibc;
    fileset = lib.fileset.fileFilter (f: f.hasExt "v") glibc;
  };
  compileTests = lib.fileset.toSource {
    root = ../tests;
    fileset = lib.fileset.unions [
      ../tests/watch.py
      ../tests/rocq_time.py
    ];
  };
  abstractFix =
    let
      source = builtins.readFile (glibc + "/Fix.v");
      sealedBinding = ''
        Module Type StartRuntime := Runtime
          with Definition state := InterpRuntime.state
          with Definition ready := InterpRuntime.ready.
        Module R : StartRuntime := InterpRuntime.'';
    in
    assert lib.assertMsg (
      builtins.length (lib.splitString sealedBinding source) == 2
    ) "glibc.nix: Fix.v must seal the interpreter runtime exactly once";
    pkgs.writeText "Fix-runtime.v" (
      lib.replaceStrings [ sealedBinding ] [ "Declare Module R : Runtime." ] source
    );

  tree =
    abstract:
    pkgs.runCommand
      "nanofil-glibc-${if abstract then "abstract" else "sealed"}-tree"
      {
        nativeBuildInputs = rocqInputs ++ [ pkgs.python3 ];
        OCAMLRUNPARAM = "o=200";
        tests = compileTests;
        compile = ./glibc/compile.sh;
      }
      ''
        set -euo pipefail
        cp -r ${glibcSrc} glibc
        chmod -R u+w glibc
        ln -s ${model.objects}/share/rocq/theories theories
        ${lib.optionalString abstract ''
          cp ${abstractFix} glibc/Fix.v
          rm glibc/hello/HelloInterpNeverPanics.v
        ''}
        python3 ${../tests/assumption_scan.py} ${lib.optionalString abstract "--abstract-fix glibc/Fix.v"} glibc
        ${lib.optionalString (!abstract) ''
          python3 ${../tests/proof_arch_check.py} --tree glibc --manifest ${../rocq/glibc/arch.json}
        ''}
        mkdir -p $out/sentence-timings times
        rocq dep -R theories Nanofil -R glibc Glibc $(find glibc -name '*.v' | sort) >rocq.dep
        duplicates=$(find glibc -name '*.v' -printf '%f\n' | sort | uniq -d)
        if [[ -n "$duplicates" ]]; then echo "Duplicate glibc module names: $duplicates" >&2; exit 1; fi
        make -j"$NIX_BUILD_CORES" -f ${./glibc/Makefile} all
        cat times/* >$out/timings.log
        awk 'function name(s) { sub(/^.*\//, "", s); sub(/\.vo$/, "", s); return s }
          $1 ~ /^glibc\/.*\.vo$/ { printf "%s:", name($1)
            for (i=2; i<=NF; i++) if ($i ~ /^glibc\/.*\.vo$/) printf " %s", name($i)
            print "" }' rocq.dep >deps
        python3 ${../tests/rocq_totals.py} --label glibc $out/timings.log deps | tee $out/totals
        mv glibc $out/
      '';
  sealed = tree false;
  abstractGeneral = tree true;
  rejectTestSrc = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.unions [
      ../tests/assumption_scan.py
      ../tests/test_scan.py
      ../tests/rocq_interface.py
      ../tests/rocq_interface_test.py
      ../tests/proof_arch_check.py
      ../tests/proof_arch_check_test.py
    ];
  };
  rejectTests =
    pkgs.runCommand "nanofil-glibc-reject-tests"
      { nativeBuildInputs = [ pkgs.python3 ]; }
      ''
        set -o pipefail
        mkdir $out
        python3 ${rejectTestSrc}/tests/test_scan.py 2>&1 | tee $out/log
        python3 ${rejectTestSrc}/tests/rocq_interface_test.py
        python3 ${rejectTestSrc}/tests/proof_arch_check_test.py
        touch $out/passed
      '';
  # The grammar round trip remains available for individual source files.
  paths = map (p: lib.removePrefix "${toString glibc}/" (toString p)) (
    lib.filter (lib.hasSuffix ".v") (lib.filesystem.listFilesRecursive glibc)
  );
  path = lib.listToAttrs (
    map (p: lib.nameValuePair (lib.removeSuffix ".v" (baseNameOf p)) p) paths
  );
  parseSrc = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.unions [
      ../web/rocq/rocq_syntax.pl
      ../web/rocq/tests/parse.sh
      ../web/rocq/tests/reprint.pl
    ];
  };
  reprint = lib.mapAttrs (
    n: file:
    pkgs.runCommand "nanofil-glibc-reprint-${n}"
      {
        nativeBuildInputs = rocqInputs ++ [
          pkgs.swi-prolog
          pkgs.python3
        ];
        # Match compilation's GC time/space tradeoff for strict reprints.
        OCAMLRUNPARAM = "o=200";
      }
      ''
        mkdir -p project/glibc verdicts
        printf '%s\n' "-R ../theories Nanofil" "-R . Glibc" >project/glibc/_RocqProject
        cp -rs ${sealed}/glibc/. project/glibc/
        ln -s ${model.objects}/share/rocq/theories project/theories
        PARSE_TMP=$PWD/verdicts PARSE_IN_PLACE=1 python3 ${watch} --label "glibc reprint ${file}" \
          --warn-after 120 --timeout 900 -- bash ${parseSrc}/web/rocq/tests/parse.sh --check 0 "$PWD/project/glibc/${file}"
        grep -q '^ok' verdicts/verdict-0
        mkdir $out
        cp verdicts/verdict-0 $out/verdict
      ''
  ) path;
  probeSrc = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.unions [
      ../rocq/glibc/probe.sh
      (lib.fileset.fileFilter (f: lib.hasPrefix "zsys-" f.name) glibc)
    ];
  };
  probes = pkgs.runCommandCC "nanofil-glibc-probes" { } ''
    mkdir $out
    FILCC=${filcc}/bin/clang bash ${probeSrc}/rocq/glibc/probe.sh >$out/log
    cat $out/log
  '';
  timingTestSrc = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.unions [
      ../tests/rocq_time.py
      ../tests/watch.py
      ../tests/rocq_time_test.py
      ../tests/rocq_totals.py
      ../tests/rocq_totals_test.py
      ./glibc/compile.sh
    ];
  };
  timingTests =
    pkgs.runCommand "nanofil-glibc-timing-tests"
      { nativeBuildInputs = [ pkgs.python3 ]; }
      ''
        set -o pipefail
        mkdir $out
        python3 ${timingTestSrc}/tests/rocq_time_test.py -v 2>&1 | tee $out/log
        python3 ${timingTestSrc}/tests/rocq_totals_test.py -v 2>&1 | tee -a $out/log
        touch $out/passed
      '';
in
pkgs.runCommand "nanofil-glibc"
  {
    passthru = {
      inherit
        model
        probes
        timingTests
        reprint
        abstractGeneral
        ;
      tree = sealed;
    };
  }
  ''
    test -f ${timingTests}/passed
    test -f ${rejectTests}/passed
    mkdir $out
    for name in timings.log totals sentence-timings glibc; do
      ln -s ${sealed}/$name $out/$name
    done
    cat ${sealed}/totals
    cp ${probes}/log $out/probes.log
  ''
