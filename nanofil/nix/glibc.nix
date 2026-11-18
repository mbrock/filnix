# The glibc check compiles every proof under rocq/glibc. Each file gets
# its own derivation, with only the compiled Nanofil and Glibc files in
# its transitive imports. A theory edit therefore rebuilds its importers,
# not every glibc proof. Where a file's importers load its interface
# rather than the file (checkVo below), an edit to one of its Qed proofs
# or to a comment rebuilds only the file itself.
#
# ```sh
# nix build -L .#checks.x86_64-linux.nanofil-glibc
# ```
#
# The check rejects unfinished proofs and assumptions declared outside a
# module type. It runs the native zsys-*.c probes with filcc, compares the
# import lists with rocq dep and records each file's compile time. The
# separate nanofil-rocq check still compiles and checks the entire model.
#
# The push check compiles every file with Fix.v's sealed runtime, and the
# scheduled nanofil-glibc-abstract checks every file except the concrete
# Hello corollary with the runtime left abstract.
#
# The grammar round trip of a glibc file is not part of the check, because
# it compiles the file a second time whenever anything the file imports
# changes. Run it for one file by hand when the site's parser changes:
#
# ```sh
# nix build -L .#checks.x86_64-linux.nanofil-glibc.reprint.OsCpuid
# ```
#
# The fixture check in rocq/glibc/code.sh confirms that Code.v files are
# nanofil's current products. It needs the user glibc capture from
# survey/glibc/capture.nix and runs by hand.
{
  pkgs,
  filcc,
  model,
}:
let
  rocq = import ./rocq-packages.nix { inherit pkgs; };
  lib = pkgs.lib;
  # native_compute compiles with this OCaml and findlib, and assembles
  # and links with the C toolchain, which runCommand does not provide.
  rocqInputs = [
    rocq.rocq-core
    rocq.stdlib
    rocq.stdpp
    rocq.iris
    rocq.rocq-core.ocamlPackages.ocaml
    rocq.rocq-core.ocamlPackages.findlib
    pkgs.stdenv.cc
  ];
  watch = ../tests/watch.py;
  glibc = ../rocq/glibc;
  # Files are named by base name, as From Glibc Require names them, so
  # two files with one base name anywhere under rocq/glibc are refused.
  paths = map (
    p: lib.removeSuffix ".v" (lib.removePrefix "${toString glibc}/" (toString p))
  ) (lib.filter (lib.hasSuffix ".v") (lib.filesystem.listFilesRecursive glibc));
  path = lib.listToAttrs (map (p: lib.nameValuePair (baseNameOf p) p) paths);
  names =
    let
      ns = map baseNameOf paths;
    in
    assert lib.assertMsg (lib.length ns == lib.length (lib.unique ns))
      "glibc.nix: two files under rocq/glibc share a base name: ${
        toString (lib.filter (n: lib.count (m: m == n) ns > 1) (lib.unique ns))
      }";
    ns;
  # Both namespaces use From NS Require sentences; the check below
  # compares their direct imports with rocq dep's.
  readImports =
    namespace:
    lib.genAttrs names (
      n:
      lib.unique (
        lib.concatMap
          (
            m:
            lib.filter (w: builtins.isString w && w != "") (
              builtins.split "[[:space:]]+" (builtins.elemAt m 2)
            )
          )
          (
            lib.filter builtins.isList (
              builtins.split
                "From[[:space:]]+${namespace}[[:space:]]+Require[[:space:]]+((Import|Export)[[:space:]]+)?([^.]*)\\."
                (builtins.readFile (glibc + "/${path.${n}}.v"))
            )
          )
      )
    );
  imports = readImports "Glibc";
  modelImports = readImports "Nanofil";
  closure = lib.genAttrs names (
    n: lib.unique (lib.concatMap (d: closure.${d} ++ [ d ]) imports.${n})
  );
  # A Glibc import can itself import Nanofil theories. Include those
  # theories and their model dependencies, not the aggregate model tree.
  modelClosure = lib.genAttrs names (
    n:
    lib.unique (
      lib.concatMap (d: model.closure.${d} ++ [ d ]) (
        lib.concatMap (d: modelImports.${d}) ([ n ] ++ closure.${n})
      )
    )
  );
  # Objects retain their logical paths in both namespaces.
  link =
    objects: n:
    lib.concatMapStrings (
      d:
      "mkdir -p glibc/${dirOf path.${d}}; ln -s ${objects.${d}}/${d}.vo glibc/${path.${d}}.vo\n"
    ) closure.${n}
    + lib.concatMapStrings (
      d:
      "mkdir -p theories/${dirOf model.path.${d}}; ln -s ${model.vo.${d}}/${d}.vo theories/${model.path.${d}}.vo\n"
    ) modelClosure.${n};
  compile =
    prefix: objects: source: n:
    pkgs.runCommand "nanofil-glibc-${prefix}${n}"
      {
        nativeBuildInputs = rocqInputs ++ [ pkgs.python3 ];
        # More free major-heap space reduces GC during large proof imports,
        # trading higher peak memory for time without skipping any checking.
        OCAMLRUNPARAM = "o=200";
      }
      ''
        set -o pipefail
        mkdir -p theories glibc/${dirOf path.${n}}
        ${link objects n}
        cp ${source n} glibc/${path.${n}}.v
        ${lib.optionalString (prefix != "interface-") ''
          # No Admitted, and no axiom outside a module type.
          python3 ${../tests/assumption_scan.py} \
            ${
              lib.optionalString (
                toString (source n) == toString abstractFix
              ) "--abstract-fix glibc/${path.${n}}.v"
            } \
            glibc/${path.${n}}.v
        ''}
        start=$(date +%s%N)
        # Keep the watchdog's status through capture, including failed compiles.
        if python3 ${watch} --label "glibc compile ${path.${n}}.v" --warn-after 120 --timeout 900 -- \
          rocq c -q -time -R theories Nanofil -R glibc Glibc glibc/${path.${n}}.v | tee sentence-timings.log; then
          status=0
        else
          status=$?
        fi
        ms=$((($(date +%s%N) - start) / 1000000))
        python3 ${../tests/rocq_time.py} glibc/${path.${n}}.v sentence-timings.log || \
          echo "warning: Rocq sentence timing reporter failed" >&2
        if [ "$status" -ne 0 ]; then exit "$status"; fi
        mkdir $out
        cp glibc/${path.${n}}.vo glibc/${path.${n}}.glob sentence-timings.log $out/
        printf '@@glibc %4d.%01ds %5d lines %s.v\n' $((ms / 1000)) $((ms % 1000 / 100)) \
          "$(wc -l <glibc/${path.${n}}.v)" ${path.${n}} >$out/time
      '';
  source = n: glibc + "/${path.${n}}.v";
  # The push check compiles each general file twice at most. checkVo
  # compiles the file itself, which checks all of its proofs. An imported
  # file whose interface (tests/rocq_interface.py) replaces at least one
  # Qed proof by Admitted also has ifaceVo, the compiled interface, and
  # that is what its importers load; every other file's importers load
  # its checkVo. Both compile against the exported objects of the file's
  # imports. The interface's derivation takes its text, not the file, so
  # an edit to a replaced proof or to a comment recompiles the file's
  # checkVo and nothing else. Opaque proofs are invisible to importers, so
  # this checks what a chain of full compiles checks, except universe
  # constraints that only a replaced proof adds; the abstract check's full
  # chain of compiles still sees those twice daily.
  interfaces =
    pkgs.runCommand "nanofil-glibc-interfaces"
      { nativeBuildInputs = [ pkgs.python3 ]; }
      ''
        python3 ${../tests/rocq_interface.py} --tree ${glibcSrc}/rocq/glibc $out
      '';
  # Reading the interfaces is an import from a derivation. Dropping the
  # string context makes each interface's derivation depend on its text
  # alone, not on every source file that the run above read.
  replaced = lib.listToAttrs (
    map
      (
        l:
        let
          w = lib.splitString " " l;
        in
        lib.nameValuePair (baseNameOf (builtins.elemAt w 0)) (
          lib.toInt (builtins.elemAt w 1)
        )
      )
      (
        lib.filter (l: l != "") (
          lib.splitString "\n" (builtins.readFile "${interfaces}/replaced")
        )
      )
  );
  interfaceSource =
    n:
    pkgs.writeText "${n}.v" (
      builtins.unsafeDiscardStringContext (
        builtins.readFile "${interfaces}/${path.${n}}.v"
      )
    );
  # A file that no general file imports needs no interface.
  imported = lib.genAttrs (lib.unique (lib.concatMap (n: imports.${n}) names)) (
    _: true
  );
  exported = n: replaced.${n} > 0 && imported ? ${n};
  ifaceVo = lib.genAttrs (lib.filter exported names) (
    compile "interface-" exportVo interfaceSource
  );
  checkVo = lib.genAttrs names (compile "" exportVo source);
  exportVo = lib.genAttrs names (
    n: if exported n then ifaceVo.${n} else checkVo.${n}
  );
  vo = exportVo;
  # Rebuild Hello's entire Glibc closure against one abstract runtime.
  # No interpreter Glibc object may enter this graph through an import.
  helloNames = closure.HelloStartNeverPanics ++ [ "HelloStartNeverPanics" ];
  runtimeFix =
    binding:
    let
      source = builtins.readFile (glibc + "/${path.Fix}.v");
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
      lib.replaceStrings [ sealedBinding ] [ binding ] source
    );
  abstractFix = runtimeFix "Declare Module R : Runtime.";
  abstractSource =
    n: if n == "Fix" then abstractFix else glibc + "/${path.${n}}.v";
  abstractNames = lib.remove "HelloInterpNeverPanics" names;
  abstractVo = lib.genAttrs abstractNames (
    compile "abstract-" abstractVo abstractSource
  );
  rejectTestSrc = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.unions [
      ../tests/assumption_scan.py
      ../tests/proof_inventory.py
      ../tests/rocq_runtime_audit.py
      ../tests/test_scan.py
      ../tests/test_nested_audit.py
      ../tests/rocq_interface.py
      ../tests/rocq_interface_test.py
    ];
  };
  rejectTests =
    pkgs.runCommand "nanofil-glibc-reject-tests"
      {
        nativeBuildInputs = rocqInputs ++ [ pkgs.python3 ];
      }
      ''
        set -o pipefail
        mkdir $out
        python3 ${rejectTestSrc}/tests/test_scan.py 2>&1 | tee $out/log
        python3 ${rejectTestSrc}/tests/test_nested_audit.py
        python3 ${rejectTestSrc}/tests/rocq_interface_test.py
        touch $out/passed
      '';
  # The scheduled check compiles and audits all runtime-general files.
  abstractGeneral =
    pkgs.runCommand "nanofil-glibc-abstract-general"
      {
        passthru = {
          vo = abstractVo;
          inherit rejectTests abstractHello abstractAudit;
        };
      }
      ''
        test -f ${rejectTests}/passed
        test -f ${abstractHello}/passed
        mkdir $out
        cat ${
          lib.concatMapStringsSep " " (n: "${abstractAudit.${n}}/summary") abstractNames
        } >$out/audit-summary
        cat ${
          lib.concatMapStringsSep " " (n: "${abstractVo.${n}}/time") abstractNames
        } >$out/timings.log
        echo "@@glibc abstract general ${toString (builtins.length abstractNames)} files compiled"
        touch $out/passed
      '';
  abstractAudit = lib.genAttrs abstractNames (
    n:
    pkgs.runCommand "nanofil-glibc-abstract-audit-${n}"
      {
        nativeBuildInputs = rocqInputs ++ [ pkgs.python3 ];
        OCAMLRUNPARAM = "o=200";
      }
      ''
        mkdir -p theories glibc/${dirOf path.${n}} $out
        ${link abstractVo n}
        ln -s ${abstractVo.${n}}/${n}.vo glibc/${path.${n}}.vo
        python3 ${watch} --label "glibc abstract audit ${path.${n}}.v" --warn-after 120 --timeout 900 -- \
          python3 ${rejectTestSrc}/tests/rocq_runtime_audit.py ${abstractSource n} ${abstractVo.${n}}/${n}.glob $out
      ''
  );
  abstractHello =
    pkgs.runCommand "nanofil-glibc-hello-abstract"
      {
        nativeBuildInputs = rocqInputs ++ [ pkgs.python3 ];
        OCAMLRUNPARAM = "o=200";
        passthru.vo = lib.getAttrs helloNames abstractVo;
      }
      ''
        set -o pipefail
        mkdir -p theories glibc/${dirOf path.HelloStartNeverPanics} $out
        ${link abstractVo "HelloStartNeverPanics"}
        ln -s ${abstractVo.HelloStartNeverPanics}/HelloStartNeverPanics.vo glibc/${path.HelloStartNeverPanics}.vo
        cat >HelloAbstractAudit.v <<'EOF'
        From Glibc Require Import HelloStartNeverPanics.
        Print Assumptions HelloStartNeverPanics.hello_never_panics.
        EOF
        python3 ${watch} --label "glibc abstract Hello audit" --warn-after 120 --timeout 900 -- \
          rocq c -q -R theories Nanofil -R glibc Glibc HelloAbstractAudit.v | tee $out/assumptions.log
        cat >expected-assumptions <<'EOF'
        Fix.R.address_space
        Fix.R.alloc
        Fix.R.at_safepoint
        Fix.R.aux_round_trip
        Fix.R.collector_live
        Fix.R.free
        Fix.R.free_succeeds
        Fix.R.fresh_allocation
        Fix.R.non_moving
        Fix.R.ready
        Fix.R.ready_kept
        Fix.R.safepoint
        Fix.R.safepoint_ready
        Fix.R.state
        EOF
        python3 - "$out/assumptions.log" <<'PY'
        import pathlib, re, sys
        text = pathlib.Path(sys.argv[1]).read_text()
        names = sorted(set(re.findall(r"^(\S+)\s*:", text, re.M)) - {"Axioms"})
        pathlib.Path("actual-assumptions").write_text("".join(name + "\n" for name in names))
        PY
        diff -u expected-assumptions actual-assumptions
        cp actual-assumptions $out/assumption-names
        cat ${
          lib.concatMapStringsSep " " (n: "${abstractVo.${n}}/time") helloNames
        } >$out/timings.log
        echo "@@glibc abstract Hello ${toString (builtins.length helloNames)} files compiled"
        touch $out/passed
      '';
  # The grammar check (web/rocq/tests/parse.sh), one file at a time and
  # by hand, since the aggregate check does not build it:
  # reprint it with every subterm in parentheses and compile the reprint
  # against the original objects of its imports, in a project laid out
  # as rocq/ is, with the model's theories beside glibc.
  parseSrc = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.unions [
      ../web/rocq/rocq_syntax.pl
      ../web/rocq/tests/parse.sh
      ../web/rocq/tests/reprint.pl
    ];
  };
  reprint = lib.genAttrs names (
    n:
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
        mkdir -p project/glibc project/theories verdicts
        printf '%s\n' "-R ../theories Nanofil" "-R . Glibc" >project/glibc/_RocqProject
        (
          cd project
          ${link exportVo n}
        )
        mkdir -p project/glibc/${dirOf path.${n}}
        cp ${glibc + "/${path.${n}}.v"} project/glibc/${path.${n}}.v
        PARSE_TMP=$PWD/verdicts PARSE_IN_PLACE=1 python3 ${watch} --label "glibc reprint ${path.${n}}.v" \
          --warn-after 120 --timeout 900 -- bash ${parseSrc}/web/rocq/tests/parse.sh --check 0 "$PWD/project/glibc/${path.${n}}.v"
        grep -q '^ok' verdicts/verdict-0
        mkdir $out
        cp verdicts/verdict-0 $out/verdict
      ''
  );
  # The native probes of the trusted contracts, which read only their
  # own sources.
  probeSrc = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.unions [
      ../rocq/glibc/probe.sh
      (lib.fileset.fileFilter (f: lib.hasPrefix "zsys-" f.name) glibc)
    ];
  };
  probes = pkgs.runCommandCC "nanofil-glibc-probes" { } ''
    FILCC=${filcc}/bin/clang bash ${probeSrc}/rocq/glibc/probe.sh | tee log
    mkdir $out
    cp log $out/
  '';
  timingTestSrc = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.unions [
      ../tests/rocq_time.py
      ../tests/watch.py
      ../tests/rocq_time_test.py
      ../tests/rocq_totals.py
      ../tests/rocq_totals_test.py
      ./glibc.nix
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
  glibcSrc = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.fileFilter (f: f.hasExt "v") glibc;
  };
in
pkgs.runCommand "nanofil-glibc"
  {
    nativeBuildInputs = rocqInputs ++ [ pkgs.python3 ];
    passthru = {
      inherit
        vo
        reprint
        probes
        model
        timingTests
        abstractHello
        abstractGeneral
        closure
        modelClosure
        ;
      # The push check's per-file compiles, which glibc-tools/affected.sh
      # builds for the edited files and their importers, and the objects
      # importers load, which glibc-tools/warm.sh copies into a tree.
      check = checkVo;
      exports = exportVo;
      inherit interfaces;
    };
  }
  ''
    set -o pipefail
    test -f ${timingTests}/passed
    test -f ${rejectTests}/passed
    # The dependency guard needs sources, not the aggregate model objects.
    # Check both namespaces, including imports through another Glibc file.
    cp -r ${glibcSrc}/rocq/glibc glibc
    cp -r ${model.src}/rocq/theories theories
    rocq dep -R theories Nanofil -R glibc Glibc $(find glibc -name '*.v' | sort) |
      awk 'function base(p,  a, k) { k = split(p, a, "/"); sub(/\..*/, "", a[k]); return a[k] }
        $1 ~ /^glibc\/.*\.vo$/ { t = base($1); d = ""
        for (i = 2; i <= NF; i++) {
          if ($i ~ /^glibc\/.*\.vo$/) { s = base($i); if (s != t) d = d " Glibc/" s }
          if ($i ~ /^theories\/.*\.vo$/) d = d " Nanofil/" base($i)
        }
        print t ":" d }' |
      while read -r line; do
        f=''${line%%:*}; set -- ''${line#*:}
        printf '%s:%s\n' "$f" "$(printf ' %s' $(printf '%s\n' "$@" | sort -u))"
      done | sort >$TMPDIR/rocqdep
    cat >$TMPDIR/nixdep <<'EOF'
    ${
      lib.concatMapStrings (
        n:
        "${n}:${
          lib.concatMapStrings (d: " ${d}") (
            lib.sort lib.lessThan (
              map (d: "Glibc/${d}") imports.${n}
              ++ map (d: "Nanofil/${d}") modelImports.${n}
            )
          )
        }\n"
      ) (lib.sort lib.lessThan names)
    }EOF
    sed -i 's/^ *//; s/ *$//' $TMPDIR/nixdep
    sort -o $TMPDIR/nixdep $TMPDIR/nixdep
    sed -i 's/ *$//' $TMPDIR/rocqdep
    if ! diff -u $TMPDIR/rocqdep $TMPDIR/nixdep; then
      echo "glibc.nix: a file's imports differ from rocq dep's (- rocq dep, + glibc.nix); write them as From Glibc/Nanofil Require" >&2
      exit 1
    fi
    mkdir $out
    cat ${
      lib.concatMapStringsSep " " (n: "${checkVo.${n}}/time") names
    } | tee $out/timings.log
    # Build-time totals (AGENTS.md, Rocq proof speed); a readout, nothing
    # fails on it. An edit here never rebuilds a theory, so only Glibc
    # imports count.
    python3 ${../tests/rocq_totals.py} --label glibc --namespace Glibc $out/timings.log $TMPDIR/nixdep | tee $out/totals
    mkdir $out/sentence-timings
    ${lib.concatMapStrings (
      n: "cp ${checkVo.${n}}/sentence-timings.log $out/sentence-timings/${n}.log\n"
    ) names}
    cat ${probes}/log | tee $out/probes.log
    echo "@@glibc ${toString (builtins.length names)} files compiled"
  ''
