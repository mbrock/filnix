# The glibc check compiles every proof under rocq/glibc and validates its
# grammar round trip. Each file gets its own derivation, with only the
# compiled Nanofil and Glibc files in its transitive imports. A theory
# edit therefore rebuilds its importers, not every glibc proof.
#
# ```sh
# nix build -L .#checks.x86_64-linux.nanofil-glibc
# ```
#
# The check rejects unfinished proofs and assumptions declared outside a
# module type. It compiles each file's reprinted source against the same
# imported objects, and runs the native zsys-*.c probes with filcc. It
# compares the import lists with rocq dep and records each file's compile
# time. The separate nanofil-rocq check still compiles and checks the
# entire model.
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
        # No Admitted, and no axiom outside a module type.
        if awk 'skip == "" && /^Module Type [A-Za-z0-9_]/ { skip = $3; sub(/[ .(].*/, "", skip); next }
          skip != "" { if ($0 ~ "^End " skip "\\.") skip = ""; next }
          { print FILENAME ":" FNR ": " $0 }' glibc/${path.${n}}.v |
          grep -wE 'Admitted|Axiom|Axioms|Parameter|Conjecture'; then
          echo "glibc: no Admitted, and no axiom outside a module type" >&2
          exit 1
        fi
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
  sealedVo = lib.genAttrs generalNames (
    n:
    assert lib.assertMsg (!importsConcrete n)
      "glibc.nix: ${path.${n}}.v imports a file of runtime-concrete.txt, so list it there too";
    compile "" sealedVo source n
  );
  concreteClosure = lib.unique (
    lib.concatMap (n: closure.${n} ++ [ n ]) concreteNames
  );
  concreteVo = lib.genAttrs concreteClosure (
    compile "concrete-" concreteVo (
      n: if n == "Fix" then concreteFix else source n
    )
  );
  vo = sealedVo // lib.getAttrs concreteNames concreteVo;
  # Rebuild Hello's entire Glibc closure against one abstract runtime.
  # No interpreter Glibc object may enter this graph through an import.
  helloNames = closure.HelloGlibcJoin ++ [ "HelloGlibcJoin" ];
  runtimeFix =
    binding:
    let
      source = builtins.readFile (glibc + "/${path.Fix}.v");
      sealedBinding = "Module R : Runtime := InterpRuntime.";
    in
    assert lib.assertMsg (
      builtins.length (lib.splitString sealedBinding source) == 2
    ) "glibc.nix: Fix.v must seal the interpreter runtime exactly once";
    pkgs.writeText "Fix-runtime.v" (
      lib.replaceStrings [ sealedBinding ] [ binding ] source
    );
  abstractFix = runtimeFix "Declare Module R : Runtime.";
  concreteFix = runtimeFix "Module R := InterpRuntime.";
  # rocq/glibc/runtime-concrete.txt lists the files that need the
  # interpreter's runtime. Every other file is general, and has an
  # abstract object.
  concretePaths = lib.filter (l: l != "" && !lib.hasPrefix "#" l) (
    lib.splitString "\n" (builtins.readFile (glibc + "/runtime-concrete.txt"))
  );
  concreteNames =
    assert lib.assertMsg (lib.all (l: lib.elem (lib.removeSuffix ".v" l) paths)
      concretePaths
    ) "glibc.nix: runtime-concrete.txt lists a file that is not under rocq/glibc";
    map (l: baseNameOf (lib.removeSuffix ".v" l)) concretePaths;
  importsConcrete = n: lib.any (d: lib.elem d concreteNames) closure.${n};
  generalNames = lib.filter (n: !lib.elem n concreteNames) names;
  abstractSource =
    n: if n == "Fix" then abstractFix else glibc + "/${path.${n}}.v";
  abstractVo = lib.genAttrs generalNames (
    n:
    assert lib.assertMsg (!importsConcrete n)
      "glibc.nix: ${path.${n}}.v imports a file of runtime-concrete.txt, so list it there too";
    compile "abstract-" abstractVo abstractSource n
  );
  # A listed file that imports no other listed file must be rejected
  # by both the sealed and abstract runtimes, so a file cannot leave
  # either check by being listed without need. rocq_reject.py accepts an error
  # that Rocq reports at a position in the file with status 1; it
  # refuses a timeout, a signal, another status and a failure to load a
  # library. The file's interpreter object is an input: the two
  # compilations differ only in the runtime binding of Fix.v, so the
  # runtime causes the rejection.
  rejected =
    prefix: objects:
    lib.genAttrs (lib.filter (n: !importsConcrete n) concreteNames) (
      n:
      pkgs.runCommand "nanofil-glibc-${prefix}rejected-${n}"
        {
          nativeBuildInputs = rocqInputs ++ [ pkgs.python3 ];
          OCAMLRUNPARAM = "o=200";
        }
        ''
          set -o pipefail
          mkdir -p theories glibc/${dirOf path.${n}} $out
          ${link objects n}
          cp ${glibc + "/${path.${n}}.v"} glibc/${path.${n}}.v
          test -f ${concreteVo.${n}}/${n}.vo
          python3 ${../tests/rocq_reject.py} --file glibc/${path.${n}}.v --timeout 900 --log $out/log -- \
            rocq c -q -R theories Nanofil -R glibc Glibc glibc/${path.${n}}.v | tee $out/verdict
        ''
    );
  sealedRejected = rejected "sealed-" sealedVo;
  abstractRejected = rejected "abstract-" abstractVo;
  # rocq_reject.py itself: it accepts a type error from Rocq, and
  # refuses a file that compiles, a timeout, a signal, an unexpected
  # status, a missing library and an error outside the file.
  rejectTestSrc = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.unions [
      ../tests/rocq_reject.py
      ../tests/rocq_reject_test.py
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
        python3 ${rejectTestSrc}/tests/rocq_reject_test.py -v 2>&1 | tee $out/log
        touch $out/passed
      '';
  # The scheduled check nanofil-glibc-abstract: every general file
  # compiles against the abstract runtime, and every listed file is
  # rejected by it.
  abstractGeneral =
    pkgs.runCommand "nanofil-glibc-abstract-general"
      {
        passthru = {
          vo = abstractVo;
          rejected = abstractRejected;
          inherit rejectTests abstractHello abstractAudit;
        };
      }
      ''
        test -f ${rejectTests}/passed
        test -f ${abstractHello}/passed
        mkdir $out
        cat ${
          lib.concatMapStringsSep " " (n: "${abstractAudit.${n}}/summary") generalNames
        } >$out/audit-summary
        cat ${
          lib.concatMapStringsSep " " (n: "${abstractVo.${n}}/time") generalNames
        } >$out/timings.log
        ${lib.concatMapStrings (
          n: "cp ${abstractRejected.${n}}/verdict $out/rejected-${n}.log\n"
        ) (lib.attrNames abstractRejected)}
        echo "@@glibc abstract general ${toString (builtins.length generalNames)} files compiled, ${toString (builtins.length concreteNames)} listed files rejected"
        touch $out/passed
      '';
  abstractAudit = lib.genAttrs generalNames (
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
          python3 ${../tests/rocq_runtime_audit.py} ${abstractVo.${n}}/${n}.glob $out
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
        mkdir -p theories glibc/${dirOf path.HelloGlibcJoin} $out
        ${link abstractVo "HelloGlibcJoin"}
        ln -s ${abstractVo.HelloGlibcJoin}/HelloGlibcJoin.vo glibc/${path.HelloGlibcJoin}.vo
        cat >HelloAbstractAudit.v <<'EOF'
        From Glibc Require Import HelloGlibcJoin.
        Print Assumptions HelloGlibcJoin.hello_never_panics.
        EOF
        python3 ${watch} --label "glibc abstract Hello audit" --warn-after 120 --timeout 900 -- \
          rocq c -q -R theories Nanofil -R glibc Glibc HelloAbstractAudit.v | tee $out/assumptions.log
        cat >expected-assumptions <<'EOF'
        Fix.R.address_space
        Fix.R.alloc
        Fix.R.at_safepoint
        Fix.R.aux_round_trip
        Fix.R.collector_live
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
  # The grammar check (web/rocq/tests/parse.sh), one file at a time:
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
          ${link (if lib.elem n concreteNames then concreteVo else sealedVo) n}
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
        touch $out/passed
      '';
  glibcSrc = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.fileFilter (f: f.hasExt "v") glibc;
  };
in
pkgs.runCommand "nanofil-glibc"
  {
    nativeBuildInputs = rocqInputs;
    passthru = {
      inherit
        vo
        reprint
        probes
        model
        timingTests
        abstractHello
        abstractGeneral
        concreteVo
        sealedRejected
        ;
    };
  }
  ''
    set -o pipefail
    test -f ${timingTests}/passed
    test -f ${rejectTests}/passed
    ${lib.concatMapStrings (n: "cat ${sealedRejected.${n}}/verdict\n") (
      lib.attrNames sealedRejected
    )}
    ${lib.concatMapStrings (
      n: "test -f ${concreteVo.${n}}/${n}.vo\n"
    ) concreteClosure}
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
      lib.concatMapStringsSep " " (n: "${vo.${n}}/time") names
    } | tee $out/timings.log
    mkdir $out/sentence-timings
    ${lib.concatMapStrings (
      n: "cp ${vo.${n}}/sentence-timings.log $out/sentence-timings/${n}.log\n"
    ) names}
    cat ${
      lib.concatMapStringsSep " " (n: "${reprint.${n}}/verdict") names
    } | tee $out/verdicts
    cat ${probes}/log | tee $out/probes.log
    echo "@@glibc ${toString (builtins.length names)} files compiled and reprinted"
  ''
