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
  rocq = pkgs.rocqPackages;
  lib = pkgs.lib;
  rocqInputs = [
    rocq.rocq-core
    rocq.stdlib
    rocq.stdpp
    rocq.iris
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
    n:
    lib.concatMapStrings (
      d:
      "mkdir -p glibc/${dirOf path.${d}}; ln -s ${vo.${d}}/${d}.vo glibc/${path.${d}}.vo\n"
    ) closure.${n}
    + lib.concatMapStrings (
      d:
      "mkdir -p theories/${dirOf model.path.${d}}; ln -s ${model.vo.${d}}/${d}.vo theories/${model.path.${d}}.vo\n"
    ) modelClosure.${n};
  vo = lib.genAttrs names (
    n:
    pkgs.runCommand "nanofil-glibc-${n}"
      {
        nativeBuildInputs = rocqInputs ++ [ pkgs.python3 ];
        # More free major-heap space reduces GC during large proof imports,
        # trading higher peak memory for time without skipping any checking.
        OCAMLRUNPARAM = "o=200";
      }
      ''
        set -o pipefail
        mkdir -p theories glibc/${dirOf path.${n}}
        ${link n}
        cp ${glibc + "/${path.${n}}.v"} glibc/${path.${n}}.v
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
      ''
  );
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
          ${link n}
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
        ;
    };
  }
  ''
    set -o pipefail
    test -f ${timingTests}/passed
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
