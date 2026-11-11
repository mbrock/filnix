# The glibc spike (rocq/glibc, docs/glibc-ir.md): programs linked with
# nanofil's IR of user glibc units, proved through the program logic,
# with libpizlo's zsys_write as the one trusted contract. Off the model's
# import path; its own push check (.github/workflows/nanofil-glibc.yml)
# compiles and caches each changed file and its importers.
#
#   nix build -L .#checks.x86_64-linux.nanofil-glibc
#
# As rocq.nix does for the model, every .v file under rocq/glibc, in
# any subdirectory, is compiled in its own derivation against the
# model's compiled theories (the nanofil-rocq model's objects) and the
# objects of the Glibc files it imports, refusing Admitted and any
# axiom outside a module type, so an edit recompiles that file and its
# importers. Each file is read back by parse.sh (web/rocq) in its own
# derivation too, and every zsys-*.c native probe of a trusted contract
# runs with filcc. The check gathers them, prints each file's compile
# time, and compares the imports read here with rocq dep's. That the
# Code.v fixtures are nanofil's current products is rocq/glibc/code.sh's
# check, which needs the user glibc capture (survey/glibc/capture.nix)
# and is run by hand.
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
  theories = "${model.objects}/share/rocq/theories";
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
  # The Glibc files each file imports, from its From Glibc Require
  # sentences; the check below compares them with rocq dep's.
  imports = lib.genAttrs names (
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
              "From[[:space:]]+Glibc[[:space:]]+Require[[:space:]]+((Import|Export)[[:space:]]+)?([^.]*)\\."
              (builtins.readFile (glibc + "/${path.${n}}.v"))
          )
        )
    )
  );
  closure = lib.genAttrs names (
    n: lib.unique (lib.concatMap (d: closure.${d} ++ [ d ]) imports.${n})
  );
  # link N: the objects of every Glibc file N imports, under glibc/ at
  # their own paths, since an object records its logical path.
  link =
    n:
    lib.concatMapStrings (
      d: "mkdir -p glibc/${dirOf path.${d}}; ln -s ${vo.${d}}/${d}.vo glibc/${path.${d}}.vo\n"
    ) closure.${n};
  vo = lib.genAttrs names (
    n:
    pkgs.runCommand "nanofil-glibc-${n}" { nativeBuildInputs = rocqInputs ++ [ pkgs.python3 ]; } ''
      set -o pipefail
      mkdir -p glibc/${dirOf path.${n}}
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
      python3 ${watch} --label "glibc compile ${path.${n}}.v" --warn-after 120 --timeout 900 -- \
        rocq c -q -R ${theories} Nanofil -R glibc Glibc glibc/${path.${n}}.v
      ms=$((($(date +%s%N) - start) / 1000000))
      mkdir $out
      cp glibc/${path.${n}}.vo glibc/${path.${n}}.glob $out/
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
      }
      ''
        mkdir -p project/glibc verdicts
        ln -s ${theories} project/theories
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
  glibcSrc = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.fileFilter (f: f.hasExt "v") glibc;
  };
in
pkgs.runCommand "nanofil-glibc"
  {
    nativeBuildInputs = rocqInputs;
    passthru = { inherit vo reprint probes; };
  }
  ''
    # Every file imports what rocq dep says it needs from Glibc.
    cp -r ${glibcSrc}/rocq/glibc glibc
    rocq dep -R ${theories} Nanofil -R glibc Glibc $(find glibc -name '*.v' | sort) |
      awk 'function base(p,  a, k) { k = split(p, a, "/"); sub(/\..*/, "", a[k]); return a[k] }
        $1 ~ /^glibc\/.*\.vo$/ { t = base($1); d = ""
        for (i = 2; i <= NF; i++) if ($i ~ /^glibc\/.*\.vo$/) { s = base($i); if (s != t) d = d " " s }
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
          lib.concatMapStrings (d: " ${d}") (lib.sort lib.lessThan imports.${n})
        }\n"
      ) (lib.sort lib.lessThan names)
    }EOF
    sed -i 's/^ *//; s/ *$//' $TMPDIR/nixdep
    sed -i 's/ *$//' $TMPDIR/rocqdep
    if ! diff -u $TMPDIR/rocqdep $TMPDIR/nixdep; then
      echo "glibc.nix: a file's imports differ from rocq dep's (- rocq dep, + glibc.nix); write them as From Glibc Require" >&2
      exit 1
    fi
    mkdir $out
    cat ${lib.concatMapStringsSep " " (n: "${vo.${n}}/time") names} | tee $out/timings.log
    cat ${lib.concatMapStringsSep " " (n: "${reprint.${n}}/verdict") names} | tee $out/verdicts
    cat ${probes}/log | tee $out/probes.log
    echo "@@glibc ${toString (builtins.length names)} files compiled and reprinted"
  ''
