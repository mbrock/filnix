# The Rocq model of the checked IR (rocq/, docs/formal.md Campaign 1):
# default: model (every theory compiled, one derivation per file) + a
# small outcome/base-verdict smoke corpus. The grammar round trip of
# web/rocq/tests/parse.sh is its own check, passthru.parse
# (checks.nanofil-rocq-parse), also one derivation per file.
# full=true opts into the complete outcome and mutation campaign below:
# compile it with the pinned nixpkgs' Rocq, refuse any Admitted or Axiom
# (none is allowed outside the Campaign 2 runtime module type in
# Runtime.v), extract and link the model, then check that it
# agrees with interp:run/5 on every run line of rocq/tests, the Fil-C
# IR fixtures, the C tests and Fil-C modules from tests/gen.pl, the
# last three with and without -O and under every --checks mode
# (rocq/scripts/agree.sh), and Lua's own functions (rocq/scripts/lua.sh); and that its
# validator reaches ir:valid_module/1's verdict on mutants of every checked module
# in the same matrix, and of the tests/c/prog programs with aliases and
# weak, thread-local or constructor data (rocq/scripts/valid.sh). Both check that
# the modules the program proofs are about are what nanofil makes today
# (rocq/scripts/programs.sh). The program logic (Language.v, Logic.v) is built on
# Iris, so the model and the parse check take stdpp and Iris from the
# same nixpkgs; the extracted driver does not use them.
{
  pkgs,
  filcc,
  full ? false,
}:
let
  rocq = import ./rocq-packages.nix { inherit pkgs; };
  ocamlPackages = rocq.rocq-core.ocamlPackages;
  lib = pkgs.lib;
  rocqInputs = [
    rocq.rocq-core
    rocq.stdlib
    rocq.stdpp
    rocq.iris
  ];
  watch = ../tests/watch.py;
  theories = ../rocq/theories;
  # Each theory is its own derivation, whose inputs are its one .v file
  # and the objects of the theories it imports, so an edit recompiles that
  # file and its importers and nothing else; every other object comes from
  # the store or a cache. Imports are read here from the sources' From
  # Nanofil Require sentences; deps below checks them against rocq dep.
  # Theories sit in one directory per layer (core, soundness, ...) but are
  # named by base name, as From Nanofil Require names them; two files
  # with one base name would make those imports ambiguous.
  paths =
    map
      (
        p:
        lib.removeSuffix ".v" (lib.removePrefix "${toString theories}/" (toString p))
      )
      (
        lib.filter (lib.hasSuffix ".v") (lib.filesystem.listFilesRecursive theories)
      );
  path = lib.listToAttrs (map (p: lib.nameValuePair (baseNameOf p) p) paths);
  names =
    let
      ns = map baseNameOf paths;
    in
    assert lib.assertMsg (lib.length ns == lib.length (lib.unique ns))
      "rocq.nix: two theories share a base name: ${
        toString (lib.filter (n: lib.count (m: m == n) ns > 1) (lib.unique ns))
      }";
    ns;
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
              "From[[:space:]]+Nanofil[[:space:]]+Require[[:space:]]+((Import|Export)[[:space:]]+)?([^.]*)\\."
              (builtins.readFile (theories + "/${path.${n}}.v"))
          )
        )
    )
  );
  closure = lib.genAttrs names (
    n: lib.unique (lib.concatMap (d: closure.${d} ++ [ d ]) imports.${n})
  );
  # link N: the objects of everything N imports, under theories/ at
  # their own paths, since an object records its logical path
  # (Nanofil.core.Syntax).
  link =
    n:
    lib.concatMapStrings (
      d:
      "mkdir -p theories/${dirOf path.${d}}; ln -s ${vo.${d}}/${d}.vo theories/${path.${d}}.vo\n"
    ) closure.${n};
  vo = lib.genAttrs names (
    n:
    pkgs.runCommand "nanofil-rocq-${n}"
      { nativeBuildInputs = rocqInputs ++ [ pkgs.python3 ]; }
      ''
        mkdir -p theories/${dirOf path.${n}} extraction
        ${link n}
        cp ${theories + "/${path.${n}}.v"} theories/${path.${n}}.v
        python3 ${watch} --label "Rocq compile ${path.${n}}.v" --warn-after 120 --timeout 900 -- \
          rocq c -q -R theories Nanofil theories/${path.${n}}.v
        mkdir $out
        cp theories/${path.${n}}.vo theories/${path.${n}}.glob $out/
        # Extract.v writes the OCaml model.
        if [ -n "$(ls extraction)" ]; then cp -r extraction $out/; fi
      ''
  );
  # The grammar check (web/rocq/tests/parse.sh), one theory at a time:
  # reprint it with every subterm in parentheses and compile the reprint
  # against the original objects of its imports. It needs neither its
  # own object nor the other reprints, so a grammar change reruns every
  # file at once and a theory edit reruns that file.
  parseSrc = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.unions [
      ../web/rocq/rocq_syntax.pl
      ../web/rocq/tests/parse.sh
      ../web/rocq/tests/reprint.pl
    ];
  };
  parseInputs = rocqInputs ++ [
    pkgs.swi-prolog
    pkgs.python3
  ];
  reprint = lib.genAttrs names (
    n:
    pkgs.runCommand "nanofil-rocq-reprint-${n}"
      { nativeBuildInputs = parseInputs; }
      ''
        mkdir -p project/theories/${dirOf path.${n}} verdicts
        echo "-R theories Nanofil" >project/_RocqProject
        (
          cd project
          ${link n}
        )
        cp ${theories + "/${path.${n}}.v"} project/theories/${path.${n}}.v
        PARSE_TMP=$PWD/verdicts PARSE_IN_PLACE=1 python3 ${watch} --label "Rocq reprint ${path.${n}}.v" \
          --warn-after 120 --timeout 900 -- bash ${parseSrc}/web/rocq/tests/parse.sh --check 0 "$PWD/project/theories/${path.${n}}.v"
        grep -q '^ok' verdicts/verdict-0
        mkdir $out
        cp verdicts/verdict-0 $out/verdict
      ''
  );
  # parse.sh's own Ltac, term and Iris fixtures.
  fixtures =
    pkgs.runCommand "nanofil-rocq-parse-fixtures"
      { nativeBuildInputs = parseInputs; }
      ''
        python3 ${watch} --label "Rocq grammar fixtures" --warn-after 120 --timeout 900 -- \
          bash ${parseSrc}/web/rocq/tests/parse.sh --fixtures | tee log
        mkdir $out
        cp log $out/
      '';
  parse = pkgs.runCommand "nanofil-rocq-parse" { } ''
    mkdir $out
    {
      ${lib.concatMapStrings (n: "cat ${reprint.${n}}/verdict\n") names}
      cat ${fixtures}/log
    } | tee $out/verdicts
    echo "parse: $(grep -c '^ok' $out/verdicts) files read and reprinted"
  '';
  theorySrc = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.unions [
      ../rocq/_RocqProject
      ../rocq/theories
    ];
  };
  driver = pkgs.stdenv.mkDerivation {
    name = "nanofil-rocq-driver";
    dontUnpack = true;
    nativeBuildInputs = [
      ocamlPackages.ocaml
      ocamlPackages.findlib
    ];
    buildInputs = [ ocamlPackages.zarith ];
    buildPhase = ''
      cp ${vo.Extract}/extraction/nanofil_model.ml ${vo.Extract}/extraction/nanofil_model.mli .
      cp ${../rocq/extraction/main.ml} main.ml
      ocamlfind ocamlopt -w -a -package zarith -linkpkg \
        nanofil_model.mli nanofil_model.ml main.ml -o nanofil-model
    '';
    installPhase = ''
      mkdir -p $out/bin
      cp nanofil-model $out/bin/
    '';
  };
  # The compiled theories as one tree, for the logic spikes (spikes.nix),
  # which compile against them. Nothing in CI's gate needs it.
  objects = pkgs.runCommand "nanofil-rocq-objects" { } ''
    mkdir -p $out/share/rocq/theories
    cp ${theorySrc}/rocq/_RocqProject $out/share/rocq/
    cp -r ${theorySrc}/rocq/theories/. $out/share/rocq/theories/
    chmod -R u+w $out/share/rocq/theories
    ${lib.concatMapStrings (
      n:
      "cp ${vo.${n}}/${n}.vo ${vo.${n}}/${n}.glob $out/share/rocq/theories/${dirOf path.${n}}/\n"
    ) names}
  '';
  # The model: every theory compiled, no Admitted or stray Axiom, imports
  # as rocq dep reads them, and the extracted driver, with the sources the
  # checks read (programs.sh compares the Code.v files). Its output is a
  # few MB; the objects stay in their own derivations.
  model =
    pkgs.runCommand "nanofil-rocq-model"
      {
        nativeBuildInputs = rocqInputs;
        passthru = {
          inherit
            vo
            reprint
            parse
            objects
            driver
            path
            closure
            ;
          src = theorySrc;
        };
      }
      ''
        cd ${theorySrc}/rocq
        # Axioms and parameters only inside Runtime.v's module type, which
        # InterpRuntime discharges; no Admitted anywhere.
        if grep -rnw Admitted theories ||
          grep -rnwE 'Axiom|Axioms|Parameter|Conjecture' --exclude=Runtime.v theories ||
          sed '/^Module Type Runtime\./,/^End Runtime\./d' theories/core/Runtime.v |
          grep -nwE 'Axiom|Axioms|Parameter|Conjecture'; then
          echo "rocq: no Admitted, and no Axiom outside the runtime module type" >&2
          exit 1
        fi
        # The per-file derivations import what rocq dep says each file needs.
        rocq dep -R theories Nanofil $(find theories -name '*.v' | sort) |
          awk 'function base(p,  a, k) { k = split(p, a, "/"); sub(/\..*/, "", a[k]); return a[k] }
            { t = base($1); d = ""
            for (i = 2; i <= NF; i++) if ($i ~ /^theories\/.*\.vo$/) { s = base($i); if (s != t) d = d " " s }
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
          echo "rocq.nix: a theory's imports differ from rocq dep's (- rocq dep, + rocq.nix); write them as From Nanofil Require" >&2
          exit 1
        fi
        ${lib.concatMapStrings (n: "test -e ${vo.${n}}/${n}.vo\n") names}
        echo "@@nanofil-rocq ${toString (builtins.length names)} theories compiled"
        mkdir -p $out/bin $out/share/rocq/theories $out/share/rocq/extraction
        cp ${driver}/bin/nanofil-model $out/bin/
        cp -r theories/. $out/share/rocq/theories/
        cp _RocqProject $out/share/rocq/
        cp ${../rocq/extraction/main.ml} $out/share/rocq/extraction/main.ml
      '';
  # The check reads compiler sources, harnesses and corpora, not the wiki,
  # benchmarks or theories (the latter enter through model above).
  corpus = pkgs.lib.fileset.toSource {
    root = ../.;
    fileset = pkgs.lib.fileset.unions [
      ../src
      ../bin
      ../tests
      ../rocq/scripts/agree.sh
      ../rocq/scripts/valid.sh
      ../rocq/scripts/lua.sh
      ../rocq/scripts/mutants.pl
      ../rocq/tests
      ../rocq/scripts/programs.sh
      ../rocq/scripts/gallina.pl
    ];
  };
  # The corpus reads the extracted driver (Extract.v's imports, a few of
  # the theories) and the sources, so it runs beside the proof compiles;
  # the check below still requires the whole model.
  corpusCheck =
    pkgs.runCommandCC
      (if full then "nanofil-rocq-full-corpus" else "nanofil-rocq-corpus")
      {
        nativeBuildInputs = [
          pkgs.swi-prolog
          pkgs.python3
          rocq.rocq-core
          rocq.stdlib
          rocq.stdpp
          rocq.iris
        ];
      }
      (
        ''
          set -o pipefail
          start=$SECONDS
          mark() {
            echo "@@nanofil-rocq $((SECONDS - start))s $*"
            start=$SECONDS
          }
          cp -r ${corpus} nanofil
          chmod -R u+w nanofil
          cp -r ${theorySrc}/rocq/. nanofil/rocq/
          chmod -R u+w nanofil
          cd nanofil
          patchShebangs rocq bin tests
          export FILCC=${filcc}/bin/clang MODEL=${driver}/bin/nanofil-model
          bin/nanofil --save-state "$TMPDIR/nanofil.state"
          export NANOFIL_STATE=$TMPDIR/nanofil.state
          # The modules the program proofs are about are nanofil's current
          # products (rocq/scripts/programs.sh, Panics.v).
          python3 tests/watch.py --label "Rocq program fixtures" -- bash rocq/scripts/programs.sh
          mark programs
        ''
        + (
          if !full then
            ''
              # A deliberately small, stable smoke corpus: every hand-written model
              # fixture plus ordinary checked IR, long doubles and data/aliases.
              export NANOFIL_CHECKS=reference NANOFIL_JOBS=$NIX_BUILD_CORES NANOFIL_MUTANTS=0
              tests/par.sh rocq/scripts/agree.sh rocq/tests/*.ir tests/filc/basic.ir tests/c/ldouble.c tests/c/prog/alias.c \
                | tee "$TMPDIR/quick-outcomes.log"
              tests/par.sh rocq/scripts/valid.sh rocq/tests/*.ir tests/filc/basic.ir tests/c/ldouble.c tests/c/prog/alias.c \
                | tee "$TMPDIR/quick-valid.log"
              mkdir -p $out
              cp "$TMPDIR"/quick-*.log $out/
              mark quick-base-verdicts
            ''
          else
            ''
              python3 tests/watch.py --label "mutant partition coverage" -- bash rocq/tests/partitions.sh
              # Hand-written checked IR (rocq/tests) goes in as written: the check
              # passes take pizlonate's output, never renew_hull or renew_if.
              NANOFIL_CHECKS=reference NANOFIL_JOBS=$NIX_BUILD_CORES tests/par.sh rocq/scripts/agree.sh rocq/tests/*.ir
              # Forty Fil-C modules of ten random functions (tests/gen.pl's filc
              # mode), which trap often and reach every reuse form, join the
              # matrix below.
              mkdir gen
              for seed in $(seq 1 40); do
                (cd src && ../bin/nanofil --script ../tests/gen.pl $seed 10 filc </dev/null) > gen/gen-$seed.ir
              done
              # Lua 5.4.7's lctype.c, lobject.c and lstring.c, the source nix/lua.nix
              # builds, with the run lines of rocq/tests/lua.c, join the outcome
              # matrix; the validator judges their mutants once, below, since each
              # is judged on the whole module.
              mkdir luasrc
              tar -xf ${pkgs.lua5_4.src} -C luasrc --strip-components=1
              rocq/scripts/lua.sh luasrc/src >lua.ir
              mark prepare
              # Modes are independent, just as in the validator matrix below. Keep
              # each mode's complete log and propagate any failing xargs child.
              for opt in plain -O; do
                for checks in reference reuse renew guard hoist schedule half forward combined hull getter extended; do
                  echo "$opt $checks"
                done
              done | xargs -P "$NIX_BUILD_CORES" -L 1 bash -c '
                set -o pipefail
                opt=$0; [ "$opt" = plain ] && opt=
                t0=$(date +%s)
                NANOFIL_OPT=$opt NANOFIL_CHECKS=$1 NANOFIL_JOBS=1 tests/par.sh rocq/scripts/agree.sh tests/filc/*.ir tests/c/*.c gen/*.ir lua.ir \
                  2>&1 | tee "$TMPDIR/agree-$0-$1.log" | grep --line-buffered "^@@nanofil-" \
                  || { echo "### agree NANOFIL_OPT=$opt NANOFIL_CHECKS=$1"; cat "$TMPDIR/agree-$0-$1.log"; exit 1; }
                echo "agree NANOFIL_OPT=$opt NANOFIL_CHECKS=$1: $(grep -c "^/" "$TMPDIR/agree-$0-$1.log") files agree ($(( $(date +%s) - t0 ))s)"'
              mark outcomes
              # The validator against ir:valid_module/1 on mutants of every checked
              # module (rocq/scripts/valid.sh, rocq/scripts/mutants.pl), in every mode at once.
              NANOFIL_CHECKS=reference NANOFIL_JOBS=$NIX_BUILD_CORES tests/par.sh rocq/scripts/valid.sh rocq/tests/*.ir
              # (xargs drops empty words, so "plain" stands for no -O.)
              for opt in plain -O; do
                for checks in reference reuse renew guard hoist schedule half forward combined hull getter extended; do
                  echo "$opt $checks"
                done
              done | xargs -P "$NIX_BUILD_CORES" -L 1 bash -c '
                set -o pipefail
                opt=$0; [ "$opt" = plain ] && opt=
                t0=$(date +%s)
                NANOFIL_OPT=$opt NANOFIL_CHECKS=$1 NANOFIL_JOBS=1 tests/par.sh rocq/scripts/valid.sh tests/filc/*.ir tests/c/*.c gen/*.ir \
                  2>&1 | tee "$TMPDIR/valid-$0-$1.log" | grep --line-buffered "^@@nanofil-" \
                  || { echo "### valid NANOFIL_OPT=$opt NANOFIL_CHECKS=$1"; cat "$TMPDIR/valid-$0-$1.log"; exit 1; }
                echo "valid NANOFIL_OPT=$opt NANOFIL_CHECKS=$1: $(grep -c "^/" "$TMPDIR/valid-$0-$1.log") files agree ($(( $(date +%s) - t0 ))s)"'
              mark validator-matrix
              # The C programs of tests/c/prog that declare an alias, a weak
              # symbol, thread-local data or a constructor, with the reference
              # checks only: they bring the corpus's aliases and its kinds of data
              # linkage. Not those with a "// cflags:" line, which compile as
              # progtest.sh does and not as cc-ir does.
              grep -lE 'alias *\(|weak|_Thread_local|__thread|thread_local|constructor|destructor' \
                $(grep -L '^// cflags:' tests/c/prog/*.c) >prog.list
              xargs -P "$NIX_BUILD_CORES" -n 1 bash -c '
                set -o pipefail
                NANOFIL_CHECKS=reference NANOFIL_JOBS=1 tests/par.sh rocq/scripts/valid.sh "$0" 2>&1 \
                  | tee "$TMPDIR/prog-$$.log" | grep --line-buffered "^@@nanofil-" \
                  || { echo "### valid $0"; cat "$TMPDIR/prog-$$.log"; exit 1; }' <prog.list
              # Lua's whole-module mutant generation alone takes minutes on one
              # core. Once the other programs finish, share its independent item
              # partitions across the available cores, without nested matrix fanout.
              NANOFIL_CHECKS=reference NANOFIL_JOBS=1 NANOFIL_MUTANT_JOBS=$NIX_BUILD_CORES \
                tests/par.sh rocq/scripts/valid.sh lua.ir | tee "$TMPDIR/prog-lua.log"
              echo "valid tests/c/prog and lua.ir: $(($(wc -l <prog.list) + 1)) modules agree"
              mark validator-programs
              mkdir -p $out
              cp "$TMPDIR"/agree-*.log "$TMPDIR"/valid-*.log "$TMPDIR"/prog-*.log $out/
            ''
        )
      );
in
pkgs.runCommand
  (if full then "nanofil-rocq-full-check" else "nanofil-rocq-check")
  {
    passthru = {
      inherit model;
      inherit (model) parse;
      corpus = corpusCheck;
    };
  }
  ''
    # Every theory compiled and the model's guards, and the corpus.
    test -e ${model}/bin/nanofil-model
    cp -r ${corpusCheck} $out
  ''
