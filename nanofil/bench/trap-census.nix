# Campaign 7 step 0. Keep hello.nix's configure, CC, flags, link and tests;
# instrument only its CC wrapper to retain the compiler products.
# nix build --impure -f nanofil/bench/trap-census.nix -o /tmp/trap-census
let
  flake = builtins.getFlake (toString ../..);
  pkgs = import flake.inputs.nixpkgs { system = "x86_64-linux"; };
  filcc = flake.packages.x86_64-linux.filcc-staging;
  nanofil = pkgs.runCommand "nanofil-census-src" { } ''
    cp -r ${../.} $out
    chmod -R u+w $out
    patchShebangs $out/bin
  '';
  hello = (import ../nix/hello.nix { inherit pkgs filcc; }).configurations.O;
  captured = hello.overrideAttrs (old: {
    name = "nanofil-hello-O-census";
    buildCommand =
      builtins.replaceStrings
        [ "echo \"== GNU hello, nanofil -O\"" "touch $out" ]
        [
          ''
            # The wrapper still produces each real object with nanofil. Save
            # the same preprocessed input and middle-end choices for the query.
            sed '/^as -o/i\
              "$NANOFIL_CENSUS_COMPILER" -O $copies $inline cc-ir "$input" >"$out.ir"\
              "$NANOFIL_CENSUS_COMPILER" --script "$NANOFIL_CENSUS_CHECKED" "$out.ir" >"$out.term"' \
              "$cc" | sed '/^rm "\$out.i"/d' > census-cc
            chmod +x census-cc
            cc=$PWD/census-cc
            export NANOFIL_CENSUS_COMPILER=${nanofil}/bin/nanofil
            export NANOFIL_CENSUS_CHECKED=${nanofil}/bench/trap-checked.pl
            echo "== GNU hello, nanofil -O, retaining census products"
          ''
          ''
            terms=$(find . -name '*.term' | wc -l)
            [ "$terms" -eq "$objects" ]
            mkdir -p $out/build
            cp -r . $out/build/
          ''
        ]
        old.buildCommand;
  });
  model =
    (import ../nix/rocq.nix { inherit pkgs filcc; }).model.overrideAttrs
      (old: {
        name = "nanofil-census-extraction";
        # The usual entry points reach valid_items but not the option-valued
        # valid. Extract that existing definition too, without editing a .v.
        buildPhase = old.buildPhase + ''
          { cat theories/core/Extract.v
            echo 'From Nanofil Require Import Validate.'
            echo 'Extraction "nanofil_model.ml" term_eqb decode_module judge judge_valid valid.'
          } | rocq repl -quiet -Q theories Nanofil
          grep -q '^val valid :' extraction/nanofil_model.mli
        '';
        installPhase = old.installPhase + ''
          mkdir -p $out/extraction
          cp extraction/nanofil_model.ml extraction/nanofil_model.mli extraction/main.ml $out/extraction/
        '';
      });
  ocaml = pkgs.rocqPackages.rocq-core.ocamlPackages;
in
pkgs.runCommandCC "nanofil-trap-census"
  {
    nativeBuildInputs = [
      pkgs.swi-prolog
      pkgs.python3
      ocaml.ocaml
      ocaml.findlib
    ];
    buildInputs = [ ocaml.zarith ];
  }
  ''
    set -o pipefail
    mkdir -p $out/hello $out/hi
    cp -r ${captured}/build $out/hello/
    chmod -R u+w $out
    export SWIPL=${pkgs.swi-prolog}/bin/swipl FILCC=${filcc}/bin/clang
    export NANOFIL_STATE=$TMPDIR/nanofil.state
    ${nanofil}/bin/nanofil --save-state "$NANOFIL_STATE"
    printf '#include <stdio.h>\nint main(void) { puts("hello"); return 0; }\n' >$out/hi/hi.c
    $FILCC -O2 -U__SIZEOF_INT128__ -E $out/hi/hi.c -o $out/hi/hi.i
    ${nanofil}/bin/nanofil -O cc-ir $out/hi/hi.i >$out/hi/hi.ir
    ${nanofil}/bin/nanofil --checks=combined outcomes $out/hi/hi.ir >$out/hi/hi.term
    ${nanofil}/bin/nanofil -O cc $out/hi/hi.i >$out/hi/hi.s
    ${pkgs.binutils}/bin/as -o $out/hi/hi.o $out/hi/hi.s
    $FILCC $out/hi/hi.o -o $out/hi/hi
    $out/hi/hi >$out/hi/stdout

    cp ${model}/extraction/* .
    # Reuse the driver's exact Prolog-term parser, not another decoder.
    sed '/^let () =/,$d' main.ml >parser.ml
    cp ${./trap-valid.ml} census.ml
    ocamlfind ocamlopt -w -a -package zarith -linkpkg nanofil_model.mli nanofil_model.ml parser.ml census.ml -o census-valid
    mkdir -p $out/bin
    cp census-valid $out/bin/
    cp ${pkgs.hello}/bin/hello $out/hello/stock-hello
    ${pkgs.binutils}/bin/nm -D $out/hello/stock-hello >$out/hello/stock-dynamic-symbols.txt
    for program in hi hello; do
      mapfile -t terms < <(find $out/$program -name '*.term' | sort)
      python3 ${nanofil}/tests/watch.py --label "$program-residual" -- \
        ${nanofil}/bin/nanofil --script ${nanofil}/bench/residual.pl --sites-only "''${terms[@]}" | tee $out/$program/residual.log
      for term in "''${terms[@]}"; do
        echo "@@nanofil-census $(date -u +%FT%TZ) valid $term"
        python3 ${nanofil}/tests/watch.py --label "valid-$term" -- \
          ./census-valid <"$term" | tee "$term.valid"
      done
      ${nanofil}/bin/nanofil --script ${nanofil}/bench/trap-census.pl "''${terms[@]}" >$out/$program/obligations.pl
    done
    ${pkgs.binutils}/bin/nm -D $out/hello/build/hello >$out/hello/dynamic-symbols.txt
    ${pkgs.binutils}/bin/nm -u $out/hello/build/src/hello.o >$out/hello/main-undefined.txt
    echo "@@nanofil-census $(date -u +%FT%TZ) finished"
  ''
