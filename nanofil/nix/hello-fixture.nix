# Hello's linked checked module, the program the Iris proof of GNU Hello
# is about (docs/logic.md, docs/formal.md's Campaign 7), regenerated
# from the real build and compared with the committed
# rocq/theories/HelloCode.v. `generated` builds `nanofil-hello-O` as
# hello.nix does (configure, flags and link unchanged), keeping each
# object's checked term as bench/trap-census.nix does, links the terms
# with rocq/link.pl from main and prints the result with
# rocq/gallina.pl. The check fails when the two differ, so the proof
# cannot go on describing a Hello nanofil no longer makes. To refresh
# the fixture: rocq/hello-fixture.sh --update. Only the files the
# compile, the census and the link read are its source, so an edit
# elsewhere in nanofil/ leaves the check's hash, and its cached result,
# unchanged (.github/workflows/nanofil-hello-fixture.yml runs it on the
# same files).
{ pkgs, filcc }:
let
  src = pkgs.lib.fileset.toSource {
    root = ../.;
    fileset = pkgs.lib.fileset.unions [
      ../bin
      ../src
      ../bench/trap-checked.pl
      ../rocq/link.pl
      ../rocq/gallina.pl
    ];
  };
  nanofil = pkgs.runCommand "nanofil-hello-fixture-src" { } ''
    cp -r ${src} $out
    chmod -R u+w $out
    patchShebangs $out/bin
  '';
  hello =
    (import ./hello.nix {
      inherit pkgs filcc;
      nanofilSrc = src;
    }).configurations.O;
  # The census's capture: the wrapper still compiles each object with
  # nanofil, and also saves its checked term.
  captured = hello.overrideAttrs (old: {
    name = "nanofil-hello-O-terms";
    buildCommand =
      builtins.replaceStrings
        [ "echo \"== GNU hello, nanofil -O\"" "touch $out" ]
        [
          ''
            sed '/^as -o/i\
              "$NANOFIL_CENSUS_COMPILER" -O $copies $inline cc-ir "$input" >"$out.ir"\
              "$NANOFIL_CENSUS_COMPILER" --script "$NANOFIL_CENSUS_CHECKED" "$out.ir" >"$out.term"' \
              "$cc" > census-cc
            chmod +x census-cc
            cc=$PWD/census-cc
            export NANOFIL_CENSUS_COMPILER=${nanofil}/bin/nanofil
            export NANOFIL_CENSUS_CHECKED=${nanofil}/bench/trap-checked.pl
            echo "== GNU hello, nanofil -O, keeping checked terms"
          ''
          ''
            terms=$(find . -name '*.term' | wc -l)
            [ "$terms" -eq "$objects" ]
            mkdir -p $out
            find . -name '*.term' | while read -r t; do
              mkdir -p "$out/$(dirname "$t")"; cp "$t" "$out/$t"
            done
          ''
        ]
        old.buildCommand;
  });
  generated =
    pkgs.runCommand "nanofil-hello-fixture-generated"
      { nativeBuildInputs = [ pkgs.swi-prolog ]; }
      ''
        cd ${captured}
        specs=()
        for t in $(find . -name '*.term' | sort); do
          o=$(basename "$t" .o.term); specs+=("''${o#libhello_a-}=$t")
        done
        mkdir -p $out
        swipl ${nanofil}/rocq/link.pl main "''${specs[@]}" >$out/hello.linked
        swipl ${nanofil}/rocq/gallina.pl hello \
          "GNU Hello 2.12.3 (nanofil-hello-O), linked by rocq/link.pl" \
          rocq/hello-fixture.sh <$out/hello.linked >$out/HelloCode.v
      '';
in
pkgs.runCommand "nanofil-hello-fixture"
  { passthru = { inherit generated captured; }; }
  ''
    if diff -u ${../rocq/theories/HelloCode.v} ${generated}/HelloCode.v; then
      echo "hello-fixture: theories/HelloCode.v is nanofil-hello-O's linked module"
      touch $out
    else
      echo "hello-fixture: theories/HelloCode.v differs; run rocq/hello-fixture.sh --update"
      exit 1
    fi
  ''
