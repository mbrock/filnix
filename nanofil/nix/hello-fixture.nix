# This build captures each checked object from nanofil-hello-O. The glibc
# image generator links those terms with the captured glibc objects.
# The capture keeps the configuration, flags and native link unchanged.
{ pkgs, filcc }:
let
  src = pkgs.lib.fileset.toSource {
    root = ../.;
    fileset = pkgs.lib.fileset.unions [
      ../bin
      ../src
      ../bench/trap-checked.pl
      ../rocq/scripts/link.pl
      ../rocq/scripts/gallina.pl
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
in
# The existing .captured path names the same derivation as the check.
captured.overrideAttrs (_: { passthru = { inherit captured; }; })
