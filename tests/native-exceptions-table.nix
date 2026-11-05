# docs/nixos.md's table of built-in native exceptions is generated from
# lib/native-exceptions.nix; this fails when the two differ. Print the
# table to paste between the markers with
#
#   nix eval --raw .#checks.x86_64-linux.native-exceptions-table.table
{ pkgs }:
let
  inherit (pkgs) lib;
  data = import ../lib/native-exceptions.nix;
  # Both systems' first, then NixOS's, then finix's.
  group =
    e:
    if lib.length e.os == 2 then
      0
    else if lib.elem "nixos" e.os then
      1
    else
      2;
  names = lib.sort (
    a: b:
    group data.${a} < group data.${b}
    || (group data.${a} == group data.${b} && a < b)
  ) (lib.attrNames data);
  mark = os: e: if lib.elem os e.os then "✓" else "";
  table = ''
    | Package | NixOS | finix | Why |
    | --- | --- | --- | --- |
  ''
  + lib.concatMapStrings (
    n:
    let
      e = data.${n};
    in
    "| `${n}` | ${mark "nixos" e} | ${mark "finix" e} | ${e.why} |\n"
  ) names;
in
pkgs.runCommand "native-exceptions-table"
  {
    inherit table;
    passAsFile = [ "table" ];
    passthru = { inherit table; };
  }
  ''
    sed -n '/<!-- native-exceptions -->/,/<!-- \/native-exceptions -->/p' ${../docs/nixos.md} |
      sed '1d;$d' > docs
    if ! diff -u docs "$tablePath"; then
      echo "docs/nixos.md: replace the table between the native-exceptions markers with" >&2
      echo "  nix eval --raw .#checks.x86_64-linux.native-exceptions-table.table" >&2
      exit 1
    fi
    touch $out
  ''
