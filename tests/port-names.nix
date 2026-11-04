# A bare port, (for pkgs.X [ … ]), is keyed by the pname of pkgs.X
# (ports/default.nix, makeOverlay), so it lands on pkgsFilc.<pname>. When
# that is not X, pkgsFilc.X may silently not carry the port. This check
# fails when the two attributes are different derivations, or when only
# one of them is marked broken. Aliases of one derivation (libkrb5 for
# krb5) pass, and so do explicitly named ports ({ bash = for pkgs.bash … }),
# which are keyed by their name.
#
# The bare ports are found in the port lists' text: the `(for pkgs.X`
# spelling, outside comments.
{ pkgs, pkgsFilc }:
let
  inherit (pkgs) lib;
  dsl = import ../ports/default.nix { inherit lib pkgs; };
  files = [
    ../ports.nix
    ../ports/media.nix
    ../ports/pipewire-consumers.nix
    ../ports/tpm2.nix
  ];

  code =
    file:
    lib.concatStringsSep "\n" (
      lib.filter (l: !(lib.hasPrefix "#" (lib.trim l))) (
        lib.splitString "\n" (builtins.readFile file)
      )
    );
  bare =
    file:
    map lib.head (
      lib.filter builtins.isList (
        builtins.split "\\(for pkgs\\.([A-Za-z0-9_'-]+)[[:space:]]" (code file)
      )
    );
  written = lib.filter (x: pkgs ? ${x}) (lib.unique (lib.concatMap bare files));

  try =
    e:
    let
      r = builtins.tryEval e;
    in
    if r.success then r.value else null;
  drvPath = n: try pkgsFilc.${n}.drvPath;
  broken = n: try (pkgsFilc.${n}.meta.broken or false);

  check =
    x:
    let
      key = (dsl.for pkgs.${x} [ ]).pname;
      same = drvPath x == drvPath key;
      bothBroken = broken x == broken key;
    in
    {
      inherit x key;
      ok = x == key || (same && bothBroken);
      why =
        if !bothBroken then
          "only one is marked broken (${x}: ${builtins.toJSON (broken x)}, ${key}: ${builtins.toJSON (broken key)})"
        else
          "they are different derivations";
    };
  results = map check written;
  failures = lib.filter (r: !r.ok) results;
  aliases = lib.filter (r: r.ok && r.x != r.key) results;
in
pkgs.runCommand "port-names-check" { } (
  if failures == [ ] then
    ''
      echo "${toString (lib.length written)} bare ports land on their own attribute or on an alias of it:"
      ${lib.concatMapStrings (r: "echo '  ${r.x} -> ${r.key}'\n") aliases}
      touch $out
    ''
  else
    ''
      echo "Bare ports that land on another attribute than the one written:"
      ${lib.concatMapStrings (
        r: "echo '  (for pkgs.${r.x} …) lands on pkgsFilc.${r.key}, and ${r.why}'\n"
      ) failures}
      echo "Name the port as its attribute ({ ${(lib.head failures).x} = for pkgs.${(lib.head failures).x} [ … ]; }) or write the attribute it lands on."
      exit 1
    ''
)
