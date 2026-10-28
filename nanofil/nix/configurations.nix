# A program check split into one derivation per nanofil configuration,
# so the configurations build in parallel instead of one after another.
#
#   import ./configurations.nix { inherit pkgs; } name configurations build
#
# configurations maps a label to NANOFIL_OPT's value; build label opt is
# the derivation that checks that configuration, named "${name}-${label}".
# The result is the check itself: it builds when every configuration's
# derivation does, links each output under its label, and exposes them
# as passthru.configurations.
{ pkgs }:
name: configurations: build:
let
  drvs = builtins.mapAttrs build configurations;
in
pkgs.runCommand name { passthru.configurations = drvs; } ''
  mkdir $out
  ${pkgs.lib.concatStrings (
    pkgs.lib.mapAttrsToList (label: drv: "ln -s ${drv} $out/${label}\n") drvs
  )}
''
