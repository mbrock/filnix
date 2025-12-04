#!/usr/bin/env bash
# Quick check of which native gems exist in nixpkgs

GEMS=$(nix eval --raw --impure --expr '
  let
    pkgs = import <nixpkgs> {};
    rubyPorts = import ./rubyports.nix { inherit pkgs; };
    allGems = pkgs.lib.flatten (builtins.attrValues rubyPorts.nativeGems);
  in builtins.concatStringsSep "\n" allGems
')

echo "Native gems in rubyports.nix:"
for gem in $GEMS; do
  if nix eval ".#pkgsFilc.ruby_3_3.gems.${gem}" >/dev/null 2>&1; then
    echo "  + $gem"
  else
    echo "  - $gem (not in nixpkgs)"
  fi
done
