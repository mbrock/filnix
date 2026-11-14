#!/usr/bin/env bash
# Build the small printer plugin with the same OCaml as the pinned Rocq.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
out=${1:?usage: plugin.sh OUTPUT}
mkdir -p "$out"
out=$(cd "$out" && pwd)
nix build --impure -o "$out/compiler" --expr "
  let f = builtins.getFlake \"git+file://$repo\";
      p = import f.inputs.nixpkgs { system = \"x86_64-linux\"; };
      rocq = import $repo/nanofil/nix/rocq-packages.nix { pkgs = p; };
  in p.buildEnv { name = \"proof-check-ocaml\";
    paths = with rocq.rocq-core.ocamlPackages; [ ocaml findlib zarith ]; }"
export PATH="$out/compiler/bin:$PATH"
export OCAMLPATH="$out/compiler/lib/ocaml/$(ocamlc -version)/site-lib:$PE_CACHE/tools/lib/ocaml/$(ocamlc -version)/site-lib${OCAMLPATH:+:$OCAMLPATH}"
cp "$here/qualify.ml" "$out/pe_qualify.ml"
(
  cd "$out"
  ocamlfind ocamlopt -rectypes -thread -package rocq-runtime.interp \
    -shared -o pe_qualify.cmxs pe_qualify.ml
  printf '%s\n' 'plugin(native) = "pe_qualify.cmxs"' >META
)
