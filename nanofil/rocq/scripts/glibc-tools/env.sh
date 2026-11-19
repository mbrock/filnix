# Source this file. It puts rocq, the standard library, std++ and Iris on
# PATH and ROCQPATH, and sets PE_MODEL to the compiled Nanofil theories of
# this checkout, so that the scripts here compile glibc trees outside Nix.
#
#   . nanofil/rocq/scripts/glibc-tools/env.sh
#
# The tools and the model are Nix outputs linked under PE_CACHE. Set
# PE_REFRESH=1 after a change under rocq/theories to rebuild the model.
# A new toolchain pin selects a new pair of links automatically.
#
# To edit theories, set PE_THEORIES=1 instead: PE_MODEL is then the
# checkout's nanofil/rocq/theories. Use rq verify --tree to check an edit.
pe_repo=$(git -C "$(dirname "${BASH_SOURCE[0]}")" rev-parse --show-toplevel)
PE_CACHE=${PE_CACHE:-$pe_repo/.amp/in/scratchpad/glibc-tools}
pe_pin=$(set -o pipefail; cat "$pe_repo/flake.lock" "$pe_repo/nanofil/nix/rocq-packages.nix" | sha256sum) || return 1
pe_linkdir=$PE_CACHE/${pe_pin%% *}
mkdir -p "$pe_linkdir" || return 1
if [ ! -e "$pe_linkdir/tools" ]; then
  nix build --impure -o "$pe_linkdir/tools" --expr "
    let flake = builtins.getFlake \"git+file://$pe_repo\";
        pkgs = import flake.inputs.nixpkgs { system = \"x86_64-linux\"; };
        rocq = import $pe_repo/nanofil/nix/rocq-packages.nix { inherit pkgs; };
    in pkgs.buildEnv {
      name = \"rocq-tools\";
      paths = [ rocq.rocq-cli rocq.stdlib rocq.stdpp rocq.iris
                rocq.rocq-core.ocamlPackages.ocaml rocq.rocq-core.ocamlPackages.findlib ];
      pathsToLink = [ \"/bin\" \"/lib\" ];
    }" || return 1
fi
export PE_CACHE
if [ -n "${PE_THEORIES:-}" ]; then
  export PE_MODEL=$pe_repo/nanofil/rocq/theories
else
  if [ ! -e "$pe_linkdir/model" ] || [ -n "${PE_REFRESH:-}" ]; then
    nix build -o "$pe_linkdir/model" "$pe_repo#checks.x86_64-linux.nanofil-rocq.model.objects" || return 1
  fi
  export PE_MODEL=$pe_linkdir/model/share/rocq/theories
fi
export PATH=$pe_linkdir/tools/bin:$PATH
ROCQPATH=$(echo "$pe_linkdir"/tools/lib/coq/*/user-contrib)
export ROCQPATH
# The gate's setting (nix/glibc.nix): less GC during large imports.
export OCAMLRUNPARAM=o=200
