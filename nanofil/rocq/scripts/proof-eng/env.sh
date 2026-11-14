# Source this file. It puts rocq, the standard library, std++ and Iris on
# PATH and ROCQPATH, and sets PE_MODEL to the compiled Nanofil theories of
# this checkout, so that the scripts here compile glibc trees outside Nix.
#
#   . nanofil/rocq/scripts/proof-eng/env.sh
#
# The tools and the model are Nix outputs linked under PE_CACHE. Set
# PE_REFRESH=1 after a change under rocq/theories to rebuild the model.
pe_repo=$(git -C "$(dirname "${BASH_SOURCE[0]}")" rev-parse --show-toplevel)
PE_CACHE=${PE_CACHE:-$pe_repo/.amp/in/scratchpad/proof-eng}
mkdir -p "$PE_CACHE"
if [ ! -e "$PE_CACHE/tools" ]; then
  nix build --impure -o "$PE_CACHE/tools" --expr "
    let flake = builtins.getFlake \"$pe_repo\";
        pkgs = import flake.inputs.nixpkgs { system = \"x86_64-linux\"; };
        rocq = import $pe_repo/nanofil/nix/rocq-packages.nix { inherit pkgs; };
    in pkgs.buildEnv {
      name = \"rocq-tools\";
      paths = [ rocq.rocq-core rocq.stdlib rocq.stdpp rocq.iris
                rocq.rocq-core.ocamlPackages.ocaml rocq.rocq-core.ocamlPackages.findlib ];
      pathsToLink = [ \"/bin\" \"/lib\" ];
    }" || return 1
fi
if [ ! -e "$PE_CACHE/model" ] || [ -n "${PE_REFRESH:-}" ]; then
  nix build -o "$PE_CACHE/model" "$pe_repo#checks.x86_64-linux.nanofil-glibc.model.objects" || return 1
fi
export PE_CACHE
export PE_MODEL=$PE_CACHE/model/share/rocq/theories
export PATH=$PE_CACHE/tools/bin:$PATH
ROCQPATH=$(echo "$PE_CACHE"/tools/lib/coq/*/user-contrib)
export ROCQPATH
# The gate's setting (nix/glibc.nix): less GC during large imports.
export OCAMLRUNPARAM=o=200
