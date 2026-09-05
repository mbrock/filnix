# Executed by the flake's writeShellApplication, with pinned Nix/Cachix tools.
# Cachix reads the user's private config or CACHIX_AUTH_TOKEN/SIGNING_KEY.
flake=${FILNIX_FLAKE:-.}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
nix build -L --keep-going "$flake#baseline" --out-link result-baseline --print-out-paths "$@" > "$work/roots"
while IFS= read -r root; do
  cachix push filc "$root"
  filc-verify-cache "$root"
done < "$work/roots"
