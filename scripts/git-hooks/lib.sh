# Sourced by the hooks and scripts/ship: puts Nix and the flake's devtools
# (treefmt, nixfmt, actionlint, shellcheck) on PATH, whatever the shell.
# shellcheck shell=bash
if ! command -v nix >/dev/null; then
  for dir in /nix/var/nix/profiles/default/bin "$HOME/.nix-profile/bin"; do
    [ -x "$dir/nix" ] && PATH="$dir:$PATH"
  done
fi
filnix_root=$(git rev-parse --show-toplevel)
if ! command -v treefmt >/dev/null || ! command -v nixfmt >/dev/null ||
  ! command -v actionlint >/dev/null; then
  devtools=$(nix --extra-experimental-features 'nix-command flakes' build --no-link \
    --print-out-paths "$filnix_root#devtools" 2>/dev/null) || {
    echo "filnix: cannot build .#devtools for the git hooks" >&2
    exit 1
  }
  PATH="$devtools/bin:$PATH"
fi
export PATH
