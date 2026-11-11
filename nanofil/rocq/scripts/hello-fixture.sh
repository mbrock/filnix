#!/usr/bin/env bash
# Check, or with --update rewrite, rocq/theories/hello_contracts/HelloCode.v: GNU Hello's
# linked checked module, regenerated from the real nanofil-hello-O build
# by nix/hello-fixture.nix (link.pl, then gallina.pl).
#
#   rocq/scripts/hello-fixture.sh            # check
#   rocq/scripts/hello-fixture.sh --update   # rewrite HelloCode.v
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
if [ "${1:-}" = --update ]; then
  out=$(nix build --no-link --print-out-paths \
    "$root#checks.x86_64-linux.nanofil-hello-fixture.generated")
  cp "$out/HelloCode.v" "$here/../theories/hello_contracts/HelloCode.v"
  chmod u+w "$here/../theories/hello_contracts/HelloCode.v"
  echo "hello-fixture: wrote theories/hello_contracts/HelloCode.v"
else
  nix build -L --no-link "$root#checks.x86_64-linux.nanofil-hello-fixture"
fi
