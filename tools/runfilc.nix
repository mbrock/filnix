{ pkgs, filcc }:

(pkgs.writeShellScriptBin "runfilc" ''
  set -euo pipefail

  if [ $# -eq 0 ]; then
    echo "Usage: runfilc <C code>"
    echo "Example: runfilc 'printf(\"hello\\n\");'"
    exit 1
  fi

  tmpdir=$(mktemp -d)
  trap "rm -rf $tmpdir" EXIT

  cat > "$tmpdir/script.c" << 'HEADERS'
  #include <stdio.h>
  #include <stdlib.h>
  #include <string.h>
  #include <stdint.h>
  #include <stdbool.h>
  HEADERS

  echo "int main() {" >> "$tmpdir/script.c"
  echo "$@" >> "$tmpdir/script.c"
  echo "}" >> "$tmpdir/script.c"
  ${filcc}/bin/clang -o "$tmpdir/script" "$tmpdir/script.c"
  exec "$tmpdir/script"
'').overrideAttrs (_: {
  meta.mainProgram = "runfilc";
})
