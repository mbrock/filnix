{ pkgs, filcc }:
pkgs.runCommand "filc-sarcasm-check" { } ''
  # Exercise driver discovery with no SaRCAsm or minilute on ambient PATH.
  ${filcc}/bin/clang -g -O2 ${./sarcasm.c} ${./sarcasm.s} -o check
  ./check
  if ./check oob > failure.log 2>&1; then
    echo "out-of-bounds assembly load unexpectedly succeeded" >&2
    exit 1
  fi
  grep -i 'filc safety error' failure.log
  grep 'asm_load' failure.log
  mkdir -p $out
  cp failure.log $out/
''
