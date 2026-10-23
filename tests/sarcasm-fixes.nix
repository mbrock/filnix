# Regression tests for our SaRCAsm .rept and call-argument carrier fixes,
# merged in release 0.687 (pizlonator/fil-c#336, #337). Both toolchain
# variants run the tests submitted with the fixes.
{ pkgs, filcc }:
pkgs.runCommand "filc-sarcasm-fixes-check" { } ''
  set -u
  # .rept in data and code: the expanded table is exact, and reading one word
  # past it traps.
  ${filcc}/bin/clang -O2 ${./sarcasm-fixes/rept-main.c} ${./sarcasm-fixes/rept.s} -o rept
  if ./rept > rept.log 2>&1; then
    echo "rept: the out-of-bounds read did not trap" >&2
    cat rept.log >&2
    exit 1
  fi
  grep -q 'rept ok' rept.log
  grep -q 'filc safety error' rept.log

  reject() {
    local src=$1 line=$2 msg=$3
    if ${filcc}/bin/clang -c "$src" -o reject.o > reject.log 2>&1; then
      echo "$src: compiled, but must be rejected" >&2
      exit 1
    fi
    grep -q "$(basename "$src"):$line:" reject.log
    grep -q "$msg" reject.log
  }
  reject ${./sarcasm-fixes/reject-rept-unmatched.s} 6 'without a matching'
  reject ${./sarcasm-fixes/reject-lea-carrier-callarg.s} 18 'passing %rdi to a call'
  reject ${./sarcasm-fixes/reject-mov-carrier-callarg.s} 16 'passing %rdi to a call'
  touch $out
''
