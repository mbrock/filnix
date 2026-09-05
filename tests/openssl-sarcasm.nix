{
  pkgs,
  filcc,
  openssl,
}:
pkgs.runCommand "filc-openssl-sarcasm-check" { } ''
  ${filcc}/bin/clang -O2 -Wno-deprecated-declarations \
    -I${openssl.dev}/include ${./openssl-sarcasm.c} \
    -L${openssl.out}/lib -Wl,-rpath,${openssl.out}/lib -lcrypto -o check
  ./check
  if ./check oob > failure.log 2>&1; then
    echo "out-of-bounds AES assembly store unexpectedly succeeded" >&2
    exit 1
  fi
  grep 'filc safety error: cannot write pointer' failure.log
  grep 'AES_encrypt' failure.log
  mkdir -p $out
  cp failure.log $out/
''
