{
  pkgs,
  filcc,
  zstd,
}:
let
  asm = zstd.assembler;
  cc = "${filcc}/bin/clang --filc-resource-dir=${asm}";
in
pkgs.runCommand "filc-zstd-sarcasm-check" { } ''
  mkdir -p $out
  cp -R ${asm}/lib/sarcasm sarcasm
  cp ${./sarcasm-zstd.luau} parser-test.luau
  ${asm.minilute}/bin/minilute parser-test.luau
  ${cc} -O2 ${./sarcasm-zstd.c} ${./sarcasm-zstd.s} -o access-test
  ./access-test
  for mode in load-oob store-oob readonly pointer-alignment; do
    if ./access-test "$mode" > "$out/$mode.log" 2>&1; then
      echo "expected access failure: $mode" >&2
      exit 1
    fi
    grep 'filc safety error' "$out/$mode.log"
  done
  grep 'alignment requirement' "$out/pointer-alignment.log"
  cp ${zstd.src}/lib/decompress/huf_decompress_amd64.S .
  chmod u+w huf_decompress_amd64.S
  ${pkgs.patch}/bin/patch -p3 < ${../patches/zstd-sarcasm.patch}
  ${cc} -O2 -c -I${zstd.src}/lib/decompress huf_decompress_amd64.S -o huf.o
  ${cc} -O2 -ffunction-sections -fdata-sections -Wl,--gc-sections \
    -I${zstd.src}/lib/decompress ${./zstd-sarcasm-loops.c} huf.o -o loops
  ./loops
  for mode in null oob store; do
    for decoder in 1 2; do
      if ./loops "$mode" "$decoder" > "$out/$mode-$decoder.log" 2>&1; then
        echo "expected decoder failure: $mode $decoder" >&2
        exit 1
      fi
      grep 'filc safety error' "$out/$mode-$decoder.log"
      grep "HUF_decompress4X$decoder.*fast_asm_loop" "$out/$mode-$decoder.log"
    done
  done
  ${pkgs.python3}/bin/python3 ${./zstd-sarcasm.py} ${zstd.bin}/bin/zstd ${pkgs.zstd}/bin/zstd
''
