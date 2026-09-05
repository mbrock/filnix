{
  pkgs,
  filcc,
  trealla,
  sarcasm-prolog,
}:
pkgs.runCommand "sarcasm-prolog-check"
  { nativeBuildInputs = [ pkgs.python3 ]; }
  ''
    ${trealla}/bin/tpl -q -f ${../experiments/sarcasm-prolog}/tests.pl > prolog.log
    grep -Fx 'prolog checks: ok' prolog.log
    if grep -E '^Error:' prolog.log; then exit 1; fi

    ${trealla}/bin/tpl -q -f ${../experiments/sarcasm-prolog}/edge-swap-test.pl > edge-swap.c
    ${filcc}/bin/clang -O2 edge-swap.c -o edge-swap
    ./edge-swap

    cp ${../experiments/sarcasm-prolog/examples/table-entry.s} input.s
    ${sarcasm-prolog}/bin/sarcasm-prolog --emit-c input.s > grouped.c
    ${sarcasm-prolog}/bin/sarcasm-prolog --no-coalesce --emit-c input.s > separate.c
    test "$(grep -c '__builtin_memcpy' grouped.c)" = 1
    test "$(grep -c '__builtin_memcpy' separate.c)" = 3
    ${sarcasm-prolog}/bin/sarcasm-prolog input.s > grouped.s
    sed 's/table_entry/table_entry_plain/g' input.s > plain-input.s
    ${sarcasm-prolog}/bin/sarcasm-prolog --no-coalesce plain-input.s > separate.s
    ${sarcasm-prolog}/bin/sarcasm-prolog ${../experiments/sarcasm-prolog/examples/scalars.s} > scalars.s
    cp ${../experiments/sarcasm-prolog/examples/pointers.s} pointers-input.s
    ${sarcasm-prolog}/bin/sarcasm-prolog pointers-input.s > pointers.s
    ${sarcasm-prolog}/bin/sarcasm-prolog --emit-c pointers-input.s > pointers.c
    grep -F 'const unsigned char *v1 = sp_address(v0,' pointers.c
    sed 's/pointer_entry/pointer_entry_plain/g' pointers-input.s > pointers-plain-input.s
    ${sarcasm-prolog}/bin/sarcasm-prolog --no-coalesce pointers-plain-input.s > pointers-plain.s
    cp ${../experiments/sarcasm-prolog/examples/stores.s} stores-input.s
    ${sarcasm-prolog}/bin/sarcasm-prolog stores-input.s > stores.s
    ${sarcasm-prolog}/bin/sarcasm-prolog --emit-c stores-input.s > stores.c
    sed -e 's/integer_update/integer_update_plain/g' -e 's/integer_store/integer_store_plain/g' stores-input.s > stores-plain-input.s
    ${sarcasm-prolog}/bin/sarcasm-prolog --no-coalesce stores-plain-input.s > stores-plain.s
    # These are already Fil-C compiler outputs, so use the ordinary assembler.
    for file in grouped separate scalars pointers pointers-plain stores stores-plain; do
      ${pkgs.binutils}/bin/as "$file.s" -o "$file.o"
    done
    ${filcc}/bin/clang -O2 ${../experiments/sarcasm-prolog/runtime.c} \
      grouped.o separate.o scalars.o pointers.o pointers-plain.o stores.o stores-plain.o -o runtime
    ./runtime
    python ${../experiments/sarcasm-prolog/safety.py}

    cp ${../experiments/sarcasm-prolog/examples/pointer-memory.s} pointer-memory-input.s
    ${sarcasm-prolog}/bin/sarcasm-prolog --emit-c pointer-memory-input.s > pointer-memory.c
    ${sarcasm-prolog}/bin/sarcasm-prolog pointer-memory-input.s > pointer-memory.s
    sed 's/slot_/slot_plain_/g' pointer-memory-input.s > pointer-memory-plain-input.s
    ${sarcasm-prolog}/bin/sarcasm-prolog --no-coalesce pointer-memory-plain-input.s > pointer-memory-plain.s
    for file in pointer-memory pointer-memory-plain; do
      ${pkgs.binutils}/bin/as "$file.s" -o "$file.o"
    done
    ${filcc}/bin/clang -O2 ${../experiments/sarcasm-prolog/pointer-memory-runtime.c} \
      pointer-memory.o pointer-memory-plain.o -o pointer-runtime
    ./pointer-runtime
    python ${../experiments/sarcasm-prolog/pointer-memory-safety.py}

    cp ${../experiments/sarcasm-prolog/examples/branches.s} branches-input.s
    ${sarcasm-prolog}/bin/sarcasm-prolog --emit-c branches-input.s > branches.c
    ${sarcasm-prolog}/bin/sarcasm-prolog branches-input.s > branches.s
    sed 's/branch_/branch_plain_/g' branches-input.s > branches-plain-input.s
    ${sarcasm-prolog}/bin/sarcasm-prolog --no-coalesce branches-plain-input.s > branches-plain.s
    for file in branches branches-plain; do
      ${pkgs.binutils}/bin/as "$file.s" -o "$file.o"
    done
    ${filcc}/bin/clang -O2 ${../experiments/sarcasm-prolog/branch-runtime.c} \
      branches.o branches-plain.o -o branch-runtime
    ./branch-runtime
    python ${../experiments/sarcasm-prolog/branch-safety.py}

    cp ${../experiments/sarcasm-prolog/examples/decoder.s} decoder-input.s
    cp ${../experiments/sarcasm-prolog/examples/loops.s} loops-input.s
    ${sarcasm-prolog}/bin/sarcasm-prolog --emit-c decoder-input.s > decoder.c
    ${sarcasm-prolog}/bin/sarcasm-prolog --no-coalesce --emit-c decoder-input.s > decoder-separate.c
    test "$(grep -c 'covering read: offset 0, width 4' decoder.c)" = 1
    test "$(grep -c 'covering read: offset .*width 2' decoder-separate.c)" = 2
    for file in decoder loops; do
      ${sarcasm-prolog}/bin/sarcasm-prolog "$file-input.s" > "$file.s"
      sed -e 's/tiny_decode/tiny_decode_plain/g' -e 's/loop_walk/loop_walk_plain/g' "$file-input.s" > "$file-plain-input.s"
      ${sarcasm-prolog}/bin/sarcasm-prolog --no-coalesce "$file-plain-input.s" > "$file-plain.s"
      ${pkgs.binutils}/bin/as "$file.s" -o "$file.o"
      ${pkgs.binutils}/bin/as "$file-plain.s" -o "$file-plain.o"
    done
    ${filcc}/bin/clang -O2 ${../experiments/sarcasm-prolog/decoder-runtime.c} \
      decoder.o decoder-plain.o loops.o loops-plain.o -o decoder-runtime
    timeout 30 ./decoder-runtime
    python ${../experiments/sarcasm-prolog/decoder-safety.py}
    ${pkgs.stdenv.cc}/bin/cc -O2 -DNATIVE ${../experiments/sarcasm-prolog/decoder-runtime.c} \
      decoder-input.s loops-input.s -o decoder-native
    timeout 30 ./decoder-native

    ${sarcasm-prolog}/bin/sarcasm-prolog --emit-ir decoder-input.s > decoder.ir
    grep -Fq 'comparison(unsigned,gt,32' decoder.ir
    mkdir decoder-flags
    for file in decoder loops; do
      ${sarcasm-prolog}/bin/sarcasm-prolog --no-simplify-conditions "$file-input.s" > "$file-flags.s"
      ${sarcasm-prolog}/bin/sarcasm-prolog --no-simplify-conditions --no-coalesce "$file-plain-input.s" > "$file-plain-flags.s"
      ${pkgs.binutils}/bin/as "$file-flags.s" -o "$file-flags.o"
      ${pkgs.binutils}/bin/as "$file-plain-flags.s" -o "$file-plain-flags.o"
    done
    ${filcc}/bin/clang -O2 ${../experiments/sarcasm-prolog/decoder-runtime.c} \
      decoder-flags.o decoder-plain-flags.o loops-flags.o loops-plain-flags.o -o decoder-flags/decoder-runtime
    pushd decoder-flags
    timeout 30 ./decoder-runtime
    python ${../experiments/sarcasm-prolog/decoder-safety.py}
    popd

    cp ${../experiments/sarcasm-prolog/examples/checks.s} checks-input.s
    ${sarcasm-prolog}/bin/sarcasm-prolog --emit-checks checks-input.s > checks.report
    python - <<'PY'
    from pathlib import Path
    reports = Path("checks.report").read_text().splitlines()
    expected = dict(zip(["cover", "diamond", "one_path", "store", "index", "cycle", "local_loop"],
                        [1, 1, 0, 0, 0, 0, 1]))
    assert len(reports) == len(expected), reports
    for line, (name, count) in zip(reports, expected.items()):
        assert line.startswith(f"checks(checks_{name},report("), line
        assert line.count("covered(reuse(") == count, line
    PY
    ${sarcasm-prolog}/bin/sarcasm-prolog --emit-c checks-input.s > checks.c
    ${sarcasm-prolog}/bin/sarcasm-prolog --verify-checks --emit-c checks-input.s > checks-verified.c
    cmp checks.c checks-verified.c
    ${sarcasm-prolog}/bin/sarcasm-prolog --verify-checks checks-input.s > checks.s
    sed 's/checks_/checks_plain_/g' checks-input.s > checks-plain-input.s
    ${sarcasm-prolog}/bin/sarcasm-prolog --verify-checks --no-coalesce checks-plain-input.s > checks-plain.s
    for file in checks checks-plain; do
      ${pkgs.binutils}/bin/as "$file.s" -o "$file.o"
    done
    ${filcc}/bin/clang -O2 ${../experiments/sarcasm-prolog/check-runtime.c} \
      checks.o checks-plain.o -o check-runtime
    timeout 30 ./check-runtime
    python ${../experiments/sarcasm-prolog/check-safety.py}
    ${pkgs.stdenv.cc}/bin/cc -O2 -DNATIVE ${../experiments/sarcasm-prolog/check-runtime.c} \
      checks-input.s -o check-native
    timeout 30 ./check-native
    if ${sarcasm-prolog}/bin/sarcasm-prolog --linear --emit-checks input.s > rejected.s 2> error; then
      echo 'unexpected acceptance of check analysis on linear IR' >&2
      exit 1
    fi
    test ! -s rejected.s
    grep -F 'check_analysis_requires_cfg' error

    mkdir protection-probes
    pushd protection-probes
    python ${../experiments/sarcasm-prolog}/protection-probe.py ${filcc}/bin/clang
    popd

    for arch in arm64 aarch64 mips; do
      if ${sarcasm-prolog}/bin/sarcasm-prolog --arch "$arch" input.s > rejected.s 2> error; then
        echo "unexpected target acceptance: $arch" >&2
        exit 1
      fi
      test ! -s rejected.s
      grep -E '(unsupported|unknown)_target' error
    done
    python ${../experiments/sarcasm-prolog/diagnostic-tests.py} ${sarcasm-prolog}/bin/sarcasm-prolog
    mkdir generated
    pushd generated
    python ${../experiments/sarcasm-prolog}/generated-tests.py \
      ${sarcasm-prolog}/bin/sarcasm-prolog ${filcc}/bin/clang \
      ${pkgs.stdenv.cc}/bin/cc ${pkgs.binutils}/bin/as
    popd
    mkdir branches
    pushd branches
    python ${../experiments/sarcasm-prolog}/branch-generated-tests.py \
      ${sarcasm-prolog}/bin/sarcasm-prolog ${filcc}/bin/clang \
      ${pkgs.stdenv.cc}/bin/cc ${pkgs.binutils}/bin/as
    popd
    mkdir loops
    pushd loops
    python ${../experiments/sarcasm-prolog}/loop-generated-tests.py \
      ${sarcasm-prolog}/bin/sarcasm-prolog ${filcc}/bin/clang \
      ${pkgs.stdenv.cc}/bin/cc ${pkgs.binutils}/bin/as
    popd
    mkdir $out
    cp -r generated branches loops protection-probes $out/
    cp grouped.c separate.c grouped.s separate.s pointers.c pointers.s stores.c stores.s prolog.log $out/
    cp pointer-memory.c pointer-memory.s $out/
    cp branches.c branches.s edge-swap.c $out/
    cp decoder.c decoder-separate.c decoder.s decoder-plain.s loops.s loops-plain.s $out/
    cp decoder-flags.s decoder-plain-flags.s loops-flags.s loops-plain-flags.s decoder.ir $out/
    cp checks.c checks.s checks-plain.s checks.report $out/
  ''
