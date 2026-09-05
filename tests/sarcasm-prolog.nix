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
    mkdir $out
    cp -r generated branches $out/
    cp grouped.c separate.c grouped.s separate.s pointers.c pointers.s stores.c stores.s prolog.log $out/
    cp pointer-memory.c pointer-memory.s $out/
    cp branches.c branches.s edge-swap.c $out/
  ''
