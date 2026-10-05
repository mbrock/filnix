{ pkgs, filcc }:
pkgs.runCommand "filc-unsafe-call-boundary-check"
  { nativeBuildInputs = [ pkgs.binutils ]; }
  ''
    cat > calls.c <<'C'
    extern unsigned long zunsafe_call(const char *, ...);
    extern unsigned long zunsafe_fast_call(const char *, ...);
    extern unsigned long zunsafe_buf_call(unsigned long, const char *, ...);
    unsigned long calls(void) {
      return zunsafe_call("filnix_native_target", 11)
        + zunsafe_fast_call("filnix_native_target", 19)
        + zunsafe_buf_call(0, "filnix_native_target", 23);
    }
    C
    for opt in -O0 -O2; do
      ${filcc}/bin/clang $opt -c calls.c -o ordinary.o
      ${filcc}/bin/clang $opt -yolo-assembler -c calls.c -o yolo.o
      nm -u ordinary.o > ordinary.symbols
      nm -u yolo.o > yolo.symbols
      for symbol in zunsafe_call zunsafe_fast_call zunsafe_buf_call; do
        grep -q "$symbol" ordinary.symbols
        if grep -q "$symbol" yolo.symbols; then
          echo "explicit opt-in failed to recognize $symbol" >&2
          exit 1
        fi
      done
      grep -q 'filnix_native_target' yolo.symbols
      if grep -q 'filnix_native_target' ordinary.symbols; then
        echo "ordinary compilation recognized an unsafe call intrinsic" >&2
        exit 1
      fi
    done
    touch $out
  ''
