# Exercise the installed shaper with upstream goldens, not the build-tree DLL.
{ pkgs, pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-graphite2-runtime-check";
  inherit (pkgsFilc.graphite2) src;
  nativeBuildInputs = [ pkgs.binutils ];
  dontConfigure = true;
  buildPhase = ''
    readelf -d ${pkgsFilc.graphite2}/lib/libgraphite2.so > dynamic.txt
    grep -F '[libpizlo.so]' dynamic.txt
    grep -F '[libc.so.6666]' dynamic.txt
    if grep -E '\[(libgcc_s\.so[^]]*|libstdc\+\+\.so[^]]*|libc\.so\.6)\]' dynamic.txt; then
      echo "unexpected native runtime dependency" >&2
      exit 1
    fi

    run_case() {
      local name=$1 font=$2 stride=$3
      shift 3
      if [ "$bytes" != 1 ]; then stride=1; fi
      ${pkgsFilc.graphite2}/bin/gr2fonttest $load -bytes "$bytes" \
        -log actual.log "tests/fonts/$font" -codes "$@"
      # CharInfo's Base is a code-unit offset. These fixtures use only
      # BMP characters of uniform UTF-8 width (3, 2 and 1 respectively).
      awk -v stride="$stride" '
        /^Char/ { chars=1 }
        chars && NF==5 && $1 ~ /^[0-9]+$/ { $5 *= stride }
        { $1=$1; print }
      ' "tests/standards/$name.log" > expected.txt
      awk '{ $1=$1; print }' actual.log > actual.txt
      diff -u expected.txt actual.txt
    }
    # Fresh faces/pools on every invocation, both preloaded and demand-loaded.
    # Goldens include reordered Myanmar marks, Arabic RTL, justification and
    # a malformed bytecode regression. UTF-8/16/32 must shape identically.
    for round in 1 2 3; do
      for load in "" -demand; do
        for bytes in 1 2 4; do
          run_case padauk1 Padauk.ttf 3 1015 102F 100F 1039 100F 1031 1038
          run_case scher1 Scheherazadegr.ttf 2 0628 0628 064E 0644 064E 0654 0627 064E -rtl
          run_case charis6 charis_r_gr.ttf 1 0048 0065 006C 006C 006F 0020 004D 0075 006D -j 107
          run_case underflow underflow.ttf 1 0062 0061 0061 0061 0061 0061 0061 0062
        done
      done
    done
    echo 'ok: 72 installed graphite2 shaping goldens; Fil-C runtime linkage'
  '';
  installPhase = ''touch "$out"'';
}
