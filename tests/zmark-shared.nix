# zmark_shared regressions (docs/zmark-shared.md): pointers stored in a marked
# shared mapping after fork are usable by every process; foreign pointers are
# refused; hostile and native writers can only move addresses within the
# mapping; an unmarked mapping behaves exactly as before; code compiled without
# -fzmark-shared fails safe on a marked mapping.
{ pkgs, pkgsFilc }:
let
  nativeWriter = pkgs.runCommandCC "zmark-native-writer" { } ''
    mkdir -p $out/bin
    $CC -O2 ${./zmark-shared/native-writer.c} -o $out/bin/native-writer
  '';
in
pkgsFilc.stdenv.mkDerivation {
  name = "filc-zmark-shared-check";
  dontUnpack = true;
  buildPhase = ''
    ln -s ${nativeWriter}/bin/native-writer native-writer
    for opt in -O0 -O2; do
      echo "== $opt"
      # zmark.c opts in; unflagged.c is ordinary code linked into the same program.
      $CC $opt -g -c ${./zmark-shared/unflagged.c} -o unflagged.o
      $CC $opt -g -fzmark-shared ${./zmark-shared/zmark.c} unflagged.o -o zmark
      bash ${./zmark-shared/run.sh}
      $CC $opt -fzmark-shared ${./zmark-shared/hashtable.c} -o hashtable
      ./hashtable 8 20000
    done
  '';
  installPhase = ''
    touch "$out"
  '';
}
