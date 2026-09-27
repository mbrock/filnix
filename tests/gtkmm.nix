# gtkmm 3 runtime check on a Broadway display; see gtkmm/gtkmm3-runtime.cc.
{ pkgs, pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-gtkmm3-runtime-check";
  dontUnpack = true;
  nativeBuildInputs = [ pkgs.pkg-config ];
  buildInputs = [ pkgsFilc.gtkmm3 ];
  FONTCONFIG_FILE = pkgs.makeFontsConf {
    fontDirectories = [ pkgs.dejavu_fonts ];
  };
  buildPhase = ''
    $CXX -std=c++17 ${./gtkmm/gtkmm3-runtime.cc} \
      $(pkg-config --cflags --libs gtkmm-3.0) -o gtkmm-check
    export XDG_RUNTIME_DIR="$TMPDIR/runtime" XDG_CACHE_HOME="$TMPDIR/cache"
    mkdir -m 700 "$XDG_RUNTIME_DIR" "$XDG_CACHE_HOME"
    export GDK_BACKEND=broadway BROADWAY_DISPLAY=:5 GTK_A11Y=none NO_AT_BRIDGE=1
    ${pkgsFilc.gtk3.out}/bin/broadwayd :5 > broadway.log 2>&1 &
    server_pid=$!
    trap 'kill "$server_pid" 2>/dev/null || true' EXIT
    for attempt in $(seq 1 100); do
      status=0
      ./gtkmm-check > result && break || status=$?
      if [ "$status" != 77 ] || ! kill -0 "$server_pid"; then
        cat broadway.log
        exit 1
      fi
      sleep 0.1
    done
    test "$status" = 0
    cat result
  '';
  installPhase = ''cp result "$out"'';
}
