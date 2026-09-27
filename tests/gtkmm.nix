# gtkmm runtime checks on a Broadway display; see gtkmm/gtkmm*-runtime.cc.
{
  pkgs,
  pkgsFilc,
  major,
}:
let
  gtkmm = if major == 3 then pkgsFilc.gtkmm3 else pkgsFilc.gtkmm4;
  gtk = if major == 3 then pkgsFilc.gtk3 else pkgsFilc.gtk4;
  module = if major == 3 then "gtkmm-3.0" else "gtkmm-4.0";
  server = if major == 3 then "broadwayd" else "gtk4-broadwayd";
in
pkgsFilc.stdenv.mkDerivation {
  name = "filc-gtkmm${toString major}-runtime-check";
  dontUnpack = true;
  nativeBuildInputs = [ pkgs.pkg-config ];
  buildInputs = [ gtkmm ];
  FONTCONFIG_FILE = pkgs.makeFontsConf {
    fontDirectories = [ pkgs.dejavu_fonts ];
  };
  buildPhase = ''
    $CXX -std=c++17 ${./gtkmm}/gtkmm${toString major}-runtime.cc \
      $(pkg-config --cflags --libs ${module}) -o gtkmm-check
    export XDG_RUNTIME_DIR="$TMPDIR/runtime" XDG_CACHE_HOME="$TMPDIR/cache"
    mkdir -m 700 "$XDG_RUNTIME_DIR" "$XDG_CACHE_HOME"
    export GDK_BACKEND=broadway BROADWAY_DISPLAY=:5 GTK_A11Y=none NO_AT_BRIDGE=1
    ${gtk.out}/bin/${server} :5 > broadway.log 2>&1 &
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
