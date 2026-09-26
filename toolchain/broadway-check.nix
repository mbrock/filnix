# Run GTK3 package tests against the backend enabled by the Fil-C GTK port.
{ pkgs, gtk }:
old:
let
  runner = pkgs.writeShellScript "filnix-broadway-check" ''
    set -euo pipefail
    export XDG_RUNTIME_DIR=$(mktemp -d)
    export XDG_CACHE_HOME="$XDG_RUNTIME_DIR/cache"
    mkdir "$XDG_CACHE_HOME"
    export FONTCONFIG_FILE=${
      pkgs.makeFontsConf { fontDirectories = [ pkgs.dejavu_fonts ]; }
    }
    export GDK_BACKEND=broadway BROADWAY_DISPLAY=:5 NO_AT_BRIDGE=1
    ${gtk.out}/bin/broadwayd :5 > broadway.log 2>&1 &
    server_pid=$!
    trap 'kill "$server_pid" 2>/dev/null || true' EXIT
    printf '#include <gtk/gtk.h>\nint main(void) { return !gtk_init_check(0, 0); }\n' |
      $CC -x c - $($PKG_CONFIG --cflags --libs gtk+-3.0) -o check-display
    ready=false
    for attempt in $(seq 1 100); do
      if ./check-display; then ready=true; break; fi
      kill -0 "$server_pid" || { cat broadway.log; exit 1; }
      sleep 0.05
    done
    $ready || { cat broadway.log; exit 1; }
    "$@"
  '';
in
assert pkgs.lib.hasInfix "xvfb-run" old.checkPhase;
{
  checkPhase =
    pkgs.lib.replaceStrings
      [ "xvfb-run -s '-screen 0 800x600x24'" "xvfb-run" "meson test" "make check" ]
      [
        "${runner}"
        "${runner}"
        "meson test --num-processes=$NIX_BUILD_CORES --timeout-multiplier=4"
        "make check VERBOSE=1"
      ]
      old.checkPhase;
  nativeCheckInputs = builtins.filter (
    input: (input.pname or "") != "xvfb-run"
  ) (old.nativeCheckInputs or [ ]);
}
