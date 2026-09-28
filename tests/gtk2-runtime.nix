{
  pkgs,
  pkgsFilc,
}:
# GTK 2 only has an X11 backend, so run the Fil-C program against a native
# Xvfb server; the X protocol is the only thing they share. The Murrine theme
# engine is a downstream consumer loaded as a module at run time.
pkgsFilc.stdenv.mkDerivation {
  name = "filc-gtk2-runtime-check";
  dontUnpack = true;
  nativeBuildInputs = [
    pkgs.pkg-config
    pkgs.xvfb
  ];
  buildInputs = [ pkgsFilc.gtk2 ];
  FONTCONFIG_FILE = pkgs.makeFontsConf {
    fontDirectories = [ pkgs.dejavu_fonts ];
  };
  buildPhase = ''
    $CC ${./gtk2-runtime.c} $(pkg-config --cflags --libs gtk+-2.0) -o gtk-check
    export HOME="$TMPDIR" XDG_CACHE_HOME="$TMPDIR/cache" NO_AT_BRIDGE=1 GTK_MODULES=gail
    export GTK_PATH=${pkgsFilc.gtk-engine-murrine}/lib/gtk-2.0
    Xvfb :7 -screen 0 800x600x24 -nolisten tcp > xvfb.log 2>&1 &
    server_pid=$!
    trap 'kill "$server_pid" 2>/dev/null || true' EXIT
    export DISPLAY=:7
    for attempt in $(seq 1 100); do
      status=0
      ./gtk-check && break || status=$?
      if [ "$status" != 77 ] || ! kill -0 "$server_pid"; then
        cat xvfb.log
        exit 1
      fi
      sleep 0.1
    done
    test "$status" = 0
  '';
  installPhase = ''
    mkdir "$out"
    cp xvfb.log "$out/"
  '';
}
