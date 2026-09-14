{
  pkgs,
  pkgsFilc,
  major,
}:
let
  soup = if major == 3 then pkgsFilc.libsoup_3 else pkgsFilc.libsoup_2_4;
  module = if major == 3 then "libsoup-3.0" else "libsoup-2.4";
in
pkgsFilc.stdenv.mkDerivation {
  name = "filc-libsoup${toString major}-runtime-check";
  dontUnpack = true;
  nativeBuildInputs = [
    pkgs.pkg-config
    pkgs.python3
  ];
  buildInputs = [ soup ];
  buildPhase = ''
    $CC ${./libsoup.c} $(pkg-config --cflags --libs ${module}) -o check
    python3 ${./libsoup-server.py} > server.log 2>&1 &
    server_pid=$!
    trap 'kill "$server_pid" 2>/dev/null || true' EXIT
    for attempt in $(seq 1 100); do
      test -s port && break
      kill -0 "$server_pid" || { cat server.log; exit 1; }
      sleep 0.05
    done
    test -s port
    ./check "http://127.0.0.1:$(cat port)/"
  '';
  installPhase = ''mkdir "$out"; cp server.log "$out/"'';
}
