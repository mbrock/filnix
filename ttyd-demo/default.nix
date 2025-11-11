{
  pkgs,
  ports,
  filc-emacs,
}:

let
  # Generate lighttpd config
  lighttpdConf = pkgs.writeText "lighttpd.conf" ''
    server.modules = (
      "mod_access",
      "mod_alias",
      "mod_accesslog",
      "mod_wstunnel",
      "mod_redirect",
    )

    server.document-root = "${./.}"
    server.port = env.PUBLIC_PORT
    server.bind = env.PUBLIC_HOST

    # Logging
    server.errorlog = env.ERROR_LOG
    accesslog.filename = env.ACCESS_LOG

    # Index file
    index-file.names = ( "index.html" )

    # MIME types
    mimetype.assign = (
      ".html" => "text/html",
      ".css"  => "text/css",
      ".js"   => "text/javascript",
      ".woff2" => "font/woff2",
      ".woff" => "font/woff",
    )

    # WebSocket proxy to ttyd backend via Unix socket
    $HTTP["url"] =~ "^/ws$" {
      wstunnel.server = ( "" => ( ( "socket" => env.TTYD_SOCKET ) ) )
      wstunnel.frame-type = "binary"
    }
  '';

in
pkgs.writeShellScriptBin "ttyd-emacs-demo" ''
  set -euo pipefail

  # Default values
  PUBLIC_PORT=''${TTYD_PUBLIC_PORT:-8080}
  PUBLIC_HOST=''${TTYD_PUBLIC_HOST:-0.0.0.0}
  RUNTIME_DIR=$(${pkgs.coreutils}/bin/mktemp -d)

  # Parse arguments
  while [[ $# -gt 0 ]]; do
    case $1 in
      --port)
        PUBLIC_PORT="$2"
        shift 2
        ;;
      --host)
        PUBLIC_HOST="$2"
        shift 2
        ;;
      --help)
        echo "Usage: ttyd-emacs-demo [--port PORT] [--host HOST]"
        echo ""
        echo "Options:"
        echo "  --port PORT   Public port to bind to (default: 8080)"
        echo "  --host HOST   Public host to bind to (default: 0.0.0.0)"
        echo ""
        echo "Environment variables:"
        echo "  TTYD_PUBLIC_PORT     Same as --port"
        echo "  TTYD_PUBLIC_HOST     Same as --host"
        exit 0
        ;;
      *)
        echo "Unknown option: $1"
        echo "Use --help for usage information"
        exit 1
        ;;
    esac
  done

  # Get actual hostname/IP for display
  HOSTNAME=$(${pkgs.hostname}/bin/hostname)
  if [[ "$PUBLIC_HOST" == "0.0.0.0" ]]; then
    DISPLAY_HOST="$HOSTNAME"
  else
    DISPLAY_HOST="$PUBLIC_HOST"
  fi

  # Cleanup function
  cleanup() {
    echo ""
    echo "Shutting down..."
    [ -n "''${TTYD_PID:-}" ] && kill $TTYD_PID 2>/dev/null || true
    [ -n "''${LIGHTTPD_PID:-}" ] && kill $LIGHTTPD_PID 2>/dev/null || true
    [ -d "$RUNTIME_DIR" ] && rm -rf "$RUNTIME_DIR"
  }
  trap cleanup EXIT INT TERM

  # Set up Unix socket path
  export TTYD_SOCKET="$RUNTIME_DIR/ttyd.sock"

  # Start ttyd on Unix socket (lighttpd will proxy to it)
  echo "Starting ttyd on Unix socket $TTYD_SOCKET..."
  ${ports.ttyd}/bin/ttyd \
    --interface "$TTYD_SOCKET" -b / --debug 7  \
    --writable --index ${./index.html} \
    ${filc-emacs}/bin/emacs -nw &
  TTYD_PID=$!

  # Wait for ttyd socket to be created
  for i in {1..30}; do
    if [ -S "$TTYD_SOCKET" ]; then
      break
    fi
    sleep 0.1
  done

  echo "Starting lighttpd on $PUBLIC_HOST:$PUBLIC_PORT..."
  export PUBLIC_PORT PUBLIC_HOST
  export ERROR_LOG="$RUNTIME_DIR/error.log"
  export ACCESS_LOG="$RUNTIME_DIR/access.log"

  ${ports.lighttpd}/bin/lighttpd -D -f ${lighttpdConf} &
  LIGHTTPD_PID=$!

  # Wait for lighttpd to start
  for i in {1..30}; do
    if ${pkgs.netcat}/bin/nc -z "$PUBLIC_HOST" "$PUBLIC_PORT" 2>/dev/null; then
      break
    fi
    sleep 0.1
  done

  echo "  http://$DISPLAY_HOST:$PUBLIC_PORT/"
  wait $TTYD_PID $LIGHTTPD_PID
''
