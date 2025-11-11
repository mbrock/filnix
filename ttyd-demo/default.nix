{
  pkgs,
  ports,
  filc-emacs,
}:

let
  # Lighttpd config template for reverse proxy with basic auth
  lighttpd-proxy-conf = pkgs.writeText "lighttpd-proxy.conf.template" ''
    server.modules = (
      "mod_access",
      "mod_accesslog",
      "mod_authn_file",
      "mod_auth",
      "mod_proxy",
    )

    server.port = PUBLIC_PORT_PLACEHOLDER
    server.bind = "PUBLIC_HOST_PLACEHOLDER"
    server.pid-file = "RUNDIR_PLACEHOLDER/lighttpd.pid"
    server.document-root = "RUNDIR_PLACEHOLDER"

    # Logging
    accesslog.filename = "RUNDIR_PLACEHOLDER/access.log"
    server.errorlog = "RUNDIR_PLACEHOLDER/error.log"

    # Basic authentication
    auth.backend = "htdigest"
    auth.backend.htdigest.userfile = "RUNDIR_PLACEHOLDER/htdigest"
    auth.require = ( "/" => (
      "method" => "digest",
      "realm" => "Fil-C Terminal",
      "require" => "valid-user"
    ))

    # Reverse proxy to ttyd
    proxy.server = ( "" => ( ( "host" => "127.0.0.1", "port" => TTYD_PORT_PLACEHOLDER ) ) )
    proxy.header = (
      "upgrade" => "enable",
      "https-remap" => "enable",
    )
  '';

in
pkgs.writeShellScriptBin "ttyd-emacs-demo" ''
  set -euo pipefail

  # Default values
  PUBLIC_PORT=''${TTYD_PUBLIC_PORT:-7681}
  PUBLIC_HOST=''${TTYD_PUBLIC_HOST:-0.0.0.0}
  TTYD_PORT=''${TTYD_INTERNAL_PORT:-17681}

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
        echo "  --port PORT   Public port to bind to (default: 7681)"
        echo "  --host HOST   Public host to bind to (default: 0.0.0.0)"
        echo ""
        echo "Environment variables:"
        echo "  TTYD_PUBLIC_PORT     Same as --port"
        echo "  TTYD_PUBLIC_HOST     Same as --host"
        echo "  TTYD_INTERNAL_PORT   Internal ttyd port (default: 17681)"
        exit 0
        ;;
      *)
        echo "Unknown option: $1"
        echo "Use --help for usage information"
        exit 1
        ;;
    esac
  done

  # Terminal colors
  if [ -t 1 ]; then
    BOLD=$(tput bold 2>/dev/null || true)
    GREEN=$(tput setaf 2 2>/dev/null || true)
    BLUE=$(tput setaf 4 2>/dev/null || true)
    CYAN=$(tput setaf 6 2>/dev/null || true)
    YELLOW=$(tput setaf 3 2>/dev/null || true)
    DIM=$(tput dim 2>/dev/null || true)
    RESET=$(tput sgr0 2>/dev/null || true)
  else
    BOLD="" GREEN="" BLUE="" CYAN="" YELLOW="" DIM="" RESET=""
  fi

  # Create runtime directory
  RUNDIR=''${XDG_RUNTIME_DIR:-/tmp}/filnix-ttyd-demo
  mkdir -p "$RUNDIR"

  # Generate random access code (12 characters: 3 groups of 4 hex digits)
  # Format: abcd-ef01-2345 (easier to read and type)
  RAW=$(${ports.coreutils}/bin/head -c 8 /dev/urandom | ${ports.coreutils}/bin/od -An -tx1 | ${ports.coreutils}/bin/tr -d ' \n' | ${ports.coreutils}/bin/cut -c1-12)
  ACCESS_CODE="''${RAW:0:4}-''${RAW:4:4}-''${RAW:8:4}"

  # Create htdigest password file
  REALM="Fil-C Terminal"
  USER=`whoami`

  # MD5 hash of "user:realm:password"
  HASH=$(echo -n "$USER:$REALM:$ACCESS_CODE" | ${ports.coreutils}/bin/md5sum | ${ports.coreutils}/bin/cut -d' ' -f1)
  echo "$USER:$REALM:$HASH" > "$RUNDIR/htdigest"

  # Generate lighttpd config
  CONF="$RUNDIR/lighttpd.conf"
  ${ports.gnused}/bin/sed \
    -e "s|PUBLIC_PORT_PLACEHOLDER|$PUBLIC_PORT|g" \
    -e "s|PUBLIC_HOST_PLACEHOLDER|$PUBLIC_HOST|g" \
    -e "s|TTYD_PORT_PLACEHOLDER|$TTYD_PORT|g" \
    -e "s|RUNDIR_PLACEHOLDER|$RUNDIR|g" \
    ${lighttpd-proxy-conf} > "$CONF"

  # Cleanup function
  cleanup() {
    echo ""
    echo "''${DIM}Shutting down...''${RESET}"
    [ -n "''${TTYD_PID:-}" ] && kill $TTYD_PID 2>/dev/null || true
    [ -n "''${LIGHTTPD_PID:-}" ] && kill $LIGHTTPD_PID 2>/dev/null || true
    rm -rf "$RUNDIR"
  }
  trap cleanup EXIT INT TERM

  # Start ttyd in background (internal port, localhost only)
  ${ports.ttyd}/bin/ttyd \
    --port "$TTYD_PORT" \
    --interface "127.0.0.1" \
    --writable \
    --index ${./index.html} \
    ${filc-emacs}/bin/emacs -nw &
  TTYD_PID=$!

  # Wait for ttyd to start
  echo "''${DIM}Starting ttyd on internal port $TTYD_PORT...''${RESET}"
  for i in {1..30}; do
    if ${pkgs.netcat}/bin/nc -z 127.0.0.1 $TTYD_PORT 2>/dev/null; then
      break
    fi
    sleep 0.1
  done

  # Start lighttpd in background
  ${ports.lighttpd}/sbin/lighttpd -D -f "$CONF" 2>&1 | ${ports.gnused}/bin/sed 's/^/[lighttpd] /' &
  LIGHTTPD_PID=$!

  # Wait a moment for lighttpd to start
  sleep 1

  # Display access information
  echo ""
  echo "''${BOLD}''${GREEN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━''${RESET}"
  echo "''${BOLD}  Fil-C Terminal (ttyd + lighttpd with memory safety)''${RESET}"
  echo "''${BOLD}''${GREEN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━''${RESET}"
  echo ""
  echo "  ''${CYAN}URL:''${RESET}      ''${BOLD}http://localhost:$PUBLIC_PORT''${RESET}"
  echo "  ''${CYAN}Username:''${RESET} ''${BOLD}$USER''${RESET}"
  echo "  ''${CYAN}Password:''${RESET} ''${BOLD}''${YELLOW}$ACCESS_CODE''${RESET}"
  echo ""
  echo "''${DIM}  • ttyd running on internal port $TTYD_PORT (localhost only)''${RESET}"
  echo "''${DIM}  • lighttpd reverse proxy with digest auth on port $PUBLIC_PORT''${RESET}"
  echo "''${DIM}  • All code compiled with Fil-C memory safety''${RESET}"
  echo ""
  echo "''${BOLD}''${GREEN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━''${RESET}"
  echo ""

  # Wait for processes
  wait $TTYD_PID $LIGHTTPD_PID
''
