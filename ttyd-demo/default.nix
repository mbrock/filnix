{
  pkgs,
  ports,
  filc-emacs,
}:

pkgs.writeShellScriptBin "ttyd-emacs-demo" ''
  set -euo pipefail

  # Default values
  PORT=''${TTYD_PORT:-7681}
  HOST=''${TTYD_HOST:-0.0.0.0}

  # Parse arguments
  while [[ $# -gt 0 ]]; do
    case $1 in
      --port)
        PORT="$2"
        shift 2
        ;;
      --host)
        HOST="$2"
        shift 2
        ;;
      --help)
        echo "Usage: ttyd-emacs-demo [--port PORT] [--host HOST]"
        echo ""
        echo "Options:"
        echo "  --port PORT   Port to bind to (default: 7681)"
        echo "  --host HOST   Host to bind to (default: 0.0.0.0)"
        echo ""
        echo "Environment variables:"
        echo "  TTYD_PORT     Same as --port"
        echo "  TTYD_HOST     Same as --host"
        exit 0
        ;;
      *)
        echo "Unknown option: $1"
        echo "Use --help for usage information"
        exit 1
        ;;
    esac
  done

  echo "ttyd listening on http://''${HOST}:''${PORT}"

  # Run ttyd with Fil-C Emacs
  exec ${ports.ttyd}/bin/ttyd \
    --port "$PORT" \
    --interface "$HOST" \
    --writable \
    --client-option enableZmodem=true \
    --client-option fontSize=14 \
    --client-option fontFamily="'Cascadia Code', 'Fira Code', 'JetBrains Mono', monospace" \
    --client-option theme='{"background": "#1e1e1e", "foreground": "#d4d4d4"}' \
    ${filc-emacs}/bin/emacs -nw
''
