{
  pkgs,
  python3,
  demo-src,
}:

let
  pyenv = python3.withPackages (
    ps: with ps; [
      uvicorn
      starlette
      msgspec
      tagflow
      pycairo
      python-multipart
      networkx
      pyvis
    ]
  );
in
pkgs.writeShellScriptBin "python-web-demo" ''
  PORT=8000
  HOST=127.0.0.1

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
      *)
        echo "Unknown option: $1"
        echo "Usage: python-web-demo [--port PORT] [--host HOST]"
        exit 1
        ;;
    esac
  done

  cd ${demo-src}
  exec ${pyenv}/bin/uvicorn app:app --host "$HOST" --port "$PORT"
''
