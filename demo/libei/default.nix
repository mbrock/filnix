{
  lib,
  pkgs,
  cnode,
  erlang,
  runnerName ? "libei-ping-demo",
  description ? "End-to-end ping demo proving libei can talk to an Erlang node",
  alive ? "libei_ping",
}:

let
  runner = pkgs.writeShellScriptBin "${runnerName}" ''
    set -euo pipefail

    tmp="$(${pkgs.coreutils}/bin/mktemp -d)"
    log="$tmp/cnode.log"
    cookie="filc_libei_cookie"
    alive="${alive}"
    server="ping_server"
    target_node=""

    cleanup() {
      if [[ -n "''${cnode_pid:-}" ]]; then
        kill "$cnode_pid" 2>/dev/null || true
        wait "$cnode_pid" 2>/dev/null || true
      fi
      ${pkgs.coreutils}/bin/rm -rf "$tmp"
    }

    trap cleanup EXIT

    ${erlang}/bin/epmd -daemon >/dev/null 2>&1 || true

    ${cnode}/bin/libei-ping-cnode \
      --alive "$alive" \
      --server "$server" \
      --cookie "$cookie" \
      >"$log" 2>&1 &
    cnode_pid=$!

    for _ in $(${pkgs.coreutils}/bin/seq 1 100); do
      target_node="$(${pkgs.gnused}/bin/sed -n 's/^READY node=\([^ ]*\) .*/\1/p' "$log" | ${pkgs.coreutils}/bin/tail -n 1)"
      if [[ -n "$target_node" ]]; then
        break
      fi
      ${pkgs.coreutils}/bin/sleep 0.1
    done

    if [[ -z "$target_node" ]]; then
      echo "${runnerName}: cnode never reported readiness" >&2
      ${pkgs.coreutils}/bin/cat "$log" >&2 || true
      exit 1
    fi

    echo "${runnerName}: probing $target_node via $server"

    if ! ${erlang}/bin/escript ${./ping_check.escript} "$cookie" "$target_node" "$server"; then
      echo "${runnerName}: Erlang-side probe failed" >&2
      ${pkgs.coreutils}/bin/cat "$log" >&2 || true
      exit 1
    fi

    wait "$cnode_pid"
    ${pkgs.coreutils}/bin/cat "$log"
  '';
in
pkgs.buildEnv {
  name = runnerName;

  paths = [
    cnode
    runner
  ];

  meta = with lib; {
    mainProgram = runnerName;
    inherit description;
    longDescription = ''
      Builds a tiny cnode with erl_interface/ei, publishes it via epmd,
      and uses an Erlang node to send a ping and verify the pong reply.
    '';
  };
}
