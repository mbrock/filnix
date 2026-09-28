# qnode: the node-compat shim in qnode.js, run by QuickJS.
{
  lib,
  runCommand,
  runtimeShell,
  quickjs,
}:
runCommand "qnode-0.1"
  {
    meta = {
      description = "Minimal Node.js compatibility layer for small CLIs, on QuickJS";
      mainProgram = "qnode";
      platforms = lib.platforms.linux;
    };
    passthru.qjs = quickjs;
  }
  ''
    install -Dm644 ${./qnode.js} $out/lib/qnode/qnode.js
    mkdir -p $out/bin
    cat > $out/bin/qnode <<EOF
    #!${runtimeShell}
    exec ${lib.getExe' quickjs "qjs"} --std \
      $out/lib/qnode/qnode.js "\$@"
    EOF
    chmod +x $out/bin/qnode
  ''
