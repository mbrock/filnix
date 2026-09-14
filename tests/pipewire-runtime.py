"""Exercise installed PipeWire clients and plugins using a private daemon."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pipewire", required=True, type=Path)
    parser.add_argument("--runner")
    parser.add_argument("--libc", required=True)
    parser.add_argument("--client", action="append", default=[])
    parser.add_argument("--wpctl")
    args = parser.parse_args()

    with tempfile.TemporaryDirectory(prefix="filnix-pipewire-") as directory:
        root = Path(directory)
        env = {k: v for k, v in os.environ.items() if not k.startswith("PIPEWIRE_")}
        env.pop("LD_LIBRARY_PATH", None)
        env.update(
            HOME=directory,
            XDG_RUNTIME_DIR=directory,
            XDG_CONFIG_HOME=directory,
            DBUS_SESSION_BUS_ADDRESS=f"unix:path={directory}/no-session-bus",
            DBUS_SYSTEM_BUS_ADDRESS=f"unix:path={directory}/no-system-bus",
            SPA_PLUGIN_DIR=str(args.pipewire / "lib/spa-0.2"),
            PIPEWIRE_MODULE_DIR=str(args.pipewire / "lib/pipewire-0.3"),
            PIPEWIRE_REMOTE="filnix-test",
            FUGC_THREADS="2",
            SDL_AUDIO_DRIVER="pipewire",
            SDL_AUDIODRIVER="pipewire",
        )
        config = root / "daemon.conf"
        config.write_text("""
context.properties = {
    core.daemon = true
    core.name = filnix-test
    support.dbus = false
}
context.spa-libs = {
    audio.convert.* = audioconvert/libspa-audioconvert
    audio.adapt = audioconvert/libspa-audioconvert
    support.* = support/libspa-support
}
context.modules = [
    { name = libpipewire-module-protocol-native }
    { name = libpipewire-module-spa-node-factory }
    { name = libpipewire-module-client-node }
    { name = libpipewire-module-adapter }
    { name = libpipewire-module-link-factory }
    { name = libpipewire-module-access }
]
""")

        def command(tool, *arguments):
            prefix = [args.runner] if args.runner else []
            return [*prefix, str(args.pipewire / "bin" / tool), *arguments]

        def run(tool, *arguments):
            return subprocess.run(
                command(tool, *arguments), env=env, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                timeout=15, check=True,
            ).stdout

        def nodes():
            return [obj for obj in json.loads(run("pw-dump"))
                    if obj.get("type") == "PipeWire:Interface:Node"]

        def named_nodes():
            return [obj for obj in nodes()
                    if obj.get("info", {}).get("props", {}).get("node.name")
                    == "filnix-null"]

        with (root / "daemon.log").open("w+") as log:
            daemon = subprocess.Popen(command("pipewire", "-c", str(config)),
                                      env=env, stdout=log, stderr=log)
            try:
                deadline = time.monotonic() + 15
                while not (root / "filnix-test").exists():
                    assert daemon.poll() is None, "daemon exited during startup"
                    assert time.monotonic() < deadline, "daemon startup timed out"
                    time.sleep(0.05)
                maps = Path(f"/proc/{daemon.pid}/maps").read_text().splitlines()
                libc_maps = [line for line in maps if "/lib/libc.so.6666" in line]
                assert libc_maps and all(args.libc in line for line in libc_maps)
                assert not named_nodes()
                run("pw-cli", "create-node", "adapter", """{
                    factory.name = support.null-audio-sink
                    node.name = filnix-null
                    node.description = "Filnix virtual sink"
                    media.class = Audio/Sink
                    object.linger = true
                    audio.position = [ FL FR ]
                }""")
                created = named_nodes()
                assert len(created) == 1, created
                for client in args.client:
                    subprocess.run([client, args.libc], env=env, check=True, timeout=20)
                if args.wpctl:
                    status = subprocess.run(
                        [args.wpctl, "status"], env=env, check=True, timeout=20,
                        text=True, stdout=subprocess.PIPE,
                    ).stdout
                    # The status includes random server cookies and process IDs.
                    # Preserve the actual assertion without putting that varying
                    # diagnostic in the Nix check's saved output.
                    assert "Filnix virtual sink" in status, status
                    print("WirePlumber: live PipeWire virtual sink discovery passed")
                run("pw-cli", "destroy", str(created[0]["id"]))
                assert not named_nodes(), "node survived destruction"
                daemon.terminate()
                assert daemon.wait(timeout=15) == 0, "daemon failed during shutdown"
                print("private libc: installed daemon, pw-cli, pw-dump, adapter "
                      "creation/destruction and clean shutdown passed")
            except BaseException as error:
                log.flush()
                log.seek(0)
                print(log.read(), file=sys.stderr, flush=True)
                if isinstance(error, subprocess.CalledProcessError):
                    print(error.stdout, error.stderr, file=sys.stderr)
                raise
            finally:
                if daemon.poll() is None:
                    daemon.kill()
                    daemon.wait()


if __name__ == "__main__":
    main()
