{ shell, path }:
let
  fixture =
    name: script: extra:
    builtins.derivation (
      {
        inherit name;
        system = builtins.currentSystem;
        builder = shell;
        args = [
          "-e"
          "-c"
          script
        ];
        PATH = path;
      }
      // extra
    );
in
rec {
  good = fixture "campaign-good" ''
    printf 'stdout-before\n'
    sleep 0.6
    printf 'stderr-after\n' >&2
    printf 'binary:\377\n'
    printf '<script>alert(1)</script>\n'
    mkdir -p "$out"
    printf 'artifact\n' > "$out/result"
  '' { };
  bad = fixture "campaign-bad" ''
    printf 'dependency-failed\n' >&2
    exit 13
  '' { };
  blocked = fixture "campaign-blocked" ''
    printf 'consumer-must-not-run\n'
    mkdir -p "$out"
  '' { dependency = bad; };
  shared = fixture "campaign-shared" ''
    mkdir -p "$out"
    printf 'shared\n' > "$out/result"
  '' { };
  left = fixture "campaign-left" ''
    mkdir -p "$out"
    printf 'left\n' > "$out/result"
  '' { inherit shared; };
  right = fixture "campaign-right" ''
    mkdir -p "$out"
    printf 'right\n' > "$out/result"
  '' { inherit shared; };
  graph = fixture "campaign-graph" ''
    mkdir -p "$out"
    printf 'graph\n' > "$out/result"
  '' { inherit left right; };
  slow = fixture "campaign-slow-x86_64-unknown-linux-gnufilc0-2026.10.03" ''
    printf 'ready-for-cancellation\n'
    sleep 3
    mkdir -p "$out"
  '' { };
}
