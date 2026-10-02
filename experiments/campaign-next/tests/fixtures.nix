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
    sleep 0.12
    printf 'stderr-after\n' >&2
    printf 'binary:\377\n'
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
  slow = fixture "campaign-slow" ''
    printf 'ready-for-cancellation\n'
    sleep 30
    mkdir -p "$out"
  '' { };
}
