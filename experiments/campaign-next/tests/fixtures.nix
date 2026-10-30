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
    printf '@nix {"action":"setPhase","phase":"configurePhase"}\n'
    printf 'stdout-before\n'
    sleep 0.6
    printf '@nix {"action":"setPhase","phase":"buildPhase"}\n'
    printf 'stderr-after\n' >&2
    printf '\033[32;1mcolored:\033[0m <text>&\n'
    printf 'binary:\377\n'
    printf '<script>alert(1)</script>\n'
    mkdir -p "$out"
    printf 'artifact\n' > "$out/result"
  '' { };
  bad = fixture "campaign-bad" ''
    printf '@nix {"action":"setPhase","phase":"buildPhase"}\n'
    printf 'dependency-failed\n' >&2
    exit 13
  '' { };
  # A failing nanofil survey build: an earlier compiler error, then
  # nanofil's own message, then the survey's counts line.
  nanofilish = fixture "campaign-nanofilish" ''
    printf '@nix {"action":"setPhase","phase":"configurePhase"}\n'
    printf 'Running phase: configurePhase\n'
    printf 'nanofil: probe refused in config.log\n'
    printf '@nix {"action":"setPhase","phase":"buildPhase"}\n'
    printf 'Running phase: buildPhase\n'
    printf 'x.c:1:2: error: something\n'
    printf 'nanofil: unsupported construct at x.c:3\n'
    printf 'nanofil-survey: 7 objects, 1 C++, 2 fallbacks\n'
    exit 1
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
  cancelled = fixture "campaign-cancelled" ''
    printf 'waiting-for-cancel\n'
    sleep 5
    mkdir -p "$out"
  '' { };
}
