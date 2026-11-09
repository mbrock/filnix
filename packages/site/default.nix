# The GitHub Pages site: pages/ as is, docs/ rendered with pandoc into
# docs/*.html, nanofil's Prolog drawn as terms into nanofil/*.html by
# nanofil/web/dterm.pl, nanofil's Rocq into nanofil/rocq/*.html by
# nanofil/web/rocq, nanofil's documents (its guide among them) into
# nanofil/docs/*.html, the nanofil playground in nanofil/play/, and
# every Nix file of filnix drawn by dterm-nix into nix/*.html.
# .github/workflows/pages.yml publishes it.
{
  pkgs,
  filcc,
  # For the option index: the flake's modules, and Nixpkgs' NixOS.
  filnix,
  nixpkgs,
}:
let
  inherit (pkgs) lib;
  # One SWI-Prolog for the dterm pages, the playground's build and the
  # playground in the browser (swipl-wasm is 10.1.19).
  swipl = import ../../nanofil/web/play/swipl.nix { inherit pkgs; };
  play = import ../../nanofil/web/play { inherit pkgs filcc swipl; };
  proofStates = import ../../nanofil/web/rocq/capture.nix { inherit pkgs; };
  # The logic spikes' states, with Iris; only the site depends on them.
  spikeStates = import ../../nanofil/web/rocq/capture.nix {
    inherit pkgs;
    spikes = true;
  };
  # The Nix files drawn as pages (dterm-nix): every Nix file of the
  # repository, but for the trees that are not filnix's own Nix: build
  # results (result*) and experiments/, scratch projects with their own
  # flakes. One that does not parse fails the build. The repository's
  # paths are listed for the links of the others.
  rel = f: lib.removePrefix "./" (lib.path.removePrefix ../.. f);
  drawn =
    f:
    let
      parts = lib.splitString "/" f;
    in
    lib.head parts != "experiments" && !lib.any (lib.hasPrefix "result") parts;
  nixPages = lib.filter drawn (
    map rel (
      lib.fileset.toList (lib.fileset.fileFilter (f: f.hasExt "nix") ../..)
    )
  );
  repoFiles = builtins.toFile "filnix-files" (
    lib.concatMapStrings (f: rel f + "\n") (lib.fileset.toList ../..)
  );
  # The option index of the NixOS and finix modules, from evaluating them
  # (dterm-nix/options.nix), as JSON.
  options = builtins.toFile "filnix-options.json" (
    builtins.toJSON (
      import ../../dterm-nix/options.nix {
        inherit lib;
        evalNixos =
          modules:
          import "${nixpkgs}/nixos/lib/eval-config.nix" {
            inherit (pkgs.stdenv.hostPlatform) system;
            inherit modules;
          };
        inherit filnix pkgs;
        nixpkgsRoot = nixpkgs;
        nixpkgsRev = nixpkgs.rev or "master";
      }
    )
  );
  src = lib.fileset.toSource {
    root = ../..;
    fileset = lib.fileset.unions [
      ../../docs
      ../../pages
      ../../nanofil/docs
      ../../nanofil/src
      ../../nanofil/web
      # nanofil's Rocq, wherever the development puts it (dterm-rocq).
      (lib.fileset.fileFilter (f: f.hasExt "v") ../../nanofil)
      ../../dterm-nix
      (lib.fileset.unions (map (f: ../.. + "/${f}") nixPages))
    ];
  };
  # Independent renderers are cached separately. The Rocq invocation still
  # sees every source for its real cross-file index and captured states.
  prologPages =
    pkgs.runCommand "filnix-prolog-pages" { nativeBuildInputs = [ swipl ]; }
      ''
        mkdir -p $out
        cp ${src}/nanofil/web/dterm.css ${src}/nanofil/web/dterm.js $out/
        swipl ${src}/nanofil/web/dterm.pl $out ${src}/nanofil/src \
          --doc=${src}/nanofil/docs/guide.md --doc=${src}/nanofil/docs/formal.md \
          --doc=${src}/nanofil/docs/filc.md --doc=${src}/nanofil/docs/iris.md \
          --concepts=${src}/nanofil/docs/concepts --rocq=${src}/nanofil/rocq/theories \
          --rocq=${src}/nanofil/rocq/spikes </dev/null
      '';
  rocqPages =
    pkgs.runCommand "filnix-rocq-pages" { nativeBuildInputs = [ swipl ]; }
      ''
        mkdir -p $out
        cp ${src}/nanofil/web/rocq/dterm-rocq.css ${src}/nanofil/web/rocq/dterm-rocq.js $out/
        mapfile -t rocq < <(cd ${src} && find nanofil -name '*.v' | sort)
        swipl ${src}/nanofil/web/rocq/dterm_rocq.pl $out ${src} \
          --states=${proofStates} --states=${spikeStates} --prolog=${src}/nanofil/src \
          --concepts=${src}/nanofil/docs/concepts "''${rocq[@]}" </dev/null
      '';
in
pkgs.runCommand "filnix-site"
  {
    nativeBuildInputs = [
      pkgs.pandoc
      swipl
    ];
    passthru = {
      inherit
        play
        proofStates
        spikeStates
        prologPages
        rocqPages
        ;
    };
  }
  ''
    export PROLOG_PAGES=${prologPages} ROCQ_PAGES=${rocqPages}
    bash ${./.}/build.sh ${src} $out ${repoFiles} ${options} ${nixpkgs} \
      ${lib.escapeShellArgs nixPages}
    cp -r ${play} $out/nanofil/play
  ''
