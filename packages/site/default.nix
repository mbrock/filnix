# The GitHub Pages site: pages/ as is, docs/ rendered with pandoc into
# docs/*.html, nanofil's Prolog drawn as terms into nanofil/*.html by
# nanofil/web/dterm.pl, nanofil's Rocq into nanofil/rocq/*.html by
# nanofil/web/rocq, nanofil's documents into nanofil/*.html (dterm) or
# nanofil/docs/*.html (pandoc), with its README as nanofil/index.html,
# the nanofil playground in nanofil/play/, and every Nix file of filnix
# drawn by dterm-nix into nix/*.html.
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
      ../../blocks
      (lib.fileset.unions (map (f: ../.. + "/${f}") nixPages))
    ];
  };
  # nanofil's documents dterm draws beside the modules, at nanofil/NAME.html,
  # with concept, module and Rocq links; README is nanofil's home page,
  # nanofil/index.html. pandoc renders the others into nanofil/docs.
  dtermDocs = [
    "README"
    "guide"
    "formal"
    "filc"
    "iris"
    "logic"
    "lambda-anf"
    "nfb-guide-argon"
    "nfb-guide-wonder"
    "nfb-guide-wonderful"
  ];
  # dterm reads Prolog, concepts, saved guide outputs and Rocq indexes.
  # Keep nanofil/docs for its document-link existence checks as well as
  # the rendered documents, but not unrelated site docs/pages/Nix.
  prologSrc = lib.fileset.toSource {
    root = ../..;
    fileset = lib.fileset.unions [
      ../../nanofil/src
      ../../nanofil/docs
      ../../nanofil/web/dterm.pl
      ../../nanofil/web/dterm_html.pl
      ../../nanofil/web/dterm_guide.pl
      ../../nanofil/web/dterm_diagram.pl
      ../../nanofil/web/dterm.css
      ../../nanofil/web/dterm.js
      ../../nanofil/web/concepts.pl
      ../../nanofil/web/c
      ../../nanofil/web/rocq/rocq_draw.pl
      ../../nanofil/web/rocq/rocq_syntax.pl
      (lib.fileset.fileFilter (f: f.hasExt "v") ../../nanofil/rocq)
    ];
  };
  # The Rocq pages read the complete Rocq/Prolog/concept index, but not
  # ordinary Markdown or the rest of the website. Keep those edits from
  # invalidating the cached rendering as well as the proof captures.
  rocqSrc = lib.fileset.toSource {
    root = ../..;
    fileset = lib.fileset.unions [
      ../../nanofil/src
      ../../nanofil/docs/concepts
      ../../nanofil/web/rocq
      ../../nanofil/web/concepts.pl
      ../../nanofil/web/dterm_html.pl
      ../../nanofil/web/c
      (lib.fileset.fileFilter (f: f.hasExt "v") ../../nanofil)
    ];
  };
  # Independent renderers are cached separately. The Rocq invocation still
  # sees every source for its real cross-file index and captured states.
  prologPages =
    pkgs.runCommand "filnix-prolog-pages" { nativeBuildInputs = [ swipl ]; }
      ''
        mkdir -p $out
        cp ${prologSrc}/nanofil/web/dterm.css ${prologSrc}/nanofil/web/dterm.js $out/
        swipl ${prologSrc}/nanofil/web/dterm.pl $out ${prologSrc}/nanofil/src \
          ${
            lib.concatMapStringsSep " " (
              d: "--doc=${prologSrc}/nanofil/docs/${d}.md"
            ) dtermDocs
          } \
          --concepts=${prologSrc}/nanofil/docs/concepts --rocq=${prologSrc}/nanofil/rocq/theories \
          --rocq=${prologSrc}/nanofil/rocq/spikes --rocq=${prologSrc}/nanofil/rocq/backend \
          --rocq=${prologSrc}/nanofil/rocq/glibc </dev/null
      '';
  rocqPages =
    pkgs.runCommand "filnix-rocq-pages" { nativeBuildInputs = [ swipl ]; }
      ''
        mkdir -p $out
        cp ${rocqSrc}/nanofil/web/rocq/dterm-rocq.css ${rocqSrc}/nanofil/web/rocq/dterm-rocq.js $out/
        mapfile -t rocq < <(cd ${rocqSrc} && find nanofil -name '*.v' | sort)
        swipl ${rocqSrc}/nanofil/web/rocq/dterm_rocq.pl $out ${rocqSrc} \
          --states=${proofStates} --states=${spikeStates} --prolog=${rocqSrc}/nanofil/src \
          --concepts=${rocqSrc}/nanofil/docs/concepts "''${rocq[@]}" </dev/null
      '';
in
pkgs.runCommand "filnix-site"
  {
    nativeBuildInputs = [
      pkgs.pandoc
      pkgs.python3
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
    export PROLOG_PAGES=${prologPages} ROCQ_PAGES=${rocqPages} \
      DTERM_DOCS=${lib.escapeShellArg (toString dtermDocs)}
    bash ${./.}/build.sh ${src} $out ${repoFiles} ${options} ${nixpkgs} \
      ${lib.escapeShellArgs nixPages}
    cp -r ${play} $out/nanofil/play
    chmod -R u+w $out/nanofil/play
    # The stream, from blocks/ (blocks/README.md), and its margin cards.
    swipl ${./.}/blocks.pl $out ${src} ${repoFiles} </dev/null
    # Every page's band, doors, crumbs and footer, from one place.
    python3 ${./.}/chrome.py $out ${src}
  ''
