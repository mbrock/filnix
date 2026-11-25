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
    "zegarmistrz"
    "logic"
    "glibc-proofs"
    "poison"
    "lambda-anf"
    "nfb-guide-argon"
    "nfb-guide-wonder"
    "nfb-guide-wonderful"
  ];
  rocqFiles = dir: lib.fileset.fileFilter (f: f.hasExt "v") dir;
  glibcGen = lib.fileset.maybeMissing ../../nanofil/rocq/glibc/gen;
  allRocq = lib.fileset.difference (rocqFiles ../../nanofil) glibcGen;
  theoriesRocq = rocqFiles ../../nanofil/rocq/theories;
  backendRocq = rocqFiles ../../nanofil/rocq/backend;
  spikesRocq = rocqFiles ../../nanofil/rocq/spikes;
  glibcRocq = lib.fileset.difference (rocqFiles ../../nanofil/rocq/glibc) glibcGen;
  otherRocq = lib.fileset.difference allRocq (
    lib.fileset.unions [
      theoriesRocq
      backendRocq
      spikesRocq
      glibcRocq
    ]
  );
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
      (lib.fileset.difference (rocqFiles ../../nanofil/rocq) glibcGen)
    ];
  };
  # The Rocq pages share the renderer, Prolog index and concept cards, but
  # are sharded by scope tree (theories, other, backend, spikes, glibc) so
  # edits in one tree hit Cachix for the others. Each shard emits its HTML
  # pages and meta.pl; downstream trees read theories' meta.pl for links.
  rocqBase = lib.fileset.unions [
    ../../nanofil/src
    ../../nanofil/docs/concepts
    ../../nanofil/web/rocq
    ../../nanofil/web/concepts.pl
    ../../nanofil/web/dterm_html.pl
    ../../nanofil/web/c
  ];
  rocqBaseSrc = lib.fileset.toSource {
    root = ../..;
    fileset = rocqBase;
  };
  mkRocqShard =
    name: fileset: globalsIn:
    let
      shardSrc = lib.fileset.toSource {
        root = ../..;
        fileset = lib.fileset.unions [
          rocqBase
          fileset
        ];
      };
      globalsFlags = lib.concatMapStringsSep " " (
        g: "--globals-in=${g}/meta.pl"
      ) globalsIn;
    in
    pkgs.runCommand "filnix-rocq-pages-${name}" { nativeBuildInputs = [ swipl ]; }
      ''
        mkdir -p $out
        # Skip generated IR fixtures (*Code.v, *Src.v, *Term.v) marked "Do not edit".
        mapfile -t rocq < <(cd ${shardSrc} && find nanofil -name '*.v' -print | sort |
          while read -r f; do head -c 1000 "$f" | grep -qi 'do not edit' || echo "$f"; done)
        swipl ${shardSrc}/nanofil/web/rocq/dterm_rocq.pl $out ${shardSrc} \
          --prolog=${shardSrc}/nanofil/src \
          --concepts=${shardSrc}/nanofil/docs/concepts \
          --no-index --meta-out=$out/meta.pl ${globalsFlags} "''${rocq[@]}" </dev/null
      '';
  # Independent renderers are cached separately. Proofs are drawn as written,
  # without captured proof states (nanofil/web/rocq/capture.nix), which
  # took the site's publishing minutes of coqc for little reading.
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
  rocqPagesTheories = mkRocqShard "theories" theoriesRocq [ ];
  rocqPagesBackend = mkRocqShard "backend" backendRocq [ rocqPagesTheories ];
  rocqPagesOther = mkRocqShard "other" otherRocq [
    rocqPagesTheories
    rocqPagesBackend
  ];
  rocqPagesSpikes = mkRocqShard "spikes" spikesRocq [ rocqPagesTheories ];
  rocqPagesGlibc = mkRocqShard "glibc" glibcRocq [ rocqPagesTheories ];
  rocqShards = [
    rocqPagesTheories
    rocqPagesOther
    rocqPagesBackend
    rocqPagesSpikes
    rocqPagesGlibc
  ];
  rocqPages =
    pkgs.runCommand "filnix-rocq-pages" { nativeBuildInputs = [ swipl ]; }
      ''
        mkdir -p $out
        cp ${rocqBaseSrc}/nanofil/web/rocq/dterm-rocq.css ${rocqBaseSrc}/nanofil/web/rocq/dterm-rocq.js $out/
        for shard in ${lib.concatStringsSep " " rocqShards}; do
          cp "$shard"/*.html "$out/"
        done
        swipl ${rocqBaseSrc}/nanofil/web/rocq/dterm_rocq.pl $out ${rocqBaseSrc} \
          --prolog=${rocqBaseSrc}/nanofil/src \
          --concepts=${rocqBaseSrc}/nanofil/docs/concepts \
          --index-only ${
            lib.concatMapStringsSep " " (s: "--meta-in=${s}/meta.pl") rocqShards
          } </dev/null
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
        prologPages
        rocqPages
        rocqPagesTheories
        rocqPagesOther
        rocqPagesBackend
        rocqPagesSpikes
        rocqPagesGlibc
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
