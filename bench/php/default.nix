# PHP 8.5 application benchmark: native Nixpkgs PHP against pkgsFilc.php85
# (release Fil-C) and pkgsFilcStaging.php85 (the staging toolchain)
# on DokuWiki, MediaWiki and WordPress (see README.md).
{
  pkgs,
  pkgsFilc,
  pkgsFilcStaging,
}:
let
  filc = pkgsFilc.php85;
  # Nixpkgs' PHP at the Fil-C build's release, with its symbol tables kept
  # so profiles resolve static functions as they do in the Fil-C build.
  native =
    (pkgs.php85.override {
      inherit (filc) version;
      hash = filc.unwrapped.src.outputHash;
      # Extension suites have timing- and CPU-affinity-sensitive tests
      # (filter's OOM test, pcntl's affinity test) that failed on loaded
      # builders, and they test nothing Fil-C-specific here.
      packageOverrides = _: prev: {
        extensions = builtins.mapAttrs (
          _: e:
          if e ? overrideAttrs then
            e.overrideAttrs {
              doCheck = false;
              dontStrip = true;
            }
          else
            e
        ) prev.extensions;
      };
    }).overrideAttrs
      {
        dontStrip = true;
        separateDebugInfo = false;
      };
  zendBench = pkgs.runCommand "php-zend-bench.php" { } ''
    tar xf ${filc.unwrapped.src} --wildcards '*/Zend/bench.php' -O > $out
  '';
in
pkgs.writeShellApplication {
  name = "php-bench";
  runtimeInputs = [
    pkgs.python3
    pkgs.perf
    pkgs.util-linux
  ];
  text = ''
    export PHP_BENCH_NATIVE=${native} PHP_BENCH_FILC=${filc} \
      PHP_BENCH_FILC_STAGING=${pkgsFilcStaging.php85} \
      PHP_BENCH_DOKUWIKI=${pkgs.dokuwiki}/share/dokuwiki \
      PHP_BENCH_MEDIAWIKI=${pkgs.mediawiki}/share/mediawiki \
      PHP_BENCH_WORDPRESS=${pkgs.wordpress}/share/wordpress \
      PHP_BENCH_WP_THEME=${pkgs.wordpressPackages.themes.twentytwentyfive} \
      PHP_BENCH_WP_SQLITE=${pkgs.wordpressPackages.plugins.sqlite-database-integration} \
      PHP_BENCH_ZEND=${zendBench}
    exec python3 -I ${./bench.py} "$@"
  '';
}
