{
  pkgs,
  ports,
  filcc,
  sarcasm,
  projeny,
}:
let
  inherit (pkgs) lib;
  # Keep this list curated: useful interactive tools plus dependencies shared by
  # many downstream packages. Every output is retained, including headers/libs.
  groups = {
    shell = [
      "bash"
      "coreutils"
      "findutils"
      "diffutils"
      "gnugrep"
      "gnused"
      "gawk"
      "file"
      "less"
      "gnutar"
      "gzip"
      "which"
    ];
    build = [
      "gnumake"
      "gnum4"
      "bison"
      "flex"
      "pkgconf"
      "autoconf"
      "automake"
      "libtool"
    ];
    compression = [
      "zlib"
      "bzip2"
      "xz"
      "zstd"
      "brotli"
      "libarchive"
    ];
    libraries = [
      "libffi"
      "gmp"
      "mpfr"
      "libmpc"
      "expat"
      "libxml2"
      "pcre2"
      "libunistring"
      "libuv"
      "libevent"
      "ncurses"
      "readline"
      "gdbm"
    ];
    network = [
      "openssl"
      "openssl-sarcasm"
      "curlMinimal"
      "openssh"
      "git"
    ];
    runtimes = [
      "python312"
      "perl"
      "ruby_3_3"
      "lua"
    ];
    data = [
      "sqlite"
      "jq"
    ];
  };
  names = lib.concatLists (builtins.attrValues groups);
  packages = lib.genAttrs names (name: ports.${name}) // {
    inherit filcc sarcasm projeny;
  };
  manifest = pkgs.writeText "filc-baseline-manifest.json" (
    builtins.toJSON {
      inherit groups;
      packages = lib.mapAttrs (name: p: {
        version = p.version or "git";
        outputs = lib.genAttrs p.outputs (output: toString (lib.getOutput output p));
      }) packages;
    }
  );
  alternativeOpenSSL = pkgs.writeShellScriptBin "openssl-sarcasm" ''
    exec ${ports.openssl-sarcasm.bin}/bin/openssl "$@"
  '';
  environment = pkgs.buildEnv {
    name = "filc-baseline-environment";
    paths =
      (lib.mapAttrsToList (name: p: lib.getBin p) (
        removeAttrs packages [ "openssl-sarcasm" ]
      ))
      ++ [ alternativeOpenSSL ];
    pathsToLink = [
      "/bin"
      "/share/terminfo"
    ];
  };
  shell = pkgs.writeShellScriptBin "filc-baseline-shell" ''
    export PATH=${environment}/bin
    export SHELL=${ports.bash}/bin/bash
    export SSL_CERT_FILE=${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt
    export CC=clang CXX=clang++ PKG_CONFIG=pkgconf
    exec ${ports.bash}/bin/bash --noprofile --rcfile ${pkgs.writeText "filc-baseline-bashrc" ''
      PS1='[filc-baseline] \w \$ '
    ''} "$@"
  '';
  baseline = pkgs.runCommand "filc-cache-baseline" { } ''
    ${pkgs.python3}/bin/python3 ${../tests/baseline.py} ${manifest}
    mkdir -p $out/packages $out/bin
    cp ${manifest} $out/manifest.json
    ln -s ${environment} $out/environment
    ln -s ${shell}/bin/filc-baseline-shell $out/bin/filc-baseline-shell
    ${lib.concatStringsSep "\n" (
      lib.mapAttrsToList (name: p: ''
        mkdir -p $out/packages/${name}
        ${lib.concatMapStringsSep "\n" (output: ''
          ln -s ${lib.getOutput output p} $out/packages/${name}/${output}
        '') p.outputs}
      '') packages
    )}
  '';
in
{
  inherit
    baseline
    shell
    environment
    packages
    manifest
    groups
    ;
}
