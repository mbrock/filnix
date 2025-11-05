{
  base,
  lib,
  filc,
  filc-sysroot,
  filc-binutils,
}:

let
  inherit (lib) setupCcache;
  inherit (filc) filc-libcxx filc-glibc;
  filc3xx = filc;
  filc3xx-tranquil = filc;

  # ccache wrapper with version script handling
  filcache =
    flavor:
    base.writeShellScriptBin ("ccache-${flavor}") ''
      ${setupCcache}

      # Fil-C Clang driver has special version script handling.
      #
      # This only works if we give the version script flag
      # to the Clang driver, not to the actual linker.
      #
      # When version scripts aren't "pizlonated" properly,
      # you get a bunch of linker errors when building anything
      # that uses version scripts (e.g. OpenSSL).
      #
      # XXX: This shouldn't really be in the ccache setup wrapper.

      # Handle both -Wl,--version-script=file and -Wl,--version-script -Wl,file
      new_args=()
      prev_was_version_script=0
      for arg in "$@"; do
        if [[ "$arg" == "-Wl,--version-script="* ]]; then
          # Form 1: -Wl,--version-script=file
          new_args+=("--version-script=''${arg#-Wl,--version-script=}")
        elif [[ "$arg" == "-Wl,--version-script,"* ]]; then
          # Form 2: -Wl,--version-script,file
          new_args+=("--version-script=''${arg#-Wl,--version-script,}")
        elif [[ "$arg" == "-Wl,-version-script" ]] || [[ "$arg" == "-Wl,--version-script" ]]; then
          # Form 3: -Wl,-version-script or -Wl,--version-script (file comes next)
          prev_was_version_script=1
        elif [[ $prev_was_version_script -eq 1 ]]; then
          # This is the file argument
          new_args+=("--version-script=''${arg#-Wl,}")
          prev_was_version_script=0
        else
          new_args+=("$arg")
        fi
      done

      exec ${base.ccache}/bin/ccache ${filc3xx}/bin/${flavor} "''${new_args[@]}"
    '';

  filcache-tranquil =
    flavor:
    base.writeShellScriptBin ("ccache-${flavor}") ''
      ${setupCcache}

      # Fil-C Clang driver has special version script handling.
      #
      # This only works if we give the version script flag
      # to the Clang driver, not to the actual linker.
      #
      # When version scripts aren't "pizlonated" properly,
      # you get a bunch of linker errors when building anything
      # that uses version scripts (e.g. OpenSSL).
      #
      # XXX: This shouldn't really be in the ccache setup wrapper.

      # Handle both -Wl,--version-script=file and -Wl,--version-script -Wl,file
      new_args=()
      prev_was_version_script=0
      for arg in "$@"; do
        if [[ "$arg" == "-Wl,--version-script="* ]]; then
          # Form 1: -Wl,--version-script=file
          new_args+=("--version-script=''${arg#-Wl,--version-script=}")
        elif [[ "$arg" == "-Wl,--version-script,"* ]]; then
          # Form 2: -Wl,--version-script,file
          new_args+=("--version-script=''${arg#-Wl,--version-script,}")
        elif [[ "$arg" == "-Wl,-version-script" ]] || [[ "$arg" == "-Wl,--version-script" ]]; then
          # Form 3: -Wl,-version-script or -Wl,--version-script (file comes next)
          prev_was_version_script=1
        elif [[ $prev_was_version_script -eq 1 ]]; then
          # This is the file argument
          new_args+=("--version-script=''${arg#-Wl,}")
          prev_was_version_script=0
        else
          new_args+=("$arg")
        fi
      done

      exec ${base.ccache}/bin/ccache ${filc3xx-tranquil}/bin/${flavor} "''${new_args[@]}"
    '';

in
rec {
  filc-cc = base.runCommand "filc-cc" { } ''
    mkdir -p $out/bin
    ln -s ${filcache "clang"}/bin/ccache-clang $out/bin/clang
    ln -s ${filcache "clang++"}/bin/ccache-clang++ $out/bin/clang++
  '';

  filc-cc-tranquil = base.runCommand "filc-cc" { } ''
    mkdir -p $out/bin
    ln -s ${filcache-tranquil "clang"}/bin/ccache-clang $out/bin/clang
    ln -s ${filcache-tranquil "clang++"}/bin/ccache-clang++ $out/bin/clang++
  '';

  filc-bintools = base.wrapBintoolsWith {
    bintools = filc-binutils;
    libc = filc-sysroot;
    defaultHardeningFlags = [ ];

    extraBuildCommands = ''
      echo "-L${filc-glibc}/lib" >> $out/nix-support/libc-ldflags
      echo "-lpizlo -lyoloc -lyolom -lc++ -lc++abi" >> $out/nix-support/libc-ldflags
      echo "${filc-sysroot}/lib/ld-yolo-x86_64.so" > $out/nix-support/dynamic-linker
    '';
  };

  filcc = base.wrapCCWith {
    cc = filc-cc;
    libc = filc-sysroot;
    libcxx = filc-libcxx;
    bintools = filc-bintools;

    extraBuildCommands = ''
      echo "-Wno-unused-command-line-argument" >> $out/nix-support/cc-cflags
      echo "-L${filc-libcxx}/lib" >> $out/nix-support/cc-ldflags
      echo "-gz=none" >> $out/nix-support/cc-cflags
    '';
  };

  filcc-tranquil = base.wrapCCWith {
    cc = filc-cc-tranquil;
    libc = filc-sysroot;
    libcxx = filc-libcxx;
    bintools = filc-bintools;

    extraBuildCommands = ''
      echo "-Wno-unused-command-line-argument" >> $out/nix-support/cc-cflags
      echo "-L${filc-libcxx}/lib" >> $out/nix-support/cc-ldflags
      echo "-gz=none" >> $out/nix-support/cc-cflags
    '';
  };

  filc-aliases = base.runCommand "filc-aliases" { } ''
    mkdir -p $out/bin
    ln -s ${filcc}/bin/clang $out/bin/filc
    ln -s ${filcc}/bin/clang++ $out/bin/filc++
  '';

  filenv = base.overrideCC base.stdenv filcc;
  filenv-tranquil = base.overrideCC base.stdenv filcc-tranquil;

  withFilC =
    pkg:
    pkg.override {
      stdenv = filenv;
    };

  withFilC-tranquil =
    pkg:
    pkg.override {
      stdenv = filenv-tranquil;
    };

  # Combine withFilC, override, and overrideAttrs in one call
  # Usage: fix base.pkg { deps = {}; attrs = old: {}; }
  fix =
    pkg:
    {
      deps ? { },
      attrs ? _: { },
      tranquilize ? false,
    }:
    let
      pkgName = pkg.pname or (builtins.parseDrvName pkg.name).name;
      hasBuildInputs = (pkg.buildInputs or [ ]) != [ ] || (pkg.propagatedBuildInputs or [ ]) != [ ];
      noDepsProvided = deps == { };
      withFilC_ = if tranquilize then withFilC-tranquil else withFilC;
    in
    if hasBuildInputs && noDepsProvided then
      throw ''
        Package '${pkgName}' has buildInputs but no deps override provided.
        Run: ./query-package.sh ${pkgName}
        Then add 'deps = { ... }' to your port configuration.
      ''
    else
      (withFilC_ (pkg.override deps)).overrideAttrs attrs;

  parallelize =
    pkg:
    pkg.overrideAttrs (_: {
      enableParallelBuilding = true;
    });

  dontTest =
    pkg:
    pkg.overrideAttrs (old: {
      doCheck = false;
    });

  debug =
    pkg:
    pkg.overrideAttrs (old: {
      nativeBuildInputs = old.nativeBuildInputs or [ ] ++ [
        base.pkgs.breakpointHook
      ];
    });
}
