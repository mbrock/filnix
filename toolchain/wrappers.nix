{
  pkgs,
  filc,
  filc-sysroot,
  filc-binutils,
}:

let
  lib = import ../lib { inherit pkgs; };
  inherit (lib) setupCcache;
  inherit (filc) filc-libcxx filc-glibc;
  filc3xx = filc;

  # ccache wrapper with version script handling
  filcache =
    flavor:
    pkgs.writeShellScriptBin "ccache-${flavor}" ''
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

      exec ${pkgs.ccache}/bin/ccache ${filc3xx}/bin/${flavor} "''${new_args[@]}"
    '';

in
rec {
  filc-cc =
    pkgs.runCommand "filc-cc"
      {
        passthru = {
          # Fil-C provides memory safety via bounds checking and GC, so some
          # hardening flags are redundant or may conflict:
          # - fortify/fortify3: CONFLICTS with Fil-C's own bounds checks
          # - stackprotector: Redundant (Fil-C catches buffer overflows)
          # - stackclashprotection: Redundant (Fil-C prevents stack corruption)
          #
          # We keep: pie, pic (needed for ASLR/shared libs), strictoverflow
          # (C semantics), format (compile warnings are helpful), and others.
          hardeningUnsupportedFlags = [
            "fortify"
            "fortify3"
            "stackprotector"
            "stackclashprotection"
          ];
        };
      }
      ''
        mkdir -p $out/bin
        ln -s ${filcache "clang"}/bin/ccache-clang $out/bin/clang
        ln -s ${filcache "clang"}/bin/ccache-clang $out/bin/filcc
        ln -s ${filcache "clang++"}/bin/ccache-clang++ $out/bin/clang++
        ln -s ${filcache "clang++"}/bin/ccache-clang++ $out/bin/filc++
      '';

  filc-bintools = pkgs.wrapBintoolsWith {
    bintools = filc-binutils;
    libc = filc-sysroot;
    defaultHardeningFlags = [ ];

    extraBuildCommands = ''
      echo "-L${filc-glibc}/lib" >> $out/nix-support/libc-ldflags
      echo "-lpizlo -lyoloc -lyolom -lc++ -lc++abi" >> $out/nix-support/libc-ldflags
      echo "${filc-sysroot}/lib/ld-yolo-x86_64.so" > $out/nix-support/dynamic-linker
    '';
  };

  filcc = pkgs.wrapCCWith {
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

  filenv = pkgs.overrideCC pkgs.stdenv filcc;

  withFilC =
    pkg:
    pkg.override {
      stdenv = filenv;
    };

  # Combine withFilC, override, and overrideAttrs in one call
  # Usage: fix pkgs.pkg { deps = {}; attrs = old: {}; }
  fix =
    pkg:
    {
      deps ? { },
      attrs ? _: { },
    }:
    let
      pkgName = pkg.pname or (builtins.parseDrvName pkg.name).name;
      hasBuildInputs = (pkg.buildInputs or [ ]) != [ ] || (pkg.propagatedBuildInputs or [ ]) != [ ];
      noDepsProvided = deps == { };
    in
    if hasBuildInputs && noDepsProvided then
      throw ''
        Package '${pkgName}' has buildInputs but no deps override provided.
        Run: ./query-package.sh ${pkgName}
        Then add 'deps = { ... }' to your port configuration.
      ''
    else
      (withFilC (pkg.override deps)).overrideAttrs attrs;

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
        pkgs.breakpointHook
      ];
    });
}
