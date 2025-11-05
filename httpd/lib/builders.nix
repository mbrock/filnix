{ pkgs, ports }:
{
  # Memory-safe bash script wrapper
  bashScript =
    name:
    {
      deps ? [ ],
      code ? null,
      src ? null,
      excludeShellChecks ? [ ],
      bashOptions ? [
        "errexit"
        "nounset"
        "pipefail"
      ],
    }:
    pkgs.writeShellApplication {
      inherit name excludeShellChecks bashOptions;
      runtimeInputs = deps;
      text = if src != null then builtins.readFile src else code;
      derivationArgs = {
        postBuild = ''
          substituteInPlace $out/bin/${name} \
            --replace-fail '${pkgs.runtimeShell}' '${ports.bash}/bin/bash'
        '';
      };
    };

  # Memory-safe C/C++ program builder
  filcProgram =
    name:
    {
      deps ? [ ],
      code ? null,
      src ? null,
      lang ? "c++",
    }:
    let
      extension = if lang == "c++" then "cpp" else "c";
      compiler = if lang == "c++" then "clang++" else "clang";
      sourceFile =
        if src != null then src else pkgs.writeText "${name}.${extension}" code;
    in
    pkgs.stdenv.mkDerivation {
      inherit name;
      src = sourceFile;
      nativeBuildInputs = [ ports.filcc ];
      buildInputs = deps;
      unpackPhase = "true";

      CFLAGS = pkgs.lib.concatMapStringsSep " " (dep: "-I${dep}/include") deps;

      LDFLAGS = pkgs.lib.concatMapStringsSep " " (dep: "-L${dep}/lib") deps;

      buildPhase = ''
        ${compiler} -o ${name} $src $CFLAGS $LDFLAGS -O2
      '';

      installPhase = ''
        mkdir -p $out/bin
        cp ${name} $out/bin/
      '';
    };

  # Build CGI document root from attrset of scripts
  cgi-bin =
    scripts:
    pkgs.runCommand "cgi-bin" { } ''
      mkdir -p $out
      ${pkgs.lib.concatStringsSep "\n" (
        pkgs.lib.mapAttrsToList (name: drv: ''
          ln -s ${drv}/bin/${name} $out/${name}
        '') scripts
      )}
    '';

  # Build document root with both CGI scripts and static files
  www-root =
    {
      scripts ? { },
      static ? { },
    }:
    pkgs.runCommand "www-root" { } ''
      mkdir -p $out
      ${pkgs.lib.concatStringsSep "\n" (
        pkgs.lib.mapAttrsToList (name: drv: ''
          ln -s ${drv}/bin/${name} $out/${name}
        '') scripts
      )}
      ${pkgs.lib.concatStringsSep "\n" (
        pkgs.lib.mapAttrsToList (name: file: ''
          ln -s ${file} $out/${name}
        '') static
      )}
    '';
}
