# Runtime libraries for Fil-C
# Note: Some runtime libraries depend on compiler stages, creating a circular dependency
# that's resolved through the fixed-point in flake.nix
{ base, lib, sources, filc1-runtime ? null, filc2 ? null }:

let
  # Stage 1: libyolo (no compiler dependencies)
  yolo = import ./libyolo.nix { inherit base lib sources; };
  inherit (yolo) libyolo-glibc libyolo;

  # Fil-C headers - always available (no compiler dependency)
  filc-stdfil-headers = base.runCommand "filc-stdfil-headers" {} ''
    mkdir -p $out
    cp ${sources.libpas-src}/filc/include/*.h $out/
  '';

  # Stage 2: libpizlo (depends on filc1-runtime)
  pizlo = if filc1-runtime != null
    then import ./libpizlo.nix {
      inherit base lib sources filc1-runtime libyolo-glibc libyolo filc-stdfil-headers;
    }
    else { libpizlo = null; };
  inherit (pizlo) libpizlo;

  # Stage 3: libmojo (depends on filc2)
  mojo = if filc2 != null && libpizlo != null
    then import ./libmojo.nix {
      inherit base sources filc2 libpizlo;
    }
    else { libmojo = null; };
  inherit (mojo) libmojo;

  # Stage 4: libxcrypt (depends on filc2, libpizlo, libmojo)
  xcrypt = if filc2 != null && libpizlo != null && libmojo != null
    then import ./libxcrypt.nix {
      inherit base sources filc2 libpizlo libmojo;
    }
    else { filc-xcrypt = null; };
  inherit (xcrypt) filc-xcrypt;

in {
  inherit libyolo-glibc libyolo;
  inherit libpizlo filc-stdfil-headers;
  inherit libmojo;
  inherit filc-xcrypt;
}
