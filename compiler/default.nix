# Fil-C compiler stages
# These build on each other in sequence and depend on runtime libraries
{
  base,
  lib,
  sources,
  runtime,
}:

let
  inherit (runtime)
    libyolo-glibc
    libyolo
    libpizlo
    filc-stdfil-headers
    libmojo
    ;

  # Stage 0: Bare LLVM/Clang compiler
  stage0 = import ./filc0.nix { inherit base lib sources; };
  inherit (stage0) filc0;

  # Stage 1: Compiler with basic yolo runtime
  stage1 = import ./filc1.nix {
    inherit
      base
      lib
      filc0
      libyolo-glibc
      libyolo
      filc-stdfil-headers
      ;
  };
  inherit (stage1) filc1 filc1-runtime;

  # Stage 2: Compiler with Fil-C runtime (libpizlo)
  stage2 = import ./filc2.nix {
    inherit
      base
      lib
      filc0
      libyolo
      libyolo-glibc
      libpizlo
      filc-stdfil-headers
      ;
  };
  inherit (stage2) filc2;

  # Stage 3: Compiler with memory-safe glibc (libmojo)
  # Note: libcxx will be built after this, so we pass null initially
  stage3 = import ./filc3.nix {
    inherit base filc2 libmojo;
    filc-libcxx = null;
  };
  inherit (stage3) filc3;

  # Build libcxx using filc3
  libcxx-build = import ./libcxx.nix {
    inherit
      base
      lib
      sources
      filc3
      libmojo
      ;
  };
  inherit (libcxx-build) filc-libcxx;

  # Rebuild stage3 with libcxx support
  stage3-with-cxx = import ./filc3.nix {
    inherit
      base
      filc2
      libmojo
      filc-libcxx
      ;
  };
  inherit (stage3-with-cxx) filc3xx;

in
{
  inherit
    filc0
    filc1
    filc1-runtime
    filc2
    filc3
    filc3xx
    filc-libcxx
    ;
}
