# Opt-in runtime experiment; never changes pkgsFilc.stdenv or its libc.
#   nix build --impure -f tests/pipewire-cancellation.nix probe
#   nix build --impure -f tests/pipewire-cancellation.nix pipewire --keep-failed
let
  f = builtins.getFlake (toString ../.);
  pkgs = import f.inputs.nixpkgs { system = "x86_64-linux"; };
  p = f.legacyPackages.x86_64-linux.pkgsFilc;
  compiler = import ../build-filc.nix {
    inherit pkgs;
    filc0 = (import ../compiler/filc0.nix { inherit pkgs; }).filc0;
  };

  # Keep the same derivation as the first isolated cancellation probe. Further
  # libc patches belong on this copy until their behavior is established.
  libc = compiler.filc-glibc.overrideAttrs (old: {
    pname = "filc-glibc-cancel-probe";
    postPatch = old.postPatch + ''
      substituteInPlace nptl/pthread_cancel.c \
        --replace-fail '#ifdef SHARED' '#if defined(SHARED) && !defined(__FILC__)'
    '';
  });

  # Meson sets LD_LIBRARY_PATH for build-tree libraries. Prepend our libc
  # inside the per-test wrapper, after Meson has prepared that environment.
  runner = pkgs.writeShellScript "with-filc-cancellation-libc" ''
    export LD_LIBRARY_PATH="${libc}/lib''${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
    exec "$@"
  '';
in
{
  inherit libc;

  # This proves that an executable built with the ordinary toolchain loads
  # the private libc and successfully unwinds through its cleanup handler.
  probe = p.stdenv.mkDerivation {
    name = "filc-private-libc-cancellation-check";
    dontUnpack = true;
    buildPhase = ''
      $CC -O2 -Werror ${./pthread-cancel.c} -pthread -o check
      FUGC_THREADS=2 ${runner} timeout 15 ./check ${libc}
    '';
    installPhase = ''touch "$out"'';
  };

  # Only this leaf derivation changes. Compilation and all dependencies still
  # use the ordinary toolchain; all Meson test processes use the private libc.
  # Blocking pause() cancellation remains an expected, enabled test failure.
  pipewire = (import ./pipewire-core.nix).overrideAttrs (old: {
    pname = "pipewire-core-cancellation-probe";
    preCheck = old.preCheck + ''
      mesonCheckFlagsArray+=(--wrapper "${runner}")
    '';
  });
}
