# Opt-in runtime experiment; never changes pkgsFilc.stdenv or its libc.
#   nix build --impure -f tests/pipewire-cancellation.nix probe
#   nix build --impure -f tests/pipewire-cancellation.nix pipewire --keep-failed
let
  f = builtins.getFlake (toString ../.);
  pkgs = import f.inputs.nixpkgs { system = "x86_64-linux"; };
  p = f.legacyPackages.x86_64-linux.pkgsFilc;
  libc = import ../runtime/filc-glibc-cancellation.nix { inherit pkgs; };

  # Meson sets LD_LIBRARY_PATH for build-tree libraries. Prepend our libc
  # inside the per-test wrapper, after Meson has prepared that environment.
  runner = pkgs.writeShellScript "with-filc-cancellation-libc" ''
    export LD_LIBRARY_PATH="${libc}/lib''${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
    exec "$@"
  '';
in
rec {
  inherit libc runner;

  # This proves that an executable built with the ordinary toolchain loads
  # the private libc and successfully unwinds through its cleanup handler.
  probe = p.stdenv.mkDerivation {
    name = "filc-private-libc-cancellation-check";
    dontUnpack = true;
    buildPhase = ''
      $CC -O2 -Werror ${./pthread-cancel.c} -pthread -o check
      FUGC_THREADS=2 ${runner} timeout 15 ./check ${libc}
      $CC -O2 -Werror -DWITH_CXX_CLEANUP -c ${./pthread-cancel.c} -o check.o
      $CXX -O2 -Werror ${./pthread-cancel-cxx.cc} check.o -pthread -o check-cxx
      FUGC_THREADS=2 ${runner} timeout 15 ./check-cxx ${libc}
    '';
    installPhase = ''touch "$out"'';
  };

  # Only this leaf derivation changes. Compilation and all dependencies still
  # use the ordinary toolchain; all Meson test processes use the private libc.
  # The original blocking-cancellation test stays enabled.
  pipewire = (import ./pipewire-core.nix).overrideAttrs (old: {
    pname = "pipewire-core-cancellation-probe";
    preCheck = old.preCheck + ''
      mesonCheckFlagsArray+=(--wrapper "${runner}")
    '';
  });

  runtime = pkgs.runCommand "pipewire-private-libc-runtime-check" { } ''
    ${pkgs.python3}/bin/python ${./pipewire-runtime.py} \
      --pipewire ${pipewire} --runner ${runner} --libc ${libc} > "$out"
  '';
}
