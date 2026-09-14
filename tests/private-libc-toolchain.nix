let
  f = builtins.getFlake (toString ../.);
  pkgs = import f.inputs.nixpkgs { system = "x86_64-linux"; };
  p = f.legacyPackages.x86_64-linux.pkgsFilc;
  private = import ../toolchain/cancellation.nix {
    inherit pkgs;
    baseStdenv = p.stdenv;
  };
in
private.stdenv.mkDerivation {
  name = "filc-cancellation-toolchain-check";
  dontUnpack = true;
  buildPhase = ''
    unset LD_LIBRARY_PATH
    $CC -O2 -Werror ${./pthread-cancel.c} -pthread -o check
    FUGC_THREADS=2 timeout 15 ./check ${private.libc}
    $CC -O2 -Werror -DWITH_CXX_CLEANUP -c ${./pthread-cancel.c} -o check.o
    $CXX -O2 -Werror ${./pthread-cancel-cxx.cc} check.o -pthread -o check-cxx
    FUGC_THREADS=2 timeout 15 ./check-cxx ${private.libc}
  '';
  installPhase = ''touch "$out"'';
}
