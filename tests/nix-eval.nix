# Run the Fil-C Nix: evaluate expressions and add a file to a local store.
{ pkgsFilc }:
pkgsFilc.stdenv.mkDerivation {
  name = "filc-nix-eval-check";
  dontUnpack = true;
  nativeBuildInputs = [ pkgsFilc.nix ];
  buildPhase = ''
    export HOME=$PWD NIX_STORE_DIR=$PWD/store NIX_STATE_DIR=$PWD/state
    export NIX_CONFIG="experimental-features = nix-command"
    test "$(nix-instantiate --eval -E 'let fib = n: if n < 2 then n else fib (n - 1) + fib (n - 2); in fib 20')" = 6765
    test "$(nix eval --raw --expr 'builtins.concatStringsSep "," (map toString [ 1 2 3 ])')" = 1,2,3
    echo hello > hello.txt
    nix-store --store "$PWD/root" --add hello.txt | grep -q hello.txt
  '';
  installPhase = ''
    touch "$out"
  '';
}
