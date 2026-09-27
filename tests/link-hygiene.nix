# Wrapper behaviour every Fil-C link relies on: `ld -r` works (the runtime's
# shared libraries are not added to relocatable links), and code inlined from
# a dependency's -dev headers does not keep that -dev output referenced.
{ pkgsFilc }:
let
  inherit (pkgsFilc) stdenv;
  headers = stdenv.mkDerivation {
    name = "filc-inline-header";
    outputs = [
      "out"
      "dev"
    ];
    dontUnpack = true;
    installPhase = ''
      mkdir -p $out $dev/include
      cat > $dev/include/twice.h <<'EOF'
      static inline int twice(const int *p, int i) { return 2 * p[i]; }
      EOF
    '';
  };
in
stdenv.mkDerivation {
  name = "filc-link-hygiene-check";
  dontUnpack = true;
  buildInputs = [ headers ];
  buildPhase = ''
    printf 'int a(int x) { return x + 1; }\n' > a.c
    printf 'int b(int x) { return x + 2; }\n' > b.c
    $CC -c a.c b.c
    $LD -r a.o b.o -o ab.o
    $CC -r a.o b.o -o ab2.o
    cat > main.c <<'EOF'
    #include <stdio.h>
    #include <twice.h>
    int a(int), b(int);
    int main(int argc, char **argv) { int v[2] = { 1, 1 }; printf("%d\n", twice(v, argc - 1) + a(0) + b(0)); return 0; }
    EOF
    # Fil-C copies debug-info file names into its stack-trace tables.
    $CC -g -O1 main.c ab.o -o main
    test "$(./main)" = 5
  '';
  installPhase = ''
    mkdir -p $out/bin
    cp main $out/bin/
  '';
  disallowedReferences = [ headers.dev ];
}
