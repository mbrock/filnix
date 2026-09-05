{
  pkgs,
  filcc,
  libffi,
}:
pkgs.runCommand "filc-libffi-runtime-check" { } ''
  ${filcc}/bin/clang -O2 -I${libffi.dev}/include ${./libffi.c} \
    -L${libffi}/lib -Wl,-rpath,${libffi}/lib -lffi -o check
  ./check
  for optimization in -O0 -O2; do
    ${filcc}/bin/clang++ $optimization -I${libffi.dev}/include ${./libffi-unwind.cc} \
      -L${libffi}/lib -Wl,-rpath,${libffi}/lib -lffi -o unwind
    ./unwind
  done
  touch $out
''
