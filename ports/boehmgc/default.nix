# The Boehm GC API on Fil-C's own collector (docs/boehm-on-fugc.md).
#
# libgc's conservative scanning of stacks, registers and data segments
# cannot work under Fil-C, and every Fil-C allocation is garbage collected
# already.  So libgc here is gc_fugc.c, which maps the API onto <stdfil.h>,
# while the headers, libcord, libgccpp and libgctba are upstream's sources
# built against it.  The ABI (symbols, headers, bdw-gc.pc) matches upstream.
{
  lib,
  stdenv,
  boehmgc,
}:

stdenv.mkDerivation {
  pname = "boehm-gc";
  inherit (boehmgc) version src;

  outputs = [
    "out"
    "dev"
    "doc"
  ];

  # Hidden pointers go through a weak pointer table under Fil-C.
  patches = [ ./hide-pointer.patch ];

  postPatch = ''
    cp ${./gc_fugc.c} gc_fugc.c
    cp ${./fugc_test.c} fugc_test.c
  '';

  dontConfigure = true;

  buildPhase = ''
    runHook preBuild
    mkdir -p build/include/gc
    cp include/*.h build/include/gc/
    cp include/extra/gc.h include/extra/gc_cpp.h build/include/
    cflags="-O2 -g -fPIC -Wall -Ibuild/include -Ibuild/include/gc -DGC_THREADS"
    so() { # name soversion objects... libs...
      local name=$1 ver=$2; shift 2
      $CC -shared -Wl,-soname,lib$name.so.''${ver%%.*} -o build/lib$name.so.$ver "$@"
      ln -sf lib$name.so.$ver build/lib$name.so.''${ver%%.*}
      ln -sf lib$name.so.$ver build/lib$name.so
    }

    $CC $cflags -c gc_fugc.c -o build/gc_fugc.o
    so gc 1.5.6 build/gc_fugc.o -lpthread -ldl
    $AR rcs build/libgc.a build/gc_fugc.o

    for f in cordbscs cordxtra cordprnt; do
      $CC $cflags -Wno-unused -c cord/$f.c -o build/$f.o
    done
    so cord 1.5.1 build/cord*.o -Lbuild -lgc
    $AR rcs build/libcord.a build/cord*.o

    $CXX $cflags -c gc_badalc.cc -o build/gc_badalc.o
    so gctba 1.5.0 build/gc_badalc.o -Lbuild -lgc
    $CXX $cflags -c gc_cpp.cc -o build/gc_cpp.o
    so gccpp 1.5.0 build/gc_cpp.o build/gc_badalc.o -Lbuild -lgc
    runHook postBuild
  '';

  doCheck = true;
  checkPhase = ''
    runHook preCheck
    $CC -O2 -Wall -Ibuild/include -DGC_THREADS fugc_test.c \
      -Lbuild -lgc -lpthread -o build/fugc_test
    LD_LIBRARY_PATH=$PWD/build build/fugc_test
    $CC -O2 -Ibuild/include -Ibuild/include/gc cord/tests/cordtest.c -Lbuild -lcord -lgc \
      -o build/cordtest
    LD_LIBRARY_PATH=$PWD/build build/cordtest
    # Upstream tests that do not depend on collector internals.
    for t in realloc_test huge_test middle smash_test threadkey_test; do
      $CC -O2 -w -Ibuild/include -Ibuild/include/gc -DGC_THREADS \
        tests/$t.c -Lbuild -lgc -lpthread -o build/$t
      echo "== $t"
      LD_LIBRARY_PATH=$PWD/build build/$t
    done
    runHook postCheck
  '';

  installPhase = ''
    runHook preInstall
    mkdir -p $out/lib $dev/include $dev/lib/pkgconfig $doc/share/doc/gc
    cp -P build/*.so* build/*.a $out/lib/
    cp -r build/include/. $dev/include/
    cat > $dev/lib/pkgconfig/bdw-gc.pc <<EOF
    prefix=$out
    exec_prefix=$out
    libdir=$out/lib
    includedir=$dev/include

    Name: Boehm-Demers-Weiser Conservative Garbage Collector
    Description: A garbage collector for C and C++ (on Fil-C's FUGC)
    Version: $version
    Libs: -L\''${libdir} -lgc -lpthread -ldl
    Cflags: -I\''${includedir}
    EOF
    cp README.md $doc/share/doc/gc/
    cp ${../../docs/boehm-on-fugc.md} $doc/share/doc/gc/boehm-on-fugc.md
    runHook postInstall
  '';

  passthru = boehmgc.passthru or { };

  meta = removeAttrs boehmgc.meta [ "position" ] // {
    description = "Boehm GC API implemented on Fil-C's garbage collector";
  };
}
