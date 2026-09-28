# jemalloc's API on Fil-C's allocator (docs/jemalloc-on-fugc.md).
#
# jemalloc carves objects out of large mmap'd extents, so under Fil-C they
# all share one capability: overflows into a neighbour and uses after free
# go unnoticed, and with the empty symbol prefix it would do that to every
# malloc in the program. Here upstream's configure still generates the
# headers, jemalloc.pc and jemalloc-config, but libjemalloc is
# jemalloc_fugc.c, which implements the non-standard API on zgc_alloc and
# leaves malloc and the other standard functions to libc.
{
  lib,
  stdenv,
  autoreconfHook,
  jemalloc,
}:

stdenv.mkDerivation {
  pname = "jemalloc";
  inherit (jemalloc) version src;

  nativeBuildInputs = [ autoreconfHook ];

  # Upstream's flags, so the generated header matches Nixpkgs' jemalloc.
  # No C++ operator new/delete replacements: libc++'s use malloc already.
  configureFlags = jemalloc.configureFlags ++ [ "--disable-cxx" ];

  postPatch = ''
    cp ${./jemalloc_fugc.c} jemalloc_fugc.c
    cp ${./test.c} fugc_test.c
  '';

  buildPhase = ''
    runHook preBuild
    mkdir -p lib
    $CC -O2 -g -fPIC -Wall -Wextra -Werror -Iinclude -c jemalloc_fugc.c -o jemalloc_fugc.o
    $CC -shared -Wl,-soname,libjemalloc.so.2 -o lib/libjemalloc.so.2 jemalloc_fugc.o
    ln -s libjemalloc.so.2 lib/libjemalloc.so
    $AR rcs lib/libjemalloc.a jemalloc_fugc.o
    runHook postBuild
  '';

  doCheck = true;
  checkPhase = ''
    runHook preCheck
    $CC -O2 -Wall -Iinclude fugc_test.c -Llib -ljemalloc -o fugc_test
    LD_LIBRARY_PATH=$PWD/lib ./fugc_test
    runHook postCheck
  '';

  installPhase = ''
    runHook preInstall
    mkdir -p $out/lib/pkgconfig $out/include/jemalloc $out/bin $out/share/doc/jemalloc
    cp -P lib/libjemalloc.so* lib/libjemalloc.a $out/lib/
    cp include/jemalloc/jemalloc.h $out/include/jemalloc/
    sed '/^Libs.private:/d' jemalloc.pc > $out/lib/pkgconfig/jemalloc.pc
    install -m755 bin/jemalloc-config bin/jemalloc.sh $out/bin/
    cp ${../../docs/jemalloc-on-fugc.md} $out/share/doc/jemalloc/jemalloc-on-fugc.md
    runHook postInstall
  '';

  doInstallCheck = true;
  installCheckPhase = ''
    ! grep missing_version_try_git_fetch_tags $out/include/jemalloc/jemalloc.h
  '';

  passthru = jemalloc.passthru or { };

  meta = removeAttrs jemalloc.meta [ "position" ] // {
    description = "jemalloc API implemented on Fil-C's garbage-collected allocator";
  };
}
