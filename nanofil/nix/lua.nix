# Lua 5.4 built entirely through the shared nanofil-cc wrapper. Compare
# deterministic float/format/libm scripts with filcc, and run Lua's
# unchanged official basic suite on both builds, plain and under GC stress.
# Repeat with nanofil's middle end enabled. reference is exposed so the
# harness and upstream suite can be checked before the compiler is ready.
{ pkgs, filcc }:
assert pkgs.lua5_4.version == "5.4.7";
let
  src = pkgs.lua5_4.src;
  officialTests = pkgs.fetchurl {
    url = "https://www.lua.org/tests/lua-5.4.7-tests.tar.gz";
    hash = "sha256-ikiY/+THYTyACTJ6ByLbekHvhh1SbHfFtGEU5Z6/gR4=";
  };
  scripts = ../tests/lua;
  # No readline dependency or source patches. LUA_USE_LINUX enables the
  # normal POSIX and dlopen interfaces; _U skips the suite's C extensions.
  # Use Lua's supported switch dispatch: GNU label addresses are not C99
  # and are outside nanofil's frontend contract. Both builds use it.
  flags = "-O2 -std=gnu99 -DLUA_USE_LINUX -DLUA_USE_JUMPTABLE=0";
  reference = pkgs.runCommandCC "nanofil-lua-reference" { inherit src; } ''
    mkdir lua official
    tar -xf $src -C lua --strip-components=1
    tar -xf ${officialTests} -C official --strip-components=1
    make -C lua/src -j$NIX_BUILD_CORES CC=${filcc}/bin/clang \
      CFLAGS="${flags}" SYSLIBS="-Wl,-E -ldl" all
    mkdir -p $out/bin
    cp lua/src/lua lua/src/luac $out/bin/
    bash ${scripts}/check.sh $out/bin/lua $out/bin/lua official $out/check
  '';
in
pkgs.runCommandCC "nanofil-lua"
  {
    inherit src;
    passthru = { inherit reference; };
  }
  ''
    cc=${import ./nanofil-cc.nix { inherit pkgs filcc; }}
    mkdir official $out
    tar -xf ${officialTests} -C official --strip-components=1
    for opt in "" -O "--registers=local" "-O --registers=local" "-O --branches=reference" "-O --registers=stack" "--checks=reuse"; do
      case "$opt" in
        "") label=plain ;;
        -O) label=optimized ;;
        --registers=local) label=local-plain ;;
        --checks=reuse) label=reuse-plain ;;
        *) label=local-optimized ;;
      esac
      echo "== Lua 5.4.7, nanofil $opt"
      rm -rf lua && mkdir lua
      tar -xf $src -C lua --strip-components=1
      export NANOFIL_OPT=$opt NANOFIL_LOG=$PWD/nanofil.log
      rm -f nanofil.log
      make -C lua/src -j$NIX_BUILD_CORES CC=$cc \
        CFLAGS="${flags}" SYSLIBS="-Wl,-E -ldl" all
      # Compare names, not just counts: not one Lua object may come from
      # a configure probe or a silent fallback to clang.
      find lua/src -name '*.o' -printf '%f\n' | sort >objects
      sort -u nanofil.log >compiled
      test -s objects
      diff -u objects compiled
      echo "nanofil compiled every one of $(wc -l <objects) Lua objects ($label)"
      mkdir -p $out/$label/bin
      cp lua/src/lua lua/src/luac $out/$label/bin/
      cp compiled $out/$label/compiled-objects.txt
      bash ${scripts}/check.sh ${reference}/bin/lua "$PWD/lua/src/lua" \
        official $out/$label/check
    done
  ''
