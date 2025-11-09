{
  stdenv,
  fetchurl,
  ncurses,
  readline,
}:
stdenv.mkDerivation rec {
  pname = "lua";
  version = "5.4.7";
  src = fetchurl {
    url = "https://www.lua.org/ftp/lua-${version}.tar.gz";
    sha256 = "sha256-n79eKO+GxphY9tPTTszDLpEcGii0Eg/z6EqqcM+/HjA=";
  };

  buildInputs = [
    ncurses
    readline
  ];

  makeFlags = [
    "CC=${stdenv.cc.targetPrefix}cc"
    "INSTALL_TOP=${placeholder "out"}"
    "INSTALL_MAN=${placeholder "out"}/share/man/man1"
    "R=${version}"
  ];

  postPatch = ''
    sed -i "s@#define LUA_ROOT[[:space:]]*\"/usr/local/\"@#define LUA_ROOT  \"$out/\"@g" \
      src/luaconf.h
    grep $out src/luaconf.h
  '';

  postInstall = ''
    mkdir -p $out/lib/pkgconfig
    cat > $out/lib/pkgconfig/lua.pc <<EOF
prefix=$out
libdir=$out/lib
includedir=$out/include

Name: Lua
Description: An Extensible Extension Language
Version: ${version}
Requires:
Libs: -L$out/lib -llua -lm -ldl
Cflags: -I$out/include
EOF
  '';

  passthru = {
    luaversion = "5.4";
    isLuaJIT = false;
  };
}
