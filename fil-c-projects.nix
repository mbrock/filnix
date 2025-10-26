{ base, filenv, filc-src, filcc }:

let
  filc-sources = base.runCommand "filc-all-sources" {} ''
    mkdir -p $out
    cp -r ${filc-src}/projects/* $out/
  '';
  
  helpers = import ./fil-c-helpers.nix { inherit base filenv; };
  
  minimal = helpers.minimal filc-sources;
  package = helpers.package filc-sources;
  configure = helpers.configure filc-sources;
  cmake = helpers.cmake filc-sources;
  make = helpers.make filc-sources;

in rec {
  zlib = configure "zlib" "1.3" {};

  zstd = make "zstd" "1.5.6" {
    flags = ["prefix=$out" "ZSTD_NO_ASM=1" "V=1"];
  };

  xz = configure "xz" "5.6.2" {
    flags = [ "--disable-assembler" ];
  };

  bzip2 = make "bzip2" "" {
    src = "bzip2";
    flags = [ "PREFIX=$out" ];
  };

  lz4 = make "lz4" "1.10.0" {
    flags = [ "PREFIX=$out" ];
  };

  grep = configure "grep" "3.11" {};

  sed = configure "sed" "4.9" {};

  diffutils = configure "diffutils" "3.10" {};

  m4 = configure "m4" "1.4.19" {};

  gnumake = configure "make" "4.4.1" {};

  bison = configure "bison" "3.8.2" {
    needs = [ m4 ];
  };

  libffi = configure "libffi" "3.4.6" {
    flags = [ "--disable-exec-static-tramp" ];
  };

  expat = configure "expat" "2.7.1" {
    pre = "cd expat";
  };

  pcre2 = configure "pcre2" "10.44" {
    needs = [zlib];
    flags = [ 
      "--enable-pcre2-16" 
      "--enable-pcre2-32"
      "--enable-pcre2grep-libz" 
    ];
  };

  libevent = configure "libevent" "2.1.12" {
    flags = [ "--disable-openssl" ];
  };

  openssl = package "openssl" "3.3.1" {
    needs = [ zlib ];
    configure = ''
      patchShebangs .
      ./Configure linux-x86_64 --prefix=$out --libdir=lib shared zlib
    '';
    build = ''
      make -j$NIX_BUILD_CORES
      make -j$NIX_BUILD_CORES libcrypto.so
    '';
    install = ''
      make -j$NIX_BUILD_CORES install_sw
      make -j$NIX_BUILD_CORES install_ssldirs
    '';
  };

  curl = configure "curl" "8.9.1" {
    needs = [ openssl nghttp2 ];
    flags = [
      "--with-openssl"
      "--with-nghttp2"
      "--with-ca-bundle=${base.cacert}/etc/ssl/certs/ca-bundle.crt"
    ];
    pre = "autoreconf -vfi";
  };

  nghttp2 = configure "nghttp2" "1.62.1" {
    flags = [ "--with-openssl" "--with-zlib" ];
    needs = [ openssl zlib ];
  };

  lua = package "lua" "5.4.7" {
    build = ''
      make -j$NIX_BUILD_CORES
    '';
    install = ''
      mkdir -p $out/bin
      cp lua $out/bin/
    '';
  };

  quickjs = package "quickjs" "" {
    src = "quickjs";
    build = ''
      make CC="$CC" HOST_CC="$CC" -j$NIX_BUILD_CORES
    '';
    install = ''
      mkdir -p $out/bin
      cp qjs $out/bin/
    '';
  };

  sqlite = package "sqlite" "" {
    src = "sqlite";
    tools = [ base.tcl ];
    build = ''
      make -f Makefile.filc TOP=$PWD CC="$CC -g -O2" \
        -j$NIX_BUILD_CORES all testfixture
    '';
    install = ''
      make -f Makefile.filc TOP=$PWD PREFIX=$out install
    '';
  };

  libpng = configure "libpng" "1.6.43" {
    needs = [ zlib ];
  };

  gmp = configure "gmp" "6.3.0" {
    flags = [
      "--enable-cxx"
      "--disable-static"
      "--disable-assembly"
    ];
  };

  ncurses = package "ncurses" "6.5-20240720" {
    flags = [
      "--disable-lib-suffixes"
      "--with-shared"
      "--without-ada"
      "--enable-pc-files"
    ];
    install = ''
      make -j$NIX_BUILD_CORES install
      ln -fs ncurses6-config $out/bin/ncursesw6-config
    '';
  };

  bash = configure "bash" "5.2.32" {
    flags = [ "--without-bash-malloc" ];
  };

  coreutils = configure "coreutils" "9.5" {};

  brotli = cmake "brotli" "1.1.0" {
    flags = [ "-DCMAKE_BUILD_TYPE=Release" ];
  };

  tcl = package "tcl" "8.6.15" {
    pre = "cd unix";
    install = ''
      make -j$NIX_BUILD_CORES install
      ln -fs tclsh8.6 $out/bin/tclsh
      ln -fs libtcl8.6.so $out/lib/libtcl.so
    '';
  };

  git = configure "git" "2.46.0" {
    needs = [ pcre2 zlib ];
    flags = [
      "--with-gitconfig=/etc/gitconfig"
      "--with-python=python3"
      "--with-pcre2=${pcre2}"
    ];
  };

  vim = configure "vim" "9.1.0660" {
    needs = [ ncurses ];
  };

  tmux = configure "tmux" "3.5a" {};

  openssh = configure "openssh" "9.8p1" {
    needs = [zlib];
  };

  libxml2 = configure "libxml2" "2.14.4" {
    needs = [ icu ];
    flags = [ "--disable-maintainer-mode" "--with-icu" ];
  };

  gettext = configure "gettext" "0.22.5" {
    flags = [ "--disable-static" "--disable-java" ];
  };

  libarchive = configure "libarchive" "3.7.4" {
    flags = [
      "--without-expat"
      "--without-nettle"
      "--without-xml2"
    ];
  };

  libuv = configure "libuv" "v1.48.0" {};

  binutils = package "binutils" "2.43.1" {
    needs = [ zlib ];
    configure = ''
      mkdir build
      cd build
      ../configure --prefix=$out \
        --enable-gold \
        --enable-ld=default \
        --enable-plugins \
        --enable-shared \
        --disable-werror \
        --enable-64-bit-bfd \
        --enable-new-dtags \
        --with-system-zlib \
        --enable-default-hash-style=gnu \
        --disable-gprofng
    '';
  };

  cmake-bootstrap = package "cmake" "3.30.2" {
    needs = [ libuv brotli nghttp2 zlib curl expat libarchive ];
    configure = ''
      ./bootstrap --prefix=$out \
        --system-libs \
        --bootstrap-system-libuv \
        --mandir=/share/man \
        --no-system-jsoncpp \
        --no-system-cppdap \
        --no-system-librhash \
        --docdir=/share/doc/cmake-3.30.2
      find . -name "*.make" -type f -exec sed -i 's/-isystem \/usr\/include//g' {} +
    '';
  };

  perl = package "perl" "5.40.0" {
    configure = ''
      sh ./Configure -der \
        -Dcc="$CC" \
        -Doptimize="-O3 -g -fno-strict-aliasing -D_GNU_SOURCE" \
        -Dprefix="$out" \
        -Dinstallprefix="$out" \
        -Dbin="$out/bin" \
        -Dprivlib="$out/lib/perl5/5.40.0" \
        -Darchlib="$out/lib/perl5/5.40.0/x86_64-linux" \
        -Dsiteprefix="$out" \
        -Dsitelib="$out/perl5/site_perl/5.40.0" \
        -Dsitearch="$out/perl5/site_perl/5.40.0/x86_64-linux" \
        -Dman1dir="$out/share/man/man1" \
        -Dman3dir="$out/share/man/man1" \
        -Dscriptdir="$out/bin" \
        -Dsitehtml1dir="$out/share/man/man1" \
        -Dsitehtml3dir="$out/share/man/man3" \
        -Dsitescript="$out/bin" \
        -Dsitebin="$out/bin" \
        -Dsiteman1dir="$out/share/man/man1" \
        -Dsiteman3dir="$out/share/man/man3" \
        -D usethreads
    '';
  };

  dash = configure "dash" "0.5.12" {};

  pkgconf = package "pkgconf" "2.3.0" {
    install = ''
      make -j$NIX_BUILD_CORES install
      ln -fs pkgconf $out/bin/pkg-config
    '';
  };

  check = configure "check" "0.15.2" {
    flags = [ "--disable-static" ];
  };

  attr = configure "attr" "2.5.2" {
    flags = [ "--disable-static" ];
  };

  libedit = configure "libedit" "20240808-3.1" {
    needs = [ ncurses ];
  };

  libcap = package "libcap" "2.70" {
    build = ''
      make prefix=$out lib=lib -j$NIX_BUILD_CORES
    '';
    install = ''
      make prefix=$out lib=lib -j$NIX_BUILD_CORES install
    '';
  };

  libpipeline = configure "libpipeline" "1.5.7" {};

  busybox = minimal "busybox" "1.37.0" {
    script = ''
      # Replace vfork with fork (vfork not available in fil-c safe glibc)
      find . -name "*.c" -o -name "*.h" | xargs sed -i 's/\bvfork\b/fork/g'
      
      # Build exactly like fil-c does
      make defconfig
      sed -i 's/^main() {}/int main() { return 0; }/' ./scripts/kconfig/lxdialog/check-lxdialog.sh
      sed -i \
        -e 's/^# CONFIG_STATIC is not set$/CONFIG_STATIC=y/' \
        -e 's/^CONFIG_TC=y$/# CONFIG_TC is not set/' \
        -e 's/^CONFIG_FEATURE_TC_INGRESS=y$/# CONFIG_FEATURE_TC_INGRESS is not set/' \
        .config
      make -j$NIX_BUILD_CORES
      
      mkdir -p $out/bin
      cp busybox $out/bin/busybox
    '';
  };

  toybox = package "toybox" "8.12" {
    build = ''
      mkdir -p compiler-bin
      ln -fs $CC compiler-bin/cc
      PATH=$PWD/compiler-bin:$PATH make distclean
      cp good-config .config
      PATH=$PWD/compiler-bin:$PATH CFLAGS="-O2 -g" make oldconfig
      PATH=$PWD/compiler-bin:$PATH CFLAGS="-O2 -g" make -j$NIX_BUILD_CORES
      PATH=$PWD/compiler-bin:$PATH CFLAGS="-O2 -g" make install PREFIX=$out
    '';
  };

  texinfo = configure "texinfo" "7.1" {};

  icu = package "icu" "76.1" {
    configure = ''
      cd icu4c/source
      THE_OS=Linux THE_COMP="the Clang C++" \
        CFLAGS="-O3 -g" CXXFLAGS="-O3 -g" \
        ./configure --enable-debug --prefix=$out
    '';
  };
}
