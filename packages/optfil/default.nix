# Fil-C at /opt/fil for ordinary x86-64 Linux systems, in the layout of
# upstream's optfil distribution: the filcc and fil++ compiler with its
# runtime, glibc, libc++ and headers, and memory-safe programs and libraries.
#
# The tree is the Nix closure of all that, with every store path rewritten
# in place to a path under /opt/fil of the same length (mkprefix.py). The
# toolchain and the packages in `merged` land directly in /opt/fil, the way
# upstream lays them out; the rest of the closure lands in /opt/fil/s.
{
  pkgs,
  pkgsFilc,
  filcc,
  sarcasm,
}:

let
  inherit (pkgs) lib;
  release = (lib.importJSON ../../lib/filc-upstream.json).release;
  name = "optfil-${release}-filnix-x86_64-linux";

  components = filcc.components;
  sysroot = filcc.libc;
  binutils = filcc.bintools.bintools;

  # Programs and libraries in /opt/fil/bin, /opt/fil/lib and /opt/fil/include.
  # Their other dependencies are found in /opt/fil/s. Libraries whose
  # pkg-config files others require are here too, so that, for example,
  # pkg-config --libs libcurl works.
  packages = with pkgsFilc; [
    bash
    bison
    brotli
    bzip2
    coreutils
    curl
    diffutils
    file
    findutils
    flex
    gawk
    git
    gnugrep
    gnum4
    gnumake
    gnused
    gnutar
    gzip
    jq
    krb5
    less
    libffi
    libidn2
    libpsl
    lua
    nano
    ncurses
    nghttp2
    nghttp3
    ngtcp2
    openssh
    openssl
    perl
    pkgconf-unwrapped
    python3
    readline
    rsync
    sqlite
    tmux
    which
    xz
    zlib
    zstd
  ];
  outputsOf =
    p:
    map (o: p.${o}) (
      lib.subtractLists [
        "man"
        "doc"
        "devdoc"
        "info"
        "debug"
      ] p.outputs
    );

  # The compiler in upstream's layout. Clang uses /opt/fil/lib and
  # /opt/fil/include, and finds ld and sarcasm in /opt/fil/bin, when its
  # executable is in /opt/fil/bin.
  toolchain =
    pkgs.runCommand "optfil-toolchain"
      {
        nativeBuildInputs = [
          pkgs.binutils-unwrapped
          pkgs.patchelf
          pkgs.rsync
        ];
      }
      ''
        mkdir -p $out/bin $out/lib $out/include/c++
        filc0=${components.filc0}

        # Clang runs on the host's glibc from /opt/fil/s; $ORIGIN/../lib
        # would make it search the Fil-C libraries first.
        install -m755 $filc0/bin/clang $out/bin/clang-20
        strip --strip-debug $out/bin/clang-20
        patchelf --set-rpath "$(patchelf --print-rpath $out/bin/clang-20 |
          sed 's|\$ORIGIN/../lib:||')" $out/bin/clang-20
        for n in filcc fil++ filcpp; do ln -s clang-20 $out/bin/$n; done
        cp -r $filc0/lib/clang $out/lib/

        for tool in ${binutils}/bin/*; do ln -s $tool $out/bin/; done
        ln -s ${sarcasm}/bin/sarcasm $out/bin/sarcasm
        ln -s pkgconf $out/bin/pkg-config

        rsync -a --chmod=u+w ${sysroot}/lib/ $out/lib/
        rsync -a --chmod=u+w ${sysroot}/bin/ $out/bin/
        cp ${components.compiler-rt}/lib/* ${components.yolounwind}/lib/* $out/lib/
        rsync -a --chmod=u+w --exclude c++ ${sysroot}/include/ $out/include/
        cp -r ${sysroot}/include/c++ $out/include/c++/v1
        chmod -R u+w $out
        install -m644 ${./README.md} $out/README.md

        # OpenSSL's directory is /opt/fil/etc/ssl. It reads the Mozilla roots
        # from cert.pem and also finds the host's hashed certificates.
        mkdir -p $out/etc/ssl
        install -m644 ${pkgsFilc.cacert}/etc/ssl/certs/ca-bundle.crt $out/etc/ssl/cert.pem
        ln -s /etc/ssl/certs $out/etc/ssl/certs
      '';

  merged = [ toolchain ] ++ lib.concatMap outputsOf packages;
  # The toolchain has the files of these.
  aliased = [
    sysroot
    components.filc-glibc
    components.yolo-glibc
    components.yolo-glibc-impl
    components.libpizlo
    components.filc-libcxx
    components.compiler-rt
    components.yolounwind
    pkgs.linuxHeaders
  ];

  closure = pkgs.closureInfo { rootPaths = merged ++ aliased; };

  tree =
    pkgs.runCommand "${name}-tree"
      {
        nativeBuildInputs = [ pkgs.python3 ];
        passthru = { inherit toolchain packages; };
      }
      ''
        mkdir -p $out
        python3 ${./mkprefix.py} $out/fil /opt/fil ${closure}/store-paths \
          --merge ${toString merged} --alias ${toString aliased}

        # pkgconf's compiled-in share/pkgconfig is in its own store path,
        # which Nix removes from the binary, so it searches lib/pkgconfig only.
        cd $out/fil/lib/pkgconfig
        for pc in ../../share/pkgconfig/*.pc; do
          [ -e "$(basename $pc)" ] || ln -s $pc .
        done
      '';
in
pkgs.runCommand "${name}.tar.xz"
  {
    nativeBuildInputs = [ pkgs.xz ];
    passthru = { inherit tree toolchain; };
  }
  ''
    tar -C ${tree} --sort=name --mtime=@1 --owner=0 --group=0 --numeric-owner \
      --mode=u+w -cf - fil | xz -T$NIX_BUILD_CORES -6 > $out
  ''
