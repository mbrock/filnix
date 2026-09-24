{
  pkgs,
  filc,
  libpizlo,
}:

let
  lib = import ../lib { inherit pkgs; };
  sources = import ../lib/sources.nix { inherit pkgs; };

in

{
  # Memory-safe glibc compiled with Fil-C
  filc-glibc = pkgs.stdenv.mkDerivation {
    pname = "filc-glibc";
    version = "2.44";
    src = "${sources.user-glibc-src}/projects/user-glibc-2.44";
    outputs = [ "out" ];
    patches = [
      ../patches/glibc-filc-cancellation.patch
      ../patches/glibc-filc-unlock-pi-errno.patch
      # Honour LOCALE_ARCHIVE and NixOS' system archive, as Nixpkgs' glibc
      # does; its 2.42 writes the same archive format as 2.44.
      "${pkgs.path}/pkgs/development/libraries/glibc/nix-locale-archive.patch"
    ];

    enableParallelBuilding = true;

    nativeBuildInputs = with pkgs; [
      gnumake
      lib.autoconf272
      bison
      python3
      binutils
      glibc.dev
    ];

    postPatch = ''
      # Add inotify_init to x86_64 syscalls.list so make-syscalls.sh generates
      # a pizlonated wrapper using zsys_inotify_init instead of using the
      # hand-written inotify_init.c which has INLINE_SYSCALL_CALL
      echo 'inotify_init	-	inotify_init	i:	__inotify_init	inotify_init' \
        >> sysdeps/unix/sysv/linux/x86_64/syscalls.list

      # Remove the .c file so syscalls.list takes precedence
      rm -f sysdeps/unix/sysv/linux/inotify_init.c
    '';

    preConfigure = ''
      # Fil-C compiler flags from build script
      FILCXXFLAGS="-nostdlibinc -Wno-ignored-attributes -Wno-pointer-sign"
      FILCFLAGS="$FILCXXFLAGS -yolo-assembler -Wno-unused-command-line-argument -Wno-macro-redefined"

      export CC="${filc}/bin/clang $FILCFLAGS -isystem ${libpizlo}/include"
      export CXX="${filc}/bin/clang++ $FILCXXFLAGS -isystem ${libpizlo}/include"

      # glibc requires out-of-tree build
      autoconf
      cd ..
      mkdir -p build
      cd build
      configureScript=$PWD/../$sourceRoot/configure

      # Fil-C defaults to the host's /lib/locale, which Nix builds and NixOS
      # do not have. Use this output, as upstream glibc does.
      echo "complocaledir=$out/lib/locale" > configparms

      # Set these in shell so $out actually expands
      configureFlagsArray+=(
        "libc_cv_slibdir=$out/lib"
      )
    '';

    configureFlags = [
      "--disable-mathvec"
      "--disable-nscd"
      "--disable-werror"
      "--with-headers=${pkgs.linuxHeaders}/include"
    ];

    # Ship C.UTF-8, as Nixpkgs' glibc does. The localedef built here is a
    # Fil-C program that cannot run yet, so use the build platform's, as
    # Nixpkgs does when cross-compiling glibc. Its 2.42 writes the same
    # locale file format; the definitions come from this source.
    postInstall = ''
      mkdir -p $out/lib/locale
      I18NPATH=../$sourceRoot/localedata \
        ${pkgs.lib.getBin pkgs.glibc}/bin/localedef \
        --no-archive \
        --alias-file=../$sourceRoot/intl/locale.alias \
        -i ../$sourceRoot/localedata/locales/C \
        -f ../$sourceRoot/localedata/charmaps/UTF-8 \
        $out/lib/locale/C.utf8
    '';

    meta.description = "Memory-safe glibc compiled with Fil-C";
  };
}
