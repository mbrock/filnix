{
  pkgs,
  filc,
  libpizlo,
}:

let
  sources = import ../lib/sources.nix { inherit pkgs; };

in

{
  # Memory-safe glibc compiled with Fil-C
  filc-glibc = pkgs.stdenv.mkDerivation {
    pname = "filc-glibc";
    version = "2.40";
    src = "${sources.user-glibc-src}/projects/user-glibc-2.40";
    outputs = [ "out" ];

    enableParallelBuilding = true;

    nativeBuildInputs = with pkgs; [
      gnumake
      autoconf
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
      FILCFLAGS="$FILCXXFLAGS -Wno-unused-command-line-argument -Wno-macro-redefined"

      export CC="${filc}/bin/clang $FILCFLAGS -isystem ${libpizlo}/include"
      export CXX="${filc}/bin/clang++ $FILCXXFLAGS -isystem ${libpizlo}/include"

      # glibc requires out-of-tree build
      autoconf
      cd ..
      mkdir -p build
      cd build
      configureScript=$PWD/../$sourceRoot/configure

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

    meta.description = "Memory-safe glibc compiled with Fil-C";
  };
}
