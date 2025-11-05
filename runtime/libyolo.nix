{
  base,
  lib,
  sources,
}:

let
  inherit (lib) setupCcache;
in
rec {
  # This just builds the Fil-C glibc yolo fork with the normal
  # host GCC toolchain.
  libyolo-glibc = base.stdenv.mkDerivation rec {
    pname = "libyolo-glibc";
    version = "2.40";
    src = "${sources.yolo-glibc-src}/projects/yolo-glibc-${version}";

    # Use single output (glibc tries to split into multiple outputs by default)
    outputs = [ "out" ];

    enableParallelBuilding = true;

    nativeBuildInputs = with base; [
      python3
      git
      file
      patchelf
      gnumake
      pkg-config
      autoconf
      bison
      gcc-unwrapped
      binutils-unwrapped
      ccache
    ];

    preConfigure = ''
      export NIX_CFLAGS_COMPILE=""
      export NIX_LDFLAGS=""

      # Set up ccache manually
      ${setupCcache}
      export CC="ccache gcc"
      export CXX="ccache g++"

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
      "--with-headers=${base.linuxHeaders}/include"
    ];
  };

  # Rename yolo-glibc components so they don't conflict with normal glibc
  libyolo =
    base.runCommand "libyolo"
      {
        nativeBuildInputs = [ base.patchelf ];
      }
      ''
        mkdir -p $out/lib
        cd $out/lib

        # Copy all .o files
        cp ${libyolo-glibc}/lib/*.o .

        # Copy and rename static libs
        cp ${libyolo-glibc}/lib/libc.a libyoloc.a
        cp ${libyolo-glibc}/lib/libc_nonshared.a libyoloc_nonshared.a
        cp ${libyolo-glibc}/lib/libm.a libyolom.a
        cp ${libyolo-glibc}/lib/*.a .  # Copy other .a files as-is
        chmod -R u+w .

        # Copy and rename dynamic linker
        cp ${libyolo-glibc}/lib/ld-linux-x86-64.so.2 ld-yolo-x86_64.so
        chmod u+w ld-yolo-x86_64.so
        patchelf --remove-rpath ld-yolo-x86_64.so

        # Copy and patch libc implementation
        cp ${libyolo-glibc}/lib/libc.so.6 libyolocimpl.so
        chmod u+w libyolocimpl.so
        patchelf --set-soname libyolocimpl.so \
                 --replace-needed ld-linux-x86-64.so.2 ld-yolo-x86_64.so \
                 --set-rpath '$ORIGIN' \
                 libyolocimpl.so

        # Copy and patch libm implementation
        cp ${libyolo-glibc}/lib/libm.so.6 libyolomimpl.so
        chmod u+w libyolomimpl.so
        patchelf --set-soname libyolomimpl.so \
                 --replace-needed ld-linux-x86-64.so.2 ld-yolo-x86_64.so \
                 --replace-needed libc.so.6 libyolocimpl.so \
                 --set-rpath '$ORIGIN' \
                 libyolomimpl.so

        # Create linker scripts
        cat > libyolom.so <<'EOF'
        OUTPUT_FORMAT(elf64-x86-64)
        GROUP(libyolomimpl.so)
        EOF

        cat > libyoloc.so <<'EOF'
        OUTPUT_FORMAT(elf64-x86-64)
        GROUP(libyolocimpl.so libyoloc_nonshared.a AS_NEEDED(ld-yolo-x86_64.so))
        EOF
      '';
}
