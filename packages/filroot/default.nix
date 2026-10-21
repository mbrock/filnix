# A relocatable Fil-C root: the same toolchain and programs as optfil, in a
# directory that works wherever it is unpacked, also read-only.
#
# Store paths are rewritten to paths under /proc/self/fd/987 of the same
# length (../optfil/mkprefix.py), and each program in bin/ is a static
# launcher that opens the root as descriptor 987 before it runs the real
# program from libexec/filroot (launcher.c, launchers.py). Interpreters,
# RUNPATHs, shebangs and compiled-in data paths then resolve inside the
# root, without environment variables.
{
  pkgs,
  optfil,
}:

let
  inherit (pkgs) lib;
  release = (lib.importJSON ../../lib/filc-upstream.json).release;
  name = "filroot-${release}-filnix-x86_64-linux";
  inherit (optfil.tree) merged aliased closure;

  launcher = pkgs.pkgsStatic.runCommandCC "filroot-launcher" { } ''
    $CC -O2 -static -Wall -Werror -o $out ${./launcher.c}
  '';

  tree =
    pkgs.runCommand "${name}-tree"
      {
        nativeBuildInputs = [ pkgs.python3 ];
        passthru = { inherit launcher; };
      }
      ''
        root=$out/${name}
        mkdir -p $out
        python3 ${../optfil/mkprefix.py} $root /proc/self/fd/987 \
          ${closure}/store-paths --relative-links \
          --merge ${toString merged} --alias ${toString aliased}

        # See ../optfil/default.nix.
        (cd $root/lib/pkgconfig
          for pc in ../../share/pkgconfig/*.pc; do
            [ -e "$(basename $pc)" ] || ln -s $pc .
          done)

        python3 ${./launchers.py} $root ${launcher}

        # Clang finds its resource directory and libc++'s headers next to
        # its executable, which is now in libexec/filroot/bin, and reads
        # these configuration files from there. Programs it links load the
        # loader and libraries through descriptor 987, like the root's own.
        cd $root/libexec/filroot
        ln -s ../../lib lib
        ln -s ../../include include
        cat > bin/clang.cfg <<'EOF'
        --filc-resource-dir=<CFGDIR>/..
        --filc-stdfil-include=<CFGDIR>/../include
        --filc-os-include=<CFGDIR>/../include
        --filc-include=<CFGDIR>/../include
        --filc-crt-path=/proc/self/fd/987/lib
        --filc-dynamic-linker=/proc/self/fd/987/lib/ld-fil1-x86_64.so
        EOF
        ln -s clang.cfg bin/clang++.cfg
        ln -s clang.cfg bin/clang-cpp.cfg

        rm $root/README.md
        install -m644 ${./README.md} $root/README.md
      '';
in
pkgs.runCommand "${name}.tar.xz"
  {
    nativeBuildInputs = [ pkgs.xz ];
    passthru = { inherit tree launcher; };
  }
  ''
    tar -C ${tree} --sort=name --mtime=@1 --owner=0 --group=0 --numeric-owner \
      --mode=u+w -cf - ${name} | xz -T$NIX_BUILD_CORES -6 > $out
  ''
