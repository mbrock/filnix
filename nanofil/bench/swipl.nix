# SWI-Prolog 9.2.9's core (no packages) for the profile in docs/perf.md:
# built by plain clang (`native`), by filcc (`ref`) and by nanofil -O
# (`O`), from the same sources with the same configuration and `-O2`,
# unstripped. The Fil-C builds apply filnix's port (nix/swipl.nix's
# patch); the native one does not, since the patched atom GC crashes
# without Fil-C. The patch's changes to the VM are casts that keep
# pointer provenance (CODE_PTR), which compile to the same code natively. Each output is an installed
# swipl; its bench/ is SWI's benchmark suite.
#
#   nix build --impure -f nanofil/bench/swipl.nix -o nanofil/bench/swipl
#   nanofil/bench/swipl/O/bin/swipl nanofil/bench/swipl/bench/run.pl --speedup=20
{
  flake ? builtins.getFlake (toString ../..),
  pkgs ? import flake.inputs.nixpkgs { system = "x86_64-linux"; },
  filcc ? flake.packages.x86_64-linux.filcc-staging,
  pkgsFilc ? flake.legacyPackages.x86_64-linux.pkgsFilcStaging,
  # `--argstr only O,ref` builds just those (and bench/).
  only ? "",
}:
let
  src = pkgs.swi-prolog.src;
  nanofil = import "${flake}/nanofil/nix/nanofil-cc.nix" {
    inherit pkgs filcc;
  };
  build =
    label: cc: libs: launcher:
    pkgs.runCommandCC "nanofil-bench-swipl-${label}"
      {
        nativeBuildInputs = [
          pkgs.cmake
          pkgs.ninja
        ];
      }
      ''
        cp -r --no-preserve=mode ${src} swipl
        ${pkgs.lib.optionalString (
          label != "native"
        ) "patch -d swipl -p1 <${flake}/patches/swi-prolog-9.2.9-filc.patch"}
        mkdir swipl/build && cd swipl/build
        # Each nanofil compile appends its user seconds and peak KB to ../ctimes.
        printf '#!${pkgs.runtimeShell}\nshift\nexec ${pkgs.time}/bin/time -f "%%U %%M" -a -o %s ${nanofil} "$@"\n' $PWD/../ctimes >../launcher
        chmod +x ../launcher
        export CC=${cc} NANOFIL_OPT=-O NANOFIL_STACK_LIMIT=4000000000
        cmake -G Ninja -DCMAKE_BUILD_TYPE=Release "-DCMAKE_C_FLAGS_RELEASE=-O2 -DNDEBUG" \
          -DCMAKE_INSTALL_PREFIX=$out -DSWIPL_PACKAGES=OFF -DUSE_GMP=ON -DUSE_TCMALLOC=OFF \
          -DINSTALL_DOCUMENTATION=OFF -DHAVE_SIGALTSTACK= -DBUILD_TESTING=OFF \
          -DCMAKE_PREFIX_PATH="${
            pkgs.lib.concatMapStringsSep ";" (p: "${p};${pkgs.lib.getDev p}") libs
          }" \
          .. >cmake.log 2>&1 || { cat cmake.log; exit 1; }
        # As nix/swipl.nix: configure with filcc, then compile with nanofil.
        ${pkgs.lib.optionalString launcher "cmake -DCMAKE_C_COMPILER_LAUNCHER=$PWD/../launcher . >>cmake.log"}
        ninja -j$NIX_BUILD_CORES >ninja.log 2>&1 || { grep -B2 -A20 FAILED ninja.log | head -80; exit 1; }
        ninja install >/dev/null
        ${pkgs.lib.optionalString launcher ''
          awk '{u += $1; if ($2 > m) m = $2} END {printf "%d compiles, %.1f s user, max %d KB\n", NR, u, m}' ../ctimes >$out/compile-time
        ''}
        ln -s $(find $out -path '*/bin/*' -name swipl -type f) $out/swipl
      '';
in
pkgs.linkFarm "nanofil-bench-swipl" (
  builtins.filter
    (
      e:
      only == ""
      || e.name == "bench"
      || builtins.elem e.name (pkgs.lib.splitString "," only)
    )
    [
      {
        name = "native";
        path = build "native" "${pkgs.llvmPackages_20.clang}/bin/clang" [
          pkgs.gmp
          pkgs.zlib
        ] false;
      }
      {
        name = "ref";
        path = build "ref" "${filcc}/bin/clang" [ pkgsFilc.gmp pkgsFilc.zlib ] false;
      }
      {
        name = "O";
        path = build "O" "${filcc}/bin/clang" [ pkgsFilc.gmp pkgsFilc.zlib ] true;
      }
      {
        name = "bench";
        path = "${src}/bench";
      }
    ]
)
