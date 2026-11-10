# The runtime benchmark's binaries and inputs (docs/perf.md). Each program
# is built by filcc -O2 (`ref`), by plain clang without Fil-C (`native`)
# and by nanofil in every mode below, through
# the same nanofil-cc wrapper the Nix checks use, and kept unstripped for
# perf. Build with
#
#   nix build --impure -f nanofil/bench -o nanofil/bench/out
#
# from the repository root (`--argstr only O,O-stack` builds just those
# nanofil modes); run.py then checks and times them.
{
  flake ? builtins.getFlake (toString ../..),
  pkgs ? import flake.inputs.nixpkgs { system = "x86_64-linux"; },
  filcc ? flake.packages.x86_64-linux.filcc-staging,
  only ? "",
}:
let
  # The flake's copy of nanofil: tracked files only, not out/ or results.
  cc = import "${flake}/nanofil/nix/nanofil-cc.nix" { inherit pkgs filcc; };
  programs = import "${flake}/nanofil/bench/programs.nix" {
    inherit pkgs filcc;
  };
  # Plain clang, no Fil-C (`native`): the LLVM version Fil-C is built
  # from, behind the same kind of Nix wrapper and with the same flags.
  native = pkgs.llvmPackages_20.clang;
  # NANOFIL_OPT for each nanofil mode. `off` is the reference backend
  # without the middle end; the others are what a user would choose.
  modes = {
    off = "";
    O = "-O";
    O-reuse = "-O --checks=reuse";
    O-refchecks = "-O --checks=reference";
    O-guard = "-O --checks=guard";
    O-temps = "-O --registers=temps";
    O-noinline = "-O --inline=none";
    O-small = "-O --inline=small";
    O-refbranches = "-O --branches=reference";
    O-stack = "-O --registers=stack";
    O-call = "-O --memcpy=call";
    O-nosimplify = "-O --simplify=none";
    O-limit4000 = "-O --registers-limit=4000";
    O-merged = "-O --bounds=merged";
    O-or = "-O --bounds=or";
    O-sign = "-O --bounds=sign";
    O-hoist = "-O --checks=hoist";
    O-hoist-merged = "-O --checks=hoist --bounds=merged";
    O-hoist-or = "-O --checks=hoist --bounds=or";
    O-schedule = "-O --checks=schedule";
    O-share-block = "-O --share=block";
    O-share-null = "-O --share=null";
    O-share = "-O --share=upper";
    O-half = "-O --checks=half";
    O-forward = "-O --checks=forward";
    O-combined = "-O --checks=combined";
    O-all = "-O --checks=combined --share=upper";
    O-hull = "-O --checks=hull";
    O-getter = "-O --checks=getter";
    O-extended = "-O --checks=extended";
    O-lowers = "-O --lowers=shared";
    O-slow = "-O --slow-calls=save";
  };
  chosen =
    if only == "" then
      modes
    else
      pkgs.lib.filterAttrs (
        m: _: builtins.elem m (pkgs.lib.splitString "," only)
      ) modes;
  # 4 MiB of C source text from the four pinned tarballs, sorted by path
  # and repeated, and 4 MiB of SHA-256 counter output. Both depend only on
  # nixpkgs' pinned sources.
  inputs =
    pkgs.runCommand "nanofil-bench-inputs"
      { nativeBuildInputs = [ pkgs.python3 ]; }
      ''
        mkdir src $out
        for s in ${pkgs.zlib.src} ${pkgs.lua5_4.src} ${pkgs.bzip2.src}; do
          tar -xf $s -C src
        done
        cp -r ${pkgs.lz4.src} src/lz4
        find src -type f \( -name '*.c' -o -name '*.h' \) | LC_ALL=C sort | xargs cat >one
        for i in 1 2 3 4 5 6 7 8; do cat one; done >many
        head -c 4194304 many >$out/text
        python3 -c '
        import hashlib, sys
        out = bytearray()
        i = 0
        while len(out) < 4194304:
            out += hashlib.sha256(b"nanofil-bench:" + i.to_bytes(8, "little")).digest()
            i += 1
        sys.stdout.buffer.write(out)' >$out/random
        test $(stat -c %s $out/text) = 4194304
      '';
in
pkgs.linkFarm "nanofil-bench" (
  [
    {
      name = "inputs";
      path = inputs;
    }
  ]
  ++ pkgs.lib.concatLists (
    pkgs.lib.mapAttrsToList (
      name: _:
      [
        {
          name = "${name}/ref";
          path = programs.build name "ref" "${filcc}/bin/clang" "" "";
        }
        {
          name = "${name}/native";
          path = programs.build name "native" "${native}/bin/clang" "" "";
        }
      ]
      ++ pkgs.lib.mapAttrsToList (mode: opt: {
        name = "${name}/${mode}";
        path = programs.build name mode cc opt "";
      }) chosen
    ) programs.progs
  )
)
