# The benchmark's programs built by a marked nanofil for instruction
# attribution (docs/perf.md): marks.patch puts a local label before each
# IR instruction, ABI action, jump part and frame-slot access. The
# post-emission passes run without the marks and remark.py puts them
# back, so the code is the unmarked compiler's. Objects carry each
# instruction's line in the marked .s, kept in s/, as DWARF line info
# (loc.awk).
#
#   nix build --impure -f nanofil/bench/profile -o nanofil/bench/profile/out
#   nix build --impure -f nanofil/bench/profile --argstr opt "-O --registers=local" ...
{
  flake ? builtins.getFlake (toString ../../..),
  pkgs ? import flake.inputs.nixpkgs { system = "x86_64-linux"; },
  filcc ? flake.packages.x86_64-linux.filcc-staging,
  opt ? "-O",
}:
let
  programs = import "${flake}/nanofil/bench/programs.nix" {
    inherit pkgs filcc;
  };
  marked =
    pkgs.runCommand "nanofil-marked"
      {
        nativeBuildInputs = [
          pkgs.swi-prolog
          pkgs.patch
        ];
      }
      ''
        mkdir $out && cp -r ${flake}/nanofil $out/nanofil
        chmod -R u+w $out
        (cd $out && patch -p1 <${./marks.patch})
        patchShebangs $out/nanofil/bin
        $out/nanofil/bin/nanofil --save-state $out/nanofil.state
      '';
  # nanofil-cc (nix/nanofil-cc.nix), but marked (remark.py), with line
  # info (loc.awk), keeping .s.
  cc = pkgs.writeShellScript "nanofil-cc-marked" ''
    set -eu
    PATH=${pkgs.swi-prolog}/bin:${pkgs.binutils-unwrapped}/bin:$PATH
    export NANOFIL_STATE=${marked}/nanofil.state
    out= src= compile= args=()
    while [ $# -gt 0 ]; do
      case $1 in
        -c) compile=1 ;;
        -o) out=$2; shift ;;
        *.c) src=$1; args+=("$1") ;;
        *) args+=("$1") ;;
      esac
      shift
    done
    if [ -z "$compile" ] || [ -z "$src" ]; then
      exec ${filcc}/bin/clang "''${args[@]}" ''${out:+-o "$out"}
    fi
    : "''${out:=$(basename "''${src%.c}").o}"
    ${filcc}/bin/clang "''${args[@]}" -E -o "$out.i"
    input=$(realpath "$out.i")
    (cd ${marked}/nanofil/src && ../bin/nanofil ''${NANOFIL_OPT:-} cc "$input" \
      </dev/null) >"$out.pre.s"
    ${pkgs.python3}/bin/python3 ${./remark.py} "$out.pre.s" "$out.s"
    rm "$out.pre.s"
    # as -g would number lines past valgrind's 20 bits (loc.awk).
    ${pkgs.gawk}/bin/awk -v base="$(basename "$out.s")" -f ${./loc.awk} "$out.s" >"$out.loc.s"
    as -o "$out" "$out.loc.s"
    rm "$out.loc.s"
    rm "$out.i"
  '';
in
pkgs.linkFarm "nanofil-profile" (
  pkgs.lib.mapAttrsToList (name: _: {
    inherit name;
    path = programs.build name "marked" cc opt ''
      # Cachegrind names a line by its .s file's base name: keep them unique.
      test -z "$(find . -name '*.o.s' -printf '%f\n' | sort | uniq -d)"
      mkdir $out/s
      find . -name '*.o.s' -exec cp -t $out/s {} +
    '';
  }) programs.progs
)
