# The benchmark's programs built for counting executed access checks
# (checks.py, docs/perf.md item 16): filcc -O2 with its check scheduler
# in each configuration, and nanofil -O with and without inlining, the
# nanofil objects assembled with `as -L` so that every block label of
# the .s stays a symbol (objdump then names each block), and the .s
# kept in s/. Neither changes .text.
#
#   nix build --impure -f nanofil/bench/profile/checks.nix -o nanofil/bench/profile/checks
#   nix build ... --argstr only ref,ref-fwd     # a subset of the variants
{
  flake ? builtins.getFlake (toString ../../..),
  pkgs ? import flake.inputs.nixpkgs { system = "x86_64-linux"; },
  filcc ? flake.packages.x86_64-linux.filcc-staging,
  only ? "",
}:
let
  programs = import "${flake}/nanofil/bench/programs.nix" {
    inherit pkgs filcc;
  };
  # filcc with extra flags on compiles (-c) only; FilPizlonator's
  # switches are cl::opts (FilPizlonator.cpp:59, 71).
  filccWith =
    flags:
    pkgs.writeShellScript "filcc-variant" ''
      for a in "$@"; do
        if [ "$a" = -c ]; then exec ${filcc}/bin/clang "$@" ${flags}; fi
      done
      exec ${filcc}/bin/clang "$@"
    '';
  noBackward = "-mllvm -filc-propagate-checks-backward=false";
  noSchedule = "-mllvm -filc-optimize-checks=false";
  filccVariants = {
    ref = "";
    ref-noinline = "-fno-inline";
    # Forward propagation only: removes checks already established on
    # every path, never moves one earlier.
    ref-fwd = noBackward;
    ref-fwd-noinline = "${noBackward} -fno-inline";
    # No scheduling at all: every access's own checks, then LLVM.
    ref-nosched = noSchedule;
    ref-nosched-noinline = "${noSchedule} -fno-inline";
  };
  nanofil =
    pkgs.runCommand "nanofil-src" { nativeBuildInputs = [ pkgs.swi-prolog ]; }
      ''
        cp -r ${flake}/nanofil $out
        chmod -R u+w $out
        patchShebangs $out/bin
        $out/bin/nanofil --save-state $out/nanofil.state
      '';
  # nix/nanofil-cc.nix, keeping the .s and its local labels.
  nanofilCc = pkgs.writeShellScript "nanofil-cc-labels" ''
    set -eu
    PATH=${pkgs.swi-prolog}/bin:${pkgs.binutils-unwrapped}/bin:$PATH
    export NANOFIL_STATE=${nanofil}/nanofil.state
    out= src= compile= inline= args=()
    while [ $# -gt 0 ]; do
      case $1 in
        -c) compile=1 ;;
        -o) out=$2; shift ;;
        -fno-inline|-O0) inline=--inline=none; args+=("$1") ;;
        *.c) src=$1; args+=("$1") ;;
        *) args+=("$1") ;;
      esac
      shift
    done
    if [ -z "$compile" ] || [ -z "$src" ]; then
      exec ${filcc}/bin/clang "''${args[@]}" ''${out:+-o "$out"}
    fi
    : "''${out:=$(basename "''${src%.c}").o}"
    ${filcc}/bin/clang "''${args[@]}" -U__SIZEOF_INT128__ -E -o "$out.i"
    input=$(realpath "$out.i")
    (cd ${nanofil}/src && ../bin/nanofil ''${NANOFIL_OPT:-} $inline cc "$input" </dev/null) >"$out.s"
    as -L -o "$out" "$out.s"
    rm "$out.i"
  '';
  nanofilVariants = {
    O = "-O";
    O-noinline = "-O --inline=none";
    # Every access keeps its own full check (no M7 reuse or renewal).
    O-refchecks = "-O --checks=reference";
    O-refchecks-noinline = "-O --checks=reference --inline=none";
    # Half checks (docs/half.md): one bound tested where an earlier check
    # of the object proves the other.
    O-half = "-O --checks=half";
  };
  # The preprocessed sources nanofil compiles (checkclass.py reads them),
  # with filcc compiling the objects so that the program links.
  preprocess = pkgs.writeShellScript "filcc-preprocess" ''
    set -eu
    out= src= compile= args=()
    for a in "$@"; do
      case $a in -c) compile=1 ;; *.c) src=$a ;; esac
    done
    while [ $# -gt 0 ]; do
      case $1 in -o) out=$2; args+=("$1" "$2"); shift ;; *) args+=("$1") ;; esac
      shift
    done
    if [ -n "$compile" ] && [ -n "$src" ]; then
      : "''${out:=$(basename "''${src%.c}").o}"
      a2=()
      skip=
      for a in "''${args[@]}"; do
        if [ -n "$skip" ]; then skip=; continue; fi
        case $a in -c) ;; -o) skip=1 ;; *) a2+=("$a") ;; esac
      done
      ${filcc}/bin/clang "''${a2[@]}" -U__SIZEOF_INT128__ -E -o "$out.i"
    fi
    exec ${filcc}/bin/clang "''${args[@]}"
  '';
  keepI = ''
    mkdir $out/i
    find . -name '*.o.i' -exec cp -t $out/i {} +
  '';
  keepS = ''
    mkdir $out/s
    find . -name '*.o.s' -exec cp -t $out/s {} +
  '';
  want = v: only == "" || builtins.elem v (pkgs.lib.splitString "," only);
  entries = pkgs.lib.concatLists (
    pkgs.lib.mapAttrsToList (
      name: _:
      pkgs.lib.mapAttrsToList (v: flags: {
        name = "${name}/${v}";
        path = programs.build name v (filccWith flags) "" "";
      }) (pkgs.lib.filterAttrs (v: _: want v) filccVariants)
      ++ pkgs.lib.optional (want "src") {
        name = "${name}/src";
        path = programs.build name "src" preprocess "" keepI;
      }
      ++ pkgs.lib.mapAttrsToList (v: opt: {
        name = "${name}/${v}";
        path = programs.build name v nanofilCc opt keepS;
      }) (pkgs.lib.filterAttrs (v: _: want v) nanofilVariants)
    ) programs.progs
  );
in
pkgs.linkFarm "nanofil-checks" entries
