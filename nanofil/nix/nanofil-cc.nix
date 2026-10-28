# nanofil-cc: a CC for building C packages with nanofil. A compile (-c
# of one .c file) is preprocessed by filcc with the same flags, compiled
# by nanofil (with $NANOFIL_OPT, e.g. -O) and assembled by GNU as, and
# the object's name is appended to $NANOFIL_LOG; -std=c23 or gnu23 also
# sets NANOFIL_STD=c23, so nanofil reads C23's keywords; -fno-builtin,
# -fno-builtin-memcpy, -fno-builtin-memmove and -ffreestanding keep every
# memcpy and memmove a call (--memcpy=call). Anything else
# (linking, configure probes) goes to filcc unchanged. On SWI, nanofil
# runs from a saved state built here, which starts in 0.05 s instead of
# 0.26 s.
{ pkgs, filcc }:
let
  nanofil =
    pkgs.runCommand "nanofil-src" { nativeBuildInputs = [ pkgs.swi-prolog ]; }
      ''
        cp -r ${../.} $out
        chmod -R u+w $out
        patchShebangs $out/bin
        $out/bin/nanofil --save-state $out/nanofil.state
      '';
in
pkgs.writeShellScript "nanofil-cc" ''
  set -eu
  PATH=${pkgs.swi-prolog}/bin:${pkgs.binutils-unwrapped}/bin:$PATH
  export NANOFIL_STATE=''${NANOFIL_STATE-${nanofil}/nanofil.state}
  out= src= compile= copies= args=()
  while [ $# -gt 0 ]; do
    case $1 in
      -c) compile=1 ;;
      -o) out=$2; shift ;;
      -std=c23|-std=gnu23|-std=c2x|-std=gnu2x) export NANOFIL_STD=c23; args+=("$1") ;;
      -fno-builtin|-fno-builtin-memcpy|-fno-builtin-memmove|-ffreestanding)
        copies=--memcpy=call; args+=("$1") ;;
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
  # Trealla resolves transitive module imports relative to the working
  # directory. Keep package builds usable on either Prolog host.
  (cd ${nanofil}/src && ../bin/nanofil ''${NANOFIL_OPT:-} $copies cc "$input" \
    </dev/null) >"$out.s"
  as -o "$out" "$out.s"
  rm "$out.i" "$out.s"
  echo "$out" >>"''${NANOFIL_LOG:-/dev/null}"
''
