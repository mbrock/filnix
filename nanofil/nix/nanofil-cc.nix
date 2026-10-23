# nanofil-cc: a CC for building C packages with nanofil. A compile (-c
# of one .c file) is preprocessed by filcc with the same flags, compiled
# by nanofil (with $NANOFIL_OPT, e.g. -O) and assembled by GNU as, and
# the object's name is appended to $NANOFIL_LOG; anything else (linking,
# configure probes) goes to filcc unchanged.
{ pkgs, filcc }:
let
  nanofil = pkgs.runCommand "nanofil-src" { } ''
    cp -r ${../.} $out
    chmod -R u+w $out
    patchShebangs $out/bin
  '';
in
pkgs.writeShellScript "nanofil-cc" ''
  set -eu
  PATH=${pkgs.swi-prolog}/bin:${pkgs.binutils-unwrapped}/bin:$PATH
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
  ${nanofil}/bin/nanofil ''${NANOFIL_OPT:-} cc "$out.i" </dev/null >"$out.s"
  as -o "$out" "$out.s"
  rm "$out.i" "$out.s"
  echo "$out" >>"''${NANOFIL_LOG:-/dev/null}"
''
