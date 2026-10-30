# nanofil-cc: a CC for building C packages with nanofil. A compile (-c
# of one .c file) is preprocessed by filcc with the same flags, compiled
# by nanofil (with $NANOFIL_OPT, e.g. -O) and assembled by GNU as, and
# the object's name is appended to $NANOFIL_LOG; -std=c23 or gnu23 also
# sets NANOFIL_STD=c23, so nanofil reads C23's keywords, and C90 modes or
# -fgnu89-inline set NANOFIL_STD=gnu89, for GNU inline semantics; -fno-builtin,
# -fno-builtin-memcpy, -fno-builtin-memmove and -ffreestanding keep every
# memcpy and memmove a call (--memcpy=call); -fno-inline and -O0 select
# --inline=none; -fcommon sets NANOFIL_COMMON=1, so tentative
# definitions are common (weak) symbols. __SIZEOF_INT128__ is not defined, since nanofil
# refuses __int128. Anything else
# (linking, configure probes) goes to filcc unchanged. On SWI, nanofil
# runs from a saved state built here, which starts in 0.05 s instead of
# 0.26 s.
{
  pkgs,
  filcc,
  # The nanofil tree to run; the survey passes one of only bin/ and src/.
  src ? ../.,
}:
let
  nanofil =
    pkgs.runCommand "nanofil-src" { nativeBuildInputs = [ pkgs.swi-prolog ]; }
      ''
        cp -r ${src} $out
        chmod -R u+w $out
        patchShebangs $out/bin
        $out/bin/nanofil --save-state $out/nanofil.state
      '';
in
pkgs.writeShellScript "nanofil-cc" ''
  set -eu
  PATH=${pkgs.swi-prolog}/bin:${pkgs.binutils-unwrapped}/bin:$PATH
  export NANOFIL_STATE=''${NANOFIL_STATE-${nanofil}/nanofil.state}
  out= src= compile= copies= inline= args=()
  while [ $# -gt 0 ]; do
    case $1 in
      -c) compile=1 ;;
      -o) out=$2; shift ;;
      -std=c23|-std=gnu23|-std=c2x|-std=gnu2x) export NANOFIL_STD=c23; args+=("$1") ;;
      -std=c89|-std=c90|-std=gnu89|-std=gnu90|-std=iso9899:1990|-std=iso9899:199409|-ansi|-fgnu89-inline)
        export NANOFIL_STD=gnu89; args+=("$1") ;;
      -std=*) unset NANOFIL_STD; args+=("$1") ;;
      -fno-builtin|-fno-builtin-memcpy|-fno-builtin-memmove|-ffreestanding)
        copies=--memcpy=call; args+=("$1") ;;
      -fno-inline|-O0) inline=--inline=none; args+=("$1") ;;
      -fcommon) export NANOFIL_COMMON=1; args+=("$1") ;;
      -fno-common) unset NANOFIL_COMMON; args+=("$1") ;;
      *.c) src=$1; args+=("$1") ;;
      *) args+=("$1") ;;
    esac
    shift
  done
  if [ -z "$compile" ] || [ -z "$src" ]; then
    exec ${filcc}/bin/clang "''${args[@]}" ''${out:+-o "$out"}
  fi
  : "''${out:=$(basename "''${src%.c}").o}"
  # nanofil refuses __int128, so it is not advertised (c_pp.pl).
  ${filcc}/bin/clang "''${args[@]}" -U__SIZEOF_INT128__ -E -o "$out.i"
  input=$(realpath "$out.i")
  # Trealla resolves transitive module imports relative to the working
  # directory. Keep package builds usable on either Prolog host.
  compile() {
    (cd ${nanofil}/src && ../bin/nanofil ''${NANOFIL_OPT:-} $copies $inline cc "$input" \
      </dev/null) >"$out.s" 2>"$out.err"
  }
  # Every compile gets SWI's default 1 GB stack first, so parallel
  # builds meet a larger one only where it is needed. One that overflows
  # it (gettext's 34 MB tree-sitter OCaml parser, about 11M tokens) is
  # compiled again, once, with a 4 GB limit.
  if ! compile; then
    if [ -n "''${NANOFIL_STACK_LIMIT:-}" ] || ! grep -q 'resource_error(stack)' "$out.err"; then
      cat "$out.err" >&2
      exit 1
    fi
    echo "nanofil-cc: $src overflowed the 1 GB stack; compiling it again with NANOFIL_STACK_LIMIT=4000000000" >&2
    export NANOFIL_STACK_LIMIT=4000000000
    compile || { cat "$out.err" >&2; exit 1; }
  fi
  cat "$out.err" >&2
  as -o "$out" "$out.s"
  rm "$out.i" "$out.s" "$out.err"
  echo "$out" >>"''${NANOFIL_LOG:-/dev/null}"
''
