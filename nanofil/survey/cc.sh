#!@bash@
# The survey's CC: every compile of C goes to nanofil-cc, one source at
# a time, including a compile and link in one step (`cc -o x x.c`, as
# configure's probes do), whose sources are compiled first and whose
# objects are then linked by filcc. Preprocessing only (-E, -M, -MM),
# linking objects and assembling go to filcc unchanged: they compile no
# C. C read from stdin (`-x c -`, as nixpkgs' GTK check phases build
# check-display) is saved to a .c file and compiled the same way. A C
# compile this wrapper cannot hand to nanofil (-S, or a file without a .c
# suffix) is not compiled by clang silently: it is logged as "fallback"
# in $NANOFIL_LOG and then refused, so a package builds with nanofil
# alone or fails.
set -eu
nf=@nanofilcc@
filcc=@filcc@/bin/clang
log=${NANOFIL_LOG:-/dev/null}
orig=("$@")
srcs=() rest=() out= compile= pponly= asm= lang= other= stdin=
while [ $# -gt 0 ]; do
  case $1 in
    -c) compile=1 ;;
    -E | -M | -MM) pponly=1; rest+=("$1") ;;
    -S) asm=1; rest+=("$1") ;;
    -o) out=$2; shift ;;
    -x) lang=$2; rest+=("$1" "$2"); shift ;;
    -x*) lang=${1#-x}; rest+=("$1") ;;
    -) if [ "$lang" = c ]; then stdin=1; else other=1; rest+=("$1"); fi ;;
    -*) rest+=("$1") ;;
    *.c) if [ -z "$lang" ] || [ "$lang" = c ] || [ "$lang" = none ]; then srcs+=("$1"); else rest+=("$1"); fi ;;
    *) if [ "$lang" = c ] && [ -f "$1" ]; then other=1; fi; rest+=("$1") ;;
  esac
  shift
done
if [ -n "$pponly" ]; then exec $filcc "${orig[@]}"; fi
if [ -n "$stdin" ]; then
  stdin_dir=$(mktemp -d)
  trap 'rm -rf "$stdin_dir"' EXIT
  cat >"$stdin_dir/stdin.c"
  srcs+=("$stdin_dir/stdin.c")
fi
if [ -n "$asm" ] && [ ${#srcs[@]} -gt 0 ] || [ -n "$other" ]; then
  echo "fallback $PWD: ${orig[*]}" >>"$log"
  echo "nanofil-survey-cc: refused, not a .c compile nanofil-cc can do: ${orig[*]}" >&2
  exit 1
fi
if [ ${#srcs[@]} = 0 ]; then exec $filcc "${orig[@]}"; fi
if [ -n "$compile" ]; then
  for s in "${srcs[@]}"; do
    if [ -n "$out" ] && [ ${#srcs[@]} = 1 ]; then o=$out; else o=$(basename "${s%.c}").o; fi
    $nf "${rest[@]}" -c "$s" -o "$o"
  done
  exit 0
fi
tmp=$(mktemp -d)
trap 'rm -rf "$tmp" ${stdin_dir:+"$stdin_dir"}' EXIT
link=() i=0 skip=
for a in "${orig[@]}"; do
  if [ "$skip" = 1 ]; then link+=("$a"); skip=; continue; fi
  if [ -n "$skip" ]; then skip=; continue; fi
  case $a in
    -o) link+=("$a"); skip=1 ;;
    -x) skip=drop ;;
    -x*) ;;
    -)
      if [ -n "$stdin" ]; then
        i=$((i + 1)); o=$tmp/$i-stdin.o
        $nf "${rest[@]}" -c "$stdin_dir/stdin.c" -o "$o"
        link+=("$o")
      else
        link+=("$a")
      fi
      ;;
    *.c)
      if printf '%s\n' "${srcs[@]}" | grep -qxF -- "$a"; then
        i=$((i + 1)); o=$tmp/$i-$(basename "${a%.c}").o
        $nf "${rest[@]}" -c "$a" -o "$o"
        link+=("$o")
      else
        link+=("$a")
      fi
      ;;
    *) link+=("$a") ;;
  esac
done
$filcc "${link[@]}"
