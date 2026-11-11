#!/usr/bin/env bash
# The leaf fixtures of user glibc (docs/glibc-ir.md) for the string,
# memory and ctype proofs: for each line of the table below, compile each
# glibc unit (from the capture of survey/glibc/capture.nix) as
# nanofil-cc would (nix/nanofil-cc.nix: nanofil -O checked-terms, with
# the environment and options survey/glibc/run.py's cc_options reads
# from the unit's compile command), link the checked modules from a
# table of the named roots with rocq/scripts/link.pl, print the result
# with rocq/scripts/gallina.pl --chunk, add the decoded module and its
# functions, and compare it with the committed rocq/glibc/string/NAMECode.v.
#
#   rocq/glibc/string/code.sh [--update] [GLIBC_PP]
#
# GLIBC_PP is the capture (default /tmp/glibc-pp if it exists, else
# build it, about six minutes once). Needs swipl on PATH.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
nf=$(cd "$here/../../.." && pwd)
nanofil="$nf/bin/nanofil"
update=
if [ "${1:-}" = --update ]; then update=1; shift; fi
if [ -n "${1:-}" ]; then pp=$1
elif [ -d /tmp/glibc-pp ]; then pp=/tmp/glibc-pp
else pp=$(nix build --no-link --print-out-paths -f "$nf/survey/glibc/capture.nix"); fi
work=$(mktemp -d)
trap '[ -n "${KEEP:-}" ] || rm -rf "$work"' EXIT
(cd "$nf/src" && "$nanofil" --save-state "$work/nanofil.state" </dev/null)
export NANOFIL_STATE="$work/nanofil.state"
unset NANOFIL_STD NANOFIL_COMMON NANOFIL_MATH_ERRNO

# NAME|ROOTS|UNITS (objects of the capture)|FUNCTIONS (decoded). A name a
# fixture's units do not define, such as strdup's malloc in MemFwd, stays
# external: MallocCode.v defines it. memcmp's one function is 661 lines
# of IR, so MemcmpCode.v is longer than the others.
fixtures='
Strcmp|strcmp|string/strcmp.os|__GI_strcmp
Strncmp|strncmp|string/strncmp.os|__GI_strncmp
Memcmp|memcmp|string/memcmp.os|__GI_memcmp
Strchr|strchr strchrnul strrchr memchr strnlen|string/strchr.os string/strchrnul.os string/strrchr.os string/memchr.os string/strnlen.os|__GI_strchr __GI___strchrnul __GI_strrchr __memchr __GI___strnlen
MemFwd|memcpy mempcpy memset strdup __errno_location mbsinit towlower towupper __ctype_b_loc __ctype_tolower_loc __ctype_toupper_loc __ctype_init __ctype_get_mb_cur_max|string/memcpy.os string/mempcpy.os string/memset.os string/strdup.os csu/errno.os csu/errno-loc.os wcsmbs/mbsinit.os wctype/wcfuncs.os ctype/ctype-info.os locale/mb_cur_max.os|__GI_memcpy __GI___mempcpy __GI_memset __GI___strdup __GI___errno_location __mbsinit __GI___towlower __GI___towupper __ctype_b_loc __ctype_tolower_loc __ctype_toupper_loc __GI___ctype_init __ctype_get_mb_cur_max
Malloc|malloc free|malloc/malloc.os|__GI___libc_malloc __GI___libc_free
'

checked() { # checked UNIT OUT: the checked module nanofil-cc compiles UNIT to
  local envs opts
  read -r envs opts < <(python3 - "$pp/$1.cmd" "$nf/survey/glibc/run.py" <<'EOF'
import importlib.util, sys
spec = importlib.util.spec_from_file_location("run", sys.argv[2])
run = importlib.util.module_from_spec(spec); spec.loader.exec_module(run)
env, opts = run.cc_options(open(sys.argv[1]).read())
print(",".join(f"{k}={v}" for k, v in env.items()) or "-", " ".join(opts))
EOF
)
  [ "$envs" = - ] && envs=
  (cd "$nf/src" && env ${envs//,/ } "$nanofil" -O $opts checked-terms "$pp/$1.i" </dev/null) >"$2"
}

status=0
while IFS='|' read -r name roots units fns; do
  [ -n "$name" ] || continue
  lower=$(echo "$name" | tr '[:upper:]' '[:lower:]')
  specs=()
  for u in $units; do
    obj=$(basename "$u" .os | tr - _)
    checked "$u" "$work/glibc_$obj.term"
    specs+=("glibc_$obj=$work/glibc_$obj.term")
  done
  # One read-only table of the roots, so one entry reaches them all.
  {
    printf 'module([data(%s_roots,ro(export),8,[' "$lower"
    sep=
    for r in $roots; do printf "%sitem(p,sym('%s',0))" "$sep" "$r"; sep=,; done
    printf '])]).\n'
  } >"$work/roots.term"
  (cd "$nf" && swipl rocq/scripts/link.pl "${lower}_roots" "roots=$work/roots.term" "${specs[@]}") >"$work/$lower.linked"
  out="$work/${name}Code.v"
  (cd "$nf" && swipl rocq/scripts/gallina.pl --chunk "$lower" \
     "user glibc's $units, linked from $roots by rocq/scripts/link.pl" \
     rocq/glibc/string/code.sh <"$work/$lower.linked") >"$out"
  {
    printf '\nFrom Nanofil Require Import Syntax Transport Semantics.\n\n'
    printf '(** The module, decoded. *)\n'
    printf 'Definition %s_module : module := Eval vm_compute in\n' "$lower"
    printf '  match decode_module %s_term with Some md => md | None => [] end.\n\n' "$lower"
    printf '(** The term decodes to the module. *)\n'
    printf 'Lemma %s_decodes : decode_module %s_term = Some %s_module.\n' "$lower" "$lower" "$lower"
    printf 'Proof. vm_compute. reflexivity. Qed.\n\n'
    printf '(** The function named n of the module, or an empty one. *)\n'
    printf 'Definition %s_fn (n : string) : func :=\n' "$lower"
    printf '  match find_direct (TAtom n) %s_module with\n' "$lower"
    printf '  | Some (Defined f) => f\n'
    printf '  | _ => mkFunc (TAtom n) (TAtom "export") (RClass W) [] []\n'
    printf '  end.\n'
    for f in $fns; do
      g=glibc$(echo "$f" | sed 's/^__GI_//; s/^_*/_/')
      printf '\n(** glibc'"'"'s `%s`. *)\n' "$f"
      printf 'Definition %s : func := Eval vm_compute in %s_fn "%s".\n' "$g" "$lower" "$f"
      printf '(** The module defines `%s` as [%s]. *)\n' "$f" "$g"
      printf 'Lemma %s_found : find_direct (TAtom "%s") %s_module = Some (Defined %s).\n' "$g" "$f" "$lower" "$g"
      printf 'Proof. vm_compute. reflexivity. Qed.\n'
    done
  } >>"$out"
  target="$here/${name}Code.v"
  if [ -n "$update" ]; then
    cp "$out" "$target"
    echo "glibc: wrote rocq/glibc/string/${name}Code.v"
  elif diff -u "$target" "$out" >"$work/diff"; then
    echo "glibc: rocq/glibc/string/${name}Code.v is current"
  else
    echo "glibc: rocq/glibc/string/${name}Code.v differs from nanofil -O of $units:"
    cat "$work/diff"
    status=1
  fi
done <<<"$fixtures"
exit $status
