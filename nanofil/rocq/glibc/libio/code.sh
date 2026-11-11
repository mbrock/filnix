#!/usr/bin/env bash
# The narrow libio and exit fixtures of user glibc (docs/glibc-ir.md) for
# hi_atexit.c's `atexit(close_stdout); puts("hello"); exit(0);`.
#
# Compile each unit below (from the capture of survey/glibc/capture.nix)
# as nanofil-cc would (nanofil -O checked-terms with the unit's
# cc_options, as rocq/glibc/string/code.sh does), link them all once
# with rocq/scripts/link.pl from a table of the roots, and, for each line
# of the fixture table, print the linked module's items named on that
# line with rocq/scripts/gallina.pl --chunk, add the decoded module and
# each function, and compare it with the committed
# rocq/glibc/libio/NAMECode.v.
#
# One link makes every local name (`glibc_genops#run_fp`) the same in
# every fixture. The linked module has 79 functions, since the jump
# tables of `c: __io_vtables` name every libio function; printed whole
# its term alone takes 20 s to elaborate. Each fixture holds only the
# functions its proofs walk, so each compiles in a few seconds. The
# proofs are stated for any genv that finds these functions at their
# names, so the whole linked program (or GNU Hello's) can use them.
#
#   rocq/glibc/libio/code.sh [--update] [GLIBC_PP]
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

# The narrow stream, syscall wrapper and exit units, with stdio.os for
# `c: stdout` and errno.os for `c: errno`. Not locale, printf or gconv;
# strlen, the mem* copies, malloc and free stay external, and the proofs
# take their rules as hypotheses.
units='libio/__fpending.os libio/ferror.os libio/filedoalloc.os libio/fileops.os
libio/genops.os libio/iofclose.os libio/iofputs.os libio/ioputs.os libio/stdfiles.os
libio/stdio.os libio/vtables.os termios/isatty_nostatus.os io/write.os io/lseek64.os
io/fstat64.os io/close_nocancel.os io/close_nocancel_nostatus.os posix/_exit.os
stdlib/exit.os stdlib/cxa_atexit.os stdlib/atexit.oS stdlib/cxa_thread_atexit_impl.os
nptl/libc-cleanup.os misc/single_threaded.os csu/errno.os misc/makedev.os io/write_nocancel.os'
roots='puts fputs __fpending ferror fclose exit atexit _exit __close_nocancel_nostatus'

# NAME|FUNCTIONS (printed and decoded, in link order).
fixtures='
Sys|__GI__exit __GI___libc_write __GI___write_nocancel __GI___fstat64 __lseek64 __GI___close_nocancel __GI___close_nocancel_nostatus __isatty_nostatus __GI___libc_cleanup_push_defer __GI___libc_cleanup_pop_restore
LibioRead|__fpending _IO_ferror __gnu_dev_major __GI__IO_file_stat __GI__IO_file_close __GI__IO_setb __GI__IO_doallocbuf __GI__IO_file_doallocate _IO_new_file_write
LibioDoWrite|_IO_new_do_write _IO_new_file_overflow
LibioGen|__GI___overflow __GI__IO_default_xsputn __GI__IO_unsave_markers __GI___call_tls_dtors
LibioXsputn|_IO_new_file_xsputn
LibioPuts|__GI__IO_puts __GI__IO_fputs
LibioUnlink|__GI__IO_un_link _IO_new_file_finish __GI__IO_default_finish
LibioCloseIt|_IO_file_close_maybe_unlink
LibioFclose|_IO_new_fclose
LibioFlush|__GI__IO_flush_all
LibioCleanup|_IO_cleanup
ExitRun|__run_exit_handlers __GI_exit
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

specs=()
for u in $units; do
  obj=$(basename "$u" | sed 's/\.o[sS]$//' | tr - _)
  checked "$u" "$work/glibc_$obj.term"
  specs+=("glibc_$obj=$work/glibc_$obj.term")
done
{
  printf 'module([data(libio_roots,ro(export),8,['
  sep=
  for r in $roots; do printf "%sitem(p,sym('%s',0))" "$sep" "$r"; sep=,; done
  printf '])]).\n'
} >"$work/roots.term"
# --ctors keeps stdfiles' constructor _IO_stdfiles_init, which links the
# three standard streams; the proofs start from its postcondition.
(cd "$nf" && swipl rocq/scripts/link.pl --ctors libio_roots "roots=$work/roots.term" "${specs[@]}") >"$work/libio.linked"

# select.pl LINKED NAME...: the module of LINKED's functions named, all
# of them there, in LINKED's order.
cat >"$work/select.pl" <<'EOF'
:- initialization(main, main).
main :-
    current_prolog_flag(argv, [F|Ns]), read_file_to_terms(F, [module(Is)], []),
    maplist([N, A]>>atom_string(A, N), Ns, As),
    include([I]>>(I = func(N, _, _, _, _), memberchk(N, As)), Is, Sel),
    length(As, K), length(Sel, K),
    write_canonical(module(Sel)), write('.'), nl.
EOF

status=0
while IFS='|' read -r name fns; do
  [ -n "$name" ] || continue
  lower=$(echo "$name" | tr '[:upper:]' '[:lower:]')
  swipl "$work/select.pl" "$work/libio.linked" $fns >"$work/$lower.sel"
  out="$work/${name}Code.v"
  (cd "$nf" && swipl rocq/scripts/gallina.pl --chunk "$lower" \
     "user glibc's narrow libio and exit units (rocq/glibc/libio/code.sh), linked from $roots by rocq/scripts/link.pl, its functions $fns" \
     rocq/glibc/libio/code.sh <"$work/$lower.sel") >"$out"
  {
    printf '\nFrom Nanofil Require Import Syntax Transport Semantics.\n\n'
    printf '(** The functions, decoded as a module. *)\n'
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
      g=glibc_$(echo "$f" | sed 's/^__GI_//')
      printf '\n(** glibc'"'"'s `%s`. *)\n' "$f"
      printf 'Definition %s : func := Eval vm_compute in %s_fn "%s".\n' "$g" "$lower" "$f"
    done
  } >>"$out"
  target="$here/${name}Code.v"
  if [ -n "$update" ]; then
    cp "$out" "$target"
    echo "glibc: wrote rocq/glibc/libio/${name}Code.v"
  elif diff -u "$target" "$out" >"$work/diff"; then
    echo "glibc: rocq/glibc/libio/${name}Code.v is current"
  else
    echo "glibc: rocq/glibc/libio/${name}Code.v differs from nanofil -O of the units:"
    cat "$work/diff"
    status=1
  fi
done <<<"$fixtures"
exit $status
