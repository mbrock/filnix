#!/usr/bin/env bash
# This script reproduces the diagnostic-state and printf-buffer leaf fixtures.
# It compiles captured glibc units with their original options, links their
# checked terms, and prints the selected bodies with gallina.pl --chunk.
#
# Run code.sh [--update] [GLIBC_PP]. The default capture comes from the
# staging glibc derivation; fixtures.sha256 pins its selected inputs.
# The source is mbrock/fil-c at 18b6663a2785c8eba6cc2a544a7711e19fc448c7.
# Its captured compiler is Fil-C 0.687, clang 20.1.8, at
# /nix/store/741jfqap41s2ggs5y6bq7pm9b38xrmrp-filc/bin/clang.
# The capture output is /nix/store/7hh45cvwzrqyqvpknnlj82vrqdmg6kxw-filc-glibc-pp-2.44.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
nf=$(cd "$here/../../.." && pwd)
update=
if [ "${1:-}" = --update ]; then update=1; shift; fi
if [ -n "${1:-}" ]; then pp=$(realpath "$1")
elif [ -d /tmp/glibc-pp ]; then pp=$(realpath /tmp/glibc-pp)
else pp=$(nix build --no-link --print-out-paths -f "$nf/survey/glibc/capture.nix"); fi
(cd "$pp" && sha256sum -c "$here/fixtures.sha256")
work=$(mktemp -d)
trap '[ -n "${KEEP:-}" ] || rm -rf "$work"' EXIT
(cd "$nf/src" && "$nf/bin/nanofil" --save-state "$work/nanofil.state" </dev/null)
export NANOFIL_STATE="$work/nanofil.state"
unset NANOFIL_STD NANOFIL_COMMON NANOFIL_MATH_ERRNO

specs=()
for unit in nptl/pthread_setcancelstate.os stdio-common/printf_buffer_done.os; do
  read -r envs opts < <(python3 - "$pp/$unit.cmd" "$nf/survey/glibc/run.py" <<'PY'
import importlib.util
import sys
spec = importlib.util.spec_from_file_location("run", sys.argv[2])
run = importlib.util.module_from_spec(spec)
spec.loader.exec_module(run)
env, opts = run.cc_options(open(sys.argv[1]).read())
print(",".join(f"{k}={v}" for k, v in env.items()) or "-", " ".join(opts))
PY
  )
  [ "$envs" = - ] && envs=
  obj=glibc_$(basename "$unit" .os)
  (cd "$nf/src" && env ${envs//,/ } "$nf/bin/nanofil" -O $opts checked-terms "$pp/$unit.i" </dev/null) > "$work/$obj.term"
  specs+=("$obj=$work/$obj.term")
done
printf '%s\n' "module([data(stdio_roots,ro(export),8,[item(p,sym('__printf_buffer_done',0)),item(p,sym('__GI___pthread_setcancelstate',0))])])." > "$work/roots.term"
(cd "$nf" && swipl rocq/scripts/link.pl --ctors stdio_roots "roots=$work/roots.term" "${specs[@]}") > "$work/linked"
cat > "$work/select.pl" <<'PL'
:- initialization(main, main).
main :-
    current_prolog_flag(argv, [File]), read_file_to_terms(File, [module(Is)], []),
    include([I]>>(I = func(N, _, _, _, _),
      memberchk(N, ['__printf_buffer_done', '__GI___pthread_setcancelstate'])), Is, Sel),
    length(Sel, 2), write_canonical(module(Sel)), write('.'), nl.
PL
swipl "$work/select.pl" "$work/linked" > "$work/selected"
(cd "$nf" && swipl rocq/scripts/gallina.pl --chunk printf_state \
  "the pinned user-glibc 2.44 cancellation and printf-buffer completion units" \
  rocq/glibc/stdio/code.sh < "$work/selected") > "$work/generated.v"
# Only the generated prose changes here; the checked term stays unchanged.
python3 - "$work/generated.v" "$work/PrintfStateCode.v" <<'PY'
import sys
text = open(sys.argv[1]).read()
_, body = text.split('*)', 1)
body = body.replace('(** The one-character atom with code n. *)',
                    '(** This helper constructs the atom containing one character with code n. *)')
body = body.replace('(** The module term. *)',
                    '(** This term contains the selected checked function bodies. *)')
header = '''(** These checked bodies implement cancellation-state changes and printf-buffer
    completion in user-glibc 2.44. The fixture supports instruction proofs
    without treating either function as an external contract.

    rocq/glibc/stdio/code.sh reproduces these terms from the pinned capture
    with gallina.pl. Regenerate this file rather than editing it. *)'''
open(sys.argv[2], 'w').write(header + body)
PY
cat >> "$work/PrintfStateCode.v" <<'COQ'

From Nanofil Require Import Syntax Transport Semantics.

(** Decoding gives the actual checked function bodies, not their specifications. *)
Definition printf_state_module : module := Eval vm_compute in
  match decode_module printf_state_term with Some md => md | None => [] end.

(** Computation checks that decoding did not take the empty fallback. *)
Lemma printf_state_decodes : decode_module printf_state_term = Some printf_state_module.
Proof. vm_compute. reflexivity. Qed.

(** Function lookup selects a decoded body for the subsequent instruction proofs. *)
Definition printf_state_fn (n : string) : func :=
  match find_direct (TAtom n) printf_state_module with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "export") (RClass W) [] []
  end.

(** This body changes the thread's cancellation flag and optionally saves its old value. *)
Definition glibc___pthread_setcancelstate : func := Eval vm_compute in
  printf_state_fn "__GI___pthread_setcancelstate".

(** This body returns the accumulated count or reports failure and integer overflow. *)
Definition glibc___printf_buffer_done : func := Eval vm_compute in
  printf_state_fn "__printf_buffer_done".

(** Lookup finds the cancellation body rather than the empty fallback. *)
Lemma printf_state_find_cancel :
  find_direct (TAtom "__GI___pthread_setcancelstate") printf_state_module =
  Some (Defined glibc___pthread_setcancelstate).
Proof. vm_compute. reflexivity. Qed.

(** Lookup finds the completion body rather than the empty fallback. *)
Lemma printf_state_find_done :
  find_direct (TAtom "__printf_buffer_done") printf_state_module =
  Some (Defined glibc___printf_buffer_done).
Proof. vm_compute. reflexivity. Qed.
COQ
test "$(wc -l < "$work/PrintfStateCode.v")" -le 700
if [ -n "$update" ]; then
  cp "$work/PrintfStateCode.v" "$here/PrintfStateCode.v"
else
  diff -u "$here/PrintfStateCode.v" "$work/PrintfStateCode.v"
fi
echo 'stdio: PrintfStateCode.v matches the pinned capture'
