#!/usr/bin/env bash
# This script reproduces the printf-buffer write, flush and FILE fixtures.
# Run buffer-code.sh [--update] [GLIBC_PP] with the same pinned capture and
# compiler as code.sh. buffer-fixtures.sha256 pins all six captured inputs.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
nf=$(cd "$here/../../.." && pwd)
update=
if [ "${1:-}" = --update ]; then update=1; shift; fi
if [ -n "${1:-}" ]; then pp=$(realpath "$1")
elif [ -d /tmp/glibc-pp ]; then pp=$(realpath /tmp/glibc-pp)
else pp=$(nix build --no-link --print-out-paths -f "$nf/survey/glibc/capture.nix"); fi
(cd "$pp" && sha256sum -c "$here/buffer-fixtures.sha256")
work=$(mktemp -d)
trap '[ -n "${KEEP:-}" ] || rm -rf "$work"' EXIT
(cd "$nf/src" && "$nf/bin/nanofil" --save-state "$work/nanofil.state" </dev/null)
export NANOFIL_STATE="$work/nanofil.state"
unset NANOFIL_STD NANOFIL_COMMON NANOFIL_MATH_ERRNO
specs=()
for unit in printf_buffer_write printf_buffer_flush printf_buffer_to_file; do
  path="$pp/stdio-common/$unit.os"
  read -r envs opts < <(python3 - "$path.cmd" "$nf/survey/glibc/run.py" <<'PY'
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
  obj=glibc_$unit
  (cd "$nf/src" && env ${envs//,/ } "$nf/bin/nanofil" -O $opts checked-terms "$path.i" </dev/null) > "$work/$obj.term"
  specs+=("$obj=$work/$obj.term")
done
printf '%s\n' "module([data(buffer_roots,ro(export),8,[item(p,sym('__printf_buffer_write',0)),item(p,sym('__printf_buffer_flush',0)),item(p,sym('__printf_buffer_flush_to_file',0)),item(p,sym('__printf_buffer_to_file_init',0)),item(p,sym('__printf_buffer_to_file_done',0))])])." > "$work/roots.term"
(cd "$nf" && swipl rocq/scripts/link.pl --ctors buffer_roots "roots=$work/roots.term" "${specs[@]}") > "$work/linked"
cat > "$work/select.pl" <<'PL'
:- initialization(main, main).
main :-
    current_prolog_flag(argv, [File, Group]), read_file_to_terms(File, [module(Is)], []),
    (Group = io -> Names = ['__printf_buffer_write', '__printf_buffer_flush']
    ; Names = ['__printf_buffer_to_file_switch',
               '__printf_buffer_flush_to_file', '__printf_buffer_to_file_init',
               '__printf_buffer_to_file_done']),
    include([I]>>(I = func(N, _, _, _, _), memberchk(N, Names)), Is, Sel),
    length(Names, N), length(Sel, N), write_canonical(module(Sel)), write('.'), nl.
PL
for group in io file; do
  if [ "$group" = io ]; then file=PrintfBufferIoCode.v; else file=PrintfBufferFileCode.v; fi
  prefix=printf_buffer_$group
  swipl "$work/select.pl" "$work/linked" "$group" > "$work/selected"
  (cd "$nf" && swipl rocq/scripts/gallina.pl --chunk "$prefix" \
    "the pinned user-glibc 2.44 printf-buffer units" \
    rocq/glibc/stdio/buffer-code.sh < "$work/selected") > "$work/generated.v"
  # Postprocessing changes only prose and adds computational lookup witnesses.
  python3 - "$work/generated.v" "$work/$file" "$prefix" "$group" <<'PY'
import sys
text = open(sys.argv[1]).read()
_, body = text.split('*)', 1)
body = body.replace('(** The one-character atom with code n. *)',
                    '(** This helper constructs the atom containing one character with code n. *)')
body = body.replace('(** The module term. *)',
                    '(** This term contains the selected checked function bodies. *)')
prefix, group = sys.argv[3:]
names = (['__printf_buffer_write', '__printf_buffer_flush'] if group == 'io' else
         ['__printf_buffer_to_file_switch',
          '__printf_buffer_flush_to_file', '__printf_buffer_to_file_init',
          '__printf_buffer_to_file_done'])
header = '''(** These checked bodies implement printf-buffer operations in user-glibc 2.44.
    They retain the source's failure paths and calls into stream operations;
    decoding these bodies does not establish contracts for those calls.

    rocq/glibc/stdio/buffer-code.sh reproduces these terms from the pinned
    capture with gallina.pl. Regenerate this file rather than editing it. *)'''
tail = f'''
From Nanofil Require Import Syntax Transport Semantics.

(** Decoding gives the actual checked bodies used by instruction proofs. *)
Definition {prefix}_module : module := Eval vm_compute in
  match decode_module {prefix}_term with Some md => md | None => [] end.

(** Computation rules out the empty fallback in the decoded module. *)
Lemma {prefix}_decodes : decode_module {prefix}_term = Some {prefix}_module.
Proof. vm_compute. reflexivity. Qed.

(** Function lookup selects a checked body without supplying its specification. *)
Definition {prefix}_fn (n : string) : func :=
  match find_direct (TAtom n) {prefix}_module with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "export") (RClass W) [] []
  end.
'''
for name in names:
    short = name.lstrip('_')
    tail += f'''
(** This definition selects the checked body of [{name}]. *)
Definition glibc___{short} : func := Eval vm_compute in
  {prefix}_fn "{name}".

(** Computation checks that lookup found the body rather than its fallback. *)
Lemma {prefix}_find_{short} :
  find_direct (TAtom "{name}") {prefix}_module = Some (Defined glibc___{short}).
Proof. vm_compute. reflexivity. Qed.
'''
open(sys.argv[2], 'w').write(header + body + tail)
PY
  test "$(wc -l < "$work/$file")" -le 700
  if [ -n "$update" ]; then cp "$work/$file" "$here/$file"
  else diff -u "$here/$file" "$work/$file"; fi
  echo "stdio: $file matches the pinned capture"
done
