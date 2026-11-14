(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude LibioStdfilesCode.
Import ListNotations.
Open Scope string_scope.

Module LibioStdfilesSrc.

Module fn_glibc_stdfiles__IO_stdfiles_init.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("stdfiles.c", 61%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("stdfiles.c", 66%nat)); ((TAtom "L2"), ("stdfiles.c", 65%nat)); ((TAtom "L3"), ("stdfiles.c", 69%nat)); ((TAtom "L5"), ("stdfiles.c", 61%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "f"); ((TAtom "v11"), "f"); ((TAtom "v14"), "f"); ((TAtom "v15"), "f"); ((TAtom "v17"), "f"); ((TAtom "v6"), "f")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L2")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "glibc_stdfiles#_IO_stdfiles_init") (code_module libiostdfiles_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn_glibc_stdfiles__IO_stdfiles_init.

End LibioStdfilesSrc.
