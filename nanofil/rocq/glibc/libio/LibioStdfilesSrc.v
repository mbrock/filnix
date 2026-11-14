(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.


From Glibc Require Import LibioStdfilesCode.
Module LibioStdfilesSrc.

Definition file_0 : string := "stdfiles.c".

Module fn_glibc_stdfiles__IO_stdfiles_init.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_0, 61%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 66%N)); ((TAtom "L2"), (file_0, 65%N)); ((TAtom "L3"), (file_0, 69%N)); ((TAtom "L5"), (file_0, 61%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "f"); ((TAtom "v11"), "f"); ((TAtom "v14"), "f"); ((TAtom "v15"), "f"); ((TAtom "v17"), "f"); ((TAtom "v6"), "f")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L2")].

End fn_glibc_stdfiles__IO_stdfiles_init.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) libiostdfiles_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["glibc_stdfiles#_IO_stdfiles_init"].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, Some labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) [("glibc_stdfiles#_IO_stdfiles_init", app (map fst fn_glibc_stdfiles__IO_stdfiles_init.block_src) fn_glibc_stdfiles__IO_stdfiles_init.loop_heads)] = true.
Proof. vm_compute. reflexivity. Qed.

End LibioStdfilesSrc.
