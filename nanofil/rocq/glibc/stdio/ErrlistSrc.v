(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Live sets and memory footprints guide execution but cannot justify a memory access.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith ZArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.


From Glibc Require Import ErrlistCode.
Module ErrlistSrc.

Definition file_0 : string := "errlist.c".

Module fn___get_errlist.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_0, 25%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_0, 29%N)); ((TAtom "L9"), (file_0, 29%N)); ((TAtom "L10"), (file_0, 29%N)); ((TAtom "L4"), (file_0, 30%N)); ((TAtom "L6"), (file_0, 31%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "v0"), "errnum"); ((TAtom "v11"), "mapped"); ((TAtom "v13"), "_sys_errlist_internal_len"); ((TAtom "v19"), "mapped"); ((TAtom "v3"), "errnum"); ((TAtom "v7"), "mapped")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].


Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L9"), [(TAtom "v0")]); ((TAtom "L10"), [(TAtom "v0")]); ((TAtom "L4"), [(TAtom "v0")]); ((TAtom "L6"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L9"), [(TAtom "v0"); (TAtom "v15")]); ((TAtom "L10"), [(TAtom "v0")]); ((TAtom "L4"), []); ((TAtom "L6"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), []); ((TAtom "L9"), [(2%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (0)), "opaque")]); ((TAtom "L10"), []); ((TAtom "L4"), [(5%N, (TApp "tmp" [(TAtom "v22")]), (0), (Some 8), true, false, (Some (TAtom "v18")), None, "opaque")]); ((TAtom "L6"), [])].


End fn___get_errlist.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) errlist_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["__get_errlist"].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("__get_errlist", app (map fst fn___get_errlist.block_src) (app (map fst fn___get_errlist.live_in) (app (map fst fn___get_errlist.live_out) (app (map fst fn___get_errlist.footprint) (fn___get_errlist.loop_heads)))))].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, Some labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) table_labels = true.
Proof. vm_compute. reflexivity. Qed.

End ErrlistSrc.
