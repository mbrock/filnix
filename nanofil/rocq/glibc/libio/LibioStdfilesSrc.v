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


Definition live_in : list (name * list name) :=
  [((TAtom "start"), []); ((TAtom "L2"), []); ((TAtom "L3"), [(TAtom "chk0"); (TAtom "pr.1")]); ((TAtom "L5"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v1")]); ((TAtom "L2"), [(TAtom "chk0"); (TAtom "pr.1")]); ((TAtom "L3"), [(TAtom "v17")]); ((TAtom "L5"), [])].

(** Stop messages can name a C field instead of reporting only an address.
    Source origins and completed layouts supply the field path; unresolved paths use "opaque".
    These paths guide messages and annotations, not memory-safety arguments.
    Local addresses name storage owned by this invocation.
    Accesses with runtime byte counts have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z * string)) :=
  [((TAtom "start"), []); ((TAtom "L2"), [(1%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)), "opaque")]); ((TAtom "L3"), [(0%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)), "opaque"); (3%N, (TApp "tmp" [(TAtom "v13")]), (0), (Some 8), false, true, (Some (TAtom "v12")), (Some (184)), "(*f)->_prevchain"); (5%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)), "opaque")]); ((TAtom "L5"), [])].


End fn_glibc_stdfiles__IO_stdfiles_init.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) libiostdfiles_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["glibc_stdfiles#_IO_stdfiles_init"].

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  [("glibc_stdfiles#_IO_stdfiles_init", app (map fst fn_glibc_stdfiles__IO_stdfiles_init.block_src) (app (map fst fn_glibc_stdfiles__IO_stdfiles_init.live_in) (app (map fst fn_glibc_stdfiles__IO_stdfiles_init.live_out) (app (map fst fn_glibc_stdfiles__IO_stdfiles_init.footprint) (fn_glibc_stdfiles__IO_stdfiles_init.loop_heads)))))].

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

End LibioStdfilesSrc.
