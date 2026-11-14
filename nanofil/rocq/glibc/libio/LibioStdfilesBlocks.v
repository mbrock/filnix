(** An executor needs to know which values and memory regions a block may use.
    These tables list live temporaries and explicit memory accesses to guide that choice.
    Wrong hints can stop execution, but they cannot justify a memory access.
    No soundness theorem may assume that these tables are correct.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith ZArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.


From Glibc Require Import LibioStdfilesSrc.
Module LibioStdfilesBlocks.

Module fn_glibc_stdfiles__IO_stdfiles_init.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), []); ((TAtom "L2"), []); ((TAtom "L3"), [(TAtom "chk0"); (TAtom "pr.1")]); ((TAtom "L5"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v1")]); ((TAtom "L2"), [(TAtom "chk0"); (TAtom "pr.1")]); ((TAtom "L3"), [(TAtom "v17")]); ((TAtom "L5"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L2"), [(1%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)))]); ((TAtom "L3"), [(0%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0))); (3%N, (TApp "tmp" [(TAtom "v13")]), (0), (Some 8), false, true, (Some (TAtom "v12")), (Some (184))); (5%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)))]); ((TAtom "L5"), [])].

End fn_glibc_stdfiles__IO_stdfiles_init.

(** Projection keeps temporary sets and access records out of the membership computation. *)
Definition block_labels : list (string * list name) := Eval lazy in
  [("glibc_stdfiles#_IO_stdfiles_init", app (map fst fn_glibc_stdfiles__IO_stdfiles_init.live_in) (app (map fst fn_glibc_stdfiles__IO_stdfiles_init.live_out) (map fst fn_glibc_stdfiles__IO_stdfiles_init.footprint)))].

(** The source sidecar projects these labels from the decoded module, not from the hint tables. *)
Lemma labels_valid :
  forallb (fun row =>
    match find (fun entry => String.eqb (fst entry) (fst row)) LibioStdfilesSrc.source_blocks with
    | Some (_, Some labels) => forallb (fun l => existsb (name_eqb l) labels) (snd row)
    | _ => false
    end) block_labels = true.
Proof. vm_compute. reflexivity. Qed.

End LibioStdfilesBlocks.
