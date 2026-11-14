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


From Glibc Require Import SaySrc.
Module SayBlocks.

Module fn_main.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].

End fn_main.

Module fn___strlen.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "iw_3.start"), [(TAtom "iw_2.v12")]); ((TAtom "iw_3.iw_1.iw_1.L3"), [(TAtom "iw_2.v12")]); ((TAtom "iw_3.iw_1.iw_1.L4"), []); ((TAtom "L28"), [(TAtom "v4")]); ((TAtom "iw_5.start"), [(TAtom "iw_4.iw_1.v13"); (TAtom "v32"); (TAtom "v37"); (TAtom "v4")]); ((TAtom "iw_5.iw_3.iw_1.iw_1.L3"), [(TAtom "iw_4.iw_1.v13"); (TAtom "v32"); (TAtom "v4")]); ((TAtom "iw_5.iw_3.iw_1.iw_1.L4"), [(TAtom "v32"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "iw_2.v12"); (TAtom "v10"); (TAtom "v4")]); ((TAtom "iw_3.start"), [(TAtom "iw_2.v12")]); ((TAtom "iw_3.iw_1.iw_1.L3"), [(TAtom "iw_3.iw_1.iw_1.v22")]); ((TAtom "iw_3.iw_1.iw_1.L4"), []); ((TAtom "L28"), [(TAtom "iw_4.iw_1.v13"); (TAtom "v32"); (TAtom "v37"); (TAtom "v4")]); ((TAtom "iw_5.start"), [(TAtom "iw_4.iw_1.v13"); (TAtom "v32"); (TAtom "v4")]); ((TAtom "iw_5.iw_3.iw_1.iw_1.L3"), [(TAtom "iw_5.iw_3.iw_1.iw_1.v22"); (TAtom "v32"); (TAtom "v4")]); ((TAtom "iw_5.iw_3.iw_1.iw_1.L4"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(5%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 8), true, false, (Some (TAtom "v0")), None)]); ((TAtom "iw_3.start"), []); ((TAtom "iw_3.iw_1.iw_1.L3"), []); ((TAtom "iw_3.iw_1.iw_1.L4"), []); ((TAtom "L28"), [(2%N, (TApp "tmp" [(TAtom "v32")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (8)))]); ((TAtom "iw_5.start"), []); ((TAtom "iw_5.iw_3.iw_1.iw_1.L3"), []); ((TAtom "iw_5.iw_3.iw_1.iw_1.L4"), [])].

End fn___strlen.

Module fn___GI___libc_write.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].

End fn___GI___libc_write.

(** Projection keeps temporary sets and access records out of the membership computation. *)
Definition block_labels : list (string * list name) := Eval lazy in
  [("main", app (map fst fn_main.live_in) (app (map fst fn_main.live_out) (map fst fn_main.footprint))); ("__strlen", app (map fst fn___strlen.live_in) (app (map fst fn___strlen.live_out) (map fst fn___strlen.footprint))); ("__GI___libc_write", app (map fst fn___GI___libc_write.live_in) (app (map fst fn___GI___libc_write.live_out) (map fst fn___GI___libc_write.footprint)))].

(** The source sidecar projects these labels from the decoded module, not from the hint tables. *)
Lemma labels_valid :
  forallb (fun row =>
    match find (fun entry => String.eqb (fst entry) (fst row)) SaySrc.source_blocks with
    | Some (_, Some labels) => forallb (fun l => existsb (name_eqb l) labels) (snd row)
    | _ => false
    end) block_labels = true.
Proof. vm_compute. reflexivity. Qed.

End SayBlocks.
