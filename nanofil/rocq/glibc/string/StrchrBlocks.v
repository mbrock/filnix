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


From Glibc Require Import StrchrSrc.
Module StrchrBlocks.

Module fn___GI_strchr.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L9"), []); ((TAtom "L10"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v7")]); ((TAtom "L9"), []); ((TAtom "L10"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v7")]), (0), (Some 1), true, false, (Some (TAtom "v7")), (Some (0)))]); ((TAtom "L9"), []); ((TAtom "L10"), [])].

End fn___GI_strchr.

Module fn___GI___strchrnul.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "iw_4.start"), [(TAtom "iw_3.v12"); (TAtom "v0")]); ((TAtom "iw_4.iw_1.iw_1.L3"), [(TAtom "iw_3.v12"); (TAtom "v0")]); ((TAtom "iw_4.iw_1.iw_1.L4"), [(TAtom "v0")]); ((TAtom "L37"), [(TAtom "iw_1.v7")]); ((TAtom "iw_6.start"), [(TAtom "iw_5.iw_1.v10"); (TAtom "v41"); (TAtom "v47")]); ((TAtom "iw_6.iw_3.iw_1.iw_1.L3"), [(TAtom "iw_5.iw_1.v10"); (TAtom "v41")]); ((TAtom "iw_6.iw_3.iw_1.iw_1.L4"), [(TAtom "v41")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "iw_1.v7"); (TAtom "iw_3.v12"); (TAtom "v0"); (TAtom "v12")]); ((TAtom "iw_4.start"), [(TAtom "iw_3.v12"); (TAtom "v0")]); ((TAtom "iw_4.iw_1.iw_1.L3"), [(TAtom "iw_4.iw_1.iw_1.v22"); (TAtom "v0")]); ((TAtom "iw_4.iw_1.iw_1.L4"), []); ((TAtom "L37"), [(TAtom "iw_1.v7"); (TAtom "iw_5.iw_1.v10"); (TAtom "v41"); (TAtom "v47")]); ((TAtom "iw_6.start"), [(TAtom "iw_5.iw_1.v10"); (TAtom "v41")]); ((TAtom "iw_6.iw_3.iw_1.iw_1.L3"), [(TAtom "iw_6.iw_3.iw_1.iw_1.v22"); (TAtom "v41")]); ((TAtom "iw_6.iw_3.iw_1.iw_1.L4"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(8%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), true, false, (Some (TAtom "v0")), None)]); ((TAtom "iw_4.start"), []); ((TAtom "iw_4.iw_1.iw_1.L3"), []); ((TAtom "iw_4.iw_1.iw_1.L4"), []); ((TAtom "L37"), [(2%N, (TApp "tmp" [(TAtom "v41")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (8)))]); ((TAtom "iw_6.start"), []); ((TAtom "iw_6.iw_3.iw_1.iw_1.L3"), []); ((TAtom "iw_6.iw_3.iw_1.iw_1.L4"), [])].

End fn___GI___strchrnul.

Module fn___GI_strrchr.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].

End fn___GI_strrchr.

Module fn___memchr.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "iw_2.L5"), [(TAtom "chk0"); (TAtom "iw_1.v7"); (TAtom "v0"); (TAtom "v16"); (TAtom "v19"); (TAtom "v25"); (TAtom "v34")]); ((TAtom "iw_2.L6"), [(TAtom "chk0"); (TAtom "iw_1.v7"); (TAtom "v0"); (TAtom "v16"); (TAtom "v19"); (TAtom "v25")]); ((TAtom "iw_6.start"), [(TAtom "iw_5.v12"); (TAtom "v0"); (TAtom "v40")]); ((TAtom "iw_6.iw_1.iw_1.L3"), [(TAtom "iw_5.v12"); (TAtom "v0"); (TAtom "v40")]); ((TAtom "iw_6.iw_1.iw_1.L4"), [(TAtom "v0"); (TAtom "v40")]); ((TAtom "L62"), []); ((TAtom "L63"), []); ((TAtom "L52"), [(TAtom "chk0"); (TAtom "iw_1.v7"); (TAtom "v19"); (TAtom "v40"); (TAtom "v43")]); ((TAtom "L72"), []); ((TAtom "L74"), [(TAtom "chk0"); (TAtom "iw_1.v7"); (TAtom "v19"); (TAtom "v40"); (TAtom "v78")]); ((TAtom "L84"), [(TAtom "iw_1.v7"); (TAtom "v40"); (TAtom "v78")]); ((TAtom "iw_7.start"), [(TAtom "iw_1.v7"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v40"); (TAtom "v78")]); ((TAtom "iw_8.start"), [(TAtom "iw_7.iw_1.iw_1.v13"); (TAtom "pr.1")]); ((TAtom "iw_8.iw_3.iw_1.iw_1.L3"), [(TAtom "iw_7.iw_1.iw_1.v13"); (TAtom "pr.1")]); ((TAtom "iw_8.iw_3.iw_1.iw_1.L4"), [(TAtom "pr.1")]); ((TAtom "L94"), [(TAtom "iw_1.v7"); (TAtom "pr.1"); (TAtom "v40"); (TAtom "v78")]); ((TAtom "iw_9.start"), [(TAtom "iw_1.v7"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v40")]); ((TAtom "iw_10.start"), [(TAtom "iw_9.iw_1.iw_1.v13"); (TAtom "pr.1"); (TAtom "v40")]); ((TAtom "iw_10.iw_3.iw_1.iw_1.L3"), [(TAtom "iw_9.iw_1.iw_1.v13"); (TAtom "pr.1"); (TAtom "v40")]); ((TAtom "iw_10.iw_3.iw_1.iw_1.L4"), [(TAtom "pr.1"); (TAtom "v40")]); ((TAtom "L123"), [(TAtom "v122")]); ((TAtom "L111"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "iw_1.v7"); (TAtom "v0"); (TAtom "v16"); (TAtom "v19"); (TAtom "v25"); (TAtom "v34")]); ((TAtom "iw_2.L5"), [(TAtom "chk0"); (TAtom "iw_1.v7"); (TAtom "iw_2.v13"); (TAtom "v0"); (TAtom "v16"); (TAtom "v19"); (TAtom "v25")]); ((TAtom "iw_2.L6"), [(TAtom "chk0"); (TAtom "iw_1.v7"); (TAtom "iw_5.v12"); (TAtom "v0"); (TAtom "v19"); (TAtom "v40"); (TAtom "v43")]); ((TAtom "iw_6.start"), [(TAtom "iw_5.v12"); (TAtom "v0"); (TAtom "v40")]); ((TAtom "iw_6.iw_1.iw_1.L3"), [(TAtom "iw_6.iw_1.iw_1.v22"); (TAtom "v0"); (TAtom "v40")]); ((TAtom "iw_6.iw_1.iw_1.L4"), [(TAtom "v60")]); ((TAtom "L62"), []); ((TAtom "L63"), []); ((TAtom "L52"), [(TAtom "chk0"); (TAtom "iw_1.v7"); (TAtom "v19"); (TAtom "v40"); (TAtom "v78")]); ((TAtom "L72"), []); ((TAtom "L74"), [(TAtom "iw_1.v7"); (TAtom "v40"); (TAtom "v78"); (TAtom "v82"); (TAtom "v83")]); ((TAtom "L84"), [(TAtom "iw_1.v7"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v40"); (TAtom "v78")]); ((TAtom "iw_7.start"), [(TAtom "iw_1.v7"); (TAtom "iw_7.iw_1.iw_1.v13"); (TAtom "pr.1"); (TAtom "v40"); (TAtom "v78")]); ((TAtom "iw_8.start"), [(TAtom "iw_7.iw_1.iw_1.v13"); (TAtom "pr.1")]); ((TAtom "iw_8.iw_3.iw_1.iw_1.L3"), [(TAtom "iw_8.iw_3.iw_1.iw_1.v22"); (TAtom "pr.1")]); ((TAtom "iw_8.iw_3.iw_1.iw_1.L4"), []); ((TAtom "L94"), [(TAtom "iw_1.v7"); (TAtom "v107"); (TAtom "v108"); (TAtom "v40"); (TAtom "v78")]); ((TAtom "iw_9.start"), [(TAtom "iw_9.iw_1.iw_1.v13"); (TAtom "pr.1"); (TAtom "v40")]); ((TAtom "iw_10.start"), [(TAtom "iw_9.iw_1.iw_1.v13"); (TAtom "pr.1"); (TAtom "v40")]); ((TAtom "iw_10.iw_3.iw_1.iw_1.L3"), [(TAtom "iw_10.iw_3.iw_1.iw_1.v22"); (TAtom "pr.1"); (TAtom "v40")]); ((TAtom "iw_10.iw_3.iw_1.iw_1.L4"), [(TAtom "v122")]); ((TAtom "L123"), []); ((TAtom "L111"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L6"), []); ((TAtom "L8"), [(5%N, (TApp "tmp" [(TAtom "v19")]), (0), (Some 8), true, false, (Some (TAtom "v0")), None)]); ((TAtom "iw_2.L5"), []); ((TAtom "iw_2.L6"), []); ((TAtom "iw_6.start"), []); ((TAtom "iw_6.iw_1.iw_1.L3"), []); ((TAtom "iw_6.iw_1.iw_1.L4"), []); ((TAtom "L62"), []); ((TAtom "L63"), []); ((TAtom "L52"), []); ((TAtom "L72"), []); ((TAtom "L74"), [(2%N, (TApp "tmp" [(TAtom "v82")]), (0), (Some 8), true, false, (Some (TAtom "v0")), None)]); ((TAtom "L84"), []); ((TAtom "iw_7.start"), []); ((TAtom "iw_8.start"), []); ((TAtom "iw_8.iw_3.iw_1.iw_1.L3"), []); ((TAtom "iw_8.iw_3.iw_1.iw_1.L4"), []); ((TAtom "L94"), [(2%N, (TApp "tmp" [(TAtom "v107")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (8)))]); ((TAtom "iw_9.start"), []); ((TAtom "iw_10.start"), []); ((TAtom "iw_10.iw_3.iw_1.iw_1.L3"), []); ((TAtom "iw_10.iw_3.iw_1.iw_1.L4"), []); ((TAtom "L123"), []); ((TAtom "L111"), [])].

End fn___memchr.

Module fn___GI___strnlen.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L8"), [(TAtom "v0"); (TAtom "v12")]); ((TAtom "L10"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2")]); ((TAtom "L8"), [(TAtom "v18")]); ((TAtom "L10"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L8"), []); ((TAtom "L10"), [])].

End fn___GI___strnlen.

(** Projection keeps temporary sets and access records out of the membership computation. *)
Definition block_labels : list (string * list name) := Eval lazy in
  [("__GI_strchr", app (map fst fn___GI_strchr.live_in) (app (map fst fn___GI_strchr.live_out) (map fst fn___GI_strchr.footprint))); ("__GI___strchrnul", app (map fst fn___GI___strchrnul.live_in) (app (map fst fn___GI___strchrnul.live_out) (map fst fn___GI___strchrnul.footprint))); ("__GI_strrchr", app (map fst fn___GI_strrchr.live_in) (app (map fst fn___GI_strrchr.live_out) (map fst fn___GI_strrchr.footprint))); ("__memchr", app (map fst fn___memchr.live_in) (app (map fst fn___memchr.live_out) (map fst fn___memchr.footprint))); ("__GI___strnlen", app (map fst fn___GI___strnlen.live_in) (app (map fst fn___GI___strnlen.live_out) (map fst fn___GI___strnlen.footprint)))].

(** The source sidecar projects these labels from the decoded module, not from the hint tables. *)
Lemma labels_valid :
  forallb (fun row =>
    match find (fun entry => String.eqb (fst entry) (fst row)) StrchrSrc.source_blocks with
    | Some (_, Some labels) => forallb (fun l => existsb (name_eqb l) labels) (snd row)
    | _ => false
    end) block_labels = true.
Proof. vm_compute. reflexivity. Qed.

End StrchrBlocks.
