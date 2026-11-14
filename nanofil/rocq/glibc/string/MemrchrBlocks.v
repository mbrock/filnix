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


From Glibc Require Import MemrchrSrc.
Module MemrchrBlocks.

Module fn___GI___memrchr.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "iw_3.L13"), [(TAtom "chk0"); (TAtom "iw_1.v7"); (TAtom "iw_2.iw_1.v13"); (TAtom "iw_3.v5"); (TAtom "v26"); (TAtom "v31"); (TAtom "v42")]); ((TAtom "iw_3.join"), [(TAtom "chk0"); (TAtom "iw_1.v7"); (TAtom "v26"); (TAtom "v31"); (TAtom "v42")]); ((TAtom "iw_4.start"), [(TAtom "v26"); (TAtom "v31"); (TAtom "v48")]); ((TAtom "iw_4.iw_1.iw_1.L3"), [(TAtom "v26"); (TAtom "v31"); (TAtom "v48")]); ((TAtom "iw_4.iw_1.iw_1.L4"), [(TAtom "v26"); (TAtom "v31")]); ((TAtom "iw_4.join"), [(TAtom "v26"); (TAtom "v31")]); ((TAtom "L61"), []); ((TAtom "L62"), []); ((TAtom "L51"), [(TAtom "chk0"); (TAtom "iw_1.v7"); (TAtom "v26"); (TAtom "v31"); (TAtom "v42")]); ((TAtom "L71"), []); ((TAtom "L73"), [(TAtom "chk0"); (TAtom "iw_1.v7"); (TAtom "v26"); (TAtom "v31"); (TAtom "v77")]); ((TAtom "L83"), [(TAtom "iw_1.v7"); (TAtom "v26"); (TAtom "v77")]); ((TAtom "iw_5.start"), [(TAtom "iw_1.v7"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v26"); (TAtom "v77")]); ((TAtom "iw_6.start"), [(TAtom "iw_5.iw_1.v6"); (TAtom "pr.1")]); ((TAtom "iw_6.iw_1.iw_3.iw_1.iw_1.L3"), [(TAtom "iw_6.iw_1.iw_1.v13"); (TAtom "pr.1")]); ((TAtom "iw_6.iw_1.iw_3.iw_1.iw_1.L4"), [(TAtom "pr.1")]); ((TAtom "iw_6.iw_1.iw_3.join"), [(TAtom "pr.1")]); ((TAtom "L93"), [(TAtom "iw_1.v7"); (TAtom "pr.1"); (TAtom "v26"); (TAtom "v77")]); ((TAtom "iw_7.start"), [(TAtom "iw_1.v7"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v26")]); ((TAtom "iw_8.start"), [(TAtom "iw_7.iw_1.v6"); (TAtom "pr.1"); (TAtom "v26")]); ((TAtom "iw_8.iw_1.iw_3.iw_1.iw_1.L3"), [(TAtom "iw_8.iw_1.iw_1.v13"); (TAtom "pr.1"); (TAtom "v26")]); ((TAtom "iw_8.iw_1.iw_3.iw_1.iw_1.L4"), [(TAtom "pr.1"); (TAtom "v26")]); ((TAtom "iw_8.iw_1.iw_3.join"), [(TAtom "pr.1"); (TAtom "v26")]); ((TAtom "L122"), [(TAtom "v121")]); ((TAtom "L110"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "iw_1.v7"); (TAtom "iw_2.iw_1.v13"); (TAtom "iw_3.v5"); (TAtom "v26"); (TAtom "v31"); (TAtom "v42")]); ((TAtom "iw_3.L13"), [(TAtom "chk0"); (TAtom "iw_1.v7"); (TAtom "iw_3.v24"); (TAtom "v26"); (TAtom "v31"); (TAtom "v42")]); ((TAtom "iw_3.join"), [(TAtom "chk0"); (TAtom "iw_1.v7"); (TAtom "v26"); (TAtom "v31"); (TAtom "v42"); (TAtom "v48")]); ((TAtom "iw_4.start"), [(TAtom "v26"); (TAtom "v31"); (TAtom "v48")]); ((TAtom "iw_4.iw_1.iw_1.L3"), [(TAtom "iw_4.iw_1.iw_1.v33"); (TAtom "v26"); (TAtom "v31")]); ((TAtom "iw_4.iw_1.iw_1.L4"), [(TAtom "iw_4.v14"); (TAtom "v26"); (TAtom "v31")]); ((TAtom "iw_4.join"), [(TAtom "v59")]); ((TAtom "L61"), []); ((TAtom "L62"), []); ((TAtom "L51"), [(TAtom "chk0"); (TAtom "iw_1.v7"); (TAtom "v26"); (TAtom "v31"); (TAtom "v77")]); ((TAtom "L71"), []); ((TAtom "L73"), [(TAtom "iw_1.v7"); (TAtom "v26"); (TAtom "v77"); (TAtom "v81"); (TAtom "v82")]); ((TAtom "L83"), [(TAtom "iw_1.v7"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v26"); (TAtom "v77")]); ((TAtom "iw_5.start"), [(TAtom "iw_1.v7"); (TAtom "iw_5.iw_1.v6"); (TAtom "pr.1"); (TAtom "v26"); (TAtom "v77")]); ((TAtom "iw_6.start"), [(TAtom "iw_6.iw_1.iw_1.v13"); (TAtom "pr.1")]); ((TAtom "iw_6.iw_1.iw_3.iw_1.iw_1.L3"), [(TAtom "iw_6.iw_1.iw_3.iw_1.iw_1.v33"); (TAtom "pr.1")]); ((TAtom "iw_6.iw_1.iw_3.iw_1.iw_1.L4"), [(TAtom "iw_6.iw_1.iw_3.v14"); (TAtom "pr.1")]); ((TAtom "iw_6.iw_1.iw_3.join"), []); ((TAtom "L93"), [(TAtom "iw_1.v7"); (TAtom "v106"); (TAtom "v107"); (TAtom "v26"); (TAtom "v77")]); ((TAtom "iw_7.start"), [(TAtom "iw_7.iw_1.v6"); (TAtom "pr.1"); (TAtom "v26")]); ((TAtom "iw_8.start"), [(TAtom "iw_8.iw_1.iw_1.v13"); (TAtom "pr.1"); (TAtom "v26")]); ((TAtom "iw_8.iw_1.iw_3.iw_1.iw_1.L3"), [(TAtom "iw_8.iw_1.iw_3.iw_1.iw_1.v33"); (TAtom "pr.1"); (TAtom "v26")]); ((TAtom "iw_8.iw_1.iw_3.iw_1.iw_1.L4"), [(TAtom "iw_8.iw_1.iw_3.v14"); (TAtom "pr.1"); (TAtom "v26")]); ((TAtom "iw_8.iw_1.iw_3.join"), [(TAtom "v121")]); ((TAtom "L122"), []); ((TAtom "L110"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L6"), []); ((TAtom "L8"), [(11%N, (TApp "tmp" [(TAtom "v31")]), (0), (Some 8), true, false, (Some (TAtom "v0")), None)]); ((TAtom "iw_3.L13"), []); ((TAtom "iw_3.join"), []); ((TAtom "iw_4.start"), []); ((TAtom "iw_4.iw_1.iw_1.L3"), []); ((TAtom "iw_4.iw_1.iw_1.L4"), []); ((TAtom "iw_4.join"), []); ((TAtom "L61"), []); ((TAtom "L62"), []); ((TAtom "L51"), []); ((TAtom "L71"), []); ((TAtom "L73"), [(2%N, (TApp "tmp" [(TAtom "v81")]), (0), (Some 8), true, false, (Some (TAtom "v0")), None)]); ((TAtom "L83"), []); ((TAtom "iw_5.start"), []); ((TAtom "iw_6.start"), []); ((TAtom "iw_6.iw_1.iw_3.iw_1.iw_1.L3"), []); ((TAtom "iw_6.iw_1.iw_3.iw_1.iw_1.L4"), []); ((TAtom "iw_6.iw_1.iw_3.join"), []); ((TAtom "L93"), [(2%N, (TApp "tmp" [(TAtom "v106")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (-8)))]); ((TAtom "iw_7.start"), []); ((TAtom "iw_8.start"), []); ((TAtom "iw_8.iw_1.iw_3.iw_1.iw_1.L3"), []); ((TAtom "iw_8.iw_1.iw_3.iw_1.iw_1.L4"), []); ((TAtom "iw_8.iw_1.iw_3.join"), []); ((TAtom "L122"), []); ((TAtom "L110"), [])].

End fn___GI___memrchr.

(** Projection keeps temporary sets and access records out of the membership computation. *)
Definition block_labels : list (string * list name) := Eval lazy in
  [("__GI___memrchr", app (map fst fn___GI___memrchr.live_in) (app (map fst fn___GI___memrchr.live_out) (map fst fn___GI___memrchr.footprint)))].

(** The source sidecar projects these labels from the decoded module, not from the hint tables. *)
Lemma labels_valid :
  forallb (fun row =>
    match find (fun entry => String.eqb (fst entry) (fst row)) MemrchrSrc.source_blocks with
    | Some (_, Some labels) => forallb (fun l => existsb (name_eqb l) labels) (snd row)
    | _ => false
    end) block_labels = true.
Proof. vm_compute. reflexivity. Qed.

End MemrchrBlocks.
