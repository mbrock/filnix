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


From Glibc Require Import StrcmpSrc.
Module StrcmpBlocks.

Module fn___GI_strcmp.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L10"), [(TAtom "v8")]); ((TAtom "L11"), [(TAtom "pr.1"); (TAtom "pr.2"); (TAtom "pr.3"); (TAtom "v8")]); ((TAtom "L37"), [(TAtom "pr.3"); (TAtom "v20"); (TAtom "v25"); (TAtom "v31"); (TAtom "v8")]); ((TAtom "L38"), [(TAtom "pr.3"); (TAtom "v20"); (TAtom "v25"); (TAtom "v31"); (TAtom "v8")]); ((TAtom "L32"), [(TAtom "v31")]); ((TAtom "L12"), [(TAtom "pr.3"); (TAtom "v20"); (TAtom "v25"); (TAtom "v8")]); ((TAtom "L13"), [(TAtom "pr.1"); (TAtom "pr.2")]); ((TAtom "iw_1.start"), [(TAtom "pr.2"); (TAtom "v51"); (TAtom "v52")]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.iw_1.start"), [(TAtom "iw_1.pr.1"); (TAtom "iw_1.pr.2"); (TAtom "iw_1.pr.3")]); ((TAtom "iw_1.L18"), [(TAtom "iw_1.pr.1"); (TAtom "iw_1.pr.2")]); ((TAtom "iw_1.iw_2.start"), [(TAtom "iw_1.pr.3"); (TAtom "iw_1.pr.4")]); ((TAtom "iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L3"), [(TAtom "iw_1.iw_2.iw_1.iw_1.v32"); (TAtom "iw_1.pr.3"); (TAtom "iw_1.pr.4")]); ((TAtom "iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L4"), [(TAtom "iw_1.pr.3"); (TAtom "iw_1.pr.4")]); ((TAtom "L58"), [(TAtom "pr.2"); (TAtom "v51"); (TAtom "v52"); (TAtom "v56")]); ((TAtom "iw_2.L36"), [(TAtom "iw_2.v14"); (TAtom "iw_2.v18")]); ((TAtom "iw_2.iw_2.start"), [(TAtom "iw_2.pr.4"); (TAtom "iw_2.v48")]); ((TAtom "iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L3"), [(TAtom "iw_2.iw_2.iw_1.iw_1.v32"); (TAtom "iw_2.pr.4"); (TAtom "iw_2.v48")]); ((TAtom "iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L4"), [(TAtom "iw_2.pr.4"); (TAtom "iw_2.v48")]); ((TAtom "iw_2.iw_3.start"), [(TAtom "iw_2.pr.1"); (TAtom "iw_2.pr.4"); (TAtom "iw_2.v14"); (TAtom "iw_2.v18"); (TAtom "iw_2.v40"); (TAtom "iw_2.v41")]); ((TAtom "iw_2.L61"), [(TAtom "iw_2.pr.1"); (TAtom "iw_2.v14"); (TAtom "iw_2.v18"); (TAtom "iw_2.v40"); (TAtom "iw_2.v41")]); ((TAtom "iw_2.iw_4.start"), [(TAtom "iw_2.pr.1"); (TAtom "iw_2.pr.4"); (TAtom "iw_2.v14"); (TAtom "iw_2.v18"); (TAtom "iw_2.v41")]); ((TAtom "iw_2.L72"), [(TAtom "iw_2.pr.1"); (TAtom "iw_2.v14"); (TAtom "iw_2.v18"); (TAtom "iw_2.v41")]); ((TAtom "iw_2.L30"), []); ((TAtom "iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L3"), [(TAtom "iw_2.iw_5.iw_1.iw_1.v32"); (TAtom "iw_2.pr.3"); (TAtom "iw_2.pr.6")]); ((TAtom "iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L4"), [(TAtom "iw_2.pr.3"); (TAtom "iw_2.pr.6")]); ((TAtom "L59"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v8")]); ((TAtom "L10"), [(TAtom "pr.1"); (TAtom "pr.2"); (TAtom "pr.3"); (TAtom "v8")]); ((TAtom "L11"), [(TAtom "pr.3"); (TAtom "v20"); (TAtom "v25"); (TAtom "v31"); (TAtom "v8")]); ((TAtom "L37"), [(TAtom "pr.3"); (TAtom "v20"); (TAtom "v25"); (TAtom "v31"); (TAtom "v40"); (TAtom "v8")]); ((TAtom "L38"), [(TAtom "pr.3"); (TAtom "v20"); (TAtom "v25"); (TAtom "v31"); (TAtom "v8")]); ((TAtom "L32"), []); ((TAtom "L12"), [(TAtom "v20"); (TAtom "v25"); (TAtom "v46"); (TAtom "v8")]); ((TAtom "L13"), [(TAtom "pr.2"); (TAtom "v51"); (TAtom "v52"); (TAtom "v56")]); ((TAtom "iw_1.start"), [(TAtom "iw_1.v8"); (TAtom "iw_1.v9"); (TAtom "v51"); (TAtom "v52")]); ((TAtom "iw_1.L10"), [(TAtom "iw_1.pr.1"); (TAtom "iw_1.pr.2"); (TAtom "iw_1.pr.3"); (TAtom "iw_1.pr.4")]); ((TAtom "iw_1.iw_1.start"), [(TAtom "iw_1.pr.1"); (TAtom "iw_1.pr.2")]); ((TAtom "iw_1.L18"), [(TAtom "iw_1.v24"); (TAtom "iw_1.v25"); (TAtom "iw_1.v27"); (TAtom "iw_1.v28")]); ((TAtom "iw_1.iw_2.start"), [(TAtom "iw_1.iw_2.iw_1.iw_1.v32"); (TAtom "iw_1.pr.3"); (TAtom "iw_1.pr.4")]); ((TAtom "iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L3"), [(TAtom "iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.v22"); (TAtom "iw_1.pr.3"); (TAtom "iw_1.pr.4")]); ((TAtom "iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L4"), [(TAtom "iw_1.iw_2.v16")]); ((TAtom "L58"), [(TAtom "iw_2.v10"); (TAtom "iw_2.v11"); (TAtom "iw_2.v14"); (TAtom "iw_2.v18"); (TAtom "iw_2.v27"); (TAtom "v51"); (TAtom "v52")]); ((TAtom "iw_2.L36"), [(TAtom "iw_2.pr.1"); (TAtom "iw_2.pr.4"); (TAtom "iw_2.v14"); (TAtom "iw_2.v18"); (TAtom "iw_2.v40"); (TAtom "iw_2.v41"); (TAtom "iw_2.v48")]); ((TAtom "iw_2.iw_2.start"), [(TAtom "iw_2.iw_2.iw_1.iw_1.v32"); (TAtom "iw_2.pr.4"); (TAtom "iw_2.v48")]); ((TAtom "iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L3"), [(TAtom "iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.v22"); (TAtom "iw_2.pr.4"); (TAtom "iw_2.v48")]); ((TAtom "iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L4"), [(TAtom "iw_2.iw_2.v16")]); ((TAtom "iw_2.iw_3.start"), [(TAtom "iw_2.pr.1"); (TAtom "iw_2.pr.4"); (TAtom "iw_2.v14"); (TAtom "iw_2.v18"); (TAtom "iw_2.v40"); (TAtom "iw_2.v41")]); ((TAtom "iw_2.L61"), [(TAtom "iw_2.v14"); (TAtom "iw_2.v18"); (TAtom "iw_2.v40"); (TAtom "iw_2.v41"); (TAtom "iw_2.v67"); (TAtom "iw_2.v68")]); ((TAtom "iw_2.iw_4.start"), [(TAtom "iw_2.pr.1"); (TAtom "iw_2.v14"); (TAtom "iw_2.v18"); (TAtom "iw_2.v41")]); ((TAtom "iw_2.L72"), [(TAtom "iw_2.v79"); (TAtom "iw_2.v86")]); ((TAtom "iw_2.L30"), [(TAtom "iw_2.iw_5.iw_1.iw_1.v32"); (TAtom "iw_2.pr.3"); (TAtom "iw_2.pr.6")]); ((TAtom "iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L3"), [(TAtom "iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.v22"); (TAtom "iw_2.pr.3"); (TAtom "iw_2.pr.6")]); ((TAtom "iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L4"), [(TAtom "iw_2.iw_5.v16")]); ((TAtom "L59"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L10"), []); ((TAtom "L11"), [(2%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 1), true, false, (Some (TAtom "pr.1")), (Some (0))); (6%N, (TApp "tmp" [(TAtom "pr.2")]), (0), (Some 1), true, false, (Some (TAtom "pr.2")), (Some (0)))]); ((TAtom "L37"), []); ((TAtom "L38"), []); ((TAtom "L32"), []); ((TAtom "L12"), []); ((TAtom "L13"), [(2%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)))]); ((TAtom "iw_1.start"), [(2%N, (TApp "tmp" [(TAtom "pr.2")]), (0), (Some 8), true, false, (Some (TAtom "pr.2")), (Some (0)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.iw_1.start"), []); ((TAtom "iw_1.L18"), [(2%N, (TApp "tmp" [(TAtom "iw_1.pr.1")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.1")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "iw_1.pr.2")]), (0), (Some 8), true, false, (Some (TAtom "iw_1.pr.2")), (Some (0)))]); ((TAtom "iw_1.iw_2.start"), []); ((TAtom "iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L3"), []); ((TAtom "iw_1.iw_2.iw_1.iw_2.iw_1.iw_1.L4"), []); ((TAtom "L58"), [(3%N, (TApp "tmp" [(TAtom "v69")]), (0), (Some 8), true, false, (Some (TAtom "pr.2")), None)]); ((TAtom "iw_2.L36"), [(2%N, (TApp "tmp" [(TAtom "iw_2.pr.2")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.pr.2")), (Some (0)))]); ((TAtom "iw_2.iw_2.start"), []); ((TAtom "iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L3"), []); ((TAtom "iw_2.iw_2.iw_1.iw_2.iw_1.iw_1.L4"), []); ((TAtom "iw_2.iw_3.start"), []); ((TAtom "iw_2.L61"), [(2%N, (TApp "tmp" [(TAtom "iw_2.pr.1")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.pr.1")), (Some (0)))]); ((TAtom "iw_2.iw_4.start"), []); ((TAtom "iw_2.L72"), [(1%N, (TApp "tmp" [(TAtom "iw_2.pr.1")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.pr.1")), (Some (0)))]); ((TAtom "iw_2.L30"), []); ((TAtom "iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L3"), []); ((TAtom "iw_2.iw_5.iw_1.iw_2.iw_1.iw_1.L4"), []); ((TAtom "L59"), [])].

End fn___GI_strcmp.

(** Projection keeps temporary sets and access records out of the membership computation. *)
Definition block_labels : list (string * list name) := Eval lazy in
  [("__GI_strcmp", app (map fst fn___GI_strcmp.live_in) (app (map fst fn___GI_strcmp.live_out) (map fst fn___GI_strcmp.footprint)))].

(** The source sidecar projects these labels from the decoded module, not from the hint tables. *)
Lemma labels_valid :
  forallb (fun row =>
    match find (fun entry => String.eqb (fst entry) (fst row)) StrcmpSrc.source_blocks with
    | Some (_, Some labels) => forallb (fun l => existsb (name_eqb l) labels) (snd row)
    | _ => false
    end) block_labels = true.
Proof. vm_compute. reflexivity. Qed.

End StrcmpBlocks.
