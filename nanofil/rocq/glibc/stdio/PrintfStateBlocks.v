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


From Glibc Require Import PrintfStateSrc.
Module PrintfStateBlocks.

Module fn___GI___pthread_setcancelstate.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L10"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L5"), []); ((TAtom "L7"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2")]); ((TAtom "L26"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2")]); ((TAtom "L27"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2")]); ((TAtom "L28"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2")]); ((TAtom "L39"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "L48"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "L56"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "L70"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38"); (TAtom "v68"); (TAtom "v69")]); ((TAtom "L71"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38"); (TAtom "v69")]); ((TAtom "iw_1.start"), [(TAtom "v38")]); ((TAtom "L72"), []); ((TAtom "iw_2.L12"), [(TAtom "chk3"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L13"), [(TAtom "chk3"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v23"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L37"), [(TAtom "chk3"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v3"); (TAtom "iw_2.v35")]); ((TAtom "iw_2.L38"), [(TAtom "chk3"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v3"); (TAtom "iw_2.v35")]); ((TAtom "iw_2.L14"), [(TAtom "chk3"); (TAtom "iw_2.v3")]); ((TAtom "L24"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L10"), [(TAtom "v0"); (TAtom "v13"); (TAtom "v2")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v2")]); ((TAtom "L5"), []); ((TAtom "L7"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v21")]); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2")]); ((TAtom "L26"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v33")]); ((TAtom "L27"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v37")]); ((TAtom "L28"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "L39"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "L48"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "L56"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38"); (TAtom "v68"); (TAtom "v69")]); ((TAtom "L70"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38"); (TAtom "v68"); (TAtom "v69")]); ((TAtom "L71"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v17"); (TAtom "v2"); (TAtom "v38")]); ((TAtom "iw_1.start"), []); ((TAtom "L72"), [(TAtom "chk3"); (TAtom "iw_2.v10"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L12"), [(TAtom "chk3"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v23"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L13"), [(TAtom "chk3"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v3"); (TAtom "iw_2.v35")]); ((TAtom "iw_2.L37"), [(TAtom "chk3"); (TAtom "iw_2.pr.1"); (TAtom "iw_2.v3"); (TAtom "iw_2.v35")]); ((TAtom "iw_2.L38"), [(TAtom "chk3"); (TAtom "iw_2.pr.2"); (TAtom "iw_2.v3")]); ((TAtom "iw_2.L14"), []); ((TAtom "L24"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L10"), []); ((TAtom "L11"), []); ((TAtom "L5"), []); ((TAtom "L7"), [(3%N, (TApp "tmp" [(TAtom "v20")]), (0), (Some 4), true, false, (Some (TAtom "v17")), (Some (792)))]); ((TAtom "L22"), []); ((TAtom "L26"), []); ((TAtom "L27"), []); ((TAtom "L28"), []); ((TAtom "L39"), []); ((TAtom "L48"), []); ((TAtom "L49"), [(1%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 4), false, true, (Some (TAtom "v2")), (Some (0)))]); ((TAtom "L41"), []); ((TAtom "L56"), [(2%N, (TApp "tmp" [(TAtom "v65")]), (0), (Some 4), true, true, (Some (TAtom "v17")), (Some (792)))]); ((TAtom "L70"), []); ((TAtom "L71"), []); ((TAtom "iw_1.start"), []); ((TAtom "L72"), [(4%N, (TApp "tmp" [(TAtom "iw_2.v5")]), (0), (Some 8), false, true, (Some (TAtom "iw_2.v3")), (Some (1608))); (7%N, (TApp "tmp" [(TAtom "iw_2.v9")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v3")), (Some (792)))]); ((TAtom "iw_2.L12"), []); ((TAtom "iw_2.L13"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v32")]), (0), (Some 4), true, true, (Some (TAtom "iw_2.v3")), (Some (792)))]); ((TAtom "iw_2.L37"), []); ((TAtom "iw_2.L38"), []); ((TAtom "iw_2.L14"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v41")]), (0), (Some 8), true, false, (Some (TAtom "iw_2.v3")), (Some (784)))]); ((TAtom "L24"), [])].

End fn___GI___pthread_setcancelstate.

Module fn___printf_buffer_done.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L20"), []); ((TAtom "L21"), [(TAtom "v27")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [(TAtom "v27")]); ((TAtom "L20"), []); ((TAtom "L21"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v3")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (32)))]); ((TAtom "L2"), []); ((TAtom "L4"), [(2%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (0))); (9%N, (TApp "tmp" [(TAtom "iw_1.v3")]), (-8), (Some 8), true, false, (Some (TAtom "v0")), (Some (24)))]); ((TAtom "L20"), [(2%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 4), false, true, (Some (TAtom "v37")), (Some (0)))]); ((TAtom "L21"), [])].

End fn___printf_buffer_done.

(** Projection keeps temporary sets and access records out of the membership computation. *)
Definition block_labels : list (string * list name) := Eval lazy in
  [("__GI___pthread_setcancelstate", app (map fst fn___GI___pthread_setcancelstate.live_in) (app (map fst fn___GI___pthread_setcancelstate.live_out) (map fst fn___GI___pthread_setcancelstate.footprint))); ("__printf_buffer_done", app (map fst fn___printf_buffer_done.live_in) (app (map fst fn___printf_buffer_done.live_out) (map fst fn___printf_buffer_done.footprint)))].

(** The source sidecar projects these labels from the decoded module, not from the hint tables. *)
Lemma labels_valid :
  forallb (fun row =>
    match find (fun entry => String.eqb (fst entry) (fst row)) PrintfStateSrc.source_blocks with
    | Some (_, Some labels) => forallb (fun l => existsb (name_eqb l) labels) (snd row)
    | _ => false
    end) block_labels = true.
Proof. vm_compute. reflexivity. Qed.

End PrintfStateBlocks.
