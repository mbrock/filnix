(** Startup calls `c: init_cpu_features` before early init, and both read
    the tunable table. The CPU contract hands the table back whole, while
    early init's contract asks for eleven of its rows in the form that
    the allocator's setup reads them: eight size tunables, two int
    tunables and the row of id 27. This module turns the one form into
    the other, for any image.

    [CpuInitTunables](CpuInitTunables.v) already splits the table into
    the eleven later rows and a remainder. The rows that it gives are
    exactly the ids of [pm_size_ids] with type 2, those of [pm_int_ids]
    with type 0, and id 27 with type 0. So the only step left is to
    collect the eleven values into one function of the id. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Values Memory Pieces Heap Logic MemLogic.
From Glibc Require Import StartTunableGetValSpec CpuInitSpec CpuInitTunables StartPtmallocInitSpec.
Import ListNotations.
Open Scope Z_scope.

Section early.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The CPU code leaves eleven rows, each with some value. Together they
    are the allocator's tunables and the row of id 27. One function tv
    gives each of these ids its value. *)
Lemma later_rows_early tl (o : pm_objs) : pm_tl o = tl ->
  ([∗ list] r ∈ icf_later_rows, ∃ v, tunable_entry tl (fst r) (snd r) v) ⊢
  ∃ tv, pm_tunables o tv ∗ tunable_entry tl 27 0 (tv 27).
Proof using Type.
  intros <-. cbn [icf_later_rows big_opL fst snd].
  iIntros "([%v14 H14] & [%v15 H15] & [%v17 H17] & [%v18 H18] & [%v19 H19] & [%v21 H21] & [%v22 H22] &
    [%v23 H23] & [%v24 H24] & [%v25 H25] & [%v27 H27] & _)".
  iExists (fun id => if id =? 14 then v14 else if id =? 15 then v15 else if id =? 17 then v17 else
    if id =? 18 then v18 else if id =? 19 then v19 else if id =? 21 then v21 else if id =? 22 then v22 else
    if id =? 23 then v23 else if id =? 24 then v24 else if id =? 25 then v25 else v27).
  rewrite /pm_tunables /pm_size_ids /pm_int_ids. cbn [big_opL Z.eqb Pos.eqb].
  iFrame "H14 H15 H17 H18 H19 H21 H22 H23 H24 H25 H27".
Qed.

(** After the CPU call, the tunable table gives early init the rows it
    reads and keeps the rest. *)
Lemma icf_tunables_early (o : pm_objs) :
  icf_tunables (pm_tl o) ⊢
  (∃ tv, pm_tunables o tv ∗ tunable_entry (pm_tl o) 27 0 (tv 27)) ∗ icf_tunables_rest (pm_tl o).
Proof using Type.
  rewrite icf_tunables_split. iIntros "[H $]". iApply (later_rows_early with "H"). reflexivity.
Qed.

End early.
