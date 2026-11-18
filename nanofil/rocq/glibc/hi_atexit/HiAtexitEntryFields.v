(** Main needs to read its greeting and stdout pointer and call through
    the stream jump table. This file describes their starting values
    and proves that they satisfy the existing library rules. Read-only fields retain their original
    bounds and [[separation-logic]] ownership requirements. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Values Memory Runtime Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import FileInv WordString HiAtexitBase HiAtexitGe HiAtexitCloseIt
  HiAtexitInitial HiAtexitInitialAlloc HiAtexitCleanup.
From Glibc Require FileInv LibioFlushInv OsWorld.
Import ListNotations.
Open Scope Z_scope.
Import LibioFlushInv FileInv HLG HLG.L OsWorld.

(** Every jump-table slot carries the actual linked function pointer. *)
Definition hi_entry_vtables_ps : list (piece * pval) :=
  [(PLive 73504, VLive (mkRegion 73504 75856 GlobalData Live))] ++
  concat (map (fun sl => hi_pointer_ps 73504 (vt_file + sl.1) (sym_ptr hge sl.2)) file_jumps).

(** The single-thread flag has value one. *)
Definition hi_entry_single_ps : list (piece * pval) :=
  [(PLive 76240, VLive (mkRegion 76240 76248 GlobalData Live)); (PByte 76240 0, VByte 1)].

(** The program reads its global stdout pointer and one aligned word
    containing hello and the terminating zero byte. *)
Definition hi_entry_program_ps : list (piece * pval) :=
  concat [[(PLive 73408, VLive (mkRegion 73408 73416 GlobalData Live))];
    hi_pointer_ps 73408 0 (mkPtr 72240 (Obj 72240));
    [(PLive 65568, VLive (mkRegion 65568 65576 GlobalData Live))]; cell 65568 0 478560413032].

Section resources.
Context `{!gen_heapGS piece pval Σ}.

(** Discarding the table's full share produces the persistent shares
    used by the existing call rules. No extra ownership is assumed. *)
Lemma hi_entry_vtables_own : pts hi_entry_vtables_ps ==∗
  vtables_ro hge 73504 (mkRegion 73504 75856 GlobalData Live).
Proof using Type.
  iIntros "H". iMod (ptsq_persist (DfracOwn 1) _ with "H") as "#H".
  iModIntro. rewrite /vtables_ro. iSplitR; [iPureIntro; vm_compute; intuition congruence|].
  iEval (rewrite /hi_entry_vtables_ps /ptsq;
    cbn [file_jumps map concat big_opL]; rewrite !big_sepL_app) in "H".
  iDestruct "H" as "(Hl & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _)".
  cbn [file_jumps big_opL]. iFrame "Hl H1 H2 H3 H4 H5 H6 H7 H8".
Qed.

(** The initialized byte supplies the persistent single-thread flag. *)
Lemma hi_entry_single_own : pts hi_entry_single_ps ==∗
  single_ro hge 76240 (mkRegion 76240 76248 GlobalData Live).
Proof using Type.
  iIntros "H". iMod (ptsq_persist (DfracOwn 1) _ with "H") as "#H".
  iModIntro. rewrite /single_ro /FileInv.ML.bytesq. iSplitR; [iPureIntro; vm_compute; intuition congruence|].
  iEval (rewrite /hi_entry_single_ps /ptsq; cbn [big_opL]) in "H".
  iDestruct "H" as "(Hl & Hb & _)". iFrame "Hl Hb". iSplit; iEmpIntro.
Qed.

(** The string predicate includes its aligned read window, not just
    the five visible characters. *)
Lemma hi_entry_program_own : pts hi_entry_program_ps ⊢
  live 73408 (mkRegion 73408 73416 GlobalData Live) ∗
  pcell 73408 0 (mkPtr 72240 (Obj 72240)) ∗
  word_string (DfracOwn 1) (mkPtr 65568 (Ro 65568)) [104; 101; 108; 108; 111].
Proof using Type.
  rewrite /hi_entry_program_ps hi_pts_concat. cbn [big_opL].
  iIntros "(Hso & Hsoc & Hstr & Hword & _)". iFrame "Hso Hsoc".
  iExists 65568, (mkRegion 65568 65576 GlobalData Live), [478560413032].
  iSplitR; [iPureIntro; apply str_shape_b_sound; vm_compute; reflexivity|].
  rewrite /wwin. iFrame "Hstr Hword".
Qed.

End resources.
