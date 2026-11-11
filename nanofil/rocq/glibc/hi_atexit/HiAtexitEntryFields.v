(** Main needs to read its greeting and stdout pointer, call through
    the stream jump table, and use the thread's cleanup fields. This
    file describes their starting values and proves that they satisfy
    the existing library rules. Read-only fields retain their original
    bounds and [[separation-logic]] ownership requirements. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Values Memory Runtime Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import FileInv WordString HiAtexitBase HiAtexitGe HiAtexitCloseIt
  HiAtexitInitial HiAtexitInitialAlloc HiAtexitCleanup HiAtexitPrepare.
Import ListNotations.
Open Scope Z_scope.
Import HFL HFL.FI HLG HLG.L HGV.ER.XL.XT.OE.OW.

(** Every jump-table slot carries the actual linked function pointer. *)
Definition hi_entry_vtables_ps : list (piece * pval) :=
  [(PLive 71072, VLive (mkRegion 71072 73424 GlobalData Live))] ++
  concat (map (fun sl => hi_pointer_ps 71072 (vt_file + sl.1) (sym_ptr hge sl.2)) file_jumps).

(** The host-prepared single-thread flag has value one. *)
Definition hi_entry_single_ps : list (piece * pval) :=
  [(PLive 73808, VLive (mkRegion 73808 73816 GlobalData Live)); (PByte 73808 0, VByte 1)].

(** The program reads its global stdout pointer and one aligned word
    containing hello and the terminating zero byte. *)
Definition hi_entry_program_ps : list (piece * pval) :=
  concat [[(PLive 70976, VLive (mkRegion 70976 70984 GlobalData Live))];
    hi_pointer_ps 70976 0 (mkPtr 69808 (Obj 69808));
    [(PLive 65568, VLive (mkRegion 65568 65576 GlobalData Live))]; cell 65568 0 478560413032].

(** The saved jump-buffer pointer remains a parameter. The cleanup
    rule owns its value without requiring a null pointer. *)
Definition hi_entry_thread_ps (jb : ptr) : list (piece * pval) :=
  concat [[(PLive 4294967296, VLive (mkRegion 4294967296 4294969856 Heap Live))];
    hi_pointer_ps 4294967296 776 null; hi_pointer_ps 4294967296 784 jb;
    byte_ps 4294967296 792 (int_bytes 0)].

Section resources.
Context `{!gen_heapGS piece pval Σ}.

(** Discarding the table's full share produces the persistent shares
    used by the existing call rules. No extra ownership is assumed. *)
Lemma hi_entry_vtables_own : pts hi_entry_vtables_ps ==∗
  vtables_ro hge 71072 (mkRegion 71072 73424 GlobalData Live).
Proof.
  iIntros "H". iMod (ptsq_persist (DfracOwn 1) _ with "H") as "#H".
  iModIntro. rewrite /vtables_ro. iSplitR; [iPureIntro; vm_compute; intuition congruence|].
  iEval (rewrite /hi_entry_vtables_ps /ptsq;
    cbn [file_jumps map concat big_opL]; rewrite !big_sepL_app) in "H".
  iDestruct "H" as "(Hl & H1 & H2 & H3 & H4 & H5 & H6 & H7 & _)".
  cbn [file_jumps big_opL]. iFrame "Hl H1 H2 H3 H4 H5 H6 H7".
Qed.

(** The initialized byte supplies the persistent single-thread flag. *)
Lemma hi_entry_single_own : pts hi_entry_single_ps ==∗
  single_ro hge 73808 (mkRegion 73808 73816 GlobalData Live).
Proof.
  iIntros "H". iMod (ptsq_persist (DfracOwn 1) _ with "H") as "#H".
  iModIntro. rewrite /single_ro. iSplitR; [iPureIntro; vm_compute; intuition congruence|].
  iEval (rewrite /hi_entry_single_ps /ptsq; cbn [big_opL]) in "H".
  iDestruct "H" as "(Hl & Hb & _)". iFrame "Hl Hb". iSplit; iEmpIntro.
Qed.

(** The string predicate includes its aligned read window, not just
    the five visible characters. *)
Lemma hi_entry_program_own : pts hi_entry_program_ps ⊢
  live 70976 (mkRegion 70976 70984 GlobalData Live) ∗
  pcell 70976 0 (mkPtr 69808 (Obj 69808)) ∗
  word_string (DfracOwn 1) (mkPtr 65568 (Ro 65568)) [104; 101; 108; 108; 111].
Proof.
  rewrite /hi_entry_program_ps hi_pts_concat. cbn [big_opL].
  iIntros "(Hso & Hsoc & Hstr & Hword & _)". iFrame "Hso Hsoc".
  iExists 65568, (mkRegion 65568 65576 GlobalData Live), [478560413032].
  iSplitR; [iPureIntro; apply str_shape_b_sound; vm_compute; reflexivity|].
  rewrite /wwin. iFrame "Hstr Hword".
Qed.

(** The freshly allocated thread has the bounds and alignment needed
    by push, pop and cleanup, for every saved jump-buffer value. *)
Lemma hi_entry_thread_own jb : pts (hi_entry_thread_ps jb) ⊢
  tcb_cleanup_inv (mkPtr 4294967296 (Obj 4294967296)).
Proof.
  rewrite /hi_entry_thread_ps hi_pts_concat. cbn [big_opL].
  iIntros "(Hl & Hcleanup & Hjmp & Hcancel & _)".
  iExists 4294967296, (mkRegion 4294967296 4294969856 Heap Live), jb.
  iSplitR; [iPureIntro; vm_compute; intuition congruence|].
  rewrite /int_cell. iFrame "Hl Hcleanup Hjmp Hcancel".
  iPureIntro. vm_compute. intuition congruence.
Qed.

End resources.
