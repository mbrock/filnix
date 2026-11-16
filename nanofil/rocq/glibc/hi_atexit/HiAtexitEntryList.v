(** Exit must find stdin and stderr in a valid list after stdout is
    closed. This file describes their initial links and idle fields,
    then proves that cleanup can use them. These fields are owned
    separately from the stdout fields used by puts. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Values Memory Runtime Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import FileInv HiAtexitBase HiAtexitGe HiAtexitInitial HiAtexitInitialAlloc HiAtexitCleanup.
From Glibc Require FileInv LibioFlushInv.
Import ListNotations.
Open Scope Z_scope.
Import LibioFlushInv FileInv HLG HLG.L.

(** The backward pointers name the preceding link, including the list
    head for stderr. The list lock and current-stream pointer are idle. *)
Definition hi_entry_list_ps : list (piece * pval) :=
  concat [hi_pointer_ps 71760 184 (mkPtr 72480 (Obj 72480));
    hi_pointer_ps 71760 104 (mkPtr 72240 (Obj 72240));
    hi_pointer_ps 72240 184 (mkPtr 71864 (Obj 71760));
    hi_pointer_ps 72240 104 (mkPtr 72000 (Obj 72000));
    hi_pointer_ps 72000 184 (mkPtr 72344 (Obj 72240)); hi_pointer_ps 72000 104 null;
    [(PLive 72480, VLive (mkRegion 72480 72488 GlobalData Live))];
    hi_pointer_ps 72480 0 (mkPtr 71760 (Obj 71760));
    [(PLive 71648, VLive (mkRegion 71648 71664 GlobalData Live))];
    byte_ps 71648 0 (int_bytes 0); byte_ps 71648 4 (int_bytes 0); hi_pointer_ps 71648 8 null;
    [(PLive 71680, VLive (mkRegion 71680 71688 GlobalData Live))]; hi_pointer_ps 71680 0 null].

(** Each remaining stream has null read and write pointers and a free
    lock. Cleanup needs no buffer object for those null capabilities. *)
Definition hi_entry_stream_ps (fb lk fl fd : Z) : list (piece * pval) :=
  concat [[(PLive fb, VLive (mkRegion fb (fb + 224) GlobalData Live))];
    byte_ps fb 0 (int_bytes fl); byte_ps fb 116 (int_bytes 0);
    byte_ps fb 112 (int_bytes fd); byte_ps fb 192 (int_bytes 0);
    hi_pointer_ps fb 136 (mkPtr lk (Obj lk));
    [(PLive lk, VLive (mkRegion lk (lk + 16) GlobalData Live))];
    byte_ps lk 0 (int_bytes 0); byte_ps lk 4 (int_bytes 0); hi_pointer_ps lk 8 null;
    concat (map (fun off => hi_pointer_ps fb off null) [8; 16; 32; 40; 80])].

(** Stderr precedes stdin after the close callback removes stdout. *)
Definition hi_entry_rest_ps : list (piece * pval) :=
  hi_entry_stream_ps 71760 72576 4222427270 2 ++
  hi_entry_stream_ps 72000 72512 4222427272 0.

Section resources.
Context `{!gen_heapGS piece pval Σ}.

(** Cleanup can traverse the initialized list in both directions.
    It also finds the list lock free. *)
Lemma hi_entry_list_own : pts hi_entry_list_ps ⊢
  io_list_inv hge [mkPtr 71760 (Obj 71760); mkPtr 72240 (Obj 72240); mkPtr 72000 (Obj 72000)].
Proof.
  rewrite /hi_entry_list_ps hi_pts_concat. cbn [big_opL].
  iIntros "(Hep & Hec & Hop & Hoc & Hip & Hic & Hla & Hlac & Hlk & Hlk0 & Hlk4 & Hlk8 & Hrf & Hrfc & _)".
  iExists 72480, (mkRegion 72480 72488 GlobalData Live),
    71648, (mkRegion 71648 71664 GlobalData Live),
    71680, (mkRegion 71680 71688 GlobalData Live).
  iSplitR; [iPureIntro; vm_compute; intuition congruence|].
  iFrame "Hla Hlac Hrf Hrfc". iSplitL "Hep Hec Hop Hoc Hip Hic".
  - cbn [chain_links head_ptr]. iExists 71760. iSplitR; [done|]. iFrame "Hep Hec".
    iExists 72240. iSplitR; [done|]. iFrame "Hop Hoc".
    iExists 72000. iSplitR; [done|]. iFrame "Hip Hic".
  - rewrite /lock_state /int_cell. iFrame "Hlk Hlk0 Hlk4 Hlk8".
    iPureIntro. vm_compute. intuition congruence.
Qed.

(** An idle static stream supplies exactly the fields cleanup reads.
    The assumptions concern object bounds and flags, not output success. *)
Lemma hi_entry_stream_own fb lk fl fd :
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= 2 ^ 63 ->
  lk mod 8 = 0 -> lk + 16 <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> Z.land fl 32768 = 0 -> 0 <= fd < 2 ^ 31 ->
  pts (hi_entry_stream_ps fb lk fl fd) ⊢
  stream_life (mkPtr fb (Obj fb)) ∗ exit_stream false (mkPtr fb (Obj fb)).
Proof.
  intros Hfb Hmod Hbound Hlkmod Hlkbound Hfl Hbits Hfd.
  rewrite /hi_entry_stream_ps hi_pts_concat. cbn [big_opL].
  iIntros "(Hl & Hfl & Hf2 & Hfd & Hmd & Hlp & Hlk & Hlk0 & Hlk4 & Hlk8 & Hptrs & _)".
  iSplitL "Hl".
  - iExists fb, (mkRegion fb (fb + 224) GlobalData Live). iFrame "Hl".
    iPureIntro. cbn [file_size r_end]. repeat split; try assumption; try reflexivity; try lia.
  - iExists fb, fl, 0, fd, 0, lk, (mkRegion lk (lk + 16) GlobalData Live),
      CNone, (mkRegion 0 0 Heap Live), 0, 0, 0, 0.
    iSplitR; [iPureIntro; repeat split; try assumption; cbn; lia|].
    iEval (rewrite hi_pts_concat; cbn [big_opL]) in "Hptrs".
    iDestruct "Hptrs" as "(H8 & H16 & H32 & H40 & H80 & _)".
    rewrite /lock_state /int_cell.
    iFrame "Hfl Hf2 Hfd Hmd Hlp Hlk Hlk0 Hlk4 Hlk8 H8 H16 H32 H40 H80".
    iPureIntro. cbn. repeat split; try assumption; lia.
Qed.

(** The remaining two streams can be owned together in list order. *)
Lemma hi_entry_rest_own : pts hi_entry_rest_ps ⊢
  [∗ list] g ∈ [mkPtr 71760 (Obj 71760); mkPtr 72000 (Obj 72000)],
    stream_life g ∗ exit_stream false g.
Proof.
  rewrite /hi_entry_rest_ps pts_app. cbn [big_opL]. iIntros "[He Hi]".
  iSplitL "He"; [iApply (hi_entry_stream_own with "He")|iSplitL "Hi"; [iApply (hi_entry_stream_own with "Hi")|done]].
  all: vm_compute; intuition congruence.
Qed.

End resources.
