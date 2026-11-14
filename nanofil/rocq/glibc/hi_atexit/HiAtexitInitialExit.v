(** Registering a callback needs an empty handler array and free locks.
    This file checks those inputs against the linked initial memory.
    They can be owned together with the streams and allocator, without
    assuming that startup has already run. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import AtexitLogic HiAtexitBase HiAtexitGe HiAtexitCloseIt HiAtexitInitial
  HiAtexitInitialAlloc HiAtexitInitialStdout HiAtexitInitialList HiAtexitExitEnv.
From stdpp Require Import list.
From Glibc Require AtexitLogic ExitRun.
Import ListNotations.
Open Scope Z_scope.
Import ExitRun AtexitLogic HLG HLG.L.

(** Each unused handler slot starts with four zero words. The last
    three words also have empty pointer capabilities. *)
Definition hi_exit_slot_ps (i : Z) : list (piece * pval) :=
  concat [cell 66928 (16 + 32 * i) 0;
    hi_pointer_ps 66928 (16 + 32 * i + 8) null;
    hi_pointer_ps 66928 (16 + 32 * i + 16) null;
    hi_pointer_ps 66928 (16 + 32 * i + 24) null].

(** Registration starts with an empty array and a free lock. The
    separate recursive exit lock is also free. *)
Definition hi_initial_exit_ps : list (piece * pval) :=
  concat [[(PLive 66864, VLive (xo_lock_reg hi_exit_objs))]; byte_ps 66864 0 [0; 0; 0; 0];
    [(PLive 73696, VLive (xo_done_reg hi_exit_objs))]; [(PByte 73696 0, VByte 0)];
    [(PLive 66896, VLive (xo_called_reg hi_exit_objs))]; cell 66896 0 0;
    [(PLive 66832, VLive (xo_funcs_reg hi_exit_objs))]; hi_pointer_ps 66832 0 (mkPtr 66928 (Obj 66928));
    [(PLive 66928, VLive (xo_init_reg hi_exit_objs))]; hi_pointer_ps 66928 0 null; cell 66928 8 0;
    concat (map hi_exit_slot_ps (seqZ 0 32));
    [(PLive 73728, VLive (mkRegion 73728 73744 GlobalData Live))];
    byte_ps 73728 0 [0; 0; 0; 0]; byte_ps 73728 4 [0; 0; 0; 0]; hi_pointer_ps 73728 8 null].

(** The loader leaves the handler array empty and the locks free.
    This check includes the stored pointers in every unused slot. *)
Lemma hi_initial_exit_agree : all_agree hi_m0 hi_initial_exit_ps.
Proof. apply checked_pieces_all_agree. vm_compute. reflexivity. Qed.

(** Registration, output and the stream-list constructor can own their
    inputs simultaneously: no object or field occurs twice. *)
Lemma hi_initial_exit_output_list_nodup :
  NoDup (hi_initial_exit_ps ++ hi_initial_list_ps ++ hi_initial_output_ps).*1.
Proof. apply hi_unique_sound. vm_compute. reflexivity. Qed.

Section resources.
Context `{!gen_heapGS piece pval Σ}.

(** An unused initial slot supplies the spare storage that atexit
    consumes when it registers a callback. *)
Lemma hi_exit_slot_own i : pts (hi_exit_slot_ps i) ⊢ spare 66928 (16 + 32 * i).
Proof.
  rewrite /hi_exit_slot_ps hi_pts_concat. cbn [big_opL].
  iIntros "(Hv & Hx & Hy & Hz & _)". iExists 0, null, null, null.
  rewrite /slot. iFrame.
Qed.

(** Grouping unused slots preserves each slot's independent ownership. *)
Lemma hi_exit_slots_own ns : pts (concat (map hi_exit_slot_ps ns)) ⊢
  [∗ list] i ∈ ns, spare 66928 (16 + 32 * i).
Proof.
  rewrite hi_pts_concat big_sepL_fmap. iIntros "Hslots".
  iApply (big_sepL_mono with "Hslots"). iIntros (i n Hin) "Hslot".
  iApply hi_exit_slot_own. iExact "Hslot".
Qed.

(** The checked static fields establish glibc's empty registration
    state and free exit lock without additional resources. *)
Lemma hi_initial_exit_own : pts hi_initial_exit_ps ⊢
  exit_funcs_inv hi_exit_objs [] 0 ∗ exit_lock_free 73728 (mkRegion 73728 73744 GlobalData Live).
Proof.
  rewrite /hi_initial_exit_ps hi_pts_concat. cbn [big_opL].
  iIntros "(Hll & Hlb & Hdl & Hdb & Hcl & Hcc & Hfl & Hfc & Hil & Hnext & Hidx & Hslots &
    Hel & He0 & He4 & He8 & _)".
  iDestruct (hi_exit_slots_own with "Hslots") as "Hspares".
  iSplitR "Hel He0 He4 He8"; last first.
  { rewrite /exit_lock_free. iFrame. }
  rewrite /exit_funcs_inv /exit_block.
  cbn [xo_lock xo_lock_reg xo_done xo_done_reg xo_called xo_called_reg xo_funcs xo_funcs_reg
    xo_init xo_init_reg hi_exit_objs List.length].
  iSplitR; [iPureIntro; split; [lia|vm_compute; intuition congruence]|].
  iFrame "Hll Hlb Hdl Hdb Hcl Hcc Hfl Hfc Hil Hnext Hidx Hspares".
  done.
Qed.

End resources.
