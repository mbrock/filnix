(** Stdout starts without a buffer, with an open output descriptor
    and a free lock. This file checks those fields against the actual
    linked initial image and constructs the stronger stdout predicate
    used by puts. It does not assume the stream-list constructor ran. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld FileInv LibioDefaultXsputnBuf LibioXsputnBase
  HiAtexitBase HiAtexitAlloc HiAtexitInitial HiAtexitInitialAlloc HiAtexitOutputState HiAtexitStdout.
From stdpp Require Import list.
Import ListNotations.
Open Scope Z_scope.
Import HP.PN.PB.PM.PC.PU.PL.
Import PI PI.CS.SW.FI PI.CS.SW.FI.ML PI.CS.SW.FI.LG PI.CS.SW.FI.L PI.CS.SW.OW.
Import HXS.XE.XL.XU.XW.XD.XC.XR.XF.XS.
Import XB XB.DX.RM.SM.TL.BY.BF.

(** Stdout's static object contains the complete FILE and jump pointer. *)
Definition hi_stdout_reg : region := mkRegion 69808 70032 GlobalData Live.

(** Stdout's separate static lock owns its two integers and owner pointer. *)
Definition hi_stdout_lock_reg : region := mkRegion 70112 70128 GlobalData Live.

(** The image contains only the fields owned by the puts predicate.
    The chain fields remain available for stream-list initialization. *)
Definition hi_stdout_ps : list (piece * pval) :=
  concat [[(PLive 69808, VLive hi_stdout_reg)];
    hi_pointer_ps 69808 216 (mkPtr (71072 + 336) (Ro 71072));
    concat (map (fun o => hi_pointer_ps 69808 o null) [8; 16; 24; 32; 56; 64; 40; 48]);
    byte_ps 69808 0 (int_bytes 4222427268); byte_ps 69808 116 (int_bytes 0);
    byte_ps 69808 112 (int_bytes 1); cell 69808 200 0; cell 69808 144 (2 ^ 64 - 1);
    byte_ps 69808 128 [0; 0]; byte_ps 69808 192 (int_bytes 0);
    concat (map (fun o => hi_pointer_ps 69808 o null) [72; 80; 96]);
    hi_pointer_ps 69808 136 (mkPtr 70112 (Obj 70112));
    [(PLive 70112, VLive hi_stdout_lock_reg)];
    byte_ps 70112 0 (int_bytes 0); byte_ps 70112 4 (int_bytes 0); hi_pointer_ps 70112 8 null].

(** Every stdout and lock piece agrees with the actual initial image. *)
Lemma hi_stdout_agree : all_agree hi_m0 hi_stdout_ps.
Proof. apply checked_pieces_all_agree. vm_compute. reflexivity. Qed.

(** The thread's initial error cell contains four zero bytes and
    four empty shadow slots, as the system-call rules require. *)
Definition hi_errno_ps : list (piece * pval) :=
  byte_ps 68176 0 [0; 0; 0; 0] ++ aux_ps 68176 0 [CNone; CNone; CNone; CNone].

(** The complete output image includes stdout, the allocator and errno. *)
Definition hi_initial_output_ps : list (piece * pval) :=
  concat [hi_stdout_ps; hi_allocator_ps; hi_errno_ps].

(** The entire output image agrees with the linked initial memory. *)
Lemma hi_initial_output_agree : all_agree hi_m0 hi_initial_output_ps.
Proof. apply checked_pieces_all_agree. vm_compute. reflexivity. Qed.

(** All three output resources can coexist in this image. This checks
    their union, not just each resource in isolation. *)
Lemma hi_initial_output_nodup : NoDup hi_initial_output_ps.*1.
Proof. apply hi_unique_sound. vm_compute. reflexivity. Qed.

Section resources.
Context `{!gen_heapGS piece pval Σ}.

(** Puts can use stdout once descriptor 1 is open. These checked fields
    establish its starting state; the caller supplies the error cell
    separately so that the proof never duplicates ownership. *)
Lemma hi_stdout_own w0 : In 1 (ow_fds w0) ->
  pts hi_stdout_ps -∗ errno_any 68176 -∗
  hi_stdout_before w0 68176 71072 (mkPtr 69808 (Obj 69808)) 0 None.
Proof.
  intros Hfd.
  rewrite /hi_stdout_ps hi_pts_concat. cbn [big_opL].
  iIntros "(Hl & Hvtp & Hbuf & Hfl & Hf2 & Hfd & Htw & Hoff & Hcol & Hmode & Hsaved & Hlp &
    Hlk & Hlk0 & Hlk4 & Hlk8 & _) Herr".
  iExists 69808, hi_stdout_reg, None, null, null, 70112, 4222427268, 0, 1, 0, (2 ^ 64 - 1).
  iSplitR; [iPureIntro; vm_compute; intuition congruence|]. iFrame "Hl Hvtp".
  iSplitL "Hbuf".
  - iEval (rewrite hi_pts_concat; cbn [big_opL]) in "Hbuf".
    iDestruct "Hbuf" as "(Hr & Hre & Hrb & Hwb & Hb & Hbe & Hwp & Hwe & _)".
    unfold wbuf, wcells, wroom, nb_base, nb_end. iFrame. done.
  - iSplitL "Hfl Hf2 Hfd Htw Hoff Hcol Hmode Herr".
    + unfold xfields_body. iFrame "Htw Hoff Hcol Herr".
      iSplitR; [iPureIntro; split_and!; try assumption; vm_compute; intuition congruence|].
      unfold int_cell. iFrame "Hfl Hf2 Hfd Hmode".
      iPureIntro. vm_compute. intuition congruence.
    + rewrite /hi_stdout_tail. iFrame "Hlp".
      iEval (rewrite hi_pts_concat; cbn [big_opL]) in "Hsaved".
      iDestruct "Hsaved" as "(H72 & H80 & H96 & _)". iFrame "H72 H80 H96".
      iExists 70112, hi_stdout_lock_reg. iSplitR; [done|].
      unfold lock_state. iFrame "Hlk Hlk8".
      iSplitR; [iPureIntro; vm_compute; intuition congruence|].
      unfold int_cell. iFrame "Hlk0 Hlk4". iPureIntro. vm_compute. intuition congruence.
Qed.

(** Puts needs both stdout and the allocator. The checked output image
    supplies their starting states together. *)
Lemma hi_initial_output_own w0 : In 1 (ow_fds w0) ->
  pts hi_initial_output_ps ⊢
  hi_malloc_state (DfracOwn 1) 66464 66624 65680 hi_mp_reg hi_tc_reg hi_dummy_reg ∗
  hi_stdout_before w0 68176 71072 (mkPtr 69808 (Obj 69808)) 0 None.
Proof.
  intros Hfd. rewrite /hi_initial_output_ps hi_pts_concat. cbn [big_opL].
  iIntros "(Hout & Halloc & Herr & _)".
  iDestruct (hi_allocator_own with "Halloc") as "Halloc". iFrame "Halloc".
  iApply (hi_stdout_own with "Hout [Herr]"); [exact Hfd|].
  iExists [0; 0; 0; 0], [CNone; CNone; CNone; CNone]. iFrame "Herr". done.
Qed.

End resources.

(** Iris can allocate the actual initial output image all at once.
    Its agreement theorem above ties this witness to the linked memory,
    rather than to an unrelated satisfiable stream fixture. *)
Lemma hi_initial_output_allocatable Σ `{!gen_heapGpreS piece pval Σ} w0 :
  In 1 (ow_fds w0) ->
  ⊢ |==> ∃ Hh : gen_heapGS piece pval Σ,
    @hi_malloc_state Σ Hh (DfracOwn 1) 66464 66624 65680 hi_mp_reg hi_tc_reg hi_dummy_reg ∗
    @hi_stdout_before Σ Hh w0 68176 71072 (mkPtr 69808 (Obj 69808)) 0 None.
Proof.
  intros Hfd.
  iMod (gen_heap_init (list_to_map hi_initial_output_ps : gmap piece pval)) as (Hh) "(_ & Hpts & _)".
  iModIntro. iExists Hh. iApply hi_initial_output_own; [exact Hfd|].
  rewrite /pts -(big_sepM_list_to_map (fun l v => pointsto l (DfracOwn 1) v));
    [iExact "Hpts"|exact hi_initial_output_nodup].
Qed.
