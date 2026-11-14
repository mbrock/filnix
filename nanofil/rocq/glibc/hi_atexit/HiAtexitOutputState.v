(** String output and overflow describe the same buffer in different
    ways. String output names its write pointers; overflow names the
    number of pending bytes. These lemmas convert the owned pieces
    without losing the buffer's heap origin or capability slots. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioSetb LibioOverflowBase LibioOverflowAllocSetg LibioDefaultXsputnBuf LibioXsputnBase HiAtexitBase.
From Glibc Require Export HiAtexitXsputnRules HiAtexitOverflowRules.
From Glibc Require FileInv LibioDefaultXsputnBuf LibioLogic LibioOverflowBase LibioXsputnBase LibioXsputnSetp OsWorld SysWrappers.
Import ListNotations.
Open Scope Z_scope.

(** The string-output state reuses the instance already checked for
    its entry rule, rather than copying the same proof modules again. *)
Import LibioXsputnSetp.
(** The overflow state also reuses its existing checked instance. *)
Import LibioOverflowBase SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Import LibioXsputnBase LibioDefaultXsputnBuf.

(** Buffer allocation clears the user-buffer bit and sets the writing
    bit. Those changes preserve stdout's fixed flags. *)
Lemma hi_xs_flags_alloc fl fl' bb sz :
  xs_flags None fl -> 0 <= fl < 2 ^ 32 -> ovf_alloc_flags fl fl' ->
  xs_flags (Some (bb, sz)) fl'.
Proof.
  intros Hflags Hfl (fl1 & Hline & Hout).
  assert (Hfixed : Z.land fl (Z.lnot 2592) = 4222427268) by exact (proj1 Hflags).
  assert (Hbase : forall f, Z.land f (Z.lnot 2592) = 4222427268 ->
    xs_flags (Some (bb, sz)) (Z.lor (setb_flags f 1) 2048)).
  { intros f Hf. unfold xs_flags, setb_flags. cbn [Z.eqb].
    rewrite !Z.land_lor_distr_l.
    change (Z.land 2048 (Z.lnot 2592)) with 0.
    rewrite Z.lor_0_r.
    split.
    - rewrite (Z.land_comm f 4294967294) -Z.land_assoc Hf.
      reflexivity.
    - intros Hzero.
      apply (f_equal (fun z => Z.testbit z 11)) in Hzero.
      rewrite Z.lor_spec in Hzero.
      change (Z.testbit (Z.land (Z.land f 4294967294) 2048) 11 || true = false)%bool in Hzero.
      rewrite Bool.orb_true_r in Hzero. discriminate. }
  assert (Hf1 : Z.land fl1 (Z.lnot 2592) = 4222427268).
  { destruct Hline as [-> | ->]; [exact Hfixed|].
    rewrite Z.land_lor_distr_l Hfixed. reflexivity. }
  destruct Hout as [-> | ->]; [apply Hbase; exact Hf1|].
  apply xs_flags_error, Hbase. exact Hf1.
Qed.

Section buffers.
Context `{!gen_heapGS piece pval Σ}.

(** A buffer's write pointer determines the pending byte count. The
    remaining capability slots are framed outside overflow's state. *)
Lemma hi_wbuf_to_ovf fb bb sz wp we fl tw off :
  wbuf fb (Some (bb, sz)) wp we -∗ int_cell fb off_flags fl -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗
  ∃ breg xs cs k, ⌜bb mod 8 = 0 /\ r_kind breg = Heap /\ length cs = Z.to_nat sz⌝ ∗
    ovf_state fb bb breg sz k we xs fl tw off ∗ auxes bb 0 cs.
Proof.
  iIntros "((Hrp & Hre & Hrb & Hwb & Hbase & Hbend) & Hwp & Hwe & Hroom) Hfl Htw Hoff".
  iDestruct "Hroom" as (breg xs cs Hp) "(Hbl & Hxs & Hcs)".
  destruct Hp as (Hb & Hal & Hsz & Hend & Hreg & Hlx & Hlc & Hx & [Hpc Hpa] & [Hec Hea] & Hheap).
  destruct wp as [wa wc]. cbn in Hpc, Hpa. subst wc.
  replace wa with (bb + (wa - bb)) by lia.
  iExists breg, xs, cs, (wa - bb). iFrame "Hcs".
  iSplit; [iPureIntro; tauto|]. unfold ovf_state. iFrame.
  iPureIntro. split_and!; first [assumption | lia].
Qed.

(** Overflow returns every byte of the same heap buffer. Its new
    pending count reconstructs string output's write pointer. *)
Lemma hi_ovf_to_wbuf fb bb breg sz k we xs fl tw off cs :
  bb mod 8 = 0 -> r_kind breg = Heap -> length cs = Z.to_nat sz ->
  ovf_state fb bb breg sz k we xs fl tw off -∗ auxes bb 0 cs -∗
  wbuf fb (Some (bb, sz)) (mkPtr (bb + k) (Obj bb)) we ∗
  int_cell fb off_flags fl ∗ icell fb off_total_written tw ∗ icell fb off_offset off.
Proof.
  intros Hal Hheap Hlc.
  iIntros "(%Hp & Hbl & Hxs & Hfl & Htw & Hoff & Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hbase & Hbend) Hcs".
  destruct Hp as (Hb & Hend & Hreg & Hsz & Hk & Hlx & Hx & Hec & Hea).
  iFrame "Hfl Htw Hoff". unfold wbuf, wcells. cbn [nb_base nb_end].
  iFrame "Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend".
  iExists breg, xs, cs. iFrame. iPureIntro. unfold room_ok, in_buf.
  cbn [ptr_cap ptr_addr]. split_and!; first [reflexivity | assumption | lia].
Qed.

End buffers.
