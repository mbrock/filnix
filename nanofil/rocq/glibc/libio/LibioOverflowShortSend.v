(** Glibc handles an overflow request differently from a character when
    an unbuffered stream is empty. An EOF request has no pending data to
    send. A character occupies the short byte until the write returns.
    In both cases the stream must again have no room and nothing pending. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld OsRegistry SysCode FileInv LibioLogic LibioPutsInv
  LibioReadCode LibioDoWriteCode LibioDoWrite LibioOverflowBase LibioOverflowShortWrite SysWrappers.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.

Section send.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context `{!Defines ge "__GI___write" glibc___libc_write}.
Context `{Hdw : !Defines ge "_IO_new_do_write" glibc__IO_new_do_write}.
Context (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write).
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The overflow function updates the flags and write counters as well
    as the byte and the pointers into the short buffer. The caller keeps
    the rest of the FILE, including the bytes beside the short buffer. *)
Definition short_state fb rb fl tw off byte : iProp Σ :=
  short_ptrs fb rb (short_ptr fb) ∗ int_cell fb off_flags fl ∗ icell fb off_total_written tw ∗
  icell fb off_offset off ∗ bytes fb off_shortbuf [byte].

(** The stream already has its write pointers at the start of the short
    buffer. An empty flush leaves them alone. A character write resets
    them there even when the kernel refuses the byte. *)
Lemma wp_short_send fb freg ch f2 fd eb mode vb vreg rb fl tw off byte from e Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2^63 ->
  (0 <= ch < 256 \/ ch = 2^32 - 1) ->
  (Z.land f2 2 = 0 \/
    Z.land f2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel)) ->
  0 <= f2 < 2^32 -> In fd (ow_fds w0) -> Z.land fl io_is_appending = 0 -> Z.land fl io_unbuffered <> 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> (mode = 0 \/ mode = 2^32 - 1) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "v2") e = Some (WInt ch) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ short_state fb rb fl tw off byte -∗
  ▷ (∀ r fl' tw' off' rb' byte', ⌜ovf_ret ch r /\ (ch = 2^32 - 1 -> r = 0) /\
       (fl' = fl \/ fl' = Z.lor fl io_err_seen) /\ (rb' = rb \/ rb' = short_ptr fb)⌝ -∗
     live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ short_state fb rb' fl' tw' off' byte' -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame glibc__IO_new_file_overflow e [] None (Enter (TAtom "L18") (Some from))) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hfb Hal Hend Hrend Hch Hready Hf2 Hin Happ Hub He Hmd Hv0 Hv2 Hc0.
  iIntros "#Hvt Hl Hfixed ((Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hbase & Hbend) & Hfl & Htw & Hoff & Hbyte) HK".
  unfold file_size in Hend. unfold short_ptr, off_shortbuf. step. step. destruct Hch as [Hch | ->].
  2: { branch. adv. load_self_using wp_raw_load_pointer_self "Hl Hwb". adv.
       load_self_using wp_raw_load_pointer_self "Hl Hwp". adv. load_self_using wp_raw_load_pointer_self "Hl Hwb".
       adv. norm. rewrite Z.sub_diag. iApply wp_call_bind; [vx | exact Hdw | reflexivity |]. iNext.
       iApply wp_glibc__IO_new_do_write_zero; [reflexivity|]. iNext. iExists _. iSplit; [done|]. iNext.
       iApply wp_ret; [reflexivity | vx |]. iNext. iApply ("HK" $! 0 fl tw off rb byte with "[%] Hl Hfixed
         [Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hfl Htw Hoff Hbyte]"); last by iFrame.
       unfold ovf_ret. intuition. }
  assert (Hne : ch <> 2^32 - 1) by lia. branch_as true.
  adv. load_self_using wp_raw_load_pointer_self "Hl Hwp". adv. load_self_using wp_raw_load_pointer_self "Hl Hbend".
  adv. branch_as true. adv. load_self_using wp_raw_load_pointer_self "Hl Hwp". adv. store "Hl" "Hwp". adv.
  iEval (rewrite bytes_ibyte) in "Hbyte". iApply (wp_raw_store_byte with "Hl Hbyte"); [vx | vx | reflexivity | ar | wi_store |].
  iNext. iIntros "Hl Hbyte". rewrite (sb_byte ch Hch). iEval (rewrite -bytes_ibyte) in "Hbyte".
  iDestruct "Hfl" as "[%Hfl Hflags]". adv. load_s32 "Hl" "Hflags". adv.
  unfold io_unbuffered in Hub. assert (0 <= Z.land fl 2 < 2^32) by (apply land_lt32; lia). branch_as false. adv. branch. adv.
  load_self_using wp_raw_load_pointer_self "Hl Hwb". adv. load_self_using wp_raw_load_pointer_self "Hl Hwp". adv.
  load_self_using wp_raw_load_pointer_self "Hl Hwb". adv. norm.
  replace (fb+131+1) with (fb+132) by lia. replace (fb+132-(fb+131)) with 1 by lia.
  iDestruct "Hfixed" as "(Hf2 & Hfd & Herr & Hcol & Hmode & Hvtp)".
  iApply wp_call_bind; [vx | exact Hdw | reflexivity |]. iNext.
  assert (H514 : Z.land fl 514 <> 0).
  { intro Hz. apply Hub. change 2 with (Z.land 514 2). rewrite Z.land_assoc Hz. reflexivity. }
  iApply (wp_short_do_write Hreg Hext Hfw with "Hvt Hl [$Hrp $Hre $Hrb $Hwb $Hwp $Hwe $Hbase $Hbend]
    [$Hflags //] Hf2 Hfd Htw Hoff Hmode Hvtp Hcol Hbyte Herr"); try first [reflexivity | assumption].
  iNext. iIntros (r fl' tw' off' Hpost) "Hl Hptrs Hfl Hf2 Hfd Htw Hoff Hmode Hvtp Hcol Hbyte Herr".
  iExists _. iSplit; [done|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  step. destruct Hpost as [[-> ->] | [Hr ->]].
  - rewrite Z.eqb_refl. branch. step. step. iApply wp_ret; [reflexivity | vx |]. iNext. rewrite (ret_byte ch Hch).
    iApply ("HK" $! ch fl tw' off' (short_ptr fb) ch with "[%] Hl [$Hf2 $Hfd $Herr $Hcol $Hmode $Hvtp] [$Hptrs $Hfl $Htw $Hoff $Hbyte]").
    unfold ovf_ret. rewrite (proj2 (Z.eqb_neq _ _) Hne). intuition.
  - rewrite (proj2 (Z.eqb_neq r 1) ltac:(lia)). branch. step. iApply wp_ret; [reflexivity | vx |]. iNext.
    iApply ("HK" $! _ _ tw' off' (short_ptr fb) ch with "[%] Hl [$Hf2 $Hfd $Herr $Hcol $Hmode $Hvtp] [$Hptrs $Hfl $Htw $Hoff $Hbyte]").
    unfold ovf_ret. intuition.
Qed.
End send.
