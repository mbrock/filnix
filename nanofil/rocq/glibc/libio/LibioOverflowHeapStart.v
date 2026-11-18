(** A stream can already own a heap buffer without having started to
    write. Its first overflow on that buffer switches it to writing;
    later overflows enter the send path directly. Both paths leave the
    same heap allocation in place, even when a write fails. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld OsRegistry SysCode SysWrappers FileInv LibioLogic
  LibioReadCode LibioDoWriteCode LibioOverflowBase LibioOverflowSetp LibioOverflowSetpRest
  LibioOverflowSetpEnd HiAtexitOverflowSend HiAtexitOverflow.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.

(** A stream with an existing buffer can set the putting and error
    bits but cannot change any other flag. A stream that skips the
    switch to writing must already have its putting bit set. *)
Definition heap_put_flags fl fl' : Prop :=
  exists v, ((v = fl /\ Z.land fl 2048 <> 0) \/ v = Z.lor fl 2048) /\
    (fl' = v \/ fl' = Z.lor v io_err_seen).

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context `{Hwrite : !Defines ge "__GI___write" glibc___libc_write}
  (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
  `{Hdwf : !Defines ge "_IO_new_do_write" glibc__IO_new_do_write}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The pointer resets do not inspect the cancellation setting. The
    eventual write selects the wrapper for the stream's flags. *)
Definition heap_switch_to_putting :=
  wp_ovf_L35 (wp_ovf_L113 (wp_ovf_L113_rest (wp_ovf_L162
    (hi_ovf_L18_nocancel w0 registry ge Hreg Hext Hwrite Hfw Hdwf)))).

(** Overflow on an existing heap buffer either uses its current write
    pointers or resets them from the empty read area before sending.
    A call with EOF flushes without adding a byte. *)
Lemma wp_heap_existing fr fb freg ch f2 fd eb mode vb vreg bb breg sz k we xs fl tw off Φ :
  call_frame glibc__IO_new_file_overflow [WPtr (mkPtr fb (Obj fb)); WInt ch] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2^63 ->
  (0 <= ch < 256 \/ ch = 2^32-1) ->
  (Z.land f2 2 = 0 \/ Z.land f2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel)) ->
  0 <= f2 < 2^32 -> In fd (ow_fds w0) -> Z.land fl io_is_appending = 0 ->
  Z.land fl 8 = 0 -> Z.land fl 256 = 0 -> ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  (mode = 0 \/ mode = 2^32-1) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗
  ovf_state fb bb breg sz k we xs fl tw off -∗
  ▷ (∀ r k' we' xs' fl' tw' off', ⌜ovf_ret ch r /\ heap_put_flags fl fl'⌝ -∗
     live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ ovf_state fb bb breg sz k' we' xs' fl' tw' off' -∗
     Φ (Ret (WInt r))) -∗ WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hfb Hal Hend Hr Hch Hready Hf2 Hin Happ Hnw Hbk He Hmd.
  iIntros "#Hvt Hl Hfx Hst HK". destruct (Z.eq_dec (Z.land fl 2048) 0) as [Hnp | Hput].
  - injection Hfr as <-. unfold file_size in Hend.
    iDestruct "Hst" as "(%Hp & Hbl & Hxs & [%Hfl Hflags] & Htw & Hoff & Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hbase & Hbend)".
    destruct Hp as (Hb & Hbe & Hreg' & Hsz & Hk & Hlen & Hbytes & Hcap & Hwe).
    assert (H2048 : 0 <= Z.land fl 2048 < 2^32) by (apply land_lt32; lia).
    step. adv. load_s32_group "Hl Hflags". adv. branch_as true. adv. load_s32_group "Hl Hflags". adv.
    branch_as false. adv. branch. adv. load_pointer "Hl Hwb Hbl" by ar.
    iNext. iIntros "Hl Hwb Hbl". adv. branch_as true.
    iApply (heap_switch_to_putting with "Hvt Hl Hfx Hbl Hxs [$Hflags //] Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend");
      try first [assumption | libio_side | lk_prove].
    iNext. iIntros (r k' we' xs' fl' tw' off' [Hr' Hflags']) "Hl Hfx Hst".
    iApply ("HK" with "[%] Hl Hfx Hst"). split; [exact Hr'|]. exists (Z.lor fl 2048). auto.
  - iApply (hi_overflow_nocancel w0 registry ge Hreg Hext Hwrite Hfw Hdwf fr fb freg ch f2 fd eb mode vb vreg
      bb breg sz k we xs fl tw off with "Hvt Hl Hfx Hst"); try assumption.
    iNext. iIntros (r k' we' xs' fl' tw' off' [Hr' Hflags']) "Hl Hfx Hst".
    iApply ("HK" with "[%] Hl Hfx Hst"). split; [exact Hr'|]. exists fl. auto.
Qed.
End rules.
