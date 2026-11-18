(** An unbuffered stream starts with no buffer. Its first overflow
    installs the short byte and enters write mode. Later overflows can
    skip both steps, but a stream which already has its short buffer
    need not yet be in write mode. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld OsRegistry FileInv LibioLogic LibioDoWriteCode
  LibioReadCode LibioPutsInv LibioSetb LibioDoAllocShort LibioOverflowBase LibioOverflowShortWrite LibioOverflowShortPut.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.

Section start.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Halloc : !Defines ge "__GI__IO_doallocbuf" glibc__IO_doallocbuf}.
Context `{!Defines ge "__GI__IO_setb" glibc__IO_setb}.
Context (Hfree : free_rule w0 registry ge).
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Installing the buffer sets USER_BUF. Switching to write mode also
    sets CURRENTLY_PUTTING, leaving all other bits alone. *)
Definition short_setup_flags (fresh : bool) fl fl' :=
  let base := if fresh then setb_flags fl 0 else fl in fl' = base \/ fl' = Z.lor base 2048.

(** Glibc has nothing to flush when it finishes setting up the short
    buffer. It leaves the read base alone if the stream was already
    writing. Otherwise it sets the read base to the short byte. *)
Lemma wp_short_start fr fb freg ch fl mode (fresh : bool) rb Φ :
  call_frame glibc__IO_new_file_overflow [WPtr (mkPtr fb (Obj fb)); WInt ch] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2^63 ->
  Z.land fl 8 = 0 -> Z.land fl 256 = 0 -> Z.land fl 2 <> 0 ->
  (fresh = true -> Z.land fl 2048 = 0) -> (mode = 0 \/ mode = 2^32-1) ->
  let p := if fresh then null else short_ptr fb in
  let be := if fresh then null else mkPtr (fb+132) (Obj fb) in
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode mode -∗
  pcell fb off_read_ptr p -∗ pcell fb 16 p -∗ pcell fb 24 rb -∗
  pcell fb off_write_base p -∗ pcell fb off_write_ptr p -∗ pcell fb off_write_end p -∗
  pcell fb off_buf_base p -∗ pcell fb off_buf_end be -∗
  ▷ (∀ e from fl' rb', ⌜lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) /\
       lookup (TAtom "v2") e = Some (WInt ch) /\ lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) /\
       short_setup_flags fresh fl fl' /\ ((fresh = false /\ rb' = rb) \/ rb' = short_ptr fb)⌝ -∗
    live fb freg -∗ int_cell fb off_flags fl' -∗ int_cell fb off_mode mode -∗ short_ptrs fb rb' (short_ptr fb) -∗
    WP (ERun (mkFrame glibc__IO_new_file_overflow e [] None (Enter (TAtom "L18") (Some from))) : gexpr) {{ Φ }}) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hfb Hal Hend Hrend Hnw Hbk Hu Hfresh Hmd. injection Hfr as <-. cbn zeta.
  iIntros "Hl [%Hfl Hflags] Hmode Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend HK". unfold file_size in Hend.
  assert (H2048 : 0 <= Z.land fl 2048 < 2^32) by (apply land_lt32; lia).
  step. adv. load_s32 "Hl" "Hflags". adv. branch_as true. adv. load_s32 "Hl" "Hflags". adv.
  destruct (Z.eq_dec (Z.land fl 2048) 0) as [Hnp | Hp].
  - branch_as false. adv. branch. adv. destruct fresh; cbn beta iota.
    + load_null "Hl" "Hwb". adv. branch. adv. iApply wp_call_bind; [vx | exact Halloc | reflexivity |]. iNext.
      iApply (wp_glibc__IO_doallocbuf_short with "Hl [$Hflags //] Hmode Hbase Hbend"); try first [reflexivity | assumption].
      { intros. iIntros "Hl Hfl Hbase Hbend HK". iApply (wp_glibc__IO_setb Hfree with "Hl Hfl Hbase Hbend [] HK"); try assumption. iLeft. done. }
      iNext. iIntros "Hl Hflags Hmode Hbase Hbend". iExists _. iSplit; [done|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
      unfold off_shortbuf. adv. load_self_using wp_raw_load_pointer_self "Hl Hbase". adv. store "Hl" "Hrb".
      adv. load_self_using wp_raw_load_pointer_self "Hl Hbase". adv. store "Hl" "Hrp".
      adv. load_self_using wp_raw_load_pointer_self "Hl Hbase". adv. store "Hl" "Hre". step.
      replace (fb+131+1) with (fb+132) by lia.
      iApply (wp_short_put with "Hl Hflags Hmode Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend");
        try first [assumption | lk_prove | unfold setb_flags; cbn [Z.eqb]; rewrite land_lor_const; [assumption|reflexivity]].
      iNext. iIntros (e' (H0 & H2 & Hc)) "Hl Hfl Hm Hs". iApply ("HK" with "[%] Hl Hfl Hm Hs"). unfold short_setup_flags. tauto.
    + unfold short_ptr, off_shortbuf. load_self_using wp_raw_load_pointer_self "Hl Hwb". adv. branch_as true.
      iApply (wp_short_put with "Hl [$Hflags //] Hmode Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend"); try first [assumption | lk_prove].
      iNext. iIntros (e' (H0 & H2 & Hc)) "Hl Hfl Hm Hs". iApply ("HK" with "[%] Hl Hfl Hm Hs"). unfold short_setup_flags. tauto.
  - destruct fresh; [exfalso; auto|]. cbn beta iota. unfold short_ptr, off_shortbuf. branch_as true. adv.
    load_self_using wp_raw_load_pointer_self "Hl Hwb". adv. branch_as true.
    iApply ("HK" with "[%] Hl [$Hflags //] Hmode [$Hrp $Hre $Hrb $Hwb $Hwp $Hwe $Hbase $Hbend]").
    split; [lk_prove|]. split; [lk_prove|]. split; [lk_prove|]. unfold short_setup_flags. intuition.
Qed.
End start.
