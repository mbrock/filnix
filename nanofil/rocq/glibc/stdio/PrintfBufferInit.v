(** The FILE-backed printf initializer sets a zero count, mode four and the
    stream pointer before calling the buffer-selection function. A stream
    with null write pointers leaves the initializer's staging array selected.
    Nonnull write pointers select direct storage only when space remains.

    This proof composes the actual checked initializer with the proved
    switch body. It preserves the stream fields and staging bytes without
    assuming that any later output succeeds. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps PrintfBufferFileCode PrintfBufferStage PrintfBufferDirect.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld PrintfBufferDirect PrintfBufferStage SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The linked program supplies the checked switch body, not an external contract. *)
Context (Hswitch : find_fn ge (TAtom "__printf_buffer_to_file_switch") =
  Some (Defined glibc___printf_buffer_to_file_switch)).

(** Updating the printf buffer leaves the process's OS resources unchanged. *)
Local Instance init_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Initialization overwrites the owned fields and returns an empty staging buffer.
    The original FILE write pointers remain null and all character bytes are framed. *)
Lemma wp_printf_buffer_init_null fr bb breg fb freg oldbase oldptr oldend oldfp written mode Φ :
  call_frame glibc___printf_buffer_to_file_init
    [WPtr (mkPtr bb (Obj bb)); WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 56 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  live bb breg -∗ live fb freg -∗ pcell fb 40 null -∗ pcell fb 48 null -∗
  pcell bb 0 oldbase -∗ pcell bb 8 oldptr -∗ pcell bb 16 oldend -∗
  icell bb 24 written -∗ int_cell bb 32 mode -∗ pcell bb 40 oldfp -∗
  ▷ (live bb breg -∗ live fb freg -∗ pcell fb 40 null -∗ pcell fb 48 null -∗
     pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
     pcell bb 8 (mkPtr (bb + 48) (Obj bb)) -∗
     pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗
     icell bb 24 0 -∗ int_cell bb 32 4 -∗ pcell bb 40 (mkPtr fb (Obj fb)) -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfrg. injection Hfr as <-.
  iIntros "Hb Hf Hwp Hwe Hbase Hptr Hend Hw [%Hm Hm] Hfp HK".
  step. step. step. check "Hb". store "Hb" "Hbase".
  step. check "Hb". store "Hb" "Hptr".
  step. check "Hb". store "Hb" "Hend".
  step. check "Hb". store_long "Hb" "Hw".
  step. check "Hb". store_int "Hb" "Hm".
  step. check "Hb". store "Hb" "Hfp".
  iApply wp_call_bind; [vx | exact Hswitch | reflexivity |]. iNext.
  iApply (PrintfBufferStage.wp_printf_buffer_switch_null w0 registry ge _ bb breg fb freg
    with "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend"); try close_side.
  iNext. iIntros "Hb Hf Hfp Hwp Hwe Hbase Hptr Hend".
  resume. iApply wp_ret_void. iNext.
  iApply ("HK" with "Hb Hf Hwp Hwe Hbase Hptr Hend Hw [Hm] Hfp").
  iSplit; [iPureIntro; lia|iExact "Hm"].
Qed.

(** When a stream has writable space, initialization selects that space.
    Otherwise it selects its own staging array. Both paths set count zero
    and mode four without changing FILE fields. Lifetime shares also cover
    streams whose character buffer is inline. *)
Lemma wp_printf_buffer_init_owned fr bb breg fb freg db dreg bo eo dqf dqd
    oldbase oldptr oldend oldfp written mode Φ :
  let start := if bo <? eo then mkPtr (db + bo) (Obj db) else mkPtr (bb + 48) (Obj bb) in
  let stop := if bo <? eo then mkPtr (db + eo) (Obj db) else mkPtr (bb + 176) (Obj bb) in
  call_frame glibc___printf_buffer_to_file_init
    [WPtr (mkPtr bb (Obj bb)); WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 56 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < db -> 0 <= bo -> 0 <= eo -> db + bo <= r_end dreg -> db + eo <= r_end dreg ->
  r_end dreg <= 2 ^ 63 ->
  live bb breg -∗ liveq dqf fb freg -∗ liveq dqd db dreg -∗
  pcell fb 40 (mkPtr (db + bo) (Obj db)) -∗ pcell fb 48 (mkPtr (db + eo) (Obj db)) -∗
  pcell bb 0 oldbase -∗ pcell bb 8 oldptr -∗ pcell bb 16 oldend -∗
  icell bb 24 written -∗ int_cell bb 32 mode -∗ pcell bb 40 oldfp -∗
  ▷ (live bb breg -∗ liveq dqf fb freg -∗ liveq dqd db dreg -∗
     pcell fb 40 (mkPtr (db + bo) (Obj db)) -∗ pcell fb 48 (mkPtr (db + eo) (Obj db)) -∗
     pcell bb 0 start -∗ pcell bb 8 start -∗ pcell bb 16 stop -∗
     icell bb 24 0 -∗ int_cell bb 32 4 -∗ pcell bb 40 (mkPtr fb (Obj fb)) -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  cbn zeta. intros Hfr Hbb Hba Hbe Hbr Hfb Hfa Hfe Hfrg Hdb Hbo Heo Hdp Hde Hdr.
  injection Hfr as <-. iIntros "Hb Hf Hd Hwp Hwe Hbase Hptr Hend Hw [%Hm Hm] Hfp HK".
  step. step. step. check "Hb". store "Hb" "Hbase".
  step. check "Hb". store "Hb" "Hptr".
  step. check "Hb". store "Hb" "Hend".
  step. check "Hb". store_long "Hb" "Hw".
  step. check "Hb". store_int "Hb" "Hm".
  step. check "Hb". store "Hb" "Hfp".
  iApply wp_call_bind; [vx | exact Hswitch | reflexivity |]. iNext.
  destruct (Z.ltb_spec bo eo) as [Hspace|Hspace].
  - iApply (PrintfBufferDirect.wp_printf_buffer_switch_direct w0 registry ge _ bb breg fb freg db dreg bo eo
      with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend"); try close_side.
    iNext. iIntros "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend".
    resume. iApply wp_ret_void. iNext.
    iApply ("HK" with "Hb Hf Hd Hwp Hwe Hbase Hptr Hend Hw [Hm] Hfp").
    iSplit; [iPureIntro; lia|iExact "Hm"].
  - iApply (PrintfBufferStage.wp_printf_buffer_switch_staging w0 registry ge _ bb breg fb freg db dreg bo eo
      with "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend"); try close_side.
    iNext. iIntros "Hb Hf Hd Hfp Hwp Hwe Hbase Hptr Hend".
    resume. iApply wp_ret_void. iNext.
    iApply ("HK" with "Hb Hf Hd Hwp Hwe Hbase Hptr Hend Hw [Hm] Hfp").
    iSplit; [iPureIntro; lia|iExact "Hm"].
Qed.

End rules.
