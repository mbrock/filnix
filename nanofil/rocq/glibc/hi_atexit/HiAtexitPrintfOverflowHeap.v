(** An error report can fill stderr's buffer while the caller holds its lock.
    Flushing must leave the caller's lock and cancellation settings as they
    were, even if the write fails. This file proves that behavior for an
    already-writing heap buffer.

    The stream must already be producing bytes into a heap buffer.
    Buffers inside FILE and streams that need a new buffer or a choice
    of orientation are not covered. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode FileInv
  LibioLogic SysWrappers LibioOverflowBase LibioGenCode LibioOverflowGen
  PrintfStreamHeap PrintfBufferOverflowCall HiAtexitBase HiAtexitOverflow.
Import ListNotations.
Open Scope Z_scope.

(** The stream view uses the same interpreter logic as the backend. *)
Module PHS := PrintfStreamHeapOn InterpRuntime HLG.
(** The wrapper checks the stream's actual overflow jump-table entry. *)
Module PHG := LibioOverflowGenOn InterpRuntime HLG.
(** The caller's callee obligation uses the same concrete logic. *)
Module PHC := PrintfBufferOverflowCallOn InterpRuntime HLG.
Import PHS PHS.PS PHS.PS.PI PHS.PS.PI.CS.SW PHS.PS.PI.CS.SW.FI
  PHS.PS.PI.CS.SW.FI.ML PHS.PS.PI.CS.SW.FI.LG PHS.PS.PI.CS.SW.FI.L.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hwrite : find_fn ge (TAtom "__GI___write") = Some (Defined glibc___libc_write))
  (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
  (Hdwf : find_fn ge (TAtom "_IO_new_do_write") = Some (Defined glibc__IO_new_do_write)).

(** The composition keeps the backend's OS interpretation throughout the call. *)
Local Instance printf_heap_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** File overflow returns the IO-ready stream and errno ownership on failure
    as well as success. Neither the lock count nor flags2 is existentially
    forgotten, and errno's value is allowed to change. *)
Lemma hi_printf_heap_file_overflow_with B fr eb vb vreg self fp mode flags2 held ch Φ :
  call_frame glibc__IO_new_file_overflow [WPtr fp; WInt ch] = Some fr ->
  (0 <= ch < 256 \/ ch = 2 ^ 32 - 1) ->
  (Z.land flags2 2 = 0 \/ Z.land flags2 2 = 2 /\
    find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel)) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  vtables_ro ge vb vreg -∗ printf_heap_stream_with B w0 vb self fp mode flags2 held -∗ errno_any eb -∗
  ▷ (∀ r, ⌜ovf_ret ch r⌝ -∗ printf_heap_stream_with B w0 vb self fp mode flags2 held -∗
     errno_any eb -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hch Hready Heb. iIntros "#Hvt Hf Herr HK".
  iDestruct "Hf" as (fb freg st bb breg sz k we xs fl tw off col Hp)
    "(Hl & Hst & Hf2 & Hfd & Hcol & Hmd & Hvtp & Htail & HB)".
  destruct Hp as (-> & Hfb & Hal & Hend & Hregend & Hheap & Hmode & Hnarrow & Hflags2 & Hvtp & Hcolumn &
    Hcol & Hfd & Happ & Hnw & Hput & Hok).
  iDestruct "Hf2" as "[%Hf2r Hf2]".
  iApply (hi_overflow_nocancel w0 registry ge Hreg Hext Hwrite Hfw Hdwf
    fr fb freg ch flags2 (fs_fileno st) eb mode vb vreg bb breg sz k we xs fl tw off with
    "Hvt Hl [Hf2 Hfd Herr Hcol Hmd Hvtp] Hst"); try assumption.
  { iFrame. done. }
  iNext. iIntros (r k' we' xs' fl' tw' off' [Hr Hfl'])
    "Hl (Hf2 & Hfd & Herr & Hcol & Hmd & Hvtp) Hst".
  assert (Hok' : flags_ok (heap_file_state st bb sz k' we' fl' tw' off')).
  { change (flags_ok (heap_file_state st bb sz k we fl' tw off)).
    destruct Hfl' as [-> | ->]; [exact Hok | apply heap_file_flags_error; exact Hok]. }
  assert (Hmask : forall mask, Z.land io_err_seen mask = 0 -> Z.land fl' mask = Z.land fl mask).
  { intros mask Hmask. destruct Hfl' as [-> | ->]; [reflexivity|].
    apply land_lor_const. exact Hmask. }
  iApply ("HK" with "[%] [Hl Hst Hf2 Hfd Hcol Hmd Hvtp Htail HB] Herr"); [exact Hr|].
  iExists fb, freg, st, bb, breg, sz, k', we', xs', fl', tw', off', col.
  iFrame "Hl Hst Hf2 Hfd Hcol Hmd Hvtp Htail HB". iPureIntro. rewrite (Hmask io_is_appending eq_refl) (Hmask io_no_writes eq_refl)
    (Hmask io_currently_putting eq_refl). tauto.
Qed.

(** The bytes-only entry retains its original contract. Calls that also own
    capability slots use the stronger rule without discarding those slots. *)
Lemma hi_printf_heap_file_overflow fr eb vb vreg self fp mode flags2 held ch Φ :
  call_frame glibc__IO_new_file_overflow [WPtr fp; WInt ch] = Some fr ->
  (0 <= ch < 256 \/ ch = 2 ^ 32 - 1) ->
  (Z.land flags2 2 = 0 \/ Z.land flags2 2 = 2 /\
    find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel)) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  vtables_ro ge vb vreg -∗ printf_heap_stream w0 vb self fp mode flags2 held -∗ errno_any eb -∗
  ▷ (∀ r, ⌜ovf_ret ch r⌝ -∗ printf_heap_stream w0 vb self fp mode flags2 held -∗
     errno_any eb -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof. exact (hi_printf_heap_file_overflow_with (fun _ _ => emp%I) fr eb vb vreg self fp mode flags2 held ch Φ). Qed.

(** The outer wrapper leaves an already narrow stream's mode unchanged.
    Its checked dispatch reaches the proved heap backend, and every canonical
    result, including EOF, returns the same stream and errno ownership. *)
Lemma hi_printf_heap_overflow
    (Hovf : ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow)
    fr eb vb vreg self fp flags2 held ch Φ :
  call_frame glibc___overflow [WPtr fp; WInt ch] = Some fr ->
  0 <= ch < 256 ->
  (Z.land flags2 2 = 0 \/ Z.land flags2 2 = 2 /\
    find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel)) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  vtables_ro ge vb vreg -∗ printf_heap_stream w0 vb self fp (2 ^ 32 - 1) flags2 held -∗ errno_any eb -∗
  ▷ (∀ r, ⌜0 <= r < 2 ^ 32 /\ ovf_ret ch r⌝ -∗
     printf_heap_stream w0 vb self fp (2 ^ 32 - 1) flags2 held -∗ errno_any eb -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hch Hready Heb. iIntros "#Hvt Hf Herr HK".
  iDestruct "Hf" as (fb freg st bb breg sz k we xs fl tw off col Hp)
    "(Hl & Hst & Hf2 & Hfd & Hcol & Hmd & Hvtp & Htail)".
  pose proof Hp as (Hfp & Hfb & Hal & Hend & Hregend & _). subst fp.
  iApply (PHG.wp_glibc___overflow w0 registry ge Hovf
    fr fb freg ch (2 ^ 32 - 1) vb vreg with "Hvt Hl Hmd Hvtp"); try assumption; try lia.
  iNext. iIntros (fr' Hfr') "Hl Hmd Hvtp".
  iApply (hi_printf_heap_file_overflow fr' eb vb vreg self (mkPtr fb (Obj fb))
    (2 ^ 32 - 1) flags2 held ch with "Hvt [Hl Hst Hf2 Hfd Hcol Hmd Hvtp Htail] Herr");
    try assumption; try (left; exact Hch).
  { iExists fb, freg, st, bb, breg, sz, k, we, xs, fl, tw, off, col. iFrame "Hl Hst Hf2 Hfd Hcol Hmd Hvtp Htail". done. }
  iNext. iIntros (r Hr) "Hf Herr".
  assert (Hrr : 0 <= r < 2 ^ 32).
  { destruct Hr as [-> | ->]; [lia|]. destruct (Z.eqb_spec ch (2 ^ 32 - 1)); lia. }
  iExists r. iSplit; [iPureIntro; split; [reflexivity|exact Hrr]|].
  iApply ("HK" with "[%] Hf Herr"). tauto.
Qed.

(** Printf's staged byte can now reach the file write through proved glibc calls.
    The caller retains the jump table and errno's storage across the call.
    A failed write may still change errno and return EOF. *)
Lemma hi_printf_heap_overflow_spec
    (Hovf : ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow)
    eb vb vreg self flags2 held :
  (Z.land flags2 2 = 0 \/ Z.land flags2 2 = 2 /\
    find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel)) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  PHC.printf_overflow_call_spec w0 registry ge
    (fun fp => printf_heap_stream w0 vb self fp (2 ^ 32 - 1) flags2 held)
    (vtables_ro ge vb vreg ∗ errno_any eb).
Proof.
  intros Hready Heb fr fp ch Φ Hch Hfr. iIntros "Hf [#Hvt Herr] HK".
  iApply (hi_printf_heap_overflow Hovf fr eb vb vreg self fp flags2 held ch with "Hvt Hf Herr");
    try assumption.
  iNext. iIntros (r [Hrr Hr]) "Hf Herr".
  iApply ("HK" with "[%] Hf [$Hvt $Herr]"). exact Hrr.
Qed.

End rules.
