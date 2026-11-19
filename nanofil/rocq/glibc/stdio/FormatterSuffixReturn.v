(** The formatter returns after writing the final literal suffix and
    reading its terminating NUL. This proof follows that return path
    and preserves the saved format pointer and readable source.
    It also covers the buffer writer's zero-length call, which does
    not access source or staging memory. Neither rule flushes a FILE. *)
From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_write_os Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps
  Fix WordString MemFwdLogic.
From Glibc Require Import FormatterSuffixScan.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L LibioLogic LibioCloseSteps.
Open Scope Z_scope.
(** The captured formatter has no stack objects to release on return. *)
Lemma formatter_no_stack_locals : local_objects Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer = [].
Proof. vm_compute. reflexivity. Qed.
Section suffix.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** A zero-length write checks the buffer mode and returns without
    reading the supplied source pointer or advancing the output cursor. *)
Lemma wp_printf_buffer_write_zero fr bb reg p Φ :
  call_frame Unit_stdioZ2dcommon_printf_buffer_write_os.fn___printf_buffer_write [WPtr (mkPtr bb (Obj bb)); WPtr p; WInt 0] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 36 <= r_end reg -> r_end reg <= 2^63 ->
  live bb reg -∗ int_cell bb 32 4 -∗
  ▷ (live bb reg -∗ int_cell bb 32 4 -∗ Φ RetVoid) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hb Ha He Hr. injection Hfr as <-. iIntros "Hl [%Hm Hm] HK".
  step. step. norm. check "Hl".
  load_bytes_dq "Hl Hm" decode (cbn; reflexivity) by ar.
  iNext. iIntros "Hl Hm". step. closed_ints. branch. step.
  step. closed_ints. branch. step. iApply wp_ret_void. iNext.
  iApply ("HK" with "Hl [Hm]"). iSplit; [done|iExact "Hm"].
Qed.
(** The saved pointer must address the source's terminating NUL.
    The rule follows the captured return blocks with an empty stack
    allocation list; it does not discard arbitrary local allocations. *)
Lemma wp_formatter_suffix_return e cb cr dq p s Φ :
  lookup (TAtom "v10") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  lookup (TAtom "chk3") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  0 < cb -> cb mod 8 = 0 -> cb + 8 <= r_end cr -> r_end cr <= 2^63 ->
  live cb cr -∗ pcell cb 0 (ptr_add p (Z.of_nat (length s))) -∗ word_string dq p s -∗
  ▷ (live cb cr -∗ pcell cb 0 (ptr_add p (Z.of_nat (length s))) -∗
    word_string dq p s -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer e [] None
    (Exec (TAtom "L1150") (skipn 15 (b_insts suffix_block)) (b_jump suffix_block))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hv Hchk Hb Ha He Hr. iIntros "Hl Hcell Hs HK".
  iDestruct (word_string_bytes with "Hs") as (sb sr ws) "(%Hshape & Hsl & Hsbytes & Hback)".
  pose proof Hshape as [Hcap Hsb Hsa Hst Hfit Hspace Hlen Hws Hbytes Hchars].
  assert (Hpend : ptr_addr p + Z.of_nat (length s) + 1 <= r_end sr).
  { unfold wstart in Hfit. pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)). lia. }
  iAssert (live_capq dq (ptr_cap p) sr) with "[Hsl]" as "Hsl".
  { destruct Hcap as [-> | ->]; iExact "Hsl". }
  cbn [skipn b_insts b_jump suffix_block]. check "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hcell Hsl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; lia |].
  iNext. iIntros "Hl Hcell Hsl".
  iAssert (liveq dq sb sr) with "[Hsl]" as "Hsl".
  { destruct Hcap as [Hc | Hc]; iEval (cbn [ptr_cap]; rewrite Hc) in "Hsl"; iExact "Hsl". }
  check_read_dq "Hsl" by (cbn [ptr_add ptr_addr]; ar).
  iNext. iIntros "Hsl".
  iEval (unfold MemFwdLogic.ML.bytesq; rewrite byte_ps_app ptsq_app) in "Hsbytes".
  iDestruct "Hsbytes" as "[Hsbytes Hnul]".
  load_bytes_dq "Hsl Hnul" decode (reflexivity) by (cbn [ptr_add ptr_addr]; ar).
  iNext. iIntros "Hsl Hnul".
  step. closed_ints. branch. step. branch. step. iApply wp_ret_void. iNext.
  iApply ("HK" with "Hl Hcell [Hsl Hsbytes Hnul Hback]").
  iApply ("Hback" with "Hsl [Hsbytes Hnul]").
  rewrite /MemFwdLogic.ML.bytesq byte_ps_app ptsq_app. iFrame.
Qed.
End suffix.
