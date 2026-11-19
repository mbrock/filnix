(** A formatter scans padded words but copies only the requested string
    bytes. This rule lends those bytes to the real staging write and then
    restores the complete [word_string] window, including its NUL
    and padding. The destination may start between aligned addresses.

    The input must be nonempty and fit the remaining staging space.
    This rule does not interpret conversions or flush the stream. *)
From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_write_os Unit_string_memcpy_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps
  LibioPutsInv MemFwdLogic WordString Fix
  PrintfStagingCopy PrintfBufferWriteWindow.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld.
Open Scope Z_scope.

Section write.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None)
  (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None).
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The write advances the staging pointer and returns exact copied bytes.
    The caller recovers the same string share without copying its NUL. *)
Lemma wp_printf_buffer_write_word fr bb reg off xs cs dq p s Φ :
  call_frame Unit_stdioZ2dcommon_printf_buffer_write_os.fn___printf_buffer_write
    [WPtr (mkPtr bb (Obj bb)); WPtr p; WInt (Z.of_nat (length s))] = Some fr ->
  find_fn ge (TAtom "__GI_memcpy") = Some (Defined Unit_string_memcpy_os.fn___GI_memcpy) ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end reg -> r_end reg <= 2 ^ 63 ->
  48 <= off -> 0 < Z.of_nat (length s) -> off + Z.of_nat (length s) <= 176 ->
  length xs = 128%nat -> length cs = length xs -> Forall (fun x => 0 <= x < 256) xs ->
  live bb reg -∗ int_cell bb 32 4 -∗ pcell bb 8 (mkPtr (bb + off) (Obj bb)) -∗
  pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ bytes bb 48 xs -∗ auxes bb 48 cs -∗
  word_string dq p s -∗
  ▷ (live bb reg -∗ int_cell bb 32 4 -∗
    pcell bb 8 (mkPtr (bb + off + Z.of_nat (length s)) (Obj bb)) -∗
    pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ window_after bb 48 xs off s -∗
    word_string dq p s -∗ Φ RetVoid) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hcpy Hb Ha He Hr Ho Hn Hroom Hxs Hcs Hx.
  iIntros "Hl Hmode Hptr Hend Hx Hcs Hs HK".
  iDestruct (word_string_bytes with "Hs") as (sb sreg ws) "(%Hs & Hsl & Hbytes & Hback)".
  pose proof Hs as [Hc Hb0 Hb8 Hst Hf Hsp Hlen Hws Hby Hch].
  assert (Hend : ptr_addr p + Z.of_nat (length s) + 1 <= r_end sreg).
  { unfold wstart in Hf. pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)). lia. }
  iEval (unfold MemFwdLogic.ML.bytesq; rewrite byte_ps_app ptsq_app) in "Hbytes".
  iDestruct "Hbytes" as "[Hs Hnul]".
  iApply (wp_printf_buffer_write_window Hmove Hmove_fn Hmove_sym
    fr bb reg off xs cs dq sb sreg (ptr_addr p - sb) (ptr_cap p) s
    with "Hl Hmode Hptr Hend Hx Hcs Hsl Hs [HK Hback Hnul]");
    [|exact Hcpy|exact Hb|exact Ha|exact He|exact Hr|exact Ho|exact Hn|exact Hroom|
     exact Hb8|lia|lia|exact Hc|exact Hxs|exact Hcs|exact Hx| |].
  - replace (sb + (ptr_addr p - sb)) with (ptr_addr p) by lia. destruct p; exact Hfr.
  - eapply Forall_impl; [|exact Hch]. cbn. intros; lia.
  - iNext. iIntros "Hl Hmode Hptr Hend Hx Hsl Hs".
    iApply ("HK" with "Hl Hmode Hptr Hend Hx [Hs Hsl Hback Hnul]").
    iApply ("Hback" with "Hsl [Hs Hnul]").
    rewrite /MemFwdLogic.ML.bytesq byte_ps_app ptsq_app. iFrame.
Qed.
End write.
