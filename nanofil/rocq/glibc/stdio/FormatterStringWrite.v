(** Glibc writes a nonempty string directly when its field width is zero.
    This proof follows that handler branch through the real buffer write
    and memcpy call, using the existing memory-copy contract.

    The string must fit in the remaining staging space. Its destination
    may be unaligned, and the write may fill the buffer exactly. The rule
    preserves one lifetime for the header and staging allocation; it
    does not cover empty strings, flushing, or the next format suffix. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps
  FormatterCode Fix WordString PrintfBufferIoCode MemFwdCode MemFwdLogic
  PrintfStagingCopy PrintfBufferWriteWindow FormatterLiteralWrite.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L LibioLogic LibioCloseSteps.
Open Scope Z_scope.
(** The width calculation leaves these temporary values for the next
    format iteration. The subtraction keeps its machine-word encoding. *)
Definition string_write_env e p n :=
  fold_left (fun e nw => put (fst nw) (snd nw) e)
    [(TAtom "pr.109", WInt n); (TAtom "pr.38", WPtr p);
     (TAtom "v1892", WInt 0); (TAtom "v1893", WInt ((-n) mod 2 ^ 64));
     (TAtom "v1894", WInt 1)] e.
Section write.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None)
  (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None).
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** The write returns the copied bytes and the advanced staging pointer.
    It preserves the source string share, buffer mode and end pointer,
    while leaving FILE fields and other caller resources in the frame. *)
Lemma wp_formatter_string_write e ls bb reg off xs cs dq p s Φ :
  lookup (TAtom "pr.111") e = Some (WInt (Z.of_nat (length s))) ->
  lookup (TAtom "pr.36") e = Some (WPtr p) ->
  lookup (TAtom "pr.66") e = Some (WInt 0) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  find_fn ge (TAtom "__printf_buffer_write") = Some (Defined glibc___printf_buffer_write) ->
  find_fn ge (TAtom "__GI_memcpy") = Some (Defined glibc_memcpy) ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end reg -> r_end reg <= 2 ^ 63 ->
  48 <= off -> 0 < Z.of_nat (length s) -> off + Z.of_nat (length s) <= 176 ->
  length xs = 128%nat -> length cs = length xs -> Forall (fun x => 0 <= x < 256) xs ->
  live bb reg -∗ int_cell bb 32 4 -∗ pcell bb 8 (mkPtr (bb + off) (Obj bb)) -∗
  pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ bytes bb 48 xs -∗ auxes bb 48 cs -∗
  word_string dq p s -∗
  ▷ (live bb reg -∗ int_cell bb 32 4 -∗
    pcell bb 8 (mkPtr (bb + off + Z.of_nat (length s)) (Obj bb)) -∗
    pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ window_after bb 48 xs off s -∗
    word_string dq p s -∗
    WP (ERun (mkFrame glibc_printf_buffer (string_write_env e p (Z.of_nat (length s))) ls None
      (Enter (TAtom "L1150") (Some (TAtom "L1887")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_printf_buffer e ls None
    (Enter (TAtom "L1831") (Some (TAtom "L1871")))) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hlen Hp Hwidth Hbuf Hwrite Hcpy Hb Ha He Hr Ho Hn Hroom Hxs Hcs Hx.
  iIntros "Hl Hmode Hptr Hend Hx Hcs Hs HK".
  iApply wp_enter; [reflexivity | vx |]. iNext.
  cbn [b_insts b_jump]. do 3 step. branch_as false. step.
  norm.
  iApply wp_call_bind; [vx | exact Hwrite | reflexivity |]. iNext.
  iApply (wp_wand with "[Hl Hmode Hptr Hend Hx Hcs Hs]").
  { iApply (wp_printf_buffer_write_word Hmove Hmove_fn Hmove_sym
      _ bb reg off xs cs dq p s
      (fun v => ⌜v = RetVoid⌝ ∗ live bb reg ∗ int_cell bb 32 4 ∗
        pcell bb 8 (mkPtr (bb + off + Z.of_nat (length s)) (Obj bb)) ∗
        pcell bb 16 (mkPtr (bb + 176) (Obj bb)) ∗ window_after bb 48 xs off s ∗
        word_string dq p s)%I with "Hl Hmode Hptr Hend Hx Hcs Hs");
      try assumption; try reflexivity.
    { rewrite (Z.mod_small (Z.of_nat (length s)) (2 ^ 64)); [reflexivity | lia]. }
    iNext. iIntros "Hl Hmode Hptr Hend Hx Hs". iFrame. done. }
  iIntros (v) "(-> & Hl & Hmode & Hptr & Hend & Hx & Hs)". resume. step.
  norm. closed_ints.
  assert (Hcmp : (sign_extension (2 ^ 32) (2 ^ 31)
    (((- Z.of_nat (length s)) mod 2 ^ 64) mod 2 ^ 32) <? 0) = true) by decide_ints.
  rewrite Hcmp. iApply ("HK" with "Hl Hmode Hptr Hend Hx Hs").
Qed.
End write.
