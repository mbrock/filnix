(** A printf buffer can copy into its own staging array without flushing.
    This rule follows the real buffer-write body and its memcpy call when
    the destination has any byte offset and the input fits the remaining
    space. Both strict room and exact fill return without a flush.

    The header and array share one allocation lifetime. The caller owns
    the staging array's bytes and capability slots, disjoint from the
    header fields. Unaligned destinations include those left by a variable
    string. Writes needing a flush remain outside this rule. Copying into
    staging does not claim that the stream emitted bytes. *)
From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_write_os Unit_string_memcpy_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps
  LibioPutsInv MemFwdLogic Fix PrintfStagingCopy.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Section write.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None)
  (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None).
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The copy preserves mode four and the end pointer, advances the write
    pointer by the input length, and returns the exact source bytes in the
    destination slice. Memcpy may change that slice's capability slots.
    FILE fields, errno and the variadic cursor stay in the caller's [[frame]]. *)
Lemma wp_printf_buffer_write_window fr bb reg off xs cs dq sb sreg so sc ys Φ :
  call_frame Unit_stdioZ2dcommon_printf_buffer_write_os.fn___printf_buffer_write
    [WPtr (mkPtr bb (Obj bb)); WPtr (mkPtr (sb + so) sc); WInt (Z.of_nat (length ys))] = Some fr ->
  find_fn ge (TAtom "__GI_memcpy") = Some (Defined Unit_string_memcpy_os.fn___GI_memcpy) ->
  0 < bb -> bb mod 8 = 0 -> bb + 176 <= r_end reg -> r_end reg <= 2 ^ 63 ->
  48 <= off -> 0 < Z.of_nat (length ys) -> off + Z.of_nat (length ys) <= 176 ->
  sb mod 8 = 0 -> 0 <= so -> sb + so + Z.of_nat (length ys) <= r_end sreg ->
  sc = Obj sb \/ sc = Ro sb -> length xs = 128%nat -> length cs = length xs ->
  Forall (fun x => 0 <= x < 256) xs -> Forall (fun y => 0 <= y < 256) ys ->
  live bb reg -∗ int_cell bb 32 4 -∗ pcell bb 8 (mkPtr (bb + off) (Obj bb)) -∗
  pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ bytes bb 48 xs -∗ auxes bb 48 cs -∗
  liveq dq sb sreg -∗ bytesq dq sb so ys -∗
  ▷ (live bb reg -∗ int_cell bb 32 4 -∗
    pcell bb 8 (mkPtr (bb + off + Z.of_nat (length ys)) (Obj bb)) -∗
    pcell bb 16 (mkPtr (bb + 176) (Obj bb)) -∗ window_after bb 48 xs off ys -∗
    liveq dq sb sreg -∗ bytesq dq sb so ys -∗ Φ RetVoid) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hcpy Hb Ha He Hr Ho Hn Hroom Hsa Hso Hse Hsc Hxs Hcs Hx Hy.
  injection Hfr as <-. iIntros "Hl [%Hm Hmode] Hptr Hend Hx Hcs Hs Hy HK".
  step. step. norm. check "Hl".
  load_bytes_dq "Hl Hmode" decode (cbn; reflexivity) by ar.
  iNext. iIntros "Hl Hmode". step. closed_ints. branch. step.
  step. norm.
  replace (0 <? Z.of_nat (length ys)) with true by (symmetry; apply Z.ltb_lt; exact Hn).
  branch. step. step. check "Hl".
  iApply (wp_raw_load_pointer_self with "Hl Hptr");
    [reflexivity | vx | reflexivity | a2 | a2 | a2 | reflexivity |].
  iNext. iIntros "Hl Hptr". step. check "Hl".
  iApply (wp_raw_load_pointer_self with "Hl Hend");
    [reflexivity | vx | reflexivity | a2 | a2 | a2 | reflexivity |].
  iNext. iIntros "Hl Hend".
  do 3 step. norm.
  replace (bb + off =? bb + 176) with false by (symmetry; apply Z.eqb_neq; lia).
  branch. step. branch. step.
  step. check "Hl".
  iApply (wp_raw_load_pointer_self with "Hl Hptr");
    [reflexivity | vx | reflexivity | a2 | a2 | a2 | reflexivity |].
  iNext. iIntros "Hl Hptr". step. check "Hl".
  iApply (wp_raw_load_pointer_self with "Hl Hend");
    [reflexivity | vx | reflexivity | a2 | a2 | a2 | reflexivity |].
  iNext. iIntros "Hl Hend". do 3 step. norm.
  replace (bb + off =? bb + 176) with false by (symmetry; apply Z.eqb_neq; lia).
  branch. step. step. check "Hl".
  iApply (wp_raw_load_pointer_self with "Hl Hend");
    [reflexivity | vx | reflexivity | a2 | a2 | a2 | reflexivity |].
  iNext. iIntros "Hl Hend". step. check "Hl".
  iApply (wp_raw_load_pointer_self with "Hl Hptr");
    [reflexivity | vx | reflexivity | a2 | a2 | a2 | reflexivity |].
  iNext. iIntros "Hl Hptr". do 4 step. norm.
  destruct (Z_lt_ge_dec (Z.of_nat (length ys)) (bb + 176 - (bb + off))) as [Hlt|Hfill];
    [replace (Z.of_nat (length ys) <? bb + 176 - (bb + off)) with true
      by (symmetry; apply Z.ltb_lt; lia); branch; step; step
    |replace (Z.of_nat (length ys) <? bb + 176 - (bb + off)) with false
      by (symmetry; apply Z.ltb_ge; lia); branch; do 4 step;
     replace (bb + 176 - (bb + off)) with (Z.of_nat (length ys)) by lia].
  all: iApply (wp_raw_load_pointer_self with "Hl Hptr");
    [reflexivity | vx | reflexivity | a2 | a2 | a2 | reflexivity |].
  all: iNext; iIntros "Hl Hptr".
  all: iApply (wp_call_memcpy_window Hmove Hmove_fn Hmove_sym
    _ _ _ _ _ _ _ _ _ bb reg 48 xs cs off dq sb sreg so sc ys
    with "Hl Hx Hcs Hs Hy");
    [cbn; rewrite !Z.mod_small; try reflexivity; ar | exact Hcpy | reflexivity | exact Hsc | ar | exact Ha | reflexivity |
     exact Hsa | lia | exact Ho | exact Hso | rewrite Hxs; cbn; lia | rewrite Hxs; cbn; lia |
     exact Hse | exact Hcs | exact Hx | exact Hy |].
  all: iNext; iIntros "Hl Hx Hs Hy".
  all: cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  all: check "Hl".
  all: iApply (wp_raw_load_pointer_self with "Hl Hptr");
    [reflexivity | vx | reflexivity | a2 | a2 | a2 | reflexivity |].
  all: iNext; iIntros "Hl Hptr".
  all: step; check "Hl"; store "Hl" "Hptr".
  all: do 5 step; norm; rewrite Z.sub_diag; closed_ints; branch; step.
  all: iApply wp_ret_void; iNext.
  all: iApply ("HK" with "Hl [Hmode] Hptr Hend Hx Hs Hy").
  all: iSplit; [done | iExact "Hmode"].
Qed.
End write.
