(** The wide formatter appends characters with the image's wide memcpy.
    This function multiplies the character count by four and calls the
    same byte copier as the narrow formatter. The copy may change shadow
    slots in the array, but it preserves the characters before the cursor. *)

From Glibc Require Import Unit_string_memcpy_os Unit_wcsmbs_wmemcpy_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import CodePrelude Fix OsWorld OsRegistry FileInv LibioLogic
  MemFwdLogic PrintfStagingCopy WPrintfDispatch.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic OsWorld.
Open Scope Z_scope.

Definition wprintf_copy_fn := Unit_wcsmbs_wmemcpy_os.fn___wmemcpy.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Section copy.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** The copied characters extend the old prefix. The rest of the array
    still contains valid bytes and has the same number of shadow slots. *)
Local Lemma after_append bb (pre tail ys : list Z) : (length ys <= length tail)%nat ->
  window_after bb 48 (pre ++ tail) (48 + Z.of_nat (length pre)) ys ⊢ ∃ tail' slots,
  ⌜length tail' = (length tail - length ys)%nat /\ Forall (fun b => 0 <= b < 256) tail' /\
    length slots = (length pre + length tail)%nat⌝ ∗ bytes bb 48 ((pre ++ ys) ++ tail') ∗ auxes bb 48 slots.
Proof using Type.
  iIntros (Hfit) "(%xs & %slots & (%L & %Ls & %V & %Hcopy & %Houtside) & Hxs & Hslots)".
  rewrite length_app in L, Ls. set (n := (length pre + length ys)%nat).
  assert (Hpre : take n xs = (pre ++ ys)%list).
  { apply (list_eq_same_length _ _ n); [apply length_app|rewrite length_take; unfold n; lia|].
    intros i x y Hi Hx Hy. rewrite lookup_take_lt in Hx; [|lia].
    destruct (Nat.lt_ge_cases i (length pre)) as [Hp|Hp].
    - rewrite lookup_app_l in Hy; [|lia]. apply (lookup_app_l_Some _ tail) in Hy.
      specialize (Houtside i y Hy ltac:(left; lia)). congruence.
    - rewrite lookup_app_r in Hy; [|lia]. specialize (Hcopy _ _ Hy).
      replace (Z.to_nat (48 + Z.of_nat (length pre) - 48) + (i - length pre))%nat with i in Hcopy by lia.
      congruence. }
  iExists (drop n xs), slots. rewrite -Hpre take_drop. iFrame. iPureIntro.
  split; [rewrite length_drop; unfold n; lia|]. split; [by apply Forall_drop|exact Ls].
Qed.

Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None)
  (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None)
  (Hmemcpy : find_fn ge (TAtom "__GI_memcpy") = Some (Defined Unit_string_memcpy_os.fn___GI_memcpy)).

(** Appending some characters needs just their source bytes, the array
    and the two object lifetimes. The caller keeps the header fields,
    including the cursor, until the copy returns. *)
Lemma wp_wprintf_copy fr bb br cs tail slots dq sb sr so sc ys Φ :
  let off := 48 + 4 * Z.of_nat (length cs) in
  call_frame wprintf_copy_fn [WPtr (mkPtr (bb+off) (Obj bb)); WPtr (mkPtr (sb+so) sc); WInt (Z.of_nat (length ys))] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb+560 <= r_end br -> (length cs + length ys <= 128)%nat ->
  (4*length cs + length tail = 512)%nat -> length slots = 512%nat -> Forall (fun b => 0 <= b < 256) tail ->
  sb mod 8 = 0 -> 0 <= so -> sb+so+4*Z.of_nat (length ys) <= r_end sr -> sc = Obj sb \/ sc = Ro sb ->
  live bb br -∗ bytes bb 48 (stage_bytes cs ++ tail) -∗ auxes bb 48 slots -∗ liveq dq sb sr -∗ bytesq dq sb so (stage_bytes ys) -∗
  ▷ (∀ tail' slots', ⌜(4 * length (cs ++ ys) + length tail' = 512)%nat /\ length slots' = 512%nat /\ Forall (fun b => 0 <= b < 256) tail'⌝ -∗
     live bb br -∗ bytes bb 48 (stage_bytes (cs ++ ys) ++ tail') -∗ auxes bb 48 slots' -∗ liveq dq sb sr -∗ bytesq dq sb so (stage_bytes ys) -∗
     Φ (Ret (WPtr (mkPtr (bb+off) (Obj bb))))) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros off Hfr Hb Hal Hend Hfit L Ls V Hsa Hso Hse Hsc. injection Hfr as <-. iIntros "Hl Hbs Ha Hs Hy HK".
  step. step. iApply (wp_call_memcpy_window Hmove Hmove_fn Hmove_sym _ _ _ _ _ _ _ _ _
    bb br 48 (stage_bytes cs ++ tail) slots off dq sb sr so sc (stage_bytes ys) with "Hl Hbs Ha Hs Hy");
    try assumption; try reflexivity; try (rewrite ?length_app !stage_bytes_length; unfold off; lia).
  - rewrite stage_bytes_length. cbn [map_option arg_x value_x]. lookups. cbn.
    change (2 ^ ((2 mod 2 ^ 32) mod 64)) with 4. unwrap2. repeat f_equal; lia.
  - lia.
  - unfold off. lia.
  - apply Forall_app. auto using stage_bytes_valid.
  - apply stage_bytes_valid.
  - iNext. iIntros "Hl Hafter Hs Hy". cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
    iApply wp_ret; [reflexivity|vx|]. iNext.
    iDestruct (after_append bb (stage_bytes cs) tail (stage_bytes ys) with "[Hafter]") as (tl sl (Ltl & Vtl & Lsl)) "[Hbs Ha]".
    + rewrite stage_bytes_length. lia.
    + rewrite stage_bytes_length. replace (48 + Z.of_nat (4*length cs)) with off by (unfold off; lia). iExact "Hafter".
    + rewrite !stage_bytes_length in Ltl, Lsl. iApply ("HK" $! tl sl with "[%] Hl [Hbs] Ha Hs Hy").
      * rewrite length_app. split_and!; try assumption; lia.
      * by rewrite /stage_bytes flat_map_app.
Qed.
End copy.
