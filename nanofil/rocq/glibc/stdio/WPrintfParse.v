(** Hello's wide formatter reads the letters l and s in separate rounds.
    The first round sets the long modifier. The second uses a different
    dispatch table and selects the handler that takes a string pointer
    from the argument list. The formatter leaves its saved format pointer
    on the s for the scan that follows the conversion. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import CodePrelude HelloImageCode230 Fix OsWorld FileInv LibioLogic
  LibioCloseSteps WPrintfScan WPrintfLength.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Definition wprintf_buffer_fn := Eval vm_compute in
  code_function (code_module (TApp "module" [TList hello_image_items_230])) "__wprintf_buffer".

Local Abbreviation reg e n x := (lookup (TAtom n) e = Some x).
Local Abbreviation obj b := (mkPtr b (Obj b)).
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** After reading the two letters, the formatter still needs to find
    the next argument, the output buffer and the rest of the format.
    It keeps their addresses in these registers. *)
Definition wparse_keep e bb ap fb :=
  reg e "v0" (WPtr (obj bb)) /\ reg e "v4" (WPtr ap) /\
  reg e "v10" (WPtr (obj fb)) /\ reg e "chk3" (WPtr (obj fb)) /\ reg e "v56" (WInt 0).

Section parse.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation at_block e l from := (ERun (mkFrame wprintf_buffer_fn e [] None (Enter (TAtom l) (Some (TAtom from)))) : sexpr).

(** The classifier reads two bytes in one table. Each byte selects
    a four-byte entry in the jump table for that round. *)
Definition wprintf_tables_ro : iProp Σ :=
  ∃ j jr t tr u ur,
    ⌜lookup (TAtom "glibc_vfwprintf_internal#jump_table") (ge_globals ge) = Some (mkPtr j (Ro j)) /\
     lookup (TAtom "glibc_vfwprintf_internal#__wprintf_buffer.step0_jumps.278") (ge_globals ge) = Some (mkPtr t (Ro t)) /\
     lookup (TAtom "glibc_vfwprintf_internal#__wprintf_buffer.step3b_jumps.282") (ge_globals ge) = Some (mkPtr u (Ro u)) /\
     0 < j /\ j+84 <= r_end jr /\ r_end jr <= 2^63 /\ 0 < t /\ t+48 <= r_end tr /\ r_end tr <= 2^63 /\
     0 < u /\ u+88 <= r_end ur /\ r_end ur <= 2^63⌝ ∗
    liveq DfracDiscarded j jr ∗ bytesq DfracDiscarded j 76 [11] ∗ bytesq DfracDiscarded j 83 [21] ∗
    liveq DfracDiscarded t tr ∗ bytesq DfracDiscarded t 44 [11;0;0;0] ∗
    liveq DfracDiscarded u ur ∗ bytesq DfracDiscarded u 84 [21;0;0;0].

Global Instance wprintf_tables_persistent : Persistent wprintf_tables_ro.
Proof using Type. rewrite /wprintf_tables_ro. apply _. Qed.

(** The handler receives a wide string conversion without a width or
    precision. It can read the pointer argument directly. *)
Lemma wp_wprintf_parse e bb ap fb fr wb b br Φ :
  wparse_keep e bb ap fb -> reg e "v23" (WPtr (mkPtr (2^64-1) CNone)) -> reg e "v13" (WPtr (obj wb)) ->
  0 < fb -> fb mod 8 = 0 -> fb+8 <= r_end fr -> r_end fr <= 2^63 ->
  wprintf_fmt_ro b br -∗ wprintf_tables_ro -∗ live fb fr -∗ pcell fb 0 (mkPtr b (Ro b)) -∗
  ▷ (∀ e', ⌜wparse_keep e' bb ap fb /\ reg e' "pr.16" (WInt 0) /\ reg e' "pr.11" (WInt 0) /\
         reg e' "pr.82" (WInt 4294967295) /\ reg e' "pr.62" (WInt 1) /\ reg e' "pr.67" (WInt 0) /\ reg e' "pr.47" (WInt 0)⌝ -∗
    live fb fr -∗ pcell fb 0 (mkPtr (b+8) (Ro b)) -∗ WP (at_block e' "L1799" "L2165") {{ Φ }}) -∗
  WP (at_block e "L80" "L68") {{ Φ }}.
Proof using Type.
  intros (Hs & Ha & Hf & Hck & Hz) H23 H13 Hfb Hfa Hfe Hfr.
  iIntros "#(%Hfmt & Hlit & Hfmt) #(%j & %jr & %t & %tr & %u & %ur & %Ht & Hjl & Hj1 & Hj2 & Htl & Ht1 & Hul & Hu2) Hl Hc HK".
  destruct Hfmt as (_ & Hb & Hb8 & Hbe & Hbr).
  destruct Ht as (Hj & Ht & Hu & Hjp & Hje & Hjr & Htp & Hte & Htr & Hup & Hue & Hur).
  Local Ltac advance_format idx c :=
    check "Hl"; iApply (wp_raw_load_pointer_dq with "Hl Hc Hlit"); [reflexivity|vx|left; reflexivity|a2|a2|a2|];
    iNext; iIntros "Hl Hc _"; step; check "Hl"; store "Hl" "Hc"; norm; unwrap2;
    iDestruct (wchar_at _ _ 0 wprintf_format idx c ltac:(reflexivity) with "Hfmt") as "[#Hword _]";
    check_read_dq "Hlit" by a2; iNext; iIntros "_";
    load_bytes_dq "Hlit Hword" decode (reflexivity) by a2; iNext; iIntros "_ _"; iClear "Hword".
  Local Ltac dispatch table classes life tag cell :=
    step; branch; do 4 step; branch; step; step_global table; step_global classes;
    do 3 step; closed_ints; check_read_dq "Hjl" by ar; iNext; iIntros "_";
    load_bytes_dq tag decode (reflexivity) by ar; iNext; iIntros "_ _";
    do 3 step; closed_ints; check_read_dq life by ar; iNext; iIntros "_";
    load_bytes_dq cell decode (reflexivity) by ar; iNext; iIntros "_ _";
    step; closed_ints; step; step; do 4 step; closed_ints; step.
  do 2 step. advance_format 1%nat 108. dispatch Ht Hj "Htl" "Hjl Hj1" "Htl Ht1".
  do 7 (step; step; closed_ints; branch).
  step. advance_format 2%nat 115. dispatch Hu Hj "Hul" "Hjl Hj2" "Hul Hu2".
  do 5 (step; step; closed_ints; branch).
  replace (b+4+4) with (b+8) by lia.
  iApply ("HK" with "[%] Hl Hc"). unfold wparse_keep. repeat split; lk_prove.
Qed.
End parse.
