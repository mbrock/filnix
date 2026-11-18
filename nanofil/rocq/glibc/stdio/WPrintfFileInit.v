(** The wide formatter in Hello always writes into a private array of
    128 wide characters. Its initializer points the cursor at this array,
    even when stdout already has room. A flush therefore calls the stream's
    xsputn slot with a character count; the formatter never calls the
    stream's overflow slot. *)

From Glibc Require Import HelloImageTypedWP.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import CodePrelude Fix OsWorld FileInv LibioLogic LibioCloseSteps.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

(** Hello calls this function before it copies the first character into the array. *)
Definition wprintf_file_init_fn := hello_image_fn___wprintf_buffer_to_file_init.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Section init.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The initializer overwrites six fields without reading the array or the
    stream. The caller keeps both outside the initializer's footprint. *)
Lemma wp_wprintf_file_init fr bb breg fp base cur stop written mode oldfp Φ :
  call_frame wprintf_file_init_fn [WPtr (mkPtr bb (Obj bb)); WPtr fp] = Some fr ->
  0 < bb -> bb mod 8 = 0 -> bb + 560 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  live bb breg -∗ pcell bb 0 base -∗ pcell bb 8 cur -∗ pcell bb 16 stop -∗
  icell bb 24 written -∗ int_cell bb 32 mode -∗ pcell bb 40 oldfp -∗
  ▷ (live bb breg -∗ pcell bb 0 (mkPtr (bb + 48) (Obj bb)) -∗
     pcell bb 8 (mkPtr (bb + 48) (Obj bb)) -∗ pcell bb 16 (mkPtr (bb + 560) (Obj bb)) -∗
     icell bb 24 0 -∗ int_cell bb 32 2 -∗ pcell bb 40 fp -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hbb Hal Hend Hreg. injection Hfr as <-.
  iIntros "Hl Hbase Hcur Hend Hw [%Hm Hm] Hfp HK".
  step. step. check "Hl". store "Hl" "Hbase".
  step. check "Hl". store "Hl" "Hcur".
  step. step. check "Hl". store "Hl" "Hend".
  step. check "Hl". store_long "Hl" "Hw".
  step. check "Hl". store_int "Hl" "Hm".
  step. check "Hl". store "Hl" "Hfp".
  iApply wp_ret_void. iNext. norm.
  replace (bb + 48 + 512) with (bb + 560) by lia.
  iApply ("HK" with "Hl Hbase Hcur Hend Hw [Hm] Hfp"). iSplit; [done | iExact "Hm"].
Qed.
End init.
