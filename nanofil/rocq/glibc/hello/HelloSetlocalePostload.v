(** When setlocale switches the character type, it calls the type's
    update `c: _nl_postload_ctype` through a table of functions. The
    update copies three table pointers from the category's data into the
    global locale, into the thread's own table pointers and into six
    older globals that programs may read directly.

    In the C locale every one of those cells already holds the value
    that the update writes. So the rule in this module takes each cell
    at its C value and gives it back at the same value, together with
    the constants that the update reads. *)

From Glibc Require Import Unit_locale_lcZ2dctype_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine StepRules Symbolic
  ExternalCalls ExternalMachine Pieces Heap Language Logic MemLogic.
From Glibc Require Import HelloImageModule HelloImageLoad HelloImageEarly OsWorld OsRegistry FileInv LibioLogic WordString
  StartCtypeInitSpec StartEarlyInitSpec StartImageEarly HelloImageLocaleObjs HelloImageCLocaleObjs GetoptShortOpt Fix.
Import ListNotations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

Section postload.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w : os_world) (fr : word -> mem -> option (res unit * mem)).
Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
#[local] Instance postload_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation sexpr := (language.expr (nanofil_lang glibc_os_registry hge)).
Local Instance postload_stable : SafepointStable (os_wi w) := os_wi_stable w.
Local Abbreviation gl := (img_a "_nl_global_locale").
Local Abbreviation glreg := (img_gd "_nl_global_locale").
Local Abbreviation lt := (img_a "__libc_tsd_LOCALE").
Local Abbreviation ltreg := (img_gd "__libc_tsd_LOCALE").
Local Abbreviation cc := (img_a "_nl_C_LC_CTYPE").
Local Abbreviation glp := (mkPtr gl (Obj gl)).
Local Abbreviation ccp := (mkPtr cc (Ro cc)).
Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation roat b k := (mkPtr (b + k) (Ro b)).
Local Abbreviation xc := (img_a "_nl_C_LC_CTYPE_class").
Local Abbreviation xu := (img_a "_nl_C_LC_CTYPE_toupper").
Local Abbreviation xl := (img_a "_nl_C_LC_CTYPE_tolower").
Local Abbreviation x32 := (img_a "_nl_C_LC_CTYPE_class32").

(** The update reads these constants, which never change. *)
Definition pl_ro : iProp Σ :=
  liveq DfracDiscarded cc (img_gd "_nl_C_LC_CTYPE") ∗
  pcellq DfracDiscarded cc 56 (rop xc) ∗ pcellq DfracDiscarded cc 64 (rop xu) ∗ pcellq DfracDiscarded cc 80 (rop xl) ∗
  pcellq DfracDiscarded cc 96 (rop x32) ∗ pcellq DfracDiscarded cc 176 (roat xu 512) ∗
  pcellq DfracDiscarded cc 184 (roat xl 512) ∗
  liveq DfracDiscarded xc (img_gd "_nl_C_LC_CTYPE_class") ∗ liveq DfracDiscarded xu (img_gd "_nl_C_LC_CTYPE_toupper") ∗
  liveq DfracDiscarded xl (img_gd "_nl_C_LC_CTYPE_tolower") ∗ liveq DfracDiscarded x32 (img_gd "_nl_C_LC_CTYPE_class32").

(** The update writes these cells, and in the C locale each of them
    already holds the value that it writes. *)
Local Abbreviation pl_cell n p := (live (img_a n) (img_gd n) ∗ pcell (img_a n) 0 p)%I.

Definition pl_cells : iProp Σ :=
  pcell gl 104 (roat xc 256) ∗ pcell gl 112 (roat xl 512) ∗ pcell gl 120 (roat xu 512) ∗
  pl_cell "__libc_tsd_CTYPE_B" (roat xc 256) ∗ pl_cell "__libc_tsd_CTYPE_TOUPPER" (roat xu 512) ∗
  pl_cell "__libc_tsd_CTYPE_TOLOWER" (roat xl 512) ∗
  pl_cell "__ctype_b" (roat xc 256) ∗ pl_cell "__ctype_toupper" (roat xu 512) ∗
  pl_cell "__ctype_tolower" (roat xl 512) ∗ pl_cell "__ctype32_b" (rop x32) ∗
  pl_cell "__ctype32_toupper" (roat xu 512) ∗ pl_cell "__ctype32_tolower" (roat xl 512).

Local Ltac hc H := iApply (wp_half_check_read_dq (glibc_program := postload_program) with H);
  [reflexivity | vx | reflexivity | right; reflexivity | a2 | a2 | lia | a2 | a2 |]; iNext; iIntros "_".
Local Ltac rd H I := check_read_dq H by a2; iNext; iIntros I.
Local Ltac ld H I := load_pointer_dq H by a2; iNext; iIntros I.

Lemma wp_postload_ctype_c fr0 dqt Φ :
  call_frame Unit_locale_lcZ2dctype_os.fn__nl_postload_ctype [] = Some fr0 ->
  liveq dqt lt ltreg -∗ pcellq dqt lt 0 glp -∗ live gl glreg -∗ pcell gl 0 ccp -∗ pl_ro -∗ pl_cells -∗
  ▷ (liveq dqt lt ltreg -∗ pcellq dqt lt 0 glp -∗ live gl glreg -∗ pcell gl 0 ccp -∗ pl_cells -∗ Φ RetVoid) -∗
  WP (ERun fr0 : sexpr) {{ Φ }}.
Proof.
  intros Hfr. injection Hfr as <-.
  iIntros "Hlt Hlc Hgl Hg0 #(Hcc & Hv0 & Hv1 & Hv2 & Hv12 & Hv15 & Hv16 & Hxc & Hxu & Hxl & H32)".
  iIntros "(H104 & H112 & H120 & (Hlb & Hcb) & (Hlu & Hcu) & (Hll & Hcl) & (Lb & Cb) & (Lu & Cu) & (Ll & Cl) & (L32 & C32) & (L3u & C3u) & (L3l & C3l)) HK".
  step.
  (* The global locale's three table pointers. *)
  step. check "Hgl". ld "Hgl Hg0 Hcc" "Hgl Hg0 _". step. step. step.
  rd "Hcc" "_". ld "Hcc Hv0 Hxc" "_ _ _". step. check "Hgl". store "Hgl" "H104".
  step. step. step. hc "Hcc". ld "Hcc Hv2 Hxl" "_ _ _". step. check "Hgl". store "Hgl" "H112".
  step. step. step. hc "Hcc". ld "Hcc Hv1 Hxu" "_ _ _". step. check "Hgl". store "Hgl" "H120".
  (* The thread's locale is the global one. *)
  step. rd "Hlt" "Hlt". ld "Hlt Hlc Hgl" "Hlt Hlc Hgl". step. step. step. step. branch.
  (* Point the thread's three table pointers at the global locale's. *)
  step. step. step. step. check "Hgl". ld "Hgl H104 Hxc" "Hgl H104 _". check "Hlb". store "Hlb" "Hcb".
  step. step. step. check "Hgl". ld "Hgl H120 Hxu" "Hgl H120 _". check "Hlu". store "Hlu" "Hcu".
  step. step. step. check "Hgl". ld "Hgl H112 Hxl" "Hgl H112 _". check "Hll". store "Hll" "Hcl".
  step. step.
  (* The six old globals are read through the thread's locale. *)
  Local Ltac via_thread := step; rd "Hlt" "Hlt"; ld "Hlt Hlc Hgl" "Hlt Hlc Hgl"; check "Hgl"; ld "Hgl Hg0 Hcc" "Hgl Hg0 _".
  cbn [app].
  step. via_thread. step. rd "Hcc" "_". ld "Hcc Hv0 Hxc" "_ _ _". step. check "Lb". store "Lb" "Cb".
  step. via_thread. step. step. rd "Hcc" "_". ld "Hcc Hv1 Hxu" "_ _ _". step. check "Lu". store "Lu" "Cu".
  step. via_thread. step. step. rd "Hcc" "_". ld "Hcc Hv2 Hxl" "_ _ _". step. check "Ll". store "Ll" "Cl".
  step. via_thread. step. step. rd "Hcc" "_". ld "Hcc Hv12 H32" "_ _ _". check "L32". store "L32" "C32".
  step. via_thread. step. step. rd "Hcc" "_". ld "Hcc Hv15 Hxu" "_ _ _". check "L3u". store "L3u" "C3u".
  step. via_thread. step. step. rd "Hcc" "_". ld "Hcc Hv16 Hxl" "_ _ _". check "L3l". store "L3l" "C3l".
  iApply wp_ret_void. iNext. iApply ("HK" with "Hlt Hlc Hgl Hg0"). iFrame.
Qed.

End postload.
