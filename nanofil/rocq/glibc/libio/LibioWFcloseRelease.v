(** After fclose unlinks a wide stdout and finishes the FILE, it still
    owns the two converters inside the wide data object. It takes the
    conversion lock once, releases both steps, and unlocks before it
    returns the saved result of closing the descriptor. *)

From Glibc Require Import Unit_libio_iofclose_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps LibioWIdle
  LibioWFwide LibioWRelease Mbrtowc HelloImageLoad HelloImageWFwideObjs HelloImageWReleaseObjs StartImageEarly Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Section release.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Local Notation dq := DfracDiscarded.
Local Abbreviation lk := (img_a "__gconv_lock").
Local Abbreviation tw := (img_a "glibc_wcsmbsload#to_wc").
Local Abbreviation tm := (img_a "glibc_wcsmbsload#to_mb").
Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation objp b := (mkPtr b (Obj b)).

(** The wide stream no longer has a backup area. Its codecvt pointer
    points inside its wide data, so the same lifetime covers both step
    pointers. The two steps themselves need only read-only shares. *)
Lemma wp_fclose_wide_release e from p1 fb freg wd wr pin Φ :
  lookup (TAtom "v0") e = Some (WPtr (objp fb)) -> lookup (TAtom "chk0") e = Some (WPtr (objp fb)) ->
  lookup (TAtom "pr.1") e = Some (WInt p1) -> 0 <= p1 < 2^32 ->
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals ge) = Some (objp fb) ->
  lookup (TAtom "_IO_2_1_stdin_") (ge_globals ge) = Some pin -> ptr_addr pin <> fb -> 0 <= ptr_addr pin < 2^64 ->
  lookup (TAtom "__gconv_lock") (ge_globals ge) = Some (objp lk) ->
  find_fn ge (TAtom "__gconv_release_step") = Some (Defined glibc_gconv_release_step) ->
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end freg -> r_end freg <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 ->
  mbr_tables -∗ ptsq dq hello_wfwide_ps -∗ ptsq dq hello_wrelease_ps -∗ gconv_lock_free -∗
  live fb freg -∗ pcell fb 160 (objp wd) -∗ pcell fb 152 (mkPtr (wd+104) (Obj wd)) -∗
  live wd wr -∗ pcell wd 72 null -∗ pcell wd 104 (rop tw) -∗ pcell wd 160 (rop tm) -∗
  ▷ (gconv_lock_free -∗ live fb freg -∗ pcell fb 160 (objp wd) -∗ pcell fb 152 (mkPtr (wd+104) (Obj wd)) -∗
     live wd wr -∗ pcell wd 72 null -∗ pcell wd 104 (rop tw) -∗ pcell wd 160 (rop tm) -∗ Φ (Ret (WInt p1))) -∗
  WP (ERun (mkFrame Unit_libio_iofclose_os.fn__IO_new_fclose e [] None (Enter (TAtom "L136") (Some from))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hv Hc Hp Hp1 Hout Hin Hneq Hinr Hlk Hrel Hfb Hfa Hfe Hfr Hwd Hwa Hwe Hwr.
  iIntros "(_ & _ & _ & _ & _ & _ & #Htw & #Htw0 & _) #Hw #Hends (Hll & % & Hlb) Hl Hwd Hcv Hwlife H72 H104 H160 HK".
  iDestruct (wfwide_tables with "Hw") as "(_ & _ & _ & #Htm & #Htm0)".
  iEval (rewrite /hello_wrelease_ps ptsq_app) in "Hends". iDestruct "Hends" as "[#Htw64 #Htm64]".
  iApply (wp_live_fit1 with "Hl"). iIntros ([? ?]) "Hl".
  iApply (wp_live_fit1 with "Hwlife"). iIntros ([? ?]) "Hwlife".
  step. step. check "Hl". load "Hl" "Hwd" "Hwlife". step. check "Hwlife". load_null "Hwlife" "H72".
  do 3 step. branch. step. step. check "Hl". load "Hl" "Hcv" "Hwlife".
  step_global Hlk. check "Hll". iApply (wp_raw_cas_w with "Hll Hlb");
    [left; reflexivity|reflexivity|reflexivity|vx|reflexivity|a2|a2|intros _; wi_store|]. iNext. iIntros "Hll Hlb".
  rewrite (_ : of_bytes (int_bytes 0) =? 0 mod 2^32 = true); [|reflexivity].
  rewrite (_ : of_bytes (int_bytes 0) mod 2^32 = 0); [|reflexivity].
  step. branch. step. step. branch. step. check "Hwlife".
  load_pointer_dq "Hwlife H104 Htw" by a2. iNext. iIntros "Hwlife H104 _".
  iApply wp_call_bind; [vx|exact Hrel|reflexivity|]. iNext.
  iApply (wp_gconv_release_static with "Htw Htw0 Htw64"); [reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|
    vm_compute; discriminate|vm_compute; discriminate|]. iNext. resume.
  step. check "Hwlife". load_pointer_dq "Hwlife H160 Htm" by a2. iNext. iIntros "Hwlife H160 _".
  iApply wp_call_bind; [vx|exact Hrel|reflexivity|]. iNext.
  iApply (wp_gconv_release_static with "Htm Htm0 Htm64"); [reflexivity|vm_compute; reflexivity|vm_compute; reflexivity|
    vm_compute; discriminate|vm_compute; discriminate|]. iNext. resume.
  step_global Hlk. check "Hll". iAssert (bytes lk 0 (int_bytes 1)) with "Hlb" as "Hlb".
  assert (0 <= 1 < 2^32) by lia. load_s32 "Hll" "Hlb". step. step. check "Hll".
  iApply (wp_raw_cas_w with "Hll Hlb");
    [left; reflexivity|reflexivity|reflexivity|vx|reflexivity|a2|a2|intros _; wi_store|]. iNext. iIntros "Hll Hlb".
  rewrite (_ : of_bytes (int_bytes 1) =? ((1 mod 2^32) mod 2^32) mod 2^32 = true); [|reflexivity].
  rewrite (_ : of_bytes (int_bytes 1) mod 2^32 = 1); [|reflexivity].
  step. branch. step. step. branch. repeat first [step|branch_as true|branch_as false].
  iApply wp_ret; [reflexivity|vx|]. iNext. rewrite (Z.mod_small p1); [|lia].
  iApply ("HK" with "[$Hll Hlb] Hl Hwd Hcv Hwlife H72 H104 H160"). iSplit; [done|iExact "Hlb"].
Qed.
End release.
