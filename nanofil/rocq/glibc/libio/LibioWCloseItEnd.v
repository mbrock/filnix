(** Closing a wide stream drops its wide buffer before it drops the
    narrow one. The conversion descriptors stay in the wide data
    object: fclose will release their steps after it unlinks stdout. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps LibioCloseItCode LibioReadCode
  LibioSetb LibioWIdle LibioWAllocCode LibioWAllocSetb LibioCloseItEnd Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Section close_it.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hwsb : !Defines ge "__GI__IO_wsetb" glibc__IO_wsetb}
  `{Hsb : !Defines ge "__GI__IO_setb" glibc__IO_setb}.
Context (Hfree : free_rule w0 registry ge) (B : Z -> Z -> ptr -> iProp Σ)
  (Hsetb : setb_spec_with w0 registry ge B).
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation objp b := (mkPtr b (Obj b)).
#[local] Hint Unfold woff_ptr : offs.

(** The stream's wide data records which buffer it owns and has no
    backup area. After setb for each buffer, the wide data still holds
    the same conversion steps, but all eleven wide pointers are null.
    Descriptor close failure takes precedence over the flush result. *)
Lemma wp_wclose_it_L221 e from p3 k fb freg fl f2 fd off ob oe p8 p16 p24 p32 p40 p48 vb tw tm wd w Φ :
  lookup (TAtom "v0") e = Some (WPtr (objp fb)) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (fb + off_fileno) (Obj fb))) ->
  lookup (TAtom "chk1") e = Some (WPtr (objp fb)) -> lookup (TAtom "v2") e = Some (WInt 0) ->
  lookup (TAtom "pr.3") e = Some (WInt p3) -> lookup (TAtom "v220") e = Some (WInt k) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2^63 ->
  0 <= fl < 2^32 -> 0 <= p3 < 2^32 -> k = 0 \/ k = 2^32-1 -> wbuf_user_ok w f2 ->
  live fb freg -∗ int_cell fb off_flags2 f2 -∗ pcell fb off_wide (objp wd) -∗ wide_data vb tw tm wd w -∗
  int_cell fb off_flags fl -∗ int_cell fb off_fileno fd -∗ icell fb off_offset off -∗
  pcell fb 8 p8 -∗ pcell fb 16 p16 -∗ pcell fb 24 p24 -∗ pcell fb 32 p32 -∗ pcell fb 40 p40 -∗ pcell fb 48 p48 -∗
  pcell fb off_buf_base ob -∗ pcell fb off_buf_end oe -∗ B fb fl ob -∗
  ▷ (live fb freg -∗ int_cell fb off_flags2 (wsetb_flags2 f2 0) -∗ pcell fb off_wide (objp wd) -∗ wide_data vb tw tm wd WbNone -∗
     int_cell fb off_flags (closed_flags fl) -∗ int_cell fb off_fileno (2^32-1) -∗ icell fb off_offset (2^64-1) -∗
     pcell fb 8 null -∗ pcell fb 16 null -∗ pcell fb 24 null -∗ pcell fb 32 null -∗ pcell fb 40 null -∗ pcell fb 48 null -∗
     pcell fb off_buf_base null -∗ pcell fb off_buf_end null -∗ Φ (Ret (WInt (if k =? 0 then p3 else k)))) -∗
  WP (ERun (mkFrame glibc__IO_file_close_maybe_unlink e [] None (Enter (TAtom "L221") (Some from))) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hv Hc Hc1 Hv2 Hp Hk Hfb Hfa Hfe Hfr Hfl Hp3 Hkr Hu.
  iIntros "Hl Hf2 Hwd Hdata Hfl Hfd Hoff H8 H16 H24 H32 H40 H48 Hbb Hbe HB HK".
  iDestruct "Hdata" as (wr ps ib ie ob' oe' ifl ic ofl oc sb sc H) "(Hw & Hps & Hst & Ha & Hi & Ho & Hsb & Hpad & Hsc & Hvt & Hbuf)".
  destruct H as (Hwd & Hwa & Hwe & Hwr & (L & D & A) & Hifl & Hofl & Lsb & Vsb & Lsc).
  assert (Eb : nth 6 ps null = wbuf_base wd w).
  { destruct w; cbn [wbuf_base] in *; [|exact (proj1 (proj2 (proj2 (proj2 A))))..].
    do 8 (destruct ps as [|? ps]; [discriminate L|]). injection A. cbn [nth]. congruence. }
  do 8 (destruct ps as [|? ps]; [discriminate L|]). change (ps = [null; null; null]) in D. subst ps.
  cbn [nth] in Eb. rewrite Eb. iDestruct "Hps" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _)".
  unfold file_size in Hfe. iApply (wp_live_fit1 with "Hl"). iIntros ([? ?]) "Hl".
  iApply (wp_live_fit1 with "Hw"). iIntros ([? ?]) "Hw".
  step. step. check "Hl". load "Hl" "Hwd" "Hw". step. check "Hw". load_null "Hw" "P9".
  do 3 step. branch. step. iApply wp_call_bind; [vx|exact Hwsb|reflexivity|]. iNext.
  iApply (wp_glibc__IO_wsetb Hfree with "Hl Hf2 Hwd Hw P6 P7 Hbuf"); try close_side.
  iNext. iIntros "Hl Hf2 Hwd Hw P6 P7". resume.
  Local Ltac wide_obj := check "Hl"; load "Hl" "Hwd" "Hw".
  step. wide_obj. step. check "Hw". store "Hw" "P2".
  wide_obj. check "Hw". store "Hw" "P0". wide_obj. step. check "Hw". store "Hw" "P1".
  wide_obj. step. load "Hl" "Hwd" "Hw". step. check "Hw". store "Hw" "P4". check "Hw". store "Hw" "P3".
  wide_obj. step. check "Hw". store "Hw" "P5". iApply wp_goto. iNext.
  iApply (wp_close_it_L223_with B Hsetb with "Hl Hfl Hfd Hoff H8 H16 H24 H32 H40 H48 Hbb Hbe HB"); try close_side.
  iNext. iIntros "Hl Hfl Hfd Hoff H8 H16 H24 H32 H40 H48 Hbb Hbe".
  iApply ("HK" with "Hl Hf2 Hwd [-Hfl Hfd Hoff H8 H16 H24 H32 H40 H48 Hbb Hbe] Hfl Hfd Hoff H8 H16 H24 H32 H40 H48 Hbb Hbe").
  iExists wr, (replicate 11 null), ib, ie, ob', oe', ifl, ic, ofl, oc, sb, sc.
  iSplit; [iPureIntro; split_and!; try assumption; by repeat split|]. cbn [replicate big_sepL]. by iFrame.
Qed.
End close_it.
