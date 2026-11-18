(** The out-of-line character writer flushes before it writes a byte.
    If the buffer has already failed, or the flush fails, it returns
    without touching the window. A successful flush gives it the strict
    inequality that both the C assertion and the byte store require. *)
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv LibioLogic CStruct CBlocks
  PrintfLayout PrintfOut PrintfSpec PrintfPutcOneCode.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope string_scope. Open Scope list_scope. Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Section putc.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (k : Z) (R : Z -> region -> Z * region * Z * Z -> iProp Σ).
Context `{!HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_flush") (flush_spec k R)}.

(** The writer returns the same backend on all three paths. Only the success
    path advances the pointer, and advancing it by one stays in the window. *)
Lemma putc_one_has_spec `{!Defines ge "__printf_buffer_putc_1" glibc_printf_buffer_putc_1} :
  HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_putc_1") (putc_spec k R).
Proof using Type*.
  intros [bb c]. exists glibc_printf_buffer_putc_1. split; [exact defines|]. split; [eexists; reflexivity|].
  intros fr Φ Hfr. injection Hfr as <-. cbn [fs_pre fs_post putc_spec].
  iIntros "[%Hc Hout] HK". iDestruct "Hout" as (breg w written mode) "(%Hmd & Hbuf & HR)". buf_open "Hbuf".
  step. step. check "Hl". load_mode "Hl" "Hmode". step. branch_eqn E.
  2: { step. branch. step. iApply wp_ret_void. iNext. iApply "HK". iSplit; [done|].
       out_close "HR" with w. exact Hw. }
  step. call_callee with bb giving "Hl Hbase Hptr Hend Hwr Hmode Hwl Hwin HR".
  { out_close "HR" with w. exact Hw. }
  clear Hmd Hw Hbb. iDestruct "Hpost" as (r br w' wr m) "((-> & %Hr & %Hmd & %Hroom) & Hbuf & HR)".
  block_resume. destruct Hr as [-> | ->]; step; step; step; step; branch; step.
  - iApply wp_ret_void. iNext. iApply "HK". iSplit; [done|]. iExists br, w', wr, m. by iFrame.
  - specialize (Hroom eq_refl). buf_open "Hbuf". unfold pwin_ok in Hw.
    step. check "Hl". load_window "Hl" "Hptr" "Hwl". step. check "Hl". load_window "Hl" "Hend" "Hwl".
    step. step. step. branch_as false. step.
    step. check "Hl". load_window "Hl" "Hptr" "Hwl". step. check "Hl". store "Hl" "Hptr". step.
    iDestruct (win_live_acc with "Hl Hwl") as "[Hwo Hback]".
    iDestruct (window_byte w' Hw Hroom with "Hwin") as (x) "[Hx Hrest]".
    check "Hwo". rule2 "Hwo" "Hx" ltac:(eapply wp_raw_store_byte; inst; [vx | vx | reflexivity | a2 | wi_store]).
    iDestruct ("Hback" with "Hwo") as "[Hl Hwl]". iDestruct ("Hrest" with "[%] Hx") as "Hwin"; [apply Z.mod_pos_bound; lia|].
    iApply wp_ret_void. iNext. iApply "HK". iSplit; [done|]. cbn [ptr_addr ptr_cap]. unwrap2.
    out_close "HR" with (PWin (pw_obj w') (pw_reg w') (pw_base w') (pw_ptr w' + 1) (pw_end w')).
    unfold pwin_ok. cbn [pw_obj pw_reg pw_base pw_ptr pw_end]. lia.
Qed.
End putc.
