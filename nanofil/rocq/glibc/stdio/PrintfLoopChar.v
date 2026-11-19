(** The conversion `%c` of the formatter's loop prints one character,
    and `%%` prints a percent sign. The code of `%c` starts at the
    block `L1796`. It reads a 32-bit argument and appends the low byte
    of it to the buffer. The code of `%%` is the block `L1151`, which
    reads no argument. This module proves the rows of the two blocks
    in the table of [PrintfLoopState](PrintfLoopState.v). *)

From Glibc Require FixVariadic.
From Glibc Require Import Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  VariadicLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv LibioLogic LibioDefaultXsputnBuf WordString StrchrnulLogic
  StrlenWord NarrowFormat
  CFrame CStruct CBlocks PrintfLayout PrintfOut PrintfSpec FormatterNames VaArgRound PrintfLoopState.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic FixVariadic.VL0.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Section char.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (k : Z) (R : Z -> region -> Z * region * Z * Z -> iProp Σ).
Context `{!Callees (loop_callees k R)}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Local Notation blocks := (loop_blocks k R).

(** The conversion `%c` pads to its width before the character. The
    conversion has no width here, so the compiled code asks for a
    padding of −1 characters, and the padding function appends
    nothing. Then the code reads the argument and appends its low
    byte. *)
Lemma char_start_holds :
  ▷ blocks_hold Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer blocks ⊢
  block_triple Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer
    (BSpec "L1796" None char_sig pl_in (conv_vals 99) (conv_pre k R FmtChar) (pl_post k R)).
Proof using Type*.
  iIntros "#IH". iModIntro.
  iIntros ([[bb [fa fc] dq bytes ds0 ap skip xs rest eb] fb wb pre tl ds i n] e from Φ) "_ %He H HK".
  row_simpl. c_env_open He.
  iDestruct "H" as "(((%Hbytes & %Hfit & %Hfb & %Hf8 & %Hfe & %Hn) & %Hne & %ds1 & -> & %Hptail) & Hout & Hs & Hfl & Hfc & Hva & #Hargs & Hwork & #Hro)".
  destruct (char_fits _ _ _ Hfit) as (x & args & Hargs_eq & Hx & Hfit1).
  destruct (skipn_cons _ _ _ _ Hargs_eq) as (Hxi & Hskip1 & Hilt).
  iEval (rewrite Hargs_eq big_sepL_cons) in "Hargs". iDestruct "Hargs" as "[_ Hargs1]". subst args.
  iDestruct (va_cur_int _ i xs x Hxi with "Hva")
    as (cb sb cur) "((-> & %Hc8 & %Hsb & %Hse & %Hsr & %Hcur0 & %Hround) & Hcur & Hsl & Hxc & Hvback)".
  block_enter. branch. step. step. step. branch. step. step.
  call_callee with (bb, 32, _) giving "Hout"; [iFrame "Hout"; iPureIntro; split; [lia | apply Z.mod_pos_bound; lia]|].
  iDestruct "Hpost" as "(-> & Hout)". block_resume. step. step.
  iApply (wp_va_arg_w _ _ _ _ _ _ _ _ cb _ cur sb _ (8 * Z.of_nat i) x with "Hcur Hsl Hxc");
    [vx | assumption | assumption | lia | cbn [r_end]; lia | cbn [r_end]; lia | assumption | exact Hround |].
  iNext. iIntros "Hcur Hsl Hxc". iDestruct ("Hvback" with "Hcur Hsl Hxc") as "Hva".
  step. step.
  call_callee with (bb, _) giving "Hout"; [iFrame "Hout"; iPureIntro; apply Z.mod_pos_bound; lia|].
  iDestruct "Hpost" as "(-> & Hout)". block_resume. branch.
  goto_block "IH" "HK" 10%nat
    with (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 (mkPtr cb (Obj cb)) skip xs rest eb) fb wb pre tl ds1 (S i) n).
  row_simpl. iFrame "Hout Hs Hfl Hfc Hva Hargs1 Hwork Hro". iPureIntro.
  split_and!; first [reflexivity | assumption | lia].
Qed.

(** The conversion `%%` appends a percent sign and reads no
    argument. *)
Lemma percent_holds :
  ▷ blocks_hold Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer blocks ⊢
  block_triple Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer
    (BSpec "L1151" None percent_sig pl_in pl_vals (conv_pre k R FmtPercent) (pl_post k R)).
Proof using Type*.
  iIntros "#IH". iModIntro.
  iIntros ([[bb [fa fc] dq bytes ds0 ap skip xs rest eb] fb wb pre tl ds i n] e from Φ) "_ %He H HK".
  row_simpl. c_env_open He.
  iDestruct "H" as "(((%Hbytes & %Hfit & %Hfb & %Hf8 & %Hfe & %Hn) & %Hne & %ds1 & -> & %Hptail) & Hout & Hown)".
  apply percent_fits in Hfit.
  block_enter.
  call_callee with (bb, 37) giving "Hout"; [iFrame "Hout"; iPureIntro; lia|].
  iDestruct "Hpost" as "(-> & Hout)". block_resume. step.
  goto_block "IH" "HK" 11%nat
    with (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 ap skip xs rest eb) fb wb pre tl ds1 i n).
  row_simpl. iFrame "Hout Hown". iPureIntro. split_and!; first [reflexivity | assumption | lia].
Qed.

(** These two rows are the rows of the conversions `%c` and `%%`. *)
Lemma char_rows_hold :
  ▷ blocks_hold Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer blocks ⊢ blocks_hold Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer (char_rows k R).
Proof using Type*.
  iIntros "#IH". iSplit; [iApply (char_start_holds with "IH")|]. iSplit; [iApply (percent_holds with "IH") | done].
Qed.

End char.
