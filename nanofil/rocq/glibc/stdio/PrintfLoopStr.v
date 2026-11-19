(** The conversion `%s` of the formatter's loop prints a string
    argument. Its code starts at the block `L1825`, which reads the
    argument. A null argument prints the constant `(null)`, and any
    other argument is a string that the code measures with
    `c: strlen`. Both ways meet at the block `L1831`, which writes the
    text. This module proves the rows of the two blocks in the table
    of [PrintfLoopState](PrintfLoopState.v). *)

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

Section str.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (k : Z) (R : Z -> region -> Z * region * Z * Z -> iProp Σ).
Context `{!Callees (loop_callees k R)}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Local Notation blocks := (loop_blocks k R).

(** The block `L1825` reads the argument of a `%s` and finds the text
    to print. *)
Lemma str_start_holds :
  ▷ blocks_hold Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer blocks ⊢
  block_triple Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer
    (BSpec "L1825" None str_sig pl_in (conv_vals 115) (conv_pre k R FmtStr) (pl_post k R)).
Proof using Type*.
  iIntros "#IH". iModIntro.
  iIntros ([[bb [fa fc] dq bytes ds0 ap skip xs rest eb] fb wb pre tl ds i n] e from Φ) "_ %He H HK".
  row_simpl. c_env_open He.
  iDestruct "H" as "(((%Hbytes & %Hfit & %Hfb & %Hf8 & %Hfe & %Hn) & %Hne & %ds1 & -> & %Hptail) & Hout & Hs & Hfl & Hfc & Hva & #Hargs & Hwork & #Hro)".
  destruct (str_fits _ _ _ Hfit) as (q & args & Hargs_eq & Hfit1).
  destruct (skipn_cons _ _ _ _ Hargs_eq) as (Hxi & Hskip1 & Hilt).
  iEval (rewrite Hargs_eq big_sepL_cons) in "Hargs". iDestruct "Hargs" as "[Hq Hargs1]". subst args.
  iDestruct (va_cur_ptr _ i xs q Hxi with "Hva")
    as (cb sb cur) "((-> & %Hc8 & %Hsb & %Hse & %Hsr & %Hcur0 & %Hround) & Hcur & Hsl & Hqc & Hvback)".
  iPoseProof "Hro" as "(_ & _ & _ & Hnt & _)". block_enter.
  iDestruct (str_arg_string with "Hq") as "[-> | (%s & #Hqs)]".
  { (* A null argument prints the constant `(null)`. *)
    iApply (wp_va_arg_ptr _ _ _ _ _ _ _ _ cb _ cur sb _ (8 * Z.of_nat i) null DfracDiscarded [] with "Hcur Hsl Hqc []");
      [vx | assumption | assumption | lia | cbn [r_end]; lia | cbn [r_end]; lia | assumption | exact Hround | cbn; lia |
       left; reflexivity | by rewrite /ptsq big_sepL_nil |].
    iNext. iIntros "Hcur Hsl Hqc _". iDestruct ("Hvback" with "Hcur Hsl Hqc") as "Hva".
    step. step. step. step. branch.
    step. step. branch. step. branch. iDestruct "Hnt" as (nb) "[%Hng Hns]". unfold null_text in Hng.
    step. step_global Hng.
    step.
    goto_block "IH" "HK" 5%nat
      with (PpIn (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 (mkPtr cb (Obj cb)) skip xs rest eb) fb wb pre tl ds1 (S i) n)
              (mkPtr nb (Ro nb)) null_text_bytes).
    row_simpl. iFrame "Hout Hs Hfl Hfc Hva Hargs1 Hwork Hro Hns". iPureIntro.
    split_and!; first [reflexivity | assumption | lia]. }
  (* Any other argument is a string, and the function measures it. *)
  iDestruct (word_string_range with "Hqs") as %Hqr.
  iApply (wp_va_arg_str _ _ _ _ _ _ _ _ cb _ cur sb _ (8 * Z.of_nat i) q DfracDiscarded s with "Hcur Hsl Hqc Hqs");
    [vx | assumption | assumption | lia | cbn [r_end]; lia | cbn [r_end]; lia | assumption | exact Hround | lia |].
  iNext. iIntros "Hcur Hsl Hqc _". iDestruct ("Hvback" with "Hcur Hsl Hqc") as "Hva".
  step. step. step. step.
  replace (ptr_addr q mod 2 ^ 64 =? 0 mod 2 ^ 64) with false
    by (symmetry; apply Z.eqb_neq; change (0 mod 2 ^ 64) with 0; rewrite Z.mod_small; lia).
  branch. step. step. branch. step. step. step. step. step. branch. step. step. branch. step.
  call_callee with (DfracDiscarded, q, s) giving ""; [iExact "Hqs"|]. iDestruct "Hpost" as "[-> _]". block_resume.
  step. step. step. rewrite !(Z.mod_small (Z.of_nat (length s))); [|lia..]. cbn [edge_label].
  goto_block "IH" "HK" 4%nat
    with (PpIn (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 (mkPtr cb (Obj cb)) skip xs rest eb) fb wb pre tl ds1 (S i) n)
            q s).
  row_simpl. iFrame "Hout Hs Hfl Hfc Hva Hargs1 Hwork Hro Hqs". iPureIntro.
  split_and!; first [reflexivity | assumption | lia].
Qed.

(** The block `L1831` writes the text. A conversion without a width
    needs no padding, but the compiled code still calls the padding
    function when the text is empty or very long. *)
Lemma print_body_holds :
  ▷ blocks_hold Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer blocks ⊢
  body_triple Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer "L1831" print_body pp_in pp_vals (print_pre k R) (fun z => pl_post k R (pp_in_ z)).
Proof using Type*.
  iIntros "#IH". iModIntro.
  iIntros ([[[bb [fa fc] dq bytes ds0 ap skip xs rest eb] fb wb pre tl ds i n] str text] e Φ) "%He H HK".
  row_simpl. c_env_open He. iDestruct "H" as "((%Hok & Hout & Hown) & #Hstr)".
  iDestruct (word_string_range with "Hstr") as %Htr.
  body_start Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer "L1831". step. step. step. branch_eqn E.
  - (* The string is empty or huge: the function pads with the difference, then writes the string. *)
    clear E. step. step. branch. step. step. step.
    call_callee with (bb, 32, _) giving "Hout"; [iFrame "Hout"; iPureIntro; split; [lia | apply Z.mod_pos_bound; lia]|].
    iDestruct "Hpost" as "(-> & Hout)". block_resume. step. step.
    call_callee with (bb, DfracDiscarded, str, text, _) giving "Hout"; [iFrame "Hout Hstr"; iPureIntro; unwrap2; lia|].
    iDestruct "Hpost" as "(-> & Hout & _)". block_resume. branch.
    goto_block "IH" "HK" 9%nat
      with (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 ap skip xs rest eb) fb wb pre tl ds i n).
    row_simpl. iFrame "Hout Hown". done.
  - (* Otherwise the function writes the string at once. *)
    clear E. step.
    call_callee with (bb, DfracDiscarded, str, text, _) giving "Hout"; [iFrame "Hout Hstr"; iPureIntro; unwrap2; lia|].
    iDestruct "Hpost" as "(-> & Hout & _)". block_resume. step.
    goto_block "IH" "HK" 8%nat
      with (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 ap skip xs rest eb) fb wb pre tl ds i n).
    row_simpl. iFrame "Hout Hown". done.
Qed.

(** The rows of the conversion `%s` are the row of its first block and
    a row for each way into the block that writes. Each of the two
    takes the step into the block, which copies the string and its
    length, and then uses the body. *)
Lemma str_rows_hold :
  ▷ blocks_hold Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer blocks ⊢ blocks_hold Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer (str_rows k R).
Proof using Type*.
  iIntros "#IH". iPoseProof (print_body_holds with "IH") as "#Hprint".
  iSplit; [iApply (str_start_holds with "IH")|]. repeat iSplit; [| | done]; iModIntro.
  - iIntros (z e from Φ) "%Hfrom %He H HK". row_simpl. iDestruct "H" as "[H #Hstr]". c_env_open He.
    iDestruct (word_string_range with "Hstr") as %Htr. block_enter_from Hfrom.
    iApply ("Hprint" $! z with "[] [H] HK");
      [iPureIntro; row_simpl; rewrite Z.mod_small; [c_env_close | lia] | row_simpl; iFrame "H Hstr"].
  - iIntros (z e from Φ) "%Hfrom %He H HK". row_simpl. iDestruct "H" as "(%Htext & H & #Hstr)". c_env_open He.
    block_enter_from Hfrom.
    iApply ("Hprint" $! z with "[] [H] HK"); [iPureIntro; row_simpl; rewrite Htext; c_env_close | row_simpl; iFrame "H Hstr"].
Qed.

End str.
