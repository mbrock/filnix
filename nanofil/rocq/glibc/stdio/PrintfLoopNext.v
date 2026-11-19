(** The formatter's loop ends every conversion at the block `L1150`.
    The block counts the conversion and steps over its last byte. It
    writes the plain text up to the next percent sign. Then it starts
    another round, or it returns when the format has ended. This
    module proves the rows of that block in the table of
    [PrintfLoopState](PrintfLoopState.v). The function reaches the
    block in five ways, and the code after the way in is the same for
    all of them. So the module proves that code once and uses the proof
    for each row. *)

From Glibc Require Import Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  VariadicLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv LibioLogic LibioDefaultXsputnBuf WordString StrchrnulLogic
  StrlenWord FxprintfStream NarrowFormat NarrowArgs DcigettextExit DcigettextPreRules
  FormatterSrc FormatterStringTable FormatterStringArg FormatterStringDispatch FormatterStringRead
  CFrame CStruct CBlocks PrintfLayout PrintfOut PrintfSpec PrintfCopy FormatterNames VaArgRound PrintfLoopState.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic StringVL.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Section next.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (k : Z) (R : Z -> region -> Z * region * Z * Z -> iProp Σ).
Context `{!Callees (loop_callees k R)}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Local Notation blocks := (loop_blocks k R).

(** The block ends a conversion. It needs the state of the loop with
    `c: f` at the last byte of the conversion. *)
Lemma next_body_holds :
  ▷ blocks_hold Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer blocks ⊢
  body_triple Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer "L1150" next_body pl_in pl_vals (next_pre k R) (pl_post k R).
Proof using Type*.
  iIntros "#IH". iModIntro. iIntros ([[bb [fa fc] dq bytes ds0 ap skip xs rest eb] fb wb pre tl ds i n] e Φ) "%He H HK".
  row_simpl. c_env_open He.
  iDestruct "H" as "(((%Hbytes & %Hfit & %Hfb & %Hf8 & %Hfe & %Hn) & %Hne & %Hp) & Hout & Hs & Hfl & Hfc & Hva & #Hargs & Hwork & #Hro)".
  destruct tl as [|c tl]; [done|]. cbn [tail] in Hp. clear Hne.
  iDestruct (word_string_range with "Hs") as %Hfr. cbn [ptr_addr] in Hfr.
  assert (Hlen : length bytes = (length pre + S (length tl))%nat) by (rewrite Hbytes length_app; reflexivity).
  body_start Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer "L1150". step. check "Hfl". load_fmt "Hfl" "Hfc" "Hs". step. check "Hfl". store "Hfl" "Hfc".
  cbn [ptr_add ptr_addr ptr_cap]. unwrap2.
  (* The rest of the format, after the conversion's last byte, is a string of its own for the search. *)
  assert (Hsplit : bytes = (pre ++ [c]) ++ tl) by (rewrite Hbytes -app_assoc; reflexivity).
  iEval (rewrite Hsplit) in "Hs". iDestruct (word_string_borrow_any with "Hs") as (dq') "[Hsuf Hsback]".
  rewrite length_app Nat2Z.inj_add. unfold ptr_add; cbn [ptr_addr ptr_cap length].
  replace (fa + (Z.of_nat (length pre) + Z.of_nat 1)) with (fa + Z.of_nat (length pre) + 1) by lia.
  pose proof (chr_idx_le 37 tl) as Hidx.
  iDestruct (word_string_range with "Hsuf") as %Hsr. cbn [ptr_addr] in Hsr.
  call_callee with (dq', mkPtr (fa + Z.of_nat (length pre) + 1) fc, tl) giving "Hsuf"; [iExact "Hsuf"|].
  iDestruct "Hpost" as "[-> Hsuf]". block_resume.
  check "Hfl". store "Hfl" "Hfc". check "Hfl". load_fmt "Hfl" "Hfc" "Hsuf". step. step. step.
  call_callee with (bb, dq', mkPtr (fa + Z.of_nat (length pre) + 1) fc, tl, _) giving "Hout Hsuf";
    [iFrame "Hout Hsuf"; iPureIntro; unwrap2; lia|].
  iDestruct "Hpost" as "(-> & Hout & Hsuf)". block_resume.
  check "Hfl". load_fmt "Hfl" "Hfc" "Hsuf".
  destruct (lit_run tl ds Hp) as (lit & tl2 & ds' & Htl & Hlit & Htl2 & Hptl & Hfit').
  destruct Htl2 as [-> | [tl' ->]].
  { (* The format ends here, and the function returns. *)
    assert (Hx : (tl ++ [0]) !! chr_idx 37 tl = Some 0) by (rewrite -Hlit Htl; apply byte_after; reflexivity).
    read_byte "Hsuf" (chr_idx 37 tl) 0 Hx. iDestruct ("Hsback" with "Hsuf") as "Hs". rewrite -Hsplit.
    step. branch. step. branch. step. iApply wp_ret_void. iNext. iApply "HK". iFrame "Hout Hs". done. }
  assert (Hx : (tl ++ [0]) !! chr_idx 37 tl = Some 37) by (rewrite -Hlit Htl; apply byte_after; reflexivity).
  read_byte "Hsuf" (chr_idx 37 tl) 37 Hx. iDestruct ("Hsback" with "Hsuf") as "Hs". rewrite -Hsplit.
  step. branch. step.
  call_callee with bb giving "Hout"; [iExact "Hout"|]. iDestruct "Hpost" as (b) "((-> & %Hb) & Hout)". block_resume.
  step. step. step. step. branch_eqn E.
  { clear E. step. iApply wp_ret_void. iNext. iApply "HK". iFrame "Hout Hs". done. }
  clear E.
  goto_block "IH" "HK" 2%nat
    with (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 ap skip xs rest eb) fb wb (pre ++ c :: lit) (37 :: tl') ds' i
            ((n + 1) mod 2 ^ 32)).
  row_simpl. iFrame "Hout Hs Hfl Hva Hargs Hwork Hro". iSplit; [iPureIntro|].
  { pose proof (Z.mod_pos_bound (n + 1) (2 ^ 32) ltac:(lia)).
    split_and!; [rewrite Hbytes Htl -app_assoc; reflexivity | exact (Hfit' _ _ Hfit) | lia..|
                 reflexivity | exact Hptl]. }
  rewrite length_app. cbn [length]. unfold ptr_add; cbn [ptr_addr ptr_cap].
  replace (fa + Z.of_nat (length pre + S (length lit))) with (fa + Z.of_nat (length pre) + 1 + Z.of_nat (chr_idx 37 tl))      by lia.
  iFrame "Hfc".
Qed.

(** Each row for the block `L1150` takes the step into the block and
    uses the body. The step copies one variable, which holds the same
    value on every way in. *)
Lemma next_rows_hold :
  ▷ blocks_hold Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer blocks ⊢ blocks_hold Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer (next_rows k R).
Proof using Type*.
  iIntros "#IH". iPoseProof (next_body_holds with "IH") as "#Hnext".
  repeat iSplit; [| | | | | done]; iModIntro; iIntros (y e from Φ) "%Hfrom %He H HK"; row_simpl; c_env_open He;
    block_enter_from Hfrom;
    (iApply ("Hnext" $! y with "[] [H] HK"); [iPureIntro; row_simpl; c_env_close | row_simpl; iExact "H"]).
Qed.

End next.
