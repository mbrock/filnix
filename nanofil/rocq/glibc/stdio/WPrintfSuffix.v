(** After printing the greeting, Hello's formatter advances past the s
    and writes the newline. Its last read sees the wide zero. It returns
    without looking at another character or restarting the parser. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import Fix OsWorld FileInv LibioLogic LibioCloseSteps WPrintfDispatch
  WPrintfWrite WPrintfLength WPrintfScan WPrintfParse WPrintfOut.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Abbreviation reg e n x := (lookup (TAtom n) e = Some x).
Local Abbreviation obj b := (mkPtr b (Obj b)).

Section tail.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (vb : Z) (self : ptr) (E : iProp Σ) `{!WideBufferCalls vb self E}.
Context `{!Defines ge "__wcschrnul" wprintf_chr_fn, !Defines ge "glibc_vfwprintf_internal#__find_specwc.gnu_inline" wprintf_scan_fn,
          !Defines ge "__wprintf_buffer_write" wprintf_write_fn}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** Both the padded and unpadded paths end here. Even if a short write
    has marked the buffer failed, the final scan stays inside the literal. *)
Lemma wp_wprintf_suffix e from bb br fp fb fr b fmtreg Φ :
  from = "L1862"%string \/ from = "L1876"%string ->
  reg e "v0" (WPtr (obj bb)) -> reg e "v10" (WPtr (obj fb)) -> reg e "chk3" (WPtr (obj fb)) ->
  reg e "pr.11" (WInt 0) -> reg e "pr.16" (WInt 0) ->
  0 < fb -> fb mod 8 = 0 -> fb+8 <= r_end fr -> r_end fr <= 2^63 ->
  wprintf_fmt_ro b fmtreg -∗ live fb fr -∗ pcell fb 0 (mkPtr (b+8) (Ro b)) -∗ wprintf_out vb self E bb br fp -∗
  ▷ (wprintf_out vb self E bb br fp -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame wprintf_buffer_fn e [] None (Enter (TAtom "L1131") (Some (TAtom from)))) : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfrom H0 H10 Hck H11 H16 Hfb Hfa Hfe Hfr. iIntros "#Hfmt Hl Hc Ho HK".
  iPoseProof "Hfmt" as "((%Hg & %Hb & %Ha & %He & %Hr) & #Hbl & #Hbs)".
  iApply wp_enter; [reflexivity|destruct Hfrom as [-> | ->]; vx|]. iNext. cbn [b_insts b_jump]. step.
  Local Ltac load_saved := check "Hl"; load_pointer_dq "Hl Hc Hbl" by a2; iNext; iIntros "Hl Hc _".
  load_saved. step. check "Hl". store "Hl" "Hc". norm. unwrap2. replace (b+8+4) with (b+12) by lia.
  iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext.
  iApply (wp_wprintf_scan _ b fmtreg true with "Hfmt"); [apply defines|reflexivity|]. iNext. resume.
  check "Hl". store "Hl" "Hc". load_saved. do 3 step. norm. unwrap2.
  replace (b+16-(b+12)) with 4 by lia. step. closed_ints.
  iDestruct (wchar_at _ _ 0 wprintf_format 3%nat 10 ltac:(reflexivity) with "Hbs") as "[#Hnl _]".
  iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext.
  iApply (wp_wprintf_out_write vb self E _ bb br fp DfracDiscarded b fmtreg 12 (Ro b) [10] with "Ho Hbl Hnl");
    [reflexivity|lia|assumption|lia|cbn; lia|lia|by right|repeat constructor; lia|].
  iNext. iIntros "Ho _ _". resume. load_saved.
  iDestruct (wchar_at _ _ 0 wprintf_format 4%nat 0 ltac:(reflexivity) with "Hbs") as "[#Hz _]".
  check_read_dq "Hbl" by a2. iNext. iIntros "_". load_bytes_dq "Hbl Hz" decode (reflexivity) by a2. iNext. iIntros "_ _".
  step. branch. step. branch. step. iApply wp_ret_void. iNext. by iApply "HK".
Qed.
End tail.
