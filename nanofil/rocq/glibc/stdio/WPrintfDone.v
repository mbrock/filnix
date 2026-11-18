(** Finishing a wide print flushes the last characters, even when the array
    is only partly full. The count routine then returns an int. If the
    stream has failed, it returns minus one; if the count overflows, it
    also stores EOVERFLOW in errno. Neither path needs another buffer. *)

From Glibc Require Import HelloImageTypedWP.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import CodePrelude Fix OsBlocks OsWorld
  FileInv LibioLogic LibioCloseSteps LibioPutsInv LibioWIdle DcigettextExit PrintfOut WPrintfFileFlush WPrintfDispatch.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Definition wprintf_count_fn := hello_image_fn___wprintf_buffer_done.
Definition wprintf_file_done_fn := hello_image_fn___wprintf_buffer_to_file_done.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Section done.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb)))
  (Hge : lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb))).

(** Hello uses the return value as an int. The count check can take either
    branch without changing the buffer, so the caller need not bound the
    total number of characters written to the stream. *)
Lemma wp_wprintf_count fr bb br fp cs written active Φ :
  call_frame wprintf_count_fn [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  wide_stage bb br fp cs written active -∗ errno_any eb -∗
  ▷ (∀ r, ⌜0 <= r < 2^32⌝ -∗ wide_stage bb br fp cs written active -∗ errno_any eb -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr. injection Hfr as <-.
  iIntros "(%tail & %slots & %H & Hl & Hbase & Hcur & Hstop & Hw & Hm & Hfp & Hbs & Ha) Herr HK".
  pose proof H as (Hbb & Hal & Hend & Hreg & Hwr & Hvalid & Hlen & _).
  step. step. check "Hl". load_mode "Hl" "Hm". step. destruct active; branch; step.
  - step. check "Hl". load_self_using wp_raw_load_pointer_self "Hl Hcur". check "Hl".
    load_self_using wp_raw_load_pointer_self "Hl Hbase". do 5 step.
    iApply (wp_raw_load with "Hl Hw"); [reflexivity | vx | reflexivity | a2 |]. iNext. iIntros "Hl Hw".
    step_named. do 7 step. branch_cases; step.
    + step. iApply wp_ret; [reflexivity|vx|]. iNext. iApply ("HK" with "[%] [-Herr] Herr");
        [apply Z.mod_pos_bound; lia | iExists tail, slots; by iFrame].
    + step_global Hge. iApply (wp_dci_errno_check eb Herr); [vx|]. iNext.
      iDestruct "Herr" as (es eslots [Hes Hslots]) "Hps". iEval (rewrite pts_app) in "Hps".
      iDestruct "Hps" as "[Hes Hea]". iApply (wp_dci_errno_store eb Herr with "Hes"); [vx|vx|exact Hes|].
      iNext. iIntros "Hes". iApply wp_ret; [reflexivity|vx|]. iNext.
      iApply ("HK" $! 4294967295 with "[%] [-Hes Hea] [Hes Hea]"); [lia | iExists tail, slots; by iFrame |].
      iExists (le_bytes 75 4), eslots. rewrite pts_app. iFrame. done.
  - iApply wp_ret; [reflexivity|vx|]. iNext. iApply ("HK" $! 4294967295 with "[%] [-Herr] Herr");
      [lia | iExists tail, slots; by iFrame].
Qed.

Context (vb : Z) (self : ptr) (E : iProp Σ)
  (Hfn : ge_fn ge "__GI__IO_wfile_xsputn" wprintf_xsputn_fn)
  (Hcall : wprintf_xsputn_call_spec vb self E)
  (Hflush : find_fn ge (TAtom "__wprintf_buffer_flush_to_file") = Some (Defined wprintf_file_flush_fn))
  (Hcount : find_fn ge (TAtom "__wprintf_buffer_done") = Some (Defined wprintf_count_fn)).

(** The final flush and the count may both write errno. They borrow the
    same cell in succession rather than requiring the caller to supply it twice. *)
Lemma wp_wprintf_file_done fr bb br fp vreg cs written active Φ :
  call_frame wprintf_file_done_fn [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  (E ⊢ errno_any eb ∗ (errno_any eb -∗ E)) ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗ file_wide ge vb self fp 1 -∗ E -∗
  wide_stage bb br fp cs written active -∗
  ▷ (∀ cs' written' active' r, ⌜0 <= r < 2^32⌝ -∗ file_wide ge vb self fp 1 -∗ E -∗
    wide_stage bb br fp cs' written' active' -∗ Φ (Ret (WInt r))) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hlend. injection Hfr as <-.
  iIntros "#Hvt #Hwv HF HE (%tail & %slots & %H & Hl & Hbase & Hcur & Hstop & Hw & Hm & Hfp & Hbs & Ha) HK".
  pose proof H as (Hbb & Hal & Hend & Hreg & _).
  step. step. check "Hl". load_mode "Hl" "Hm". step. destruct active; branch; step.
  - iApply wp_call_bind; [vx | exact Hflush | reflexivity |]. iNext.
    iApply (wp_wprintf_stage_flush vb self E Hfn Hcall with "Hvt Hwv HF HE [Hl Hbase Hcur Hstop Hw Hm Hfp Hbs Ha]");
      [reflexivity | iExists tail, slots; iFrame; done |]. iNext. iIntros (ok) "HF HE Hstage". resume.
    iDestruct (Hlend with "HE") as "[Herr Hback]". iApply wp_call_bind; [vx | exact Hcount | reflexivity |]. iNext.
    iApply (wp_wprintf_count with "Hstage Herr"); [reflexivity |]. iNext. iIntros (r Hr) "Hstage Herr".
    resume. iApply wp_ret; [reflexivity|vx|]. iNext. rewrite !Z.mod_mod; try lia. rewrite (Z.mod_small r (2^32) Hr).
    iApply ("HK" with "[%] HF [Hback Herr] Hstage"); [exact Hr | by iApply "Hback"].
  - iApply wp_ret; [reflexivity|vx|]. iNext. iApply ("HK" $! cs written false 4294967295 with "[%] HF HE [-]");
      [lia | iExists tail, slots; by iFrame].
Qed.
End done.
