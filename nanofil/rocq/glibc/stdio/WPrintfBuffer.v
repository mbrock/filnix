(** Hello calls the wide formatter with one conversion and a final
    newline. This proof runs the formatter from its entry to its return.
    It uses the built-in conversion tables because Hello has registered
    no handlers of its own. *)

From Glibc Require FixVariadic.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic VariadicLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv LibioLogic LibioCloseSteps PrintfSpec PrintfLoopState
  DcigettextExit DcigettextPreRules WPrintfDispatch WPrintfLength WPrintfPad WPrintfWrite WPrintfParse
  WPrintfScan WPrintfString WPrintfOut.
From Glibc Require Import WideBytes.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic LibioCloseSteps OsWorld FixVariadic.VL0.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Abbreviation obj b := (mkPtr b (Obj b)).
Local Abbreviation size xs := (Z.of_nat (length xs)).

Section format.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (vb : Z) (self : ptr) (E : iProp Σ) `{!WideBufferCalls vb self E}.
Context `{!Defines ge "__wcschrnul" wprintf_chr_fn, !Defines ge "glibc_vfwprintf_internal#__find_specwc.gnu_inline" wprintf_scan_fn,
          !Defines ge "__wprintf_buffer_write" wprintf_write_fn, !Defines ge "__wcslen" wprintf_length_fn,
          !Defines ge "glibc_vfwprintf_internal#__wprintf_buffer_pad" wprintf_pad_inline_fn,
          !Defines ge "glibc_vfwprintf_internal#__wprintf_buffer_has_failed" wprintf_failed_fn}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

Local Ltac alloc b H := iApply wp_alloc; [vm_compute; reflexivity|vm_compute; congruence|vm_compute; congruence|
  intros ? ? ? ? Hfresh Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hfresh Hw)|]; iNext; iIntros (b H) "Hobj".

(** The caller lends errno for the entry load and gets the whole source
    string back. The formatter never needs an upper bound of INT_MAX on
    the number of wide characters in that string. *)
Lemma wp_wprintf_buffer fr bb br fp fmt rr ap dq b r xs eb Φ :
  call_frame wprintf_buffer_fn [WPtr (obj bb); WPtr (mkPtr fmt (Ro fmt)); WPtr ap; WInt 0] = Some fr ->
  ow_errno w0 = Some (obj eb) -> lookup (TAtom "__libc_errno") (ge_globals ge) = Some (obj eb) ->
  (E ⊢ errno_any eb ∗ (errno_any eb -∗ E)) ->
  0 < b -> b mod 8 = 0 -> b+4*size xs+4 <= r_end r -> r_end r <= 2^63 -> Forall (fun c => 0 < c < 256) xs ->
  wprintf_fmt_ro fmt rr -∗ wprintf_tables_ro -∗ printf_ro -∗
  va_at ap 8 [WPtr (mkPtr fmt (Ro fmt)); WPtr (obj b)] -∗ wprintf_out vb self E bb br fp -∗
  liveq dq b r -∗ bytesq dq b 0 (stage_bytes (xs++[0])) -∗
  ▷ (wprintf_out vb self E bb br fp -∗ liveq dq b r -∗ bytesq dq b 0 (stage_bytes (xs++[0])) -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Herr Hge Hlend Hb Ha He Hr V. injection Hfr as <-. iIntros "#Hfmt #Ht #Hro Hva Ho Hl Hb HK". step.
  alloc fb Hfb. change (0 < fb /\ fb mod 16 = 0 /\ fb+16 <= 2^48) in Hfb. destruct Hfb as (Hfb & Hf16 & Hfe).
  iDestruct (obj_zero_block with "Hobj") as "(Hfl & Hxs & Has)"; [compute; discriminate|].
  iAssert (live fb (mkRegion fb (fb+16) Heap Live)) with "Hfl" as "Hfl".
  iDestruct (zero_cell_prefix fb 0 8 with "Hxs Has") as "(Hfc & _ & _)".
  alloc wb Hwb. iClear "Hobj". alloc cb Hcb. change (0 < cb /\ cb mod 16 = 0 /\ cb+32 <= 2^48) in Hcb.
  destruct Hcb as (Hcb & Hc16 & Hce). iDestruct (obj_zero_block with "Hobj") as "(Hcl & Hxs & Has)"; [compute; discriminate|].
  iAssert (live cb (mkRegion cb (cb+32) Heap Live)) with "Hcl" as "Hcl".
  iDestruct (zero_cell_prefix cb 0 24 with "Hxs Has") as "(Hcc & _ & _)".
  do 6 (let x := fresh in let Hx := fresh in alloc x Hx; clear Hx; iClear "Hobj").
  step_global Hge. iApply (wp_dci_errno_check eb Herr); [vx|]. iNext.
  iDestruct "Ho" as "(Hvt & HF & HE & Hstage)". iDestruct (Hlend with "HE") as "[Herr Hback]".
  iDestruct "Herr" as (bs caps [L C]) "Hps". iEval (rewrite pts_app) in "Hps". iDestruct "Hps" as "[Heb Hea]".
  iApply (wp_dci_errno_load eb Herr with "Heb"); [vx|exact L|]. iNext. iIntros "Heb".
  iAssert (wprintf_out vb self E bb br fp) with "[Hvt HF Hback Heb Hea Hstage]" as "Ho".
  { iFrame "Hvt HF Hstage". iApply "Hback". iExists bs, caps. rewrite pts_app. iFrame. done. }
  iDestruct (va_at_cursor with "Hva") as (ab sb) "((-> & %Hab & %Ha8 & %Hae & %Hsb & %Hse & _) & Hal & Hac & Hsl & Hva)".
  step. check "Hal". load_pointer_dq "Hal Hac Hsl" by a2. iNext. iIntros "Hal Hac Hsl".
  iDestruct ("Hva" with "Hal Hac Hsl") as "Hva".
  assert (Hc8 : cb mod 8 = 0) by (Z.div_mod_to_equations; lia). assert (Hf8 : fb mod 8 = 0) by (Z.div_mod_to_equations; lia).
  check "Hcl". store "Hcl" "Hcc". iClear "Hcl Hcc".
  iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext.
  iApply (wp_wprintf_scan _ fmt rr false with "Hfmt"); [apply defines|by rewrite Z.add_0_r|]. iNext. resume.
  rewrite Z.add_0_r. check "Hfl". store "Hfl" "Hfc". do 3 step. norm. rewrite Z.sub_diag. step. closed_ints.
  iPoseProof "Hfmt" as "((%Hg & %Hfmt & %Hfmt8 & %Hfmte & %Hfmtr) & #Hbl & #Hbs)".
  iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext.
  iApply (wp_wprintf_out_write vb self E _ bb br fp DfracDiscarded fmt rr 0 (Ro fmt) [] with "Ho Hbl []");
    [by rewrite Z.add_0_r|lia|assumption|lia|cbn; lia|lia|by right|constructor|by rewrite /bytesq /ptsq big_sepL_nil|].
  iNext. iIntros "Ho _ _". resume. iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext.
  iApply (wp_wprintf_out_failed vb self E with "Ho"); [reflexivity|]. iNext. iIntros (failed) "Ho". resume. step.
  destruct failed; branch; step. { iApply wp_ret_void. iNext. by iApply ("HK" with "Ho Hl Hb"). }
  check "Hfl". load_pointer_dq "Hfl Hfc Hbl" by a2. iNext. iIntros "Hfl Hfc _".
  iDestruct (wchar_at _ _ 0 wprintf_format 0%nat 37 ltac:(reflexivity) with "Hbs") as "[#Hpc _]".
  check_read_dq "Hbl" by a2. iNext. iIntros "_". load_bytes_dq "Hbl Hpc" decode (reflexivity) by a2. iNext. iIntros "_ _".
  step. branch. iPoseProof "Hro" as "(_ & _ & _ & _ & Hn1 & Hn2 & Hn3)".
  Local Ltac read_null res := let g := fresh in let gr := fresh in let Hg := fresh in
    let B := fresh in let A := fresh in let F := fresh in let R := fresh in
    iDestruct res as (g gr (Hg & B & A & F & R)) "[#Hnl #Hnc]";
    step; step_global Hg; check_read_dq "Hnl" by a2; iNext; iIntros "_";
    iApply (wp_raw_load_pointer_dq with "Hnl Hnc []"); [reflexivity|vx|left; reflexivity|a2|a2|cbn; lia|done|];
    iNext; iIntros "_ _ _"; iClear "Hnl Hnc".
  read_null "Hn1". do 3 step. branch. read_null "Hn2". do 4 step. branch. read_null "Hn3". do 4 step. branch.
  iApply (wp_wprintf_parse _ bb (obj ab) fb _ wb fmt rr with "Hfmt Ht Hfl Hfc");
    [unfold wparse_keep; repeat split; reflexivity|reflexivity|reflexivity|assumption|assumption|cbn; lia|cbn; lia|].
  iNext. iIntros (e' (K & R16 & R11 & R82 & R62 & R67 & R47)) "Hfl Hfc".
  iApply (wp_wprintf_string vb self E with "Hfmt Hfl Hfc Hva Ho Hl Hb HK"); first [assumption|cbn; lia].
  Unshelve. all: first [exact DfracDiscarded|exact (mkRegion 0 0 Heap Live)].
Qed.
End format.
