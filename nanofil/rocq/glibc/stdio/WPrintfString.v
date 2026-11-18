(** Hello passes a pointer to its allocated greeting for the wide string
    conversion. The formatter measures the string in wide characters and
    excludes its terminator from the write. Its width test uses only the
    low 32 bits of the difference. A very long greeting can therefore
    request padding even though the format specifies no width. Both paths
    rejoin at the newline, including when a flush accepted a short write. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic VariadicLogic.
From Glibc Require Import Fix OsWorld FileInv LibioLogic LibioCloseSteps CBlocks PrintfSpec
  VaArgRound PrintfLoopState WPrintfDispatch WPrintfLength WPrintfPad WPrintfWrite
  WPrintfParse WPrintfScan WPrintfOut WPrintfSuffix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation reg e n x := (lookup (TAtom n) e = Some x).
Local Abbreviation obj b := (mkPtr b (Obj b)).
Local Abbreviation size xs := (Z.of_nat (length xs)).

Section argument.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (vb : Z) (self : ptr) (E : iProp Σ) `{!WideBufferCalls vb self E}.
Context `{!Defines ge "__wcschrnul" wprintf_chr_fn, !Defines ge "glibc_vfwprintf_internal#__find_specwc.gnu_inline" wprintf_scan_fn,
          !Defines ge "__wprintf_buffer_write" wprintf_write_fn, !Defines ge "__wcslen" wprintf_length_fn,
          !Defines ge "glibc_vfwprintf_internal#__wprintf_buffer_pad" wprintf_pad_inline_fn}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** The writer borrows the text before the terminator. On return the
    caller owns the same complete string, whether or not the stream failed. *)
Local Lemma write_text fr bb br fp dq b r xs Φ :
  call_frame wprintf_write_fn [WPtr (obj bb); WPtr (obj b); WInt (size xs)] = Some fr ->
  0 < b -> b mod 8 = 0 -> b+4*size xs+4 <= r_end r -> r_end r <= 2^63 -> Forall (fun c => 0 < c < 256) xs ->
  wprintf_out vb self E bb br fp -∗ liveq dq b r -∗ bytesq dq b 0 (stage_bytes (xs++[0])) -∗
  ▷ (wprintf_out vb self E bb br fp -∗ liveq dq b r -∗ bytesq dq b 0 (stage_bytes (xs++[0])) -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hb Ha He Hr V. rewrite /stage_bytes flat_map_app /bytesq byte_ps_app ptsq_app.
  iIntros "Ho Hl [Hbs Hz] HK". iApply (wp_wprintf_out_write vb self E _ bb br fp dq b r 0 (Obj b) xs with "Ho Hl Hbs");
    [by rewrite Z.add_0_r|lia|assumption|lia|lia|lia|by left|eapply Forall_impl; [|exact V]; cbn; intros; lia|].
  iNext. iIntros "Ho Hl Hbs". iApply ("HK" with "Ho Hl [$Hbs $Hz]").
Qed.

(** The captured argument instruction recovers the greeting's capability
    from the variadic snapshot. The string remains live through the length
    scan, optional padding, counted write and final literal. *)
Lemma wp_wprintf_string e bb br fp ap fb fr fmt rr dq b r xs Φ :
  wparse_keep e bb ap fb -> reg e "pr.16" (WInt 0) -> reg e "pr.11" (WInt 0) ->
  reg e "pr.82" (WInt 4294967295) -> reg e "pr.62" (WInt 1) -> reg e "pr.67" (WInt 0) -> reg e "pr.47" (WInt 0) ->
  0 < fb -> fb mod 8 = 0 -> fb+8 <= r_end fr -> r_end fr <= 2^63 ->
  0 < b -> b mod 8 = 0 -> b+4*size xs+4 <= r_end r -> r_end r <= 2^63 -> Forall (fun c => 0 < c < 256) xs ->
  wprintf_fmt_ro fmt rr -∗ live fb fr -∗ pcell fb 0 (mkPtr (fmt+8) (Ro fmt)) -∗
  va_at ap 8 [WPtr (mkPtr fmt (Ro fmt)); WPtr (obj b)] -∗ wprintf_out vb self E bb br fp -∗
  liveq dq b r -∗ bytesq dq b 0 (stage_bytes (xs++[0])) -∗
  ▷ (wprintf_out vb self E bb br fp -∗ liveq dq b r -∗ bytesq dq b 0 (stage_bytes (xs++[0])) -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame wprintf_buffer_fn e [] None (Enter (TAtom "L1799") (Some (TAtom "L2165")))) : sexpr) {{ Φ }}.
Proof using Type*.
  intros (Hbb & Hap & Hfb & Hck & Hz) H16 H11 H82 H62 H67 H47 Hf Hfa Hfe Hfr Hb Ha He Hr V.
  iIntros "#Hfmt Hfl Hfc Hva Ho Hl Hbs HK".
  iDestruct (va_at_cur _ 1%nat with "Hva") as "Hva".
  iDestruct (va_cur_ptr _ 1%nat [WPtr (mkPtr fmt (Ro fmt)); WPtr (obj b)] (obj b) eq_refl with "Hva")
    as (cb sb cur) "((-> & %Hc8 & %Hsb & %Hse & %Hsr & %Hcur & %Hround) & Hcur & Hsl & Hqc & _)".
  step. iApply (wp_va_arg_ptr _ _ _ _ _ _ _ _ cb _ cur sb _ 8 (obj b) dq [(PLive b, VLive r)] with "Hcur Hsl Hqc Hl");
    [vx|assumption|assumption|lia|exact Hse|exact Hsr|assumption|exact Hround|cbn; lia|right; eexists _, _; split; by left|].
  iNext. iIntros "_ _ _ Hl". do 4 step. branch_as true. step. step. branch. step. branch. step. step. branch. step.
  iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext.
  iApply (wp_wprintf_length _ dq b r xs with "Hl Hbs"); try assumption; [reflexivity|].
  iNext. iIntros "Hl Hbs". resume. do 4 step. norm. unwrap2. do 3 step. branch_cases.
  Local Ltac write_arg bb br fp dq b r xs :=
    iApply wp_call_bind; [vx|apply defines|reflexivity|]; iNext; norm; unwrap2;
    iApply (write_text _ bb br fp dq b r xs with "Ho Hl Hbs"); [reflexivity|assumption..|];
    iNext; iIntros "Ho Hl Hbs"; resume.
  Local Ltac suffix vb self E bb br fp fb fr fmt rr :=
    iApply (wp_wprintf_suffix vb self E _ _ bb br fp fb fr fmt rr with "Hfmt Hfl Hfc Ho");
    [first [by left|by right]|lk_prove|lk_prove|lk_prove|lk_prove|lk_prove|assumption..|];
    iNext; iIntros "Ho"; by iApply ("HK" with "Ho Hl Hbs").
  - step. step. branch. step. step. step.
    iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext.
    iApply (wp_wprintf_out_pad vb self E _ bb br fp with "Ho"); [reflexivity|apply Z.mod_pos_bound; lia|].
    iNext. iIntros "Ho". resume. step. step. write_arg bb br fp dq b r xs. branch.
    suffix vb self E bb br fp fb fr fmt rr.
  - step. write_arg bb br fp dq b r xs. step. suffix vb self E bb br fp fb fr fmt rr.
Qed.
End argument.
