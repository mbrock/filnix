(** When status is zero, error attempts to print a report and then returns
    with the previous cancellation setting. This proof follows the control
    flow from message printing to return. The printing functions themselves
    still need separate proofs.

    The caller must reconnect the resources returned by message handling
    to the resources lent to the remaining calls. That exchange accounts
    for errno ownership on both successful and failed formatter paths. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps SysWrappers
  PrintfStateCode ErrorCode ErrorEntry ErrorText ErrorTextTail ErrorMessage Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic OsWorld SysWrappers.
Open Scope Z_scope.

Section report.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (tb : Z) (treg : region) (old : Z)
  (sb : Z) (sreg : region) (fb : Z) (dq : dfrac) (freg : region)
  (newline : ptr) (newlinefn : func) (newlineframe : frame) (flushfn : func) (flushframe : frame)
  (R S Q T E : iProp Σ).
Context (Hold : old = 0 \/ old = 1) (Hself : ow_self w0 = mkPtr tb (Obj tb))
  (Htb : 0 < tb) (Hta : tb mod 8 = 0) (Hte : tb + 796 <= r_end treg) (Htr : r_end treg <= 2 ^ 63)
  (Hcancel : find_fn ge (TAtom "__GI___pthread_setcancelstate") = Some (Defined glibc___pthread_setcancelstate))
  (Hgstderr : lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr sb (Obj sb)))
  (Hsb : 0 < sb) (Hsa : sb mod 8 = 0) (Hse : sb + 8 <= r_end sreg) (Hsr : r_end sreg <= 2 ^ 63)
  (Hptr : 0 <= fb < 2 ^ 64)
  (Hnewline : lookup (TAtom "glibc_error#str.254") (ge_globals ge) = Some newline)
  (Hfx : find_fn ge (TAtom "__fxprintf") = Some (Defined newlinefn))
  (Hfxframe : call_frame newlinefn [WPtr null;WPtr newline] = Some newlineframe)
  (Hflush : find_fn ge (TAtom "__GI__IO_fflush") = Some (Defined flushfn))
  (Hfframe : call_frame flushfn [WPtr (mkPtr fb (Obj fb))] = Some flushframe).
Context (Hfxcall : ⊢ R -∗ WP (ERun newlineframe : gexpr)
    {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ S }})
  (Hflushcall : ⊢ liveq dq fb freg -∗ S -∗
    WP (ERun flushframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ liveq dq fb freg ∗ Q }}).
Context (eb : Z) (ereg : region) (wide : ptr) (widefn : func) (wideframe : frame)
  (V : ptr -> iProp Σ) (P : iProp Σ) (U : Z -> Z -> Z -> iProp Σ).
Context (Hwide : lookup (TAtom "glibc_error#str.253") (ge_globals ge) = Some wide)
  (Hwidefn : find_fn ge (TAtom "__GI_fputws_unlocked") = Some (Defined widefn))
  (Hwideframe : call_frame widefn [WPtr wide;WPtr (mkPtr fb (Obj fb))] = Some wideframe)
  (Hwidecall : forall r en md, 0 < md < 2 ^ 31 -> ⊢ liveq dq fb freg -∗ int_cell fb 192 md -∗
    (live eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ U r en md) -∗
    WP (ERun wideframe : gexpr) {{ v, ∃ result, ⌜v = Ret (WInt result)⌝ ∗ liveq dq fb freg ∗
      int_cell fb 192 md ∗ (live eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ U r en md) }})
  (Hexchange : forall r en md, error_message_returned fb freg eb ereg r en md ∗ U r en md ⊢ R).

(** Error prints the message, optional errno text and a newline on the same
    stream. Each call returns the stream before the next call uses it.
    The caller must supply what the next call needs. *)
Lemma wp_error_report_zero_loans (RP RQ : iProp Σ)
    (Hexchange_text : forall r en md, error_message_returned fb freg eb ereg r en md ∗ U r en md ⊢ RP)
    (Hnewline_loan : ⊢ live sb sreg -∗ pcell sb 0 (mkPtr fb (Obj fb)) -∗ liveq dq fb freg -∗ R -∗
      WP (ERun newlineframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
        live sb sreg ∗ pcell sb 0 (mkPtr fb (Obj fb)) ∗ liveq dq fb freg ∗ S }})
    e from errnum fmt ap mode cb nb nreg count
    textfmt strerrorfn formatter formatterframe (borrowed : ptr -> iProp Σ) Φ :
  error_inputs e 0 errnum fmt ap mode cb -> 0 <= errnum < 2 ^ 32 ->
  lookup (TAtom "error_message_count") (ge_globals ge) = Some (mkPtr nb (Obj nb)) ->
  0 < nb -> nb + 4 <= r_end nreg -> r_end nreg <= 2 ^ 63 ->
  lookup (TAtom "glibc_error#str.252") (ge_globals ge) = Some textfmt ->
  find_fn ge (TAtom "__GI___strerror_r") = Some (Defined strerrorfn) ->
  (forall b, exists fr, call_frame strerrorfn [WInt errnum;WPtr (mkPtr b (Obj b));WInt 1024] = Some fr /\
    (⊢ obj b (heap_req 4 1024) -∗ RP -∗ WP (ERun fr : gexpr)
      {{ v, ∃ p, ⌜v = Ret (WPtr p)⌝ ∗ error_text_buffer borrowed b p ∗ T }})) ->
  (forall b p, exists fr, call_frame newlinefn [WPtr null;WPtr textfmt;WPtr p] = Some fr /\
    (⊢ live sb sreg -∗ pcell sb 0 (mkPtr fb (Obj fb)) -∗ liveq dq fb freg -∗
      error_text_buffer borrowed b p -∗ T -∗ WP (ERun fr : gexpr)
      {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ live sb sreg ∗ pcell sb 0 (mkPtr fb (Obj fb)) ∗
        liveq dq fb freg ∗ error_text_buffer borrowed b p ∗ RQ }})) ->
  ((if decide (errnum = 0) then RP else RQ) ⊢ R) ->
  find_fn ge (TAtom "__vfxprintf") = Some (Defined formatter) ->
  call_frame formatter [WPtr (mkPtr fb (Obj fb));WPtr fmt;WPtr ap;WInt (mode mod 2 ^ 32)] = Some formatterframe ->
  (⊢ liveq dq fb freg -∗ V ap -∗ P -∗ WP (ERun formatterframe : gexpr)
    {{ v, ∃ r en md, ⌜v = Ret (WInt r)⌝ ∗ liveq dq fb freg ∗ V ap ∗
      error_message_pending fb freg eb ereg r en md ∗ U r en md }}) ->
  live nb nreg -∗ int_cell nb 0 count -∗
  live tb treg -∗ int_cell tb 792 1 -∗
  live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
  live sb sreg -∗ pcell sb 0 (mkPtr fb (Obj fb)) -∗ liveq dq fb freg -∗ V ap -∗ P -∗ E -∗
  (live nb nreg -∗ int_cell nb 0 ((count + 1) mod 2 ^ 32) -∗ error_text_scratch borrowed errnum -∗
    live tb treg -∗ int_cell tb 792 old -∗
    live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
    live sb sreg -∗ pcell sb 0 (mkPtr fb (Obj fb)) -∗ liveq dq fb freg -∗ V ap -∗ Q -∗ E -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc_error_internal e [] None
    (Enter (TAtom "iw_2.start") (Some from))) : gexpr) {{ Φ }}.
Proof using Hcancel Hext Hfframe Hflush Hflushcall Hfx Hfxframe Hgstderr Hnewline Hold Hptr Hreg Hsa Hsb Hse Hself Hsr Hta Htb Hte Htr Hwide Hwidecall Hwidefn Hwideframe.
  intros Hinputs Herr Hcount Hnb Hne Hnr Htext Hstr Hstrcall Htextcall Hready Hfmtfn Hfmtframe Hformat.
  iIntros "Hnl Hcount Ht Hflag Hcl Hsaved Hsl Hsp Hfl HV HP HE HK".
  iApply (wp_error_message (dqe := DfracOwn 1) _ _ 0 errnum fmt ap mode cb sb sreg fb freg dq eb ereg
    formatter formatterframe wide widefn wideframe V P U
    (live nb nreg ∗ int_cell nb 0 count ∗ live tb treg ∗ int_cell tb 792 1 ∗
      live cb (mkRegion cb (cb + 16) Heap Live) ∗ int_cell cb 0 old ∗ E)%I
    with "Hsl Hsp Hfl HV HP [$Hnl $Hcount $Ht $Hflag $Hcl $Hsaved $HE]"); try assumption.
  iIntros (e' predecessor r en md Hinputs') "Hsl Hsp Hfl HV Hfields HU (Hnl & Hcount & Ht & Hflag & Hcl & Hsaved & HE)".
  iDestruct (Hexchange_text r en md with "[$Hfields $HU]") as "HR".
  iApply (wp_error_text_tail_zero_loans Hreg Hext tb treg old sb sreg (mkPtr fb (Obj fb)) dq freg
    newline newlinefn newlineframe flushfn flushframe R S Q T (V ap ∗ E)%I
    with "Hnl Hcount Ht Hflag Hcl Hsaved Hsl Hsp Hfl HR [$HV $HE]"); try eassumption.
  iIntros "Hnl Hcount Hscratch Ht Hflag Hcl Hsaved Hsl Hsp Hfl HQ [HV HE]".
  iApply ("HK" with "Hnl Hcount Hscratch Ht Hflag Hcl Hsaved Hsl Hsp Hfl HV HQ HE").
Qed.

(** The formatter receives and returns ownership tied to the same ap.
    Its result may be negative, and neither fallback nor subsequent
    printing is required to succeed. The prefix remains outside this rule. *)
Lemma wp_error_report_zero_loan
    (Hnewline_loan : ⊢ live sb sreg -∗ pcell sb 0 (mkPtr fb (Obj fb)) -∗ liveq dq fb freg -∗ R -∗
      WP (ERun newlineframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
        live sb sreg ∗ pcell sb 0 (mkPtr fb (Obj fb)) ∗ liveq dq fb freg ∗ S }})
    e from errnum fmt ap mode cb nb nreg count
    textfmt strerrorfn formatter formatterframe (borrowed : ptr -> iProp Σ) Φ :
  error_inputs e 0 errnum fmt ap mode cb -> 0 <= errnum < 2 ^ 32 ->
  lookup (TAtom "error_message_count") (ge_globals ge) = Some (mkPtr nb (Obj nb)) ->
  0 < nb -> nb + 4 <= r_end nreg -> r_end nreg <= 2 ^ 63 ->
  lookup (TAtom "glibc_error#str.252") (ge_globals ge) = Some textfmt ->
  find_fn ge (TAtom "__GI___strerror_r") = Some (Defined strerrorfn) ->
  (forall b, exists fr, call_frame strerrorfn [WInt errnum;WPtr (mkPtr b (Obj b));WInt 1024] = Some fr /\
    (⊢ obj b (heap_req 4 1024) -∗ R -∗ WP (ERun fr : gexpr)
      {{ v, ∃ p, ⌜v = Ret (WPtr p)⌝ ∗ error_text_buffer borrowed b p ∗ T }})) ->
  (forall b p, exists fr, call_frame newlinefn [WPtr null;WPtr textfmt;WPtr p] = Some fr /\
    (⊢ error_text_buffer borrowed b p -∗ T -∗ WP (ERun fr : gexpr)
      {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ error_text_buffer borrowed b p ∗ R }})) ->
  find_fn ge (TAtom "__vfxprintf") = Some (Defined formatter) ->
  call_frame formatter [WPtr (mkPtr fb (Obj fb));WPtr fmt;WPtr ap;WInt (mode mod 2 ^ 32)] = Some formatterframe ->
  (⊢ liveq dq fb freg -∗ V ap -∗ P -∗ WP (ERun formatterframe : gexpr)
    {{ v, ∃ r en md, ⌜v = Ret (WInt r)⌝ ∗ liveq dq fb freg ∗ V ap ∗
      error_message_pending fb freg eb ereg r en md ∗ U r en md }}) ->
  live nb nreg -∗ int_cell nb 0 count -∗
  live tb treg -∗ int_cell tb 792 1 -∗
  live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
  live sb sreg -∗ pcell sb 0 (mkPtr fb (Obj fb)) -∗ liveq dq fb freg -∗ V ap -∗ P -∗ E -∗
  (live nb nreg -∗ int_cell nb 0 ((count + 1) mod 2 ^ 32) -∗ error_text_scratch borrowed errnum -∗
    live tb treg -∗ int_cell tb 792 old -∗
    live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
    live sb sreg -∗ pcell sb 0 (mkPtr fb (Obj fb)) -∗ liveq dq fb freg -∗ V ap -∗ Q -∗ E -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc_error_internal e [] None
    (Enter (TAtom "iw_2.start") (Some from))) : gexpr) {{ Φ }}.
Proof using Hcancel Hexchange Hext Hfframe Hflush Hflushcall Hfx Hfxframe Hgstderr Hnewline Hold Hptr Hreg Hsa Hsb Hse Hself Hsr Hta Htb Hte Htr Hwide Hwidecall Hwidefn Hwideframe.
  intros Hinputs Herr Hcount Hnb Hne Hnr Htext Hstr Hstrcall Htextcall Hfmtfn Hfmtframe Hformat.
  iIntros "Hnl Hcount Ht Hflag Hcl Hsaved Hsl Hsp Hfl HV HP HE HK".
  iApply (wp_error_report_zero_loans R R Hexchange Hnewline_loan with
    "Hnl Hcount Ht Hflag Hcl Hsaved Hsl Hsp Hfl HV HP HE HK"); try eassumption.
  { intros b p. destruct (Htextcall b p) as (fr & Hframe & Hcall).
    exists fr. split; [done |]. iIntros "Hsl Hsp Hfl Hb HT".
    iApply (wp_wand with "[Hb HT]"); [iApply (Hcall with "Hb HT") |].
    iIntros (v) "H". iDestruct "H" as (r ->) "[Hb HR]". iExists r. iFrame. done. }
  destruct (decide (errnum = 0)); done.
Qed.

(** A caller whose newline contract leaves stderr untouched can still
    use the original report rule. The loan is then just a frame. *)
Lemma wp_error_report_zero e from errnum fmt ap mode cb nb nreg count
    textfmt strerrorfn formatter formatterframe (borrowed : ptr -> iProp Σ) Φ :
  error_inputs e 0 errnum fmt ap mode cb -> 0 <= errnum < 2 ^ 32 ->
  lookup (TAtom "error_message_count") (ge_globals ge) = Some (mkPtr nb (Obj nb)) ->
  0 < nb -> nb + 4 <= r_end nreg -> r_end nreg <= 2 ^ 63 ->
  lookup (TAtom "glibc_error#str.252") (ge_globals ge) = Some textfmt ->
  find_fn ge (TAtom "__GI___strerror_r") = Some (Defined strerrorfn) ->
  (forall b, exists fr, call_frame strerrorfn [WInt errnum;WPtr (mkPtr b (Obj b));WInt 1024] = Some fr /\
    (⊢ obj b (heap_req 4 1024) -∗ R -∗ WP (ERun fr : gexpr)
      {{ v, ∃ p, ⌜v = Ret (WPtr p)⌝ ∗ error_text_buffer borrowed b p ∗ T }})) ->
  (forall b p, exists fr, call_frame newlinefn [WPtr null;WPtr textfmt;WPtr p] = Some fr /\
    (⊢ error_text_buffer borrowed b p -∗ T -∗ WP (ERun fr : gexpr)
      {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ error_text_buffer borrowed b p ∗ R }})) ->
  find_fn ge (TAtom "__vfxprintf") = Some (Defined formatter) ->
  call_frame formatter [WPtr (mkPtr fb (Obj fb));WPtr fmt;WPtr ap;WInt (mode mod 2 ^ 32)] = Some formatterframe ->
  (⊢ liveq dq fb freg -∗ V ap -∗ P -∗ WP (ERun formatterframe : gexpr)
    {{ v, ∃ r en md, ⌜v = Ret (WInt r)⌝ ∗ liveq dq fb freg ∗ V ap ∗
      error_message_pending fb freg eb ereg r en md ∗ U r en md }}) ->
  live nb nreg -∗ int_cell nb 0 count -∗
  live tb treg -∗ int_cell tb 792 1 -∗
  live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
  live sb sreg -∗ pcell sb 0 (mkPtr fb (Obj fb)) -∗ liveq dq fb freg -∗ V ap -∗ P -∗ E -∗
  (live nb nreg -∗ int_cell nb 0 ((count + 1) mod 2 ^ 32) -∗ error_text_scratch borrowed errnum -∗
    live tb treg -∗ int_cell tb 792 old -∗
    live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
    live sb sreg -∗ pcell sb 0 (mkPtr fb (Obj fb)) -∗ liveq dq fb freg -∗ V ap -∗ Q -∗ E -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc_error_internal e [] None
    (Enter (TAtom "iw_2.start") (Some from))) : gexpr) {{ Φ }}.
Proof using Hcancel Hexchange Hext Hfframe Hflush Hflushcall Hfx Hfxcall Hfxframe Hgstderr Hnewline Hold Hptr Hreg Hsa Hsb Hse Hself Hsr Hta Htb Hte Htr Hwide Hwidecall Hwidefn Hwideframe.
  intros Hinputs Herr Hcount Hnb Hne Hnr Htext Hstr Hstrcall Htextcall Hfmtfn Hfmtframe Hformat.
  iIntros "Hnl Hcount Ht Hflag Hcl Hsaved Hsl Hsp Hfl HV HP HE HK".
  iApply (wp_error_report_zero_loan with "Hnl Hcount Ht Hflag Hcl Hsaved Hsl Hsp Hfl HV HP HE HK"); try assumption.
  iIntros "Hsl Hsp Hr HR". iApply (wp_wand with "[HR]"); [iApply (Hfxcall with "HR") |].
  iIntros (v) "H". iDestruct "H" as (r ->) "HS". iExists r. iFrame. done.
  all: try eassumption.
Qed.
End report.
