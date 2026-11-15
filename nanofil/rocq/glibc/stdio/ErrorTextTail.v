(** When status is zero, error counts the message, prints any errno text,
    and returns after restoring cancellation. This proof joins the counting
    and printing steps to the returning tail.

    The caller keeps the new strerror buffer and any borrowed text until
    return. Earlier message output, printing, and flushing stderr still
    require separate proofs. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps SysWrappers
  PrintfStateCode ErrorCode ErrorEntry ErrorTail ErrorText Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic OsWorld SysWrappers.
Open Scope Z_scope.

Section returning.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (tb : Z) (treg : region) (old : Z)
  (sb : Z) (sreg : region) (stderr : ptr) (dq : dfrac) (rreg : region)
  (newline : ptr) (newlinefn : func) (newlineframe : frame) (flushfn : func) (flushframe : frame)
  (R S Q T E : iProp Σ).
Context (Hold : old = 0 \/ old = 1) (Hself : ow_self w0 = mkPtr tb (Obj tb))
  (Htb : 0 < tb) (Hta : tb mod 8 = 0) (Hte : tb + 796 <= r_end treg) (Htr : r_end treg <= 2 ^ 63)
  (Hcancel : find_fn ge (TAtom "__GI___pthread_setcancelstate") = Some (Defined glibc___pthread_setcancelstate))
  (Hgstderr : lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr sb (Obj sb)))
  (Hsb : 0 < sb) (Hsa : sb mod 8 = 0) (Hse : sb + 8 <= r_end sreg) (Hsr : r_end sreg <= 2 ^ 63)
  (Hptr : 0 <= ptr_addr stderr < 2 ^ 64)
  (Hnewline : lookup (TAtom "glibc_error#str.254") (ge_globals ge) = Some newline)
  (Hfx : find_fn ge (TAtom "__fxprintf") = Some (Defined newlinefn))
  (Hfxframe : call_frame newlinefn [WPtr null;WPtr newline] = Some newlineframe)
  (Hflush : find_fn ge (TAtom "__GI__IO_fflush") = Some (Defined flushfn))
  (Hfframe : call_frame flushfn [WPtr stderr] = Some flushframe).
Context (Hfxcall : ⊢ R -∗ WP (ERun newlineframe : gexpr)
    {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ S }})
  (Hflushcall : ⊢ live_capq dq (ptr_cap stderr) rreg -∗ S -∗
    WP (ERun flushframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
      live_capq dq (ptr_cap stderr) rreg ∗ Q }}).

(** The saved errno argument may be any 32-bit word. Zero skips errno text;
    nonzero lends the allocated buffer to strerror and retains its result.
    The newline and stderr-flush contracts allow failure in either case. *)
Lemma wp_error_text_tail_zero_loan
    (Hnewline_loan : ⊢ live sb sreg -∗ pcell sb 0 stderr -∗ live_capq dq (ptr_cap stderr) rreg -∗ R -∗
      WP (ERun newlineframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
        live sb sreg ∗ pcell sb 0 stderr ∗ live_capq dq (ptr_cap stderr) rreg ∗ S }})
    e from errnum fmt ap mode cb nb nreg count
    textfmt strerrorfn (borrowed : ptr -> iProp Σ) Φ :
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
  live nb nreg -∗ int_cell nb 0 count -∗
  live tb treg -∗ int_cell tb 792 1 -∗
  live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
  live sb sreg -∗ pcell sb 0 stderr -∗ live_capq dq (ptr_cap stderr) rreg -∗ R -∗ E -∗
  (live nb nreg -∗ int_cell nb 0 ((count + 1) mod 2 ^ 32) -∗ error_text_scratch borrowed errnum -∗
    live tb treg -∗ int_cell tb 792 old -∗
    live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
    live sb sreg -∗ pcell sb 0 stderr -∗ live_capq dq (ptr_cap stderr) rreg -∗ Q -∗ E -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc_error_internal e [] None
    (Enter (TAtom "iw_2.L19") (Some from))) : gexpr) {{ Φ }}.
Proof.
  intros Hinputs Herr Hcount Hnb Hne Hnr Htext Hstr Hstrcall Htextcall.
  iIntros "Hnl Hcount Ht Hflag Hcl Hsaved Hsl Hsp Hr HR HE HK".
  iApply (wp_error_text _ _ 0 errnum fmt ap mode cb nb nreg count textfmt strerrorfn newlinefn
    borrowed R T (live tb treg ∗ int_cell tb 792 1 ∗
      live cb (mkRegion cb (cb + 16) Heap Live) ∗ int_cell cb 0 old ∗
      live sb sreg ∗ pcell sb 0 stderr ∗ live_capq dq (ptr_cap stderr) rreg ∗ E)%I
    with "Hnl Hcount HR [$Ht $Hflag $Hcl $Hsaved $Hsl $Hsp $Hr $HE]"); try assumption.
  iIntros (e' predecessor Hinputs') "Hnl Hcount Hscratch HR (Ht & Hflag & Hcl & Hsaved & Hsl & Hsp & Hr & HE)".
  iApply (wp_error_tail_loan Hreg Hext tb treg old sb sreg stderr dq rreg
    newline newlinefn newlineframe flushfn flushframe R S Q
    (live nb nreg ∗ int_cell nb 0 ((count + 1) mod 2 ^ 32) ∗ error_text_scratch borrowed errnum ∗ E)%I
    with "Ht Hflag Hcl Hsaved Hsl Hsp Hr HR [$Hnl $Hcount $Hscratch $HE]"); try assumption; try exact Hinputs'; try lia.
  iSplit; [|iIntros (e'' Hnz); contradiction].
  iIntros "Ht Hflag Hcl Hsaved Hsl Hsp Hr HQ (Hnl & Hcount & Hscratch & HE)".
  iApply ("HK" with "Hnl Hcount Hscratch Ht Hflag Hcl Hsaved Hsl Hsp Hr HQ HE").
Qed.

(** The original newline contract can leave stderr with its caller. This
    corollary keeps that interface for existing count-and-text proofs. *)
Lemma wp_error_text_tail_zero e from errnum fmt ap mode cb nb nreg count
    textfmt strerrorfn (borrowed : ptr -> iProp Σ) Φ :
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
  live nb nreg -∗ int_cell nb 0 count -∗
  live tb treg -∗ int_cell tb 792 1 -∗
  live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
  live sb sreg -∗ pcell sb 0 stderr -∗ live_capq dq (ptr_cap stderr) rreg -∗ R -∗ E -∗
  (live nb nreg -∗ int_cell nb 0 ((count + 1) mod 2 ^ 32) -∗ error_text_scratch borrowed errnum -∗
    live tb treg -∗ int_cell tb 792 old -∗
    live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
    live sb sreg -∗ pcell sb 0 stderr -∗ live_capq dq (ptr_cap stderr) rreg -∗ Q -∗ E -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc_error_internal e [] None
    (Enter (TAtom "iw_2.L19") (Some from))) : gexpr) {{ Φ }}.
Proof.
  intros Hinputs Herr Hcount Hnb Hne Hnr Htext Hstr Hstrcall Htextcall.
  iIntros "Hnl Hcount Ht Hflag Hcl Hsaved Hsl Hsp Hr HR HE HK".
  iApply (wp_error_text_tail_zero_loan with "Hnl Hcount Ht Hflag Hcl Hsaved Hsl Hsp Hr HR HE HK"); try assumption.
  iIntros "Hsl Hsp Hr HR". iApply (wp_wand with "[HR]"); [iApply (Hfxcall with "HR") |].
  iIntros (v) "H". iDestruct "H" as (r ->) "HS". iExists r. iFrame. done.
  all: try eassumption.
Qed.
End returning.
