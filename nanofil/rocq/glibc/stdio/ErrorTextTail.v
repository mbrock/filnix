(** When status is zero, error counts the message, prints any errno text,
    and returns after restoring cancellation. This proof joins the counting
    and printing steps to the returning tail.

    The caller keeps the new strerror buffer and any borrowed text until
    return. Earlier message output, printing, and flushing stderr still
    require separate proofs. *)
From Glibc Require Import Unit_misc_error_os Unit_nptl_pthread_setcancelstate_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps SysWrappers
  ErrorEntry ErrorTail ErrorText Fix.
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
  (Hcancel : find_fn ge (TAtom "__GI___pthread_setcancelstate") = Some (Defined Unit_nptl_pthread_setcancelstate_os.fn___GI___pthread_setcancelstate))
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

(** Text printing and the newline borrow the same stderr resources in turn.
    A separate resource exchange prepares the newline after text returns;
    zero errno instead prepares it directly from the original resources. *)
Lemma wp_error_text_tail_zero_loans (P U : iProp Σ)
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
    (⊢ obj b (heap_req 4 1024) -∗ P -∗ WP (ERun fr : gexpr)
      {{ v, ∃ p, ⌜v = Ret (WPtr p)⌝ ∗ error_text_buffer borrowed b p ∗ T }})) ->
  (forall b p, exists fr, call_frame newlinefn [WPtr null;WPtr textfmt;WPtr p] = Some fr /\
    (⊢ live sb sreg -∗ pcell sb 0 stderr -∗ live_capq dq (ptr_cap stderr) rreg -∗
      error_text_buffer borrowed b p -∗ T -∗ WP (ERun fr : gexpr)
      {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ live sb sreg ∗ pcell sb 0 stderr ∗
        live_capq dq (ptr_cap stderr) rreg ∗ error_text_buffer borrowed b p ∗ U }})) ->
  ((if decide (errnum = 0) then P else U) ⊢ R) ->
  live nb nreg -∗ int_cell nb 0 count -∗
  live tb treg -∗ int_cell tb 792 1 -∗
  live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
  live sb sreg -∗ pcell sb 0 stderr -∗ live_capq dq (ptr_cap stderr) rreg -∗ P -∗ E -∗
  (live nb nreg -∗ int_cell nb 0 ((count + 1) mod 2 ^ 32) -∗ error_text_scratch borrowed errnum -∗
    live tb treg -∗ int_cell tb 792 old -∗
    live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
    live sb sreg -∗ pcell sb 0 stderr -∗ live_capq dq (ptr_cap stderr) rreg -∗ Q -∗ E -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e [] None
    (Enter (TAtom "iw_2.L19") (Some from))) : gexpr) {{ Φ }}.
Proof using Hcancel Hext Hfframe Hflush Hflushcall Hfx Hfxframe Hgstderr Hnewline Hold Hptr Hreg Hsa Hsb Hse Hself Hta Htb Hte Htr.
  intros Hinputs Herr Hcount Hnb Hne Hnr Htext Hstr Hstrcall Htextcall Hready.
  iIntros "Hnl Hcount Ht Hflag Hcl Hsaved Hsl Hsp Hr HP HE HK".
  iApply (wp_error_text_loan _ _ 0 errnum fmt ap mode cb nb nreg count textfmt strerrorfn newlinefn
    borrowed (live sb sreg ∗ pcell sb 0 stderr ∗ live_capq dq (ptr_cap stderr) rreg)%I P T U
    (live tb treg ∗ int_cell tb 792 1 ∗
      live cb (mkRegion cb (cb + 16) Heap Live) ∗ int_cell cb 0 old ∗ E)%I
    with "Hnl Hcount [$Hsl $Hsp $Hr] HP [$Ht $Hflag $Hcl $Hsaved $HE] [HK]"); try assumption.
  { intros b p. destruct (Htextcall b p) as (fr & Hframe & Hcall).
    exists fr. split; [done |]. iIntros "(Hsl & Hsp & Hr) Hb HT".
    iApply (wp_wand with "[Hsl Hsp Hr Hb HT]"); [iApply (Hcall with "Hsl Hsp Hr Hb HT") |].
    iIntros (v) "H". iDestruct "H" as (r ->) "(Hsl & Hsp & Hr & Hb & HU)".
    iExists r. iFrame. done. }
  iIntros (e' predecessor Hinputs') "Hnl Hcount Hscratch (Hsl & Hsp & Hr) HU (Ht & Hflag & Hcl & Hsaved & HE)".
  iPoseProof (Hready with "HU") as "HR".
  iApply (wp_error_tail_loan Hreg Hext tb treg old sb sreg stderr dq rreg
    newline newlinefn newlineframe flushfn flushframe R S Q
    (live nb nreg ∗ int_cell nb 0 ((count + 1) mod 2 ^ 32) ∗ error_text_scratch borrowed errnum ∗ E)%I
    with "Ht Hflag Hcl Hsaved Hsl Hsp Hr HR [$Hnl $Hcount $Hscratch $HE]"); try assumption; try exact Hinputs'; try lia.
  iSplit; [|iIntros (e'' Hnz); contradiction].
  iIntros "Ht Hflag Hcl Hsaved Hsl Hsp Hr HQ (Hnl & Hcount & Hscratch & HE)".
  iApply ("HK" with "Hnl Hcount Hscratch Ht Hflag Hcl Hsaved Hsl Hsp Hr HQ HE").
Qed.

(** Strerror may borrow the caller's thread lifetime for its translation
    locks. This rule routes that lifetime through the text step and recovers
    it before the returning tail. Cancellation remains one outside the loan,
    and the text formatter does not receive the thread lifetime. *)
Lemma wp_error_text_tail_thread_loan (P U : iProp Σ)
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
    (⊢ obj b (heap_req 4 1024) -∗ live tb treg -∗ P -∗ WP (ERun fr : gexpr)
      {{ v, ∃ p, ⌜v = Ret (WPtr p)⌝ ∗ live tb treg ∗ error_text_buffer borrowed b p ∗ T }})) ->
  (forall b p, exists fr, call_frame newlinefn [WPtr null;WPtr textfmt;WPtr p] = Some fr /\
    (⊢ live sb sreg -∗ pcell sb 0 stderr -∗ live_capq dq (ptr_cap stderr) rreg -∗
      error_text_buffer borrowed b p -∗ T -∗ WP (ERun fr : gexpr)
      {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ live sb sreg ∗ pcell sb 0 stderr ∗
        live_capq dq (ptr_cap stderr) rreg ∗ error_text_buffer borrowed b p ∗ U }})) ->
  ((if decide (errnum = 0) then P else U) ⊢ R) ->
  live nb nreg -∗ int_cell nb 0 count -∗
  live tb treg -∗ int_cell tb 792 1 -∗
  live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
  live sb sreg -∗ pcell sb 0 stderr -∗ live_capq dq (ptr_cap stderr) rreg -∗ P -∗ E -∗
  (live nb nreg -∗ int_cell nb 0 ((count + 1) mod 2 ^ 32) -∗ error_text_scratch borrowed errnum -∗
    live tb treg -∗ int_cell tb 792 old -∗
    live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
    live sb sreg -∗ pcell sb 0 stderr -∗ live_capq dq (ptr_cap stderr) rreg -∗ Q -∗ E -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e [] None
    (Enter (TAtom "iw_2.L19") (Some from))) : gexpr) {{ Φ }}.
Proof using Hcancel Hext Hfframe Hflush Hflushcall Hfx Hfxframe Hgstderr Hnewline Hold Hptr Hreg Hsa Hsb Hse Hself Hta Htb Hte Htr.
  intros Hinputs Herr Hcount Hnb Hne Hnr Htext Hstr Hstrcall Htextcall Hready.
  iIntros "Hnl Hcount Ht Hflag Hcl Hsaved Hsl Hsp Hr HP HE HK".
  iApply (wp_error_text_loan _ _ 0 errnum fmt ap mode cb nb nreg count textfmt strerrorfn newlinefn
    borrowed (live sb sreg ∗ pcell sb 0 stderr ∗ live_capq dq (ptr_cap stderr) rreg)%I
    (live tb treg ∗ P)%I (live tb treg ∗ T)%I (live tb treg ∗ U)%I
    (int_cell tb 792 1 ∗ live cb (mkRegion cb (cb + 16) Heap Live) ∗ int_cell cb 0 old ∗ E)%I
    with "Hnl Hcount [$Hsl $Hsp $Hr] [$Ht $HP] [$Hflag $Hcl $Hsaved $HE] [HK]"); try assumption.
  { intros b. destruct (Hstrcall b) as (fr & Hframe & Hcall).
    exists fr. split; [done |]. iIntros "Hb [Ht HP]".
    iApply (wp_wand with "[Hb Ht HP]"); [iApply (Hcall with "Hb Ht HP") |].
    iIntros (v) "H". iDestruct "H" as (p ->) "(Ht & Hb & HT)". iExists p. iFrame. done. }
  { intros b p. destruct (Htextcall b p) as (fr & Hframe & Hcall).
    exists fr. split; [done |]. iIntros "(Hsl & Hsp & Hr) Hb [Ht HT]".
    iApply (wp_wand with "[Hsl Hsp Hr Hb HT]"); [iApply (Hcall with "Hsl Hsp Hr Hb HT") |].
    iIntros (v) "H". iDestruct "H" as (r ->) "(Hsl & Hsp & Hr & Hb & HU)".
    iExists r. iFrame. done. }
  iIntros (e' predecessor Hinputs') "Hnl Hcount Hscratch (Hsl & Hsp & Hr) HU (Hflag & Hcl & Hsaved & HE)".
  iAssert (live tb treg ∗ R)%I with "[HU]" as "[Ht HR]".
  { destruct (decide (errnum = 0)); iDestruct "HU" as "[Ht HU]"; iFrame "Ht"; iApply (Hready with "HU"). }
  iApply (wp_error_tail_loan Hreg Hext tb treg old sb sreg stderr dq rreg
    newline newlinefn newlineframe flushfn flushframe R S Q
    (live nb nreg ∗ int_cell nb 0 ((count + 1) mod 2 ^ 32) ∗ error_text_scratch borrowed errnum ∗ E)%I
    with "Ht Hflag Hcl Hsaved Hsl Hsp Hr HR [$Hnl $Hcount $Hscratch $HE]"); try assumption; try exact Hinputs'; try lia.
  iSplit; [|iIntros (e'' Hnz); contradiction].
  iIntros "Ht Hflag Hcl Hsaved Hsl Hsp Hr HQ (Hnl & Hcount & Hscratch & HE)".
  iApply ("HK" with "Hnl Hcount Hscratch Ht Hflag Hcl Hsaved Hsl Hsp Hr HQ HE").
Qed.

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
  WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e [] None
    (Enter (TAtom "iw_2.L19") (Some from))) : gexpr) {{ Φ }}.
Proof using Hcancel Hext Hfframe Hflush Hflushcall Hfx Hfxframe Hgstderr Hnewline Hold Hptr Hreg Hsa Hsb Hse Hself Hta Htb Hte Htr.
  intros Hinputs Herr Hcount Hnb Hne Hnr Htext Hstr Hstrcall Htextcall.
  iIntros "Hnl Hcount Ht Hflag Hcl Hsaved Hsl Hsp Hr HR HE HK".
  iApply (wp_error_text_tail_zero_loans R R Hnewline_loan with
    "Hnl Hcount Ht Hflag Hcl Hsaved Hsl Hsp Hr HR HE HK"); try eassumption.
  { intros b p. destruct (Htextcall b p) as (fr & Hframe & Hcall).
    exists fr. split; [done |]. iIntros "Hsl Hsp Hr Hb HT".
    iApply (wp_wand with "[Hb HT]"); [iApply (Hcall with "Hb HT") |].
    iIntros (v) "H". iDestruct "H" as (r ->) "[Hb HR]". iExists r. iFrame. done. }
  destruct (decide (errnum = 0)); done.
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
  WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e [] None
    (Enter (TAtom "iw_2.L19") (Some from))) : gexpr) {{ Φ }}.
Proof using Hcancel Hext Hfframe Hflush Hflushcall Hfx Hfxcall Hfxframe Hgstderr Hnewline Hold Hptr Hreg Hsa Hsb Hse Hself Hta Htb Hte Htr.
  intros Hinputs Herr Hcount Hnb Hne Hnr Htext Hstr Hstrcall Htextcall.
  iIntros "Hnl Hcount Ht Hflag Hcl Hsaved Hsl Hsp Hr HR HE HK".
  iApply (wp_error_text_tail_zero_loan with "Hnl Hcount Ht Hflag Hcl Hsaved Hsl Hsp Hr HR HE HK"); try assumption.
  iIntros "Hsl Hsp Hr HR". iApply (wp_wand with "[HR]"); [iApply (Hfxcall with "HR") |].
  iIntros (v) "H". iDestruct "H" as (r ->) "HS". iExists r. iFrame. done.
  all: try eassumption.
Qed.
End returning.
