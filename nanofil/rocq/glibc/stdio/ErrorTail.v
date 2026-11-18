(** After printing the message and any errno text, error prints a newline
    and flushes stderr. Neither call has to succeed for reporting to finish.
    A zero status restores the saved cancellation setting and returns.

    A nonzero status instead calls exit, which must run its normal cleanup.
    That call still needs a separate proof. The earlier message printing
    and errno lookup also remain outside this proof. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps SysWrappers
  PrintfStateCode ErrorCode ErrorEntry ErrorRestore Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic OsWorld SysWrappers.
Open Scope Z_scope.

Section tail_lend.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (Hreg : holds_os registry) (Hext : sys_external ge).

(** Before the flush, error reads the stderr pointer, and that read
    needs the stream object to be alive. A caller may hold stderr in a
    form that hides its region, such as an idle stream. This rule lets
    such a caller lend the lifetime for the read alone and hand the
    whole stream to the newline and the flush. *)
Lemma wp_error_tail_lend {dqs : dfrac} tb treg old sb sreg stderr
    newline newlinefn newlineframe flushfn flushframe (O R S Q E : iProp Σ)
    e from status errnum fmt ap mode cb Φ :
  old = 0 \/ old = 1 -> ow_self w0 = mkPtr tb (Obj tb) ->
  0 < tb -> tb mod 8 = 0 -> tb + 796 <= r_end treg -> r_end treg <= 2 ^ 63 ->
  find_fn ge (TAtom "__GI___pthread_setcancelstate") = Some (Defined glibc___pthread_setcancelstate) ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr sb (Obj sb)) ->
  0 < sb -> sb mod 8 = 0 -> sb + 8 <= r_end sreg ->
  0 <= ptr_addr stderr < 2 ^ 64 ->
  lookup (TAtom "glibc_error#str.254") (ge_globals ge) = Some newline ->
  find_fn ge (TAtom "__fxprintf") = Some (Defined newlinefn) ->
  call_frame newlinefn [WPtr null;WPtr newline] = Some newlineframe ->
  find_fn ge (TAtom "__GI__IO_fflush") = Some (Defined flushfn) ->
  call_frame flushfn [WPtr stderr] = Some flushframe ->
  (⊢ liveq dqs sb sreg -∗ pcellq dqs sb 0 stderr -∗ O -∗ R -∗
    WP (ERun newlineframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
      liveq dqs sb sreg ∗ pcellq dqs sb 0 stderr ∗ O ∗ S }}) ->
  (O ⊢ ∃ dq rreg, live_capq dq (ptr_cap stderr) rreg ∗ (live_capq dq (ptr_cap stderr) rreg -∗ O)) ->
  (⊢ O -∗ S -∗ WP (ERun flushframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ O ∗ Q }}) ->
  error_inputs e status errnum fmt ap mode cb -> 0 <= status < 2 ^ 32 ->
  live tb treg -∗ int_cell tb 792 1 -∗
  live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
  liveq dqs sb sreg -∗ pcellq dqs sb 0 stderr -∗ O -∗ R -∗ E -∗
  ((live tb treg -∗ int_cell tb 792 old -∗
      live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
      liveq dqs sb sreg -∗ pcellq dqs sb 0 stderr -∗ O -∗ Q -∗ E -∗ Φ RetVoid) ∧
    (∀ e', ⌜status <> 0⌝ -∗ ⌜error_inputs e' status errnum fmt ap mode cb⌝ -∗
      live tb treg -∗ int_cell tb 792 1 -∗
      live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
      liveq dqs sb sreg -∗ pcellq dqs sb 0 stderr -∗ O -∗ Q -∗ E -∗
      WP (ERun (mkFrame glibc_error_internal e' [] None
        (Enter (TAtom "iw_2.L100") (Some (TAtom "iw_2.L92")))) : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_error_internal e [] None
    (Enter (TAtom "iw_2.L92") (Some from))) : gexpr) {{ Φ }}.
Proof using Hext Hreg.
  intros Hold Hself Htb Hta Hte Htr Hcancel Hgstderr Hsb Hsa Hse Hptr Hnewline Hfx Hfxframe
    Hflush Hfframe Hnewline_loan Hopen Hflushcall Hinputs Hstatusrange.
  destruct Hinputs as (Hstatus & Herrnum & Hfmt & Hap & Hmode & Hsave & Hchk).
  iIntros "Ht Hflag Hcl Hsaved Hsl Hsp HO HR HE HK".
  step. step.
  iApply wp_call_bind; [vx | exact Hfx | exact Hfxframe |]. iNext.
  iApply (wp_wand with "[Hsl Hsp HO HR]"); [iApply (Hnewline_loan with "Hsl Hsp HO HR") |].
  iIntros (v) "H". iDestruct "H" as (r ->) "(Hsl & Hsp & HO & HS)". resume.
  step. iApply (wp_live_fit with "Hsl"). iIntros ([Hs0 Hs48]) "Hsl".
  check_read_dq "Hsl" by a2. iNext. iIntros "Hsl".
  iDestruct (Hopen with "HO") as (dq rreg) "[Hr Hclose]".
  iApply (wp_raw_load_pointer_dq with "Hsl Hsp Hr");
    [reflexivity | vx | left; reflexivity | a2 | a2 | exact Hptr |].
  iNext. iIntros "Hsl Hsp Hr". iSpecialize ("Hclose" with "Hr").
  iApply wp_call_bind; [vx | exact Hflush | exact Hfframe |]. iNext.
  iApply (wp_wand with "[Hclose HS]"); [iApply (Hflushcall with "Hclose HS") |].
  iIntros (v) "H". iDestruct "H" as (r' ->) "[HO HQ]". resume.
  destruct (Z.eq_dec status 0) as [Hz | Hz].
  - branch_as true. iDestruct "HK" as "[HK _]".
    iApply (wp_error_restore Hreg Hext _ _ status errnum fmt ap mode cb old tb treg
      (liveq dqs sb sreg ∗ pcellq dqs sb 0 stderr ∗ O ∗ Q ∗ E)%I
      with "Ht Hflag Hcl Hsaved [$Hsl $Hsp $HO $HQ $HE]"); try assumption.
    { unfold error_inputs. repeat split; lk_prove. }
    iIntros "Ht Hflag Hcl Hsaved (Hsl & Hsp & HO & HQ & HE)".
    iApply ("HK" with "Ht Hflag Hcl Hsaved Hsl Hsp HO HQ HE").
  - branch_as false. iDestruct "HK" as "[_ HK]".
    iApply ("HK" with "[%] [%] Ht Hflag Hcl Hsaved Hsl Hsp HO HQ HE"); [exact Hz |].
    unfold error_inputs. repeat split; lk_prove.
Qed.
End tail_lend.

Section tail.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (tb : Z) (treg : region) (old : Z)
  (sb : Z) (sreg : region) (stderr : ptr) (dq : dfrac) (rreg : region)
  (newline : ptr) (newlinefn : func) (newlineframe : frame) (flushfn : func) (flushframe : frame)
  (R S Q E : iProp Σ).
Context {dqs : dfrac}.
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

(** The newline and flush contracts may return errors and change errno.
    They receive only the resources their callers lend; stderr is not
    assumed to have the closed stdout fields. *)
Context (Hfxcall : ⊢ R -∗ WP (ERun newlineframe : gexpr)
    {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ S }})
  (Hflushcall : ⊢ live_capq dq (ptr_cap stderr) rreg -∗ S -∗
    WP (ERun flushframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
      live_capq dq (ptr_cap stderr) rreg ∗ Q }}).

(** Exiting the process requires different work from returning to the caller.
    For nonzero status, this rule stops before the call to __GI_exit and
    leaves cancellation disabled. The saved flag remains available there. *)
Lemma wp_error_tail_loan
    (Hnewline_loan : ⊢ liveq dqs sb sreg -∗ pcellq dqs sb 0 stderr -∗ live_capq dq (ptr_cap stderr) rreg -∗ R -∗
      WP (ERun newlineframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
        liveq dqs sb sreg ∗ pcellq dqs sb 0 stderr ∗ live_capq dq (ptr_cap stderr) rreg ∗ S }})
    e from status errnum fmt ap mode cb Φ :
  error_inputs e status errnum fmt ap mode cb -> 0 <= status < 2 ^ 32 ->
  live tb treg -∗ int_cell tb 792 1 -∗
  live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
  liveq dqs sb sreg -∗ pcellq dqs sb 0 stderr -∗ live_capq dq (ptr_cap stderr) rreg -∗ R -∗ E -∗
  ((live tb treg -∗ int_cell tb 792 old -∗
      live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
      liveq dqs sb sreg -∗ pcellq dqs sb 0 stderr -∗ live_capq dq (ptr_cap stderr) rreg -∗ Q -∗ E -∗ Φ RetVoid) ∧
    (∀ e', ⌜status <> 0⌝ -∗ ⌜error_inputs e' status errnum fmt ap mode cb⌝ -∗
      live tb treg -∗ int_cell tb 792 1 -∗
      live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
      liveq dqs sb sreg -∗ pcellq dqs sb 0 stderr -∗ live_capq dq (ptr_cap stderr) rreg -∗ Q -∗ E -∗
      WP (ERun (mkFrame glibc_error_internal e' [] None
        (Enter (TAtom "iw_2.L100") (Some (TAtom "iw_2.L92")))) : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_error_internal e [] None
    (Enter (TAtom "iw_2.L92") (Some from))) : gexpr) {{ Φ }}.
Proof using Hcancel Hext Hfframe Hflush Hflushcall Hfx Hfxframe Hgstderr Hnewline Hold Hptr Hreg Hsa Hsb Hse Hself Hta Htb Hte Htr.
  intros Hinputs Hstatusrange.
  iApply (wp_error_tail_lend Hreg Hext (dqs := dqs) tb treg old sb sreg stderr newline newlinefn newlineframe
    flushfn flushframe (live_capq dq (ptr_cap stderr) rreg)); try eassumption.
  iIntros "H". iExists dq, rreg. iFrame "H". iIntros "H". iExact "H".
Qed.

(** A newline contract that does not use stderr can keep the same ownership
    outside the call. This recovers the original tail rule unchanged. *)
Lemma wp_error_tail e from status errnum fmt ap mode cb Φ :
  error_inputs e status errnum fmt ap mode cb -> 0 <= status < 2 ^ 32 ->
  live tb treg -∗ int_cell tb 792 1 -∗
  live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
  liveq dqs sb sreg -∗ pcellq dqs sb 0 stderr -∗ live_capq dq (ptr_cap stderr) rreg -∗ R -∗ E -∗
  ((live tb treg -∗ int_cell tb 792 old -∗
      live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
      liveq dqs sb sreg -∗ pcellq dqs sb 0 stderr -∗ live_capq dq (ptr_cap stderr) rreg -∗ Q -∗ E -∗ Φ RetVoid) ∧
    (∀ e', ⌜status <> 0⌝ -∗ ⌜error_inputs e' status errnum fmt ap mode cb⌝ -∗
      live tb treg -∗ int_cell tb 792 1 -∗
      live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
      liveq dqs sb sreg -∗ pcellq dqs sb 0 stderr -∗ live_capq dq (ptr_cap stderr) rreg -∗ Q -∗ E -∗
      WP (ERun (mkFrame glibc_error_internal e' [] None
        (Enter (TAtom "iw_2.L100") (Some (TAtom "iw_2.L92")))) : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_error_internal e [] None
    (Enter (TAtom "iw_2.L92") (Some from))) : gexpr) {{ Φ }}.
Proof using Hcancel Hext Hfframe Hflush Hflushcall Hfx Hfxcall Hfxframe Hgstderr Hnewline Hold Hptr Hreg Hsa Hsb Hse Hself Hta Htb Hte Htr.
  intros Hinputs Hrange. iIntros "Ht Hflag Hcl Hsaved Hsl Hsp Hr HR HE HK".
  iApply (wp_error_tail_loan with "Ht Hflag Hcl Hsaved Hsl Hsp Hr HR HE HK"); try assumption.
  iIntros "Hsl Hsp Hr HR". iApply (wp_wand with "[HR]"); [iApply (Hfxcall with "HR") |].
  iIntros (v) "H". iDestruct "H" as (r ->) "HS". iExists r. iFrame. done.
Qed.

(** Hello passes status zero to error. Its returning tail therefore needs
    no exit contract, but still needs both printing and stderr-flush contracts. *)
Lemma wp_error_tail_zero e from errnum fmt ap mode cb Φ :
  error_inputs e 0 errnum fmt ap mode cb ->
  live tb treg -∗ int_cell tb 792 1 -∗
  live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
  liveq dqs sb sreg -∗ pcellq dqs sb 0 stderr -∗ live_capq dq (ptr_cap stderr) rreg -∗ R -∗ E -∗
  (live tb treg -∗ int_cell tb 792 old -∗
    live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗
    liveq dqs sb sreg -∗ pcellq dqs sb 0 stderr -∗ live_capq dq (ptr_cap stderr) rreg -∗ Q -∗ E -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc_error_internal e [] None
    (Enter (TAtom "iw_2.L92") (Some from))) : gexpr) {{ Φ }}.
Proof using Hcancel Hext Hfframe Hflush Hflushcall Hfx Hfxcall Hfxframe Hgstderr Hnewline Hold Hptr Hreg Hsa Hsb Hse Hself Hta Htb Hte Htr.
  intros Hinputs. iIntros "Ht Hflag Hcl Hsaved Hsl Hsp Hr HR HE HK".
  iApply (wp_error_tail with "Ht Hflag Hcl Hsaved Hsl Hsp Hr HR HE"); [exact Hinputs | lia |].
  iSplit; [iExact "HK" |]. iIntros (e' Hnz). contradiction.
Qed.
End tail.
