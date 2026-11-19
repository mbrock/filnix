(** Error counts each report before deciding whether to print errno text.
    The counter wraps at 32 bits. The decision uses the original errno
    argument, not the mutable thread errno cell.

    The strerror contract owns the fresh buffer and supplies any borrowed
    result. A result that aliases the buffer uses its existing lifetime.
    Printing keeps these resources available to the reporting continuation. *)
From Glibc Require Import Unit_misc_error_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps SysWrappers
  ErrorEntry Fix.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L
  FileInv LibioLogic OsWorld SysWrappers.
Open Scope Z_scope.

Section text.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The caller supplies the borrowed alternative, including its readable
    bytes and lifetime where needed. No second lifetime is required when
    strerror returns the buffer itself. *)
Definition error_text_buffer (borrowed : ptr -> iProp Σ) b p : iProp Σ :=
  ∃ contents, ⌜length contents = 1024%nat⌝ ∗
    live b (mkRegion b (b + 1024) Heap Live) ∗ bytes b 0 contents ∗
    (⌜p = mkPtr b (Obj b) /\ exists prefix suffix,
       contents = (prefix ++ [0] ++ suffix)%list /\ Forall (fun c => 0 < c < 256) prefix⌝ ∨ borrowed p).

Definition error_text_scratch (borrowed : ptr -> iProp Σ) errnum : iProp Σ :=
  (if decide (errnum = 0) then emp else ∃ b p, error_text_buffer borrowed b p)%I.

Lemma error_count_unsigned n : 0 <= n < 2 ^ 32 ->
  extended Uw W (of_bytes (le_bytes n 4)) = Some (WInt n).
Proof using Type*. intros Hn. rewrite of_bytes_int; [|exact Hn]. cbn. by rewrite !(Z.mod_small n (2 ^ 32)). Qed.

(** Every report increments the counter, including reports with no errno
    text. This proof follows those instructions and the buffer allocation;
    strerror and text printing still require their own proofs. *)
Lemma wp_error_text_loan e from status errnum fmt ap mode cb nb nreg count
    textfmt strerrorfn printfn (borrowed : ptr -> iProp Σ) (L R S Q E : iProp Σ) Φ :
  error_inputs e status errnum fmt ap mode cb -> 0 <= errnum < 2 ^ 32 ->
  lookup (TAtom "error_message_count") (ge_globals ge) = Some (mkPtr nb (Obj nb)) ->
  0 < nb -> nb + 4 <= r_end nreg -> r_end nreg <= 2 ^ 63 ->
  lookup (TAtom "glibc_error#str.252") (ge_globals ge) = Some textfmt ->
  find_fn ge (TAtom "__GI___strerror_r") = Some (Defined strerrorfn) ->
  find_fn ge (TAtom "__fxprintf") = Some (Defined printfn) ->
  (forall b, exists fr, call_frame strerrorfn [WInt errnum;WPtr (mkPtr b (Obj b));WInt 1024] = Some fr /\
    (⊢ obj b (heap_req 4 1024) -∗ R -∗ WP (ERun fr : gexpr)
      {{ v, ∃ p, ⌜v = Ret (WPtr p)⌝ ∗ error_text_buffer borrowed b p ∗ S }})) ->
  (forall b p, exists fr, call_frame printfn [WPtr null;WPtr textfmt;WPtr p] = Some fr /\
    (⊢ L -∗ error_text_buffer borrowed b p -∗ S -∗ WP (ERun fr : gexpr)
      {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ L ∗ error_text_buffer borrowed b p ∗ Q }})) ->
  live nb nreg -∗ int_cell nb 0 count -∗ L -∗ R -∗ E -∗
  (∀ e' predecessor, ⌜error_inputs e' status errnum fmt ap mode cb⌝ -∗
    live nb nreg -∗ int_cell nb 0 ((count + 1) mod 2 ^ 32) -∗
    error_text_scratch borrowed errnum -∗ L -∗ (if decide (errnum = 0) then R else Q) -∗ E -∗
    WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e' [] None
      (Enter (TAtom "iw_2.L92") (Some predecessor))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e [] None
    (Enter (TAtom "iw_2.L19") (Some from))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hinputs Herrrange Hglobal Hnb Hne Hnr Htext Hstr Hfx Hstrcall Hfxcall.
  destruct Hinputs as (Hstatus & Herrnum & Hfmt & Hap & Hmode & Hsave & Hchk).
  iIntros "Hl [%Hcount Hbytes] HL HR HE HK".
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hnb0 Hnb48]) "Hl".
  step. step. check "Hl".
  iApply (wp_raw_load_sub_bytes_dq with "Hl Hbytes");
    [reflexivity | vx | reflexivity | apply error_count_unsigned; assumption | left; reflexivity | a2 |].
  iNext. iIntros "Hl Hbytes". step. check "Hl". store_int "Hl" "Hbytes".
  iEval (rewrite Z.mod_mod; [|lia]) in "Hbytes".
  iEval (rewrite (Z.mod_small count (2 ^ 32)); [|exact Hcount]) in "Hbytes".
  change (1 mod 2 ^ 32) with 1.
  destruct (Z.eq_dec errnum 0) as [Hz | Hz].
  - branch_as true. iEval (rewrite decide_True; [|done]) in "HK".
    iApply ("HK" with "[%] Hl [Hbytes] [] HL HR HE").
    { unfold error_inputs. repeat split; lk_prove. }
    { iSplit; [iPureIntro; apply Z.mod_pos_bound; lia | iExact "Hbytes"]. }
    unfold error_text_scratch. rewrite decide_True; done.
  - branch_as false. step.
    iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
      intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
    iNext. iIntros (b Hb) "Hobj".
    destruct (Hstrcall b) as (fr & Hfr & Hcall).
    iApply wp_call_bind; [vx | exact Hstr | |].
    { rewrite (Z.mod_small errnum (2 ^ 32)); [exact Hfr | exact Herrrange]. }
    iNext.
    iApply (wp_wand with "[Hobj HR]"); [iApply (Hcall with "Hobj HR") |].
    iIntros (v) "H". iDestruct "H" as (p ->) "[Hb HS]". resume. step.
    destruct (Hfxcall b p) as (fr' & Hfr' & Hcall').
    iApply wp_call_bind; [vx | exact Hfx | exact Hfr' |]. iNext.
    iApply (wp_wand with "[HL Hb HS]"); [iApply (Hcall' with "HL Hb HS") |].
    iIntros (v) "H". iDestruct "H" as (r ->) "(HL & Hb & HQ)". resume. step.
    iEval (rewrite decide_False; [|done]) in "HK".
    iApply ("HK" with "[%] Hl [Hbytes] [Hb] HL HQ HE").
    { unfold error_inputs. repeat split; lk_prove. }
    { iSplit; [iPureIntro; apply Z.mod_pos_bound; lia | iExact "Hbytes"]. }
    unfold error_text_scratch. rewrite decide_False; [iExists b,p; iExact "Hb" | done].
Qed.

(** A report without an error number prints no errno text, so it calls
    neither `c: strerror_r` nor the text printer. It only counts the
    report and goes on to the newline. *)
Lemma wp_error_count_zero e from status fmt ap mode cb nb nreg count (E : iProp Σ) Φ :
  error_inputs e status 0 fmt ap mode cb ->
  lookup (TAtom "error_message_count") (ge_globals ge) = Some (mkPtr nb (Obj nb)) ->
  0 < nb -> nb + 4 <= r_end nreg -> r_end nreg <= 2 ^ 63 ->
  live nb nreg -∗ int_cell nb 0 count -∗ E -∗
  (∀ e' predecessor, ⌜error_inputs e' status 0 fmt ap mode cb⌝ -∗
    live nb nreg -∗ int_cell nb 0 ((count + 1) mod 2 ^ 32) -∗ E -∗
    WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e' [] None
      (Enter (TAtom "iw_2.L92") (Some predecessor))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e [] None
    (Enter (TAtom "iw_2.L19") (Some from))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hinputs Hglobal Hnb Hne Hnr.
  destruct Hinputs as (Hstatus & Herrnum & Hfmt & Hap & Hmode & Hsave & Hchk).
  iIntros "Hl [%Hcount Hbytes] HE HK".
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hnb0 Hnb48]) "Hl".
  step. step. check "Hl".
  iApply (wp_raw_load_sub_bytes_dq with "Hl Hbytes");
    [reflexivity | vx | reflexivity | apply error_count_unsigned; assumption | left; reflexivity | a2 |].
  iNext. iIntros "Hl Hbytes". step. check "Hl". store_int "Hl" "Hbytes".
  iEval (rewrite Z.mod_mod; [|lia]) in "Hbytes".
  iEval (rewrite (Z.mod_small count (2 ^ 32)); [|exact Hcount]) in "Hbytes".
  change (1 mod 2 ^ 32) with 1.
  branch_as true.
  iApply ("HK" with "[%] Hl [Hbytes] HE").
  { unfold error_inputs. repeat split; lk_prove. }
  iSplit; [iPureIntro; apply Z.mod_pos_bound; lia | iExact "Hbytes"].
Qed.

(** Existing callers can keep their stream ownership outside text printing.
    An empty loan recovers the original count-and-text interface. *)
Lemma wp_error_text e from status errnum fmt ap mode cb nb nreg count
    textfmt strerrorfn printfn (borrowed : ptr -> iProp Σ) (R S E : iProp Σ) Φ :
  error_inputs e status errnum fmt ap mode cb -> 0 <= errnum < 2 ^ 32 ->
  lookup (TAtom "error_message_count") (ge_globals ge) = Some (mkPtr nb (Obj nb)) ->
  0 < nb -> nb + 4 <= r_end nreg -> r_end nreg <= 2 ^ 63 ->
  lookup (TAtom "glibc_error#str.252") (ge_globals ge) = Some textfmt ->
  find_fn ge (TAtom "__GI___strerror_r") = Some (Defined strerrorfn) ->
  find_fn ge (TAtom "__fxprintf") = Some (Defined printfn) ->
  (forall b, exists fr, call_frame strerrorfn [WInt errnum;WPtr (mkPtr b (Obj b));WInt 1024] = Some fr /\
    (⊢ obj b (heap_req 4 1024) -∗ R -∗ WP (ERun fr : gexpr)
      {{ v, ∃ p, ⌜v = Ret (WPtr p)⌝ ∗ error_text_buffer borrowed b p ∗ S }})) ->
  (forall b p, exists fr, call_frame printfn [WPtr null;WPtr textfmt;WPtr p] = Some fr /\
    (⊢ error_text_buffer borrowed b p -∗ S -∗ WP (ERun fr : gexpr)
      {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ error_text_buffer borrowed b p ∗ R }})) ->
  live nb nreg -∗ int_cell nb 0 count -∗ R -∗ E -∗
  (∀ e' predecessor, ⌜error_inputs e' status errnum fmt ap mode cb⌝ -∗
    live nb nreg -∗ int_cell nb 0 ((count + 1) mod 2 ^ 32) -∗
    error_text_scratch borrowed errnum -∗ R -∗ E -∗
    WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e' [] None
      (Enter (TAtom "iw_2.L92") (Some predecessor))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e [] None
    (Enter (TAtom "iw_2.L19") (Some from))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hinputs Herrrange Hglobal Hnb Hne Hnr Htext Hstr Hfx Hstrcall Hfxcall.
  iIntros "Hl Hcount HR HE HK".
  iApply (wp_error_text_loan e from status errnum fmt ap mode cb nb nreg count
    textfmt strerrorfn printfn borrowed emp R S R E with "Hl Hcount [] HR HE [HK]"); try assumption.
  { intros b p. destruct (Hfxcall b p) as (fr & Hframe & Hcall).
    exists fr. split; [done |]. iIntros "_ Hb HS".
    iApply (wp_wand with "[Hb HS]"); [iApply (Hcall with "Hb HS") |].
    iIntros (v) "H". iDestruct "H" as (r ->) "[Hb HR]". iExists r. iFrame. done. }
  { done. }
  iIntros (e' predecessor Hinputs') "Hl Hcount Hscratch _ HR HE".
  iApply ("HK" with "[%] Hl Hcount Hscratch [HR] HE"); [done |].
  destruct (decide (errnum = 0)); iExact "HR".
Qed.
End text.
