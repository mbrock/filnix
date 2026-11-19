(** When error_print_progname is null, error prints the program name itself.
    This rule follows that branch without requiring a custom callback to
    exist. It disables cancellation and flushes stdout before printing the
    prefix, then passes the original arguments to the message continuation. *)
From Glibc Require Import Unit_misc_error_os Unit_nptl_pthread_setcancelstate_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps
  SysWrappers CancelState ErrorEntry Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps
  OsWorld SysWrappers.
Open Scope Z_scope.

Section entry.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Local Instance error_default_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The default-prefix block reads the program name and calls its formatter.
    It preserves the original arguments without needing to know how the
    preceding cancellation and flush calls populated other temporaries. *)
Lemma error_default_prefix_block e from status errnum fmt ap mode cb
    nb nreg pname dqn namer prefix prefixfn prefixframe (S Q : iProp Σ) Φ :
  error_inputs e status errnum fmt ap mode cb ->
  lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (mkPtr nb (Obj nb)) ->
  0 < nb -> nb mod 8 = 0 -> nb + 8 <= r_end nreg -> r_end nreg <= 2 ^ 63 ->
  0 <= ptr_addr pname < 2 ^ 64 ->
  lookup (TAtom "glibc_error#str.255") (ge_globals ge) = Some prefix ->
  find_fn ge (TAtom "__fxprintf") = Some (Defined prefixfn) ->
  call_frame prefixfn [WPtr null;WPtr prefix;WPtr pname] = Some prefixframe ->
  (⊢ live_capq dqn (ptr_cap pname) namer -∗ S -∗
    WP (ERun prefixframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
      live_capq dqn (ptr_cap pname) namer ∗ Q }}) ->
  live nb nreg -∗ pcell nb 0 pname -∗ live_capq dqn (ptr_cap pname) namer -∗ S -∗
  (∀ e', ⌜error_inputs e' status errnum fmt ap mode cb⌝ -∗
    live nb nreg -∗ pcell nb 0 pname -∗ live_capq dqn (ptr_cap pname) namer -∗ Q -∗
    WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e' [] None
      (Enter (TAtom "iw_2.start") (Some (TAtom "L13")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e [] None
    (Enter (TAtom "L13") (Some from))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hinputs Hn Hnb Hna Hne Hnr Hnu Hprefix Hfx Hfxframe Hfxcall.
  iIntros "Hnl Hnp Hname HS HK". step. step. step.
  iApply (wp_live_fit1 with "Hnl"). iIntros ([Hn0 Hn48]) "Hnl".
  check "Hnl".
  iApply (wp_raw_load_pointer_dq with "Hnl Hnp Hname");
    [reflexivity | vx | left; reflexivity | a2 | a2 | exact Hnu |].
  iNext. iIntros "Hnl Hnp Hname".
  iApply wp_call_bind; [vx | exact Hfx | exact Hfxframe |]. iNext.
  iApply (wp_wand with "[Hname HS]"); [iApply (Hfxcall with "Hname HS") |].
  iIntros (v) "H". iDestruct "H" as (r ->) "[Hname HQ]". resume. step.
  iApply ("HK" with "[%] Hnl Hnp Hname HQ").
  destruct Hinputs as (? & ? & ? & ? & ? & ? & ?).
  unfold error_inputs. repeat split; lk_prove.
Qed.

(** The captured start block allocates and initializes the saved-state slot,
    then disables cancellation. Its remaining instructions flush stdout
    and choose between the custom and default prefixes. *)
Definition error_after_cancel : point := Eval vm_compute in
  match find_block (TAtom "start") (fn_blocks Unit_misc_error_os.fn___error_internal) with
  | Some b => Exec (TAtom "start") (skipn 4 (b_insts b)) (b_jump b)
  | None => Enter (TAtom "start") None
  end.

(** After disabling cancellation, error flushes stdout and reads the callback
    pointer. The caller keeps permission to access the thread and the saved
    cancellation state while these operations select the default prefix. *)
Lemma error_default_start_suffix e status errnum fmt ap mode cb
    ob oreg stdout dqo outr pb preg flushfn flushframe (R S : iProp Σ) Φ :
  error_inputs e status errnum fmt ap mode cb ->
  lookup (TAtom "stdout") (ge_globals ge) = Some (mkPtr ob (Obj ob)) ->
  0 < ob -> ob mod 8 = 0 -> ob + 8 <= r_end oreg -> r_end oreg <= 2 ^ 63 ->
  0 <= ptr_addr stdout < 2 ^ 64 ->
  lookup (TAtom "error_print_progname") (ge_globals ge) = Some (mkPtr pb (Obj pb)) ->
  0 < pb -> pb mod 8 = 0 -> pb + 8 <= r_end preg -> r_end preg <= 2 ^ 63 ->
  find_fn ge (TAtom "__GI__IO_fflush") = Some (Defined flushfn) ->
  call_frame flushfn [WPtr stdout] = Some flushframe ->
  (⊢ live_capq dqo (ptr_cap stdout) outr -∗ R -∗
    WP (ERun flushframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
      live_capq dqo (ptr_cap stdout) outr ∗ S }}) ->
  live ob oreg -∗ pcell ob 0 stdout -∗ live_capq dqo (ptr_cap stdout) outr -∗
  live pb preg -∗ pcell pb 0 null -∗ R -∗
  (∀ e', ⌜error_inputs e' status errnum fmt ap mode cb⌝ -∗
    live ob oreg -∗ pcell ob 0 stdout -∗ live_capq dqo (ptr_cap stdout) outr -∗
    live pb preg -∗ pcell pb 0 null -∗ S -∗
    WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e' [] None
      (Enter (TAtom "L13") (Some (TAtom "start")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e [] None error_after_cancel) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hinputs Ho Hob Hoa Hoe Hor Hou Hp Hpb Hpa Hpe Hpr Hflush Hff Hflushcall.
  iIntros "Hol Hop Hout Hpl Hpp HR HK". unfold error_after_cancel.
  step. iApply (wp_live_fit1 with "Hol"). iIntros ([Ho0 Ho48]) "Hol".
  check "Hol".
  iApply (wp_raw_load_pointer_dq with "Hol Hop Hout");
    [reflexivity | vx | left; reflexivity | a2 | a2 | exact Hou |].
  iNext. iIntros "Hol Hop Hout".
  iApply wp_call_bind; [vx | exact Hflush | exact Hff |]. iNext.
  iApply (wp_wand with "[Hout HR]"); [iApply (Hflushcall with "Hout HR") |].
  iIntros (v) "H". iDestruct "H" as (r ->) "[Hout HS]". resume.
  step. iApply (wp_live_fit1 with "Hpl"). iIntros ([Hp0 Hp48]) "Hpl".
  check "Hpl".
  iAssert (live_capq DfracDiscarded (ptr_cap null) preg) with "[]" as "Hnull"; [done |].
  iApply (wp_raw_load_pointer_dq with "Hpl Hpp Hnull");
    [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; lia |].
  iNext. iIntros "Hpl Hpp _". step. step. branch_as true.
  iApply ("HK" with "[%] Hol Hop Hout Hpl Hpp HS").
  destruct Hinputs as (? & ? & ? & ? & ? & ? & ?).
  unfold error_inputs. repeat split; lk_prove.
Qed.

(** The flush and prefix may fail or change errno. Neither call changes
    the saved error argument. The callback cell is read and returned as
    null; the proof never checks or invokes a callback function. *)
Lemma wp_error_internal_default_entry status errnum fmt ap mode tb treg state
    ob oreg stdout dqo outr pb preg nb nreg pname dqn namer prefix
    flushfn flushframe prefixfn prefixframe (R S Q E : iProp Σ) Φ :
  ow_self w0 = mkPtr tb (Obj tb) ->
  0 < tb -> tb mod 8 = 0 -> tb + 796 <= r_end treg -> r_end treg <= 2 ^ 63 ->
  state = 0 \/ state = 1 ->
  find_fn ge (TAtom "__GI___pthread_setcancelstate") = Some (Defined Unit_nptl_pthread_setcancelstate_os.fn___GI___pthread_setcancelstate) ->
  lookup (TAtom "stdout") (ge_globals ge) = Some (mkPtr ob (Obj ob)) ->
  0 < ob -> ob mod 8 = 0 -> ob + 8 <= r_end oreg -> r_end oreg <= 2 ^ 63 ->
  0 <= ptr_addr stdout < 2 ^ 64 ->
  lookup (TAtom "error_print_progname") (ge_globals ge) = Some (mkPtr pb (Obj pb)) ->
  0 < pb -> pb mod 8 = 0 -> pb + 8 <= r_end preg -> r_end preg <= 2 ^ 63 ->
  lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (mkPtr nb (Obj nb)) ->
  0 < nb -> nb mod 8 = 0 -> nb + 8 <= r_end nreg -> r_end nreg <= 2 ^ 63 ->
  0 <= ptr_addr pname < 2 ^ 64 ->
  lookup (TAtom "glibc_error#str.255") (ge_globals ge) = Some prefix ->
  find_fn ge (TAtom "__GI__IO_fflush") = Some (Defined flushfn) ->
  call_frame flushfn [WPtr stdout] = Some flushframe ->
  (⊢ live_capq dqo (ptr_cap stdout) outr -∗ R -∗
    WP (ERun flushframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
      live_capq dqo (ptr_cap stdout) outr ∗ S }}) ->
  find_fn ge (TAtom "__fxprintf") = Some (Defined prefixfn) ->
  call_frame prefixfn [WPtr null;WPtr prefix;WPtr pname] = Some prefixframe ->
  (⊢ live_capq dqn (ptr_cap pname) namer -∗ S -∗
    WP (ERun prefixframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
      live_capq dqn (ptr_cap pname) namer ∗ Q }}) ->
  live tb treg -∗ int_cell tb 792 state -∗
  live ob oreg -∗ pcell ob 0 stdout -∗ live_capq dqo (ptr_cap stdout) outr -∗
  live pb preg -∗ pcell pb 0 null -∗
  live nb nreg -∗ pcell nb 0 pname -∗ live_capq dqn (ptr_cap pname) namer -∗ R -∗ E -∗
  (∀ e from cb, ⌜error_inputs e status errnum fmt ap mode cb⌝ -∗
    live tb treg -∗ int_cell tb 792 1 -∗
    live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 state -∗
    live ob oreg -∗ pcell ob 0 stdout -∗ live_capq dqo (ptr_cap stdout) outr -∗
    live pb preg -∗ pcell pb 0 null -∗
    live nb nreg -∗ pcell nb 0 pname -∗ live_capq dqn (ptr_cap pname) namer -∗ Q -∗ E -∗
    WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e [] None
      (Enter (TAtom "iw_2.start") (Some from))) : gexpr) {{ Φ }}) -∗
  WP (ERun (error_internal_frame status errnum fmt ap mode) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hself Htb Htal Hte Htr Hstate Hcancel Ho Hob Hoa Hoe Hor Hou
    Hp Hpb Hpa Hpe Hpr Hn Hnb Hna Hne Hnr Hnu Hprefix Hflush Hff Hflushcall Hfx Hfxframe Hfxcall.
  iIntros "Ht Hstate Hol Hop Hout Hpl Hpp Hnl Hnp Hname HR HE HK".
  unfold error_internal_frame. step.
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (cb [Hcb0 [Hcal Hcend]]) "Hobj".
  change (cb + 16 <= 2 ^ 48) in Hcend.
  iDestruct (obj_zero_block with "Hobj") as "(Hcl & Hbytes & Haux)"; [compute; discriminate |].
  iAssert (live cb (mkRegion cb (cb + 16) Heap Live)) with "Hcl" as "Hcl".
  set (creg := mkRegion cb (cb + 16) Heap Live) in *.
  assert (Hcre : r_end creg = cb + 16) by reflexivity.
  change (Z.to_nat (req_extent (heap_req 4 4))) with 16%nat.
  change (replicate 16 0) with ([0;0;0;0] ++ replicate 12 0)%list.
  rewrite bytes_app. iDestruct "Hbytes" as "[Hsave _]".
  check "Hcl". store_int "Hcl" "Hsave".
  iApply wp_call_bind; [vx | exact Hcancel | reflexivity |]. iNext.
  iApply (error_disable Hreg Hext _ tb treg cb _ state with "Ht Hstate Hcl [Hsave]");
    try reflexivity; try assumption; try (cbn; lia).
  { iSplit; [done | iExact "Hsave"]. }
  iNext. iIntros "Ht Hstate Hcl Hsave". resume.
  iApply (error_default_start_suffix _ status errnum fmt ap mode cb
    ob oreg stdout dqo outr pb preg flushfn flushframe R S
    with "Hol Hop Hout Hpl Hpp HR"); try assumption.
  { unfold error_inputs. repeat split; lk_prove. }
  iIntros (e' Hinputs) "Hol Hop Hout Hpl Hpp HS".
  iApply (error_default_prefix_block _ _ status errnum fmt ap mode cb
    nb nreg pname dqn namer prefix prefixfn prefixframe S Q
    with "Hnl Hnp Hname HS"); try assumption.
  iIntros (e'' Hinputs') "Hnl Hnp Hname HQ".
  iApply ("HK" with "[%] Ht Hstate Hcl Hsave Hol Hop Hout Hpl Hpp Hnl Hnp Hname HQ HE").
  exact Hinputs'.
Qed.
End entry.
