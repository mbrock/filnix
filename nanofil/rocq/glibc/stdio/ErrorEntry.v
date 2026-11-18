(** Error reporting first disables cancellation, flushes stdout and prints
    the program name. This module executes that prefix of __error_internal.
    The message formatter and the rest of reporting remain a continuation.

    Hello may report a failure after closing stdout. This rule still needs
    proof that the stdout object is alive and that flushing its closed state
    is safe. The global cells of stdout and the callback may be shared,
    and a null callback needs no contract for the function it would call. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps
  SysWrappers PrintfStateCode CancelState ErrorCode Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps
  OsWorld SysWrappers.
Open Scope Z_scope.

(** These registers carry the original arguments and the saved-state slot.
    Neither the stream flush nor the prefix call may replace them. *)
Definition error_inputs e status errnum fmt ap mode cb : Prop :=
  lookup (TAtom "v0") e = Some (WInt status) /\
  lookup (TAtom "v2") e = Some (WInt errnum) /\
  lookup (TAtom "v4") e = Some (WPtr fmt) /\
  lookup (TAtom "v6") e = Some (WPtr ap) /\
  lookup (TAtom "v8") e = Some (WInt mode) /\
  lookup (TAtom "v10") e = Some (WPtr (mkPtr cb (Obj cb))) /\
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr cb (Obj cb))).

(** Binding the internal function does not copy or advance the cursor. *)
Definition error_internal_frame status errnum fmt ap mode :=
  mkFrame glibc_error_internal
    (put (TAtom "v8") (WInt mode) (put (TAtom "v6") (WPtr ap)
      (put (TAtom "v4") (WPtr fmt) (put (TAtom "v2") (WInt errnum)
        (put (TAtom "v0") (WInt status) []))))) [] None (Enter (TAtom "start") None).
Lemma error_internal_call_frame status errnum fmt ap mode :
  call_frame glibc_error_internal [WInt status;WInt errnum;WPtr fmt;WPtr ap;WInt mode] =
    Some (error_internal_frame status errnum fmt ap mode).
Proof. reflexivity. Qed.

Section entry.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Local Instance error_entry_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Both supported cancellation states save their actual old value.
    Other flag combinations, including asynchronous cancellation, are excluded. *)
Lemma error_disable fr tb treg cb creg state Φ :
  call_frame glibc___pthread_setcancelstate [WInt 1;WPtr (mkPtr cb (Obj cb))] = Some fr ->
  ow_self w0 = mkPtr tb (Obj tb) ->
  0 < tb -> tb mod 8 = 0 -> tb + 796 <= r_end treg -> r_end treg <= 2 ^ 63 ->
  0 < cb -> cb + 4 <= r_end creg -> r_end creg <= 2 ^ 63 -> state = 0 \/ state = 1 ->
  live tb treg -∗ int_cell tb 792 state -∗ live cb creg -∗ int_cell cb 0 0 -∗
  ▷ (live tb treg -∗ int_cell tb 792 1 -∗ live cb creg -∗ int_cell cb 0 state -∗
    Φ (Ret (WInt 0))) -∗ WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hself Htb Htal Hte Htr Hcb Hce Hcr [-> | ->];
    iIntros "Ht Hs Hl Hv HK".
  - iApply (wp_cancel_disable_save Hreg Hext fr tb treg cb creg 0 0 with "Ht Hs Hl Hv HK");
      try assumption; try lia. rewrite Z.add_0_r. exact Hfr.
  - iApply (wp_cancel_disabled_save Hreg Hext fr tb treg cb creg 0 0 with "Ht Hs Hl Hv HK");
      try assumption; try lia. rewrite Z.add_0_r. exact Hfr.
Qed.

(** Reporting continues even when flushing or printing the program name
    returns an error. These calls may change errno, but the saved error
    argument stays unchanged. The caller lends resources R to flushing,
    then S to the prefix call, and receives Q before message formatting.
    Resources E remain untouched, including any saved argument cursor. *)
Lemma wp_error_internal_entry {dqs dqp : dfrac} status errnum fmt ap mode tb treg state
    ob oreg stdout dqo outr pb preg callback dqc cbr nb nreg pname dqn namer prefix
    flushfn flushframe prefixfn prefixframe cbname cbfn cbframe
    (R S Q E : iProp Σ) Φ :
  ow_self w0 = mkPtr tb (Obj tb) ->
  0 < tb -> tb mod 8 = 0 -> tb + 796 <= r_end treg -> r_end treg <= 2 ^ 63 ->
  state = 0 \/ state = 1 ->
  find_fn ge (TAtom "__GI___pthread_setcancelstate") = Some (Defined glibc___pthread_setcancelstate) ->
  lookup (TAtom "stdout") (ge_globals ge) = Some (mkPtr ob (Obj ob)) ->
  0 < ob -> ob mod 8 = 0 -> ob + 8 <= r_end oreg -> r_end oreg <= 2 ^ 63 ->
  0 <= ptr_addr stdout < 2 ^ 64 ->
  lookup (TAtom "error_print_progname") (ge_globals ge) = Some (mkPtr pb (Obj pb)) ->
  0 < pb -> pb mod 8 = 0 -> pb + 8 <= r_end preg -> r_end preg <= 2 ^ 63 ->
  0 <= ptr_addr callback < 2 ^ 64 ->
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
  (ptr_addr callback <> 0 -> ptr_cap callback = Fn cbname) ->
  (ptr_addr callback <> 0 -> function_check_res ge callback = Some ok) ->
  (ptr_addr callback <> 0 -> find_fn ge cbname = Some (Defined cbfn)) ->
  (ptr_addr callback <> 0 -> indirect_call_conv cbfn CVoid [] [] = Some (Converted [] None)) ->
  (ptr_addr callback <> 0 -> call_frame cbfn [] = Some cbframe) ->
  (ptr_addr callback <> 0 -> ⊢ S -∗ WP (ERun cbframe : gexpr) {{ v, ⌜v = RetVoid⌝ ∗ Q }}) ->
  live tb treg -∗ int_cell tb 792 state -∗
  liveq dqs ob oreg -∗ pcellq dqs ob 0 stdout -∗ live_capq dqo (ptr_cap stdout) outr -∗
  liveq dqp pb preg -∗ pcellq dqp pb 0 callback -∗ live_capq dqc (ptr_cap callback) cbr -∗
  live nb nreg -∗ pcell nb 0 pname -∗ live_capq dqn (ptr_cap pname) namer -∗ R -∗ E -∗
  (∀ e from cb, ⌜error_inputs e status errnum fmt ap mode cb⌝ -∗
    live tb treg -∗ int_cell tb 792 1 -∗
    live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 state -∗
    liveq dqs ob oreg -∗ pcellq dqs ob 0 stdout -∗ live_capq dqo (ptr_cap stdout) outr -∗
    liveq dqp pb preg -∗ pcellq dqp pb 0 callback -∗ live_capq dqc (ptr_cap callback) cbr -∗
    live nb nreg -∗ pcell nb 0 pname -∗ live_capq dqn (ptr_cap pname) namer -∗ Q -∗ E -∗
    WP (ERun (mkFrame glibc_error_internal e [] None
      (Enter (TAtom "iw_2.start") (Some from))) : gexpr) {{ Φ }}) -∗
  WP (ERun (error_internal_frame status errnum fmt ap mode) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hself Htb Htal Hte Htr Hstate Hcancel Ho Hob Hoa Hoe Hor Hou
    Hp Hpb Hpa Hpe Hpr Hcu Hn Hnb Hna Hne Hnr Hnu Hprefix Hflush Hff Hflushcall
    Hfx Hfxframe Hfxcall Hcap Hcheck Hcbfn Hconv Hcbframe Hcbcall.
  iIntros "Ht Hstate Hol Hop Hout Hpl Hpp Hcb Hnl Hnp Hname HR HE HK".
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
  iApply (error_disable _ tb treg cb _ state with "Ht Hstate Hcl [Hsave]");
    try reflexivity; try assumption; try (cbn; lia).
  { iSplit; [done | iExact "Hsave"]. }
  iNext. iIntros "Ht Hstate Hcl Hsave". resume.
  step. iApply (wp_live_fit with "Hol"). iIntros ([Ho0 Ho48]) "Hol".
  check_read_dq "Hol" by a2. iNext. iIntros "Hol".
  iApply (wp_raw_load_pointer_dq with "Hol Hop Hout");
    [reflexivity | vx | left; reflexivity | a2 | a2 | exact Hou |].
  iNext. iIntros "Hol Hop Hout".
  iApply wp_call_bind; [vx | exact Hflush | exact Hff |]. iNext.
  iApply (wp_wand with "[Hout HR]"); [iApply (Hflushcall with "Hout HR") |].
  iIntros (v) "H". iDestruct "H" as (r ->) "[Hout HS]". resume.
  step. iApply (wp_live_fit with "Hpl"). iIntros ([Hp0 Hp48]) "Hpl".
  check_read_dq "Hpl" by a2. iNext. iIntros "Hpl".
  iApply (wp_raw_load_pointer_dq with "Hpl Hpp Hcb");
    [reflexivity | vx | left; reflexivity | a2 | a2 | exact Hcu |].
  iNext. iIntros "Hpl Hpp Hcb". step. step.
  destruct (Z.eq_dec (ptr_addr callback) 0) as [Hz|Hz].
  - branch_as true. step. step. step.
    iApply (wp_live_fit1 with "Hnl"). iIntros ([Hn0 Hn48]) "Hnl".
    check "Hnl".
    iApply (wp_raw_load_pointer_dq with "Hnl Hnp Hname");
      [reflexivity | vx | left; reflexivity | a2 | a2 | exact Hnu |].
    iNext. iIntros "Hnl Hnp Hname".
    iApply wp_call_bind; [vx | exact Hfx | exact Hfxframe |]. iNext.
    iApply (wp_wand with "[Hname HS]"); [iApply (Hfxcall with "Hname HS") |].
    iIntros (v) "H". iDestruct "H" as (r' ->) "[Hname HQ]". resume. step.
    iApply ("HK" with "[%] Ht Hstate Hcl Hsave Hol Hop Hout Hpl Hpp Hcb Hnl Hnp Hname HQ HE").
    unfold error_inputs. repeat split; lk_prove.
  - branch_as false. step. step. check_read_dq "Hpl" by a2. iNext. iIntros "Hpl".
    iApply (wp_raw_load_pointer_dq with "Hpl Hpp Hcb");
      [reflexivity | vx | left; reflexivity | a2 | a2 | exact Hcu |].
    iNext. iIntros "Hpl Hpp Hcb".
    iApply wp_check_function; [vx | apply Hcheck; exact Hz |]. iNext.
    iApply wp_raw_call_bind; [vx | apply Hcap; exact Hz | apply Hcheck; exact Hz | vx |
      exact (Hcbfn Hz) | exact (Hconv Hz) | |].
    { destruct (variadic_func cbfn); cbn; rewrite ?skipn_nil; exact (Hcbframe Hz). }
    iNext. iApply (wp_wand with "[HS]"); [iApply (Hcbcall Hz with "HS") |].
    iIntros (v) "[-> HQ]". resume. step.
    iApply ("HK" with "[%] Ht Hstate Hcl Hsave Hol Hop Hout Hpl Hpp Hcb Hnl Hnp Hname HQ HE").
    unfold error_inputs. repeat split; lk_prove.
Qed.
End entry.
