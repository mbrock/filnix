(** A public error call with a null program-name callback uses the default
    prefix. This rule runs its argument wrapper and the closed-stdout flush
    before that prefix. It retains the original argument cursor and cleanup
    fields for the report and requires no custom callback function. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Heap
  Language Logic MemLogic Identity VariadicLogic.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps SysWrappers
  ErrorCode ErrorEntry ErrorDefaultEntry ErrorCall PrintfStateCode FflushCode FileSyncCode
  FflushClosed HelloClosedStdout HelloErrorClosed HelloErrorCall Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic
  LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section call.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (fb : Z) (freg : region) (vb lb : Z) (lbreg : region) (ob : Z) (oreg : region)
  (pb : Z) (preg : region) (nb : Z) (nreg : region) (pname : ptr) (dqn : dfrac) (namer : region).
Let loan := error_stdout_loan fb freg ob oreg.
Let private := error_private_cells pb preg null DfracDiscarded preg nb nreg pname dqn namer.
Context (Hreg : holds_os registry) (Hext : sys_external ge)
  (Hsync : ge_fn ge "_IO_new_file_sync" glibc__IO_new_file_sync).

(** Flushing stdout leaves it closed. The caller proves that printing the
    prefix and the report preserves the arguments and the thread's cleanup
    fields, so the public wrapper can finish after the report returns. *)
Lemma wp_call_error_default_closed f e ls l args rest j status errnum fmt ys state
    vbreg sb sreg prefix prefixfn prefixframe (D Q Done E : iProp Σ) Φ :
  let flush := error_closed_flush fb vb lb lbreg vbreg sb sreg D in
  map_option (arg_x ge e) args = Some (WInt status :: WInt errnum :: WPtr fmt :: ys) ->
  find_fn ge (TAtom "error") = Some (Defined glibc_error) ->
  forallb snapshot_word ys = true -> 0 <= status < 2 ^ 32 -> 0 <= errnum < 2 ^ 32 ->
  find_fn ge (TAtom "__error_internal") = Some (Defined glibc_error_internal) ->
  state = 0 \/ state = 1 ->
  find_fn ge (TAtom "__GI___pthread_setcancelstate") = Some (Defined glibc___pthread_setcancelstate) ->
  lookup (TAtom "stdout") (ge_globals ge) = Some (mkPtr ob (Obj ob)) ->
  0 < ob -> ob mod 8 = 0 -> ob + 8 <= r_end oreg -> r_end oreg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  lookup (TAtom "error_print_progname") (ge_globals ge) = Some (mkPtr pb (Obj pb)) ->
  0 < pb -> pb mod 8 = 0 -> pb + 8 <= r_end preg -> r_end preg <= 2 ^ 63 ->
  lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (mkPtr nb (Obj nb)) ->
  0 < nb -> nb mod 8 = 0 -> nb + 8 <= r_end nreg -> r_end nreg <= 2 ^ 63 ->
  0 <= ptr_addr pname < 2 ^ 64 ->
  lookup (TAtom "glibc_error#str.255") (ge_globals ge) = Some prefix ->
  find_fn ge (TAtom "__GI__IO_fflush") = Some (Defined glibc__IO_fflush) ->
  find_fn ge (TAtom "__fxprintf") = Some (Defined prefixfn) ->
  call_frame prefixfn [WPtr null;WPtr prefix;WPtr pname] = Some prefixframe ->
  (⊢ live_capq dqn (ptr_cap pname) namer -∗ flush -∗
    WP (ERun prefixframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
      live_capq dqn (ptr_cap pname) namer ∗ Q }}) ->
  (forall tb treg jb ap, ow_self w0 = mkPtr tb (Obj tb) ->
    0 < tb -> tb mod 8 = 0 -> tb + 796 <= r_end treg -> r_end treg <= 2 ^ 63 ->
    ⊢ error_closed_report fb freg ob oreg pb preg null DfracDiscarded preg nb nreg pname dqn namer
      tb treg state status errnum fmt ap 0 Q
      (error_va ap (WInt status :: WInt errnum :: WPtr fmt :: ys) ∗ error_cleanup_fields tb jb)%I
      (fun v => ⌜v = RetVoid⌝ ∗ Done)%I) ->
  error_thread_ready state -∗ loan -∗ private -∗ flush -∗ E -∗
  ▷ (Done -∗ E -∗ WP (ERun (mkFrame f e ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call CVoid (Global (TAtom "error")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros flush Hargs Hpublic Hys Hstatus Herrnum Hinternal Hstate Hcancel
    Ho Hob Hoa Hoe Hor Hfb Hfa Hfe Hfr Hp Hpb Hpa Hpe Hpr
    Hn Hnb Hna Hne Hnr Hnu Hprefix Hflush Hfx Hfxframe Hfxcall Hreport.
  assert (Hcall : forall ap, ⊢ error_va ap (WInt status :: WInt errnum :: WPtr fmt :: ys) -∗
    (error_thread_ready state ∗ loan ∗ private ∗ flush) -∗
    WP (ERun (error_internal_frame status errnum fmt ap 0) : gexpr)
      {{ v, ⌜v = RetVoid⌝ ∗ Done }}).
  { intros ap. iIntros "Hva (Ht & Ho & Hp & Hflush)".
    iDestruct "Ht" as (tb treg jb [Hself [Htb [Hta [Hte Htr]]]]) "(Ht & Hflag & Hcleanup)".
    assert (Hflushcall : ⊢ live fb freg -∗ flush -∗
      WP (ERun (mkFrame glibc__IO_fflush [(TAtom "v0", WPtr (mkPtr fb (Obj fb)))] [] None
        (Enter (TAtom "start") None)) : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗ live fb freg ∗ flush }}).
    { iIntros "Hl (Hfields & #Hvt & #Hslot & #Hs & HD)".
      iApply (wp_wand with "[Hl Hfields HD]").
      { iApply (wp_closed_stdout_fflush Hreg Hext Hsync _ fb freg vb lb lbreg sb sreg vbreg D
          with "Hvt Hslot Hs Hl [$Hfields $HD]"); try reflexivity; try assumption.
        rewrite Hself. cbn. lia. }
      iIntros (v) "H". iDestruct "H" as (r ->) "[Hl [Hfields HD]]".
      iExists r. iSplit; [done |]. iFrame "Hl". unfold flush, error_closed_flush.
      iFrame "Hfields Hvt Hslot Hs HD". }
    iDestruct "Ho" as "(Hol & Hop & Hout)".
    iDestruct "Hp" as "(Hpl & Hpp & _ & Hnl & Hnp & Hname)".
    iApply (wp_error_internal_default_entry Hreg Hext status errnum fmt ap 0 tb treg state
      ob oreg (mkPtr fb (Obj fb)) (DfracOwn 1) freg pb preg nb nreg pname dqn namer prefix
      glibc__IO_fflush _ prefixfn prefixframe flush flush Q
      (error_va ap (WInt status :: WInt errnum :: WPtr fmt :: ys) ∗ error_cleanup_fields tb jb)%I
      with "Ht Hflag Hol Hop Hout Hpl Hpp Hnl Hnp Hname Hflush [$Hva $Hcleanup]");
      try assumption; try reflexivity; try (cbn; lia); try exact Hflushcall.
    iIntros (env from saved Hinputs) "Ht Hflag Hsavedl Hsaved Hol Hop Hout Hpl Hpp Hnl Hnp Hname HQ HE".
    iApply (Hreport tb treg jb ap Hself Htb Hta Hte Htr $! env from saved with
      "[%] Ht Hflag Hsavedl Hsaved [Hol Hop Hout] [Hpl Hpp Hnl Hnp Hname] HQ HE");
      [exact Hinputs | unfold error_stdout_loan; iFrame | unfold error_private_cells; iFrame; done]. }
  iIntros "Ht Ho Hp Hflush HE HK".
  iApply (wp_call_error_wrapper f e ls l args rest j status errnum fmt ys
    (fun ap => error_internal_frame status errnum fmt ap 0)
    (error_thread_ready state ∗ loan ∗ private ∗ flush)%I Done E
    with "[$Ht $Ho $Hp $Hflush] HE HK"); try assumption.
  intros ap. apply error_internal_call_frame.
Qed.
End call.
