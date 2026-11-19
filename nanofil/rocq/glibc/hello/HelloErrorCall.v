(** Hello calls error to explain a failed close. This proof follows that
    call through argument setup, cancellation setup and the attempt to flush
    closed stdout. The caller must still prove the code that prints the
    program name and reports the message.

    Cancellation may be enabled or disabled before this call. The call
    disables it and remembers its old value. The existing cleanup invariant
    supplies the enabled case without adding ownership. *)
From Glibc Require Import Unit_libio_fileops_os Unit_libio_iofflush_os Unit_misc_error_os Unit_nptl_pthread_setcancelstate_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity VariadicLogic.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic SysWrappers
  ErrorCall ErrorEntry HelloErrorClosed Fix.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic OsWorld SysWrappers.
Open Scope Z_scope.

Section call.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Cancellation setup does not touch the cleanup pointers. They remain
    available to the reporting suffix alongside the saved old flag. *)
Definition error_cleanup_fields tb jb : iProp Σ :=
  pcell tb off_cleanup null ∗ pcell tb off_cleanup_jmp jb.
Definition error_thread_ready state : iProp Σ :=
  ∃ tb treg jb, ⌜ow_self w0 = mkPtr tb (Obj tb) /\ 0 < tb /\ tb mod 8 = 0 /\
    tb + 796 <= r_end treg /\ r_end treg <= 2 ^ 63⌝ ∗
    live tb treg ∗ int_cell tb 792 state ∗ error_cleanup_fields tb jb.

(** The existing cleanup invariant says cancellation is enabled. Unpacking
    it exposes that zero flag and the memory it already owns. *)
Lemma error_cleanup_exchange : tcb_cleanup_inv (ow_self w0) ⊣⊢ error_thread_ready 0.
Proof using Type.
  unfold tcb_cleanup_inv, error_thread_ready, error_cleanup_fields.
  iSplit; iIntros "H"; iDestruct "H" as (tb treg jb Hfacts) "(Hl & H1 & H2 & H3)";
    iExists tb, treg, jb; iSplit; try iFrame;
    iPureIntro; unfold off_cancelhandling in *; destruct Hfacts as (? & ? & ? & ? & ?);
    repeat split; auto; lia.
Qed.

Context (fb : Z) (freg : region) (vb lb : Z) (lbreg : region) (ob : Z) (oreg : region)
  (pb : Z) (preg : region) (callback : ptr) (dqc : dfrac) (cbr : region)
  (nb : Z) (nreg : region) (pname : ptr) (dqn : dfrac) (namer : region).
Let loan := error_stdout_loan fb freg ob oreg.
Let private := error_private_cells pb preg callback dqc cbr nb nreg pname dqn namer.
Let report := error_closed_report fb freg ob oreg pb preg callback dqc cbr nb nreg pname dqn namer.
Context (Hreg : holds_os registry) (Hext : sys_external ge)
  (Hsync : ge_fn ge "_IO_new_file_sync" Unit_libio_fileops_os.fn__IO_new_file_sync).

(** Replacing error with another definition does not preserve this rule:
    its public name must resolve to the captured function. Message reporting
    receives the original argument snapshot, its cursor at byte 24, mode
    zero and the saved error number. The program-name calls need separate
    contracts for fxprintf with a null stream and for a custom callback. *)
Lemma wp_call_error_closed f e ls l args rest j status errnum fmt ys state
    vbreg sb sreg prefix prefixfn prefixframe cbname cbfn cbframe
    (D Q Done E : iProp Σ) Φ :
  let flush := error_closed_flush fb vb lb lbreg vbreg sb sreg D in
  map_option (arg_x ge e) args = Some (WInt status :: WInt errnum :: WPtr fmt :: ys) ->
  find_fn ge (TAtom "error") = Some (Defined Unit_misc_error_os.fn___error) ->
  forallb snapshot_word ys = true -> 0 <= status < 2 ^ 32 -> 0 <= errnum < 2 ^ 32 ->
  find_fn ge (TAtom "__error_internal") = Some (Defined Unit_misc_error_os.fn___error_internal) ->
  state = 0 \/ state = 1 ->
  find_fn ge (TAtom "__GI___pthread_setcancelstate") = Some (Defined Unit_nptl_pthread_setcancelstate_os.fn___GI___pthread_setcancelstate) ->
  lookup (TAtom "stdout") (ge_globals ge) = Some (mkPtr ob (Obj ob)) ->
  0 < ob -> ob mod 8 = 0 -> ob + 8 <= r_end oreg -> r_end oreg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  lookup (TAtom "error_print_progname") (ge_globals ge) = Some (mkPtr pb (Obj pb)) ->
  0 < pb -> pb mod 8 = 0 -> pb + 8 <= r_end preg -> r_end preg <= 2 ^ 63 ->
  0 <= ptr_addr callback < 2 ^ 64 ->
  lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (mkPtr nb (Obj nb)) ->
  0 < nb -> nb mod 8 = 0 -> nb + 8 <= r_end nreg -> r_end nreg <= 2 ^ 63 ->
  0 <= ptr_addr pname < 2 ^ 64 ->
  lookup (TAtom "glibc_error#str.255") (ge_globals ge) = Some prefix ->
  find_fn ge (TAtom "__GI__IO_fflush") = Some (Defined Unit_libio_iofflush_os.fn___GI__IO_fflush) ->
  find_fn ge (TAtom "__fxprintf") = Some (Defined prefixfn) ->
  call_frame prefixfn [WPtr null;WPtr prefix;WPtr pname] = Some prefixframe ->
  (⊢ live_capq dqn (ptr_cap pname) namer -∗ flush -∗
    WP (ERun prefixframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
      live_capq dqn (ptr_cap pname) namer ∗ Q }}) ->
  (ptr_addr callback <> 0 -> ptr_cap callback = Fn cbname) ->
  (ptr_addr callback <> 0 -> function_check_res ge callback = Some ok) ->
  find_fn ge cbname = Some (Defined cbfn) ->
  indirect_call_conv cbfn CVoid [] [] = Some (Converted [] None) ->
  call_frame cbfn [] = Some cbframe ->
  (⊢ flush -∗ WP (ERun cbframe : gexpr) {{ v, ⌜v = RetVoid⌝ ∗ Q }}) ->
  (forall tb treg jb ap, ow_self w0 = mkPtr tb (Obj tb) ->
    0 < tb -> tb mod 8 = 0 -> tb + 796 <= r_end treg -> r_end treg <= 2 ^ 63 ->
    ⊢ report tb treg state status errnum fmt ap 0 Q
      (error_va ap (WInt status :: WInt errnum :: WPtr fmt :: ys) ∗ error_cleanup_fields tb jb)%I
      (fun v => ⌜v = RetVoid⌝ ∗ Done)%I) ->
  error_thread_ready state -∗ loan -∗ private -∗ flush -∗ E -∗
  ▷ (Done -∗ E -∗ WP (ERun (mkFrame f e ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call CVoid (Global (TAtom "error")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Hext Hreg Hsync cbr dqc.
  intros flush Hargs Hpublic Hys Hstatus Herrnum Hinternal Hstate Hcancel
    Ho Hob Hoa Hoe Hor Hfb Hfa Hfe Hfr Hp Hpb Hpa Hpe Hpr Hcu
    Hn Hnb Hna Hne Hnr Hnu Hprefix Hflush Hfx Hfxframe Hfxcall
    Hcap Hcheck Hcbfn Hconv Hcbframe Hcbcall Hreport.
  assert (Hcall : forall ap, ⊢ error_va ap (WInt status :: WInt errnum :: WPtr fmt :: ys) -∗
    (error_thread_ready state ∗ loan ∗ private ∗ flush) -∗
    WP (ERun (error_internal_frame status errnum fmt ap 0) : gexpr)
      {{ v, ⌜v = RetVoid⌝ ∗ Done }}).
  { intros ap. iIntros "Hva (Ht & Ho & Hp & Hflush)".
    iDestruct "Ht" as (tb treg jb [Hself [Htb [Hta [Hte Htr]]]]) "(Ht & Hflag & Hcleanup)".
    iApply (wp_error_closed_entry fb freg vb lb lbreg ob oreg pb preg callback dqc cbr nb nreg pname dqn namer
      Hreg Hext Hsync status errnum fmt ap 0 tb treg state vbreg sb sreg prefix prefixfn prefixframe
      cbname cbfn cbframe D Q (error_va ap (WInt status :: WInt errnum :: WPtr fmt :: ys) ∗
        error_cleanup_fields tb jb)%I
      with "Ht Hflag Ho Hp Hflush [$Hva $Hcleanup]"); try assumption.
    iApply Hreport; assumption. }
  iIntros "Ht Ho Hp Hflush HE HK".
  iApply (wp_call_error_wrapper f e ls l args rest j status errnum fmt ys
    (fun ap => error_internal_frame status errnum fmt ap 0)
    (error_thread_ready state ∗ loan ∗ private ∗ flush)%I Done E
    with "[$Ht $Ho $Hp $Hflush] HE HK"); try assumption.
  intros ap. apply error_internal_call_frame.
Qed.
End call.
