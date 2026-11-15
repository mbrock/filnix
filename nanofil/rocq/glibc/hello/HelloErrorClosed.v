(** Hello can report an error after closing stdout. Reporting tries to
    flush stdout again, so its memory must remain available. This proof
    uses the memory that fclose returned to execute that flush.

    Printing the program name and the message still need separate proofs.
    Reporting disables thread cancellation and saves its previous setting.
    The proof stops before the code that restores that setting. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps SysWrappers
  PrintfStateCode ErrorCode ErrorEntry FflushCode FileSyncCode HelloClosedStdout Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic
  LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section closed.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (fb : Z) (freg : region) (vb lb : Z) (lbreg : region) (ob : Z) (oreg : region).

(** The lower retained diagnostic state owns this cell and target already.
    Lending them moves ownership; a global lookup alone supplies neither. *)
Definition error_stdout_loan : iProp Σ :=
  live ob oreg ∗ pcell ob 0 (mkPtr fb (Obj fb)) ∗ live fb freg.
Lemma error_stdout_exchange :
  (live ob oreg ∗ pcell ob 0 (mkPtr fb (Obj fb))) ∗ closed_stdout fb freg vb lb lbreg
  ⊣⊢ error_stdout_loan ∗ closed_stdout_fields fb vb lb lbreg.
Proof.
  unfold error_stdout_loan, closed_stdout. iSplit.
  - iIntros "((Ho & Hp) & Hl & Hfields)". iFrame.
  - iIntros "((Ho & Hp & Hl) & Hfields)". iFrame.
Qed.

(** The flush reads a separately lent sync slot. Keeping it outside the
    vtable invariant preserves the existing invariant's meaning. *)
Definition error_closed_flush vbreg sb sreg (D : iProp Σ) : iProp Σ :=
  closed_stdout_fields fb vb lb lbreg ∗ vtables_ro ge vb vbreg ∗
  pcellq DfracDiscarded vb (vt_file + 96) (sym_ptr ge "_IO_new_file_sync") ∗
  single_ro ge sb sreg ∗ D.

Context (pb : Z) (preg : region) (callback : ptr) (dqc : dfrac) (cbr : region)
  (nb : Z) (nreg : region) (pname : ptr) (dqn : dfrac) (namer : region).

(** The caller supplies the callback and program-name cells and their
    targets. The retained stdout state cannot manufacture these resources. *)
Definition error_private_cells : iProp Σ :=
  live pb preg ∗ pcell pb 0 callback ∗ live_capq dqc (ptr_cap callback) cbr ∗
  live nb nreg ∗ pcell nb 0 pname ∗ live_capq dqn (ptr_cap pname) namer.

(** After printing the program name, execution reaches the message itself.
    This remaining code receives the original arguments and argument cursor.
    Its temporary cell records the previous cancellation flag. *)
Definition error_closed_report tb treg state status errnum fmt ap mode
    (Q E : iProp Σ) Φ : iProp Σ :=
  ∀ e from cb, ⌜error_inputs e status errnum fmt ap mode cb⌝ -∗
    live tb treg -∗ int_cell tb 792 1 -∗
    live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 state -∗
    error_stdout_loan -∗ error_private_cells -∗ Q -∗ E -∗
    WP (ERun (mkFrame glibc_error_internal e [] None
      (Enter (TAtom "iw_2.start") (Some from))) : gexpr) {{ Φ }}.

Context (Hreg : holds_os registry) (Hext : sys_external ge)
  (Hsync : ge_fn ge "_IO_new_file_sync" glibc__IO_new_file_sync).

(** The prefix may consume the closed fields or other lent state. Its
    contract, rather than an assumption about output success, determines
    what reaches the reporting suffix. Both callback branches are covered. *)
Lemma wp_error_closed_entry status errnum fmt ap mode tb treg state
    vbreg sb sreg prefix prefixfn prefixframe cbname cbfn cbframe
    (D Q E : iProp Σ) Φ :
  ow_self w0 = mkPtr tb (Obj tb) ->
  0 < tb -> tb mod 8 = 0 -> tb + 796 <= r_end treg -> r_end treg <= 2 ^ 63 ->
  state = 0 \/ state = 1 ->
  find_fn ge (TAtom "__GI___pthread_setcancelstate") = Some (Defined glibc___pthread_setcancelstate) ->
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
  find_fn ge (TAtom "__GI__IO_fflush") = Some (Defined glibc__IO_fflush) ->
  find_fn ge (TAtom "__fxprintf") = Some (Defined prefixfn) ->
  call_frame prefixfn [WPtr null;WPtr prefix;WPtr pname] = Some prefixframe ->
  (⊢ live_capq dqn (ptr_cap pname) namer -∗ error_closed_flush vbreg sb sreg D -∗
    WP (ERun prefixframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
      live_capq dqn (ptr_cap pname) namer ∗ Q }}) ->
  (ptr_addr callback <> 0 -> ptr_cap callback = Fn cbname) ->
  (ptr_addr callback <> 0 -> function_check_res ge callback = Some ok) ->
  find_fn ge cbname = Some (Defined cbfn) ->
  indirect_call_conv cbfn CVoid [] [] = Some (Converted [] None) ->
  call_frame cbfn [] = Some cbframe ->
  (⊢ error_closed_flush vbreg sb sreg D -∗
    WP (ERun cbframe : gexpr) {{ v, ⌜v = RetVoid⌝ ∗ Q }}) ->
  live tb treg -∗ int_cell tb 792 state -∗ error_stdout_loan -∗ error_private_cells -∗
  error_closed_flush vbreg sb sreg D -∗ E -∗
  error_closed_report tb treg state status errnum fmt ap mode Q E Φ -∗
  WP (ERun (error_internal_frame status errnum fmt ap mode) : gexpr) {{ Φ }}.
Proof.
  intros Hself Htb Hta Hte Htr Hstate Hcancel Ho Hob Hoa Hoe Hor Hfb Hfa Hfe Hfr
    Hp Hpb Hpa Hpe Hpr Hcu Hn Hnb Hna Hne Hnr Hnu Hprefix Hflush
    Hfx Hfxframe Hfxcall Hcap Hcheck Hcbfn Hconv Hcbframe Hcbcall.
  assert (Hflushcall : ⊢ live fb freg -∗ error_closed_flush vbreg sb sreg D -∗
    WP (ERun (mkFrame glibc__IO_fflush [(TAtom "v0", WPtr (mkPtr fb (Obj fb)))] [] None
      (Enter (TAtom "start") None)) : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
        live fb freg ∗ error_closed_flush vbreg sb sreg D }}).
  { iIntros "Hl (Hfields & #Hvt & #Hslot & #Hs & HD)".
    iApply (wp_wand with "[Hl Hfields HD]").
    { iApply (wp_closed_stdout_fflush Hreg Hext Hsync _ fb freg vb lb lbreg sb sreg vbreg D
        with "Hvt Hslot Hs Hl [$Hfields $HD]");
        try reflexivity; try assumption. rewrite Hself. cbn. lia. }
    iIntros (v) "H". iDestruct "H" as (r ->) "[Hl [Hfields HD]]".
    iExists r. iSplit; [done |]. iFrame "Hl". unfold error_closed_flush.
    iFrame "Hfields". iFrame "Hvt Hslot Hs HD". }
  iIntros "Ht Hstate (Hol & Hop & Hout) (Hpl & Hpp & Hcb & Hnl & Hnp & Hname) HR HE HK".
  iApply (wp_error_internal_entry Hreg Hext status errnum fmt ap mode tb treg state
    ob oreg (mkPtr fb (Obj fb)) (DfracOwn 1) freg pb preg callback dqc cbr nb nreg pname dqn namer prefix
    glibc__IO_fflush _ prefixfn prefixframe cbname cbfn cbframe
    (error_closed_flush vbreg sb sreg D) (error_closed_flush vbreg sb sreg D) Q E
    with "Ht Hstate Hol Hop Hout Hpl Hpp Hcb Hnl Hnp Hname HR HE");
    try assumption; try reflexivity; try (cbn; lia); try exact Hflushcall.
  iIntros (e from cb Hinputs) "Ht Hflag Hcl Hsave Hol Hop Hout Hpl Hpp Hcb Hnl Hnp Hname HQ HE".
  iApply ("HK" with "[%] Ht Hflag Hcl Hsave [Hol Hop Hout] [Hpl Hpp Hcb Hnl Hnp Hname] HQ HE");
    [exact Hinputs | unfold error_stdout_loan; iFrame | unfold error_private_cells; iFrame].
Qed.
End closed.
