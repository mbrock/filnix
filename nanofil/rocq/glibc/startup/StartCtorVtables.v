(** This module proves the contract of `c: check_stdfiles_vtables`,
    stated in [StartCtorVtablesSpec](StartCtorVtablesSpec.v), over the
    function's compiled body. For each standard stream the body loads the
    table pointer, subtracts the start of `c: __io_vtables`, and checks
    that the offset lies inside that table.

    ## How the proof is arranged

    A failed check would end the program, so the proof must show that
    all three checks pass. They pass because each stream's table pointer
    lies 336 bytes into the array, well inside it. The runner of
    constructors then uses the contract and never this file. *)

From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps StartCode GlibcSpec StartCtorVtablesSpec.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** ## The walk through the body

    The body checks stdin, then stdout, then stderr, in the same way
    each time. It loads the stream's table pointer, measures how far it
    lies from the start of the table, and compares that distance with
    the table's size. *)

(** The body returns once all three checks pass, and gives back what it
    read. *)
Lemma wp_check_vtables fr fi fireg fo foreg fe fereg vb vreg dq Φ :
  call_frame start_check_vtables_fn [] = Some fr ->
  lookup (TAtom "_IO_2_1_stdin_") (ge_globals ge) = Some (mkPtr fi (Obj fi)) ->
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals ge) = Some (mkPtr fo (Obj fo)) ->
  lookup (TAtom "_IO_2_1_stderr_") (ge_globals ge) = Some (mkPtr fe (Obj fe)) ->
  lookup (TAtom "__io_vtables") (ge_globals ge) = Some (mkPtr vb (Ro vb)) ->
  0 < fi -> fi mod 8 = 0 -> fi + 224 <= r_end fireg <= 2 ^ 48 ->
  0 < fo -> fo mod 8 = 0 -> fo + 224 <= r_end foreg <= 2 ^ 48 ->
  0 < fe -> fe mod 8 = 0 -> fe + 224 <= r_end fereg <= 2 ^ 48 -> 0 <= vb < 2 ^ 48 ->
  vt_ok dq fi fireg vb -∗ vt_ok dq fo foreg vb -∗ vt_ok dq fe fereg vb -∗ liveq dq vb vreg -∗
  ▷ (vt_ok dq fi fireg vb -∗ vt_ok dq fo foreg vb -∗ vt_ok dq fe fereg vb -∗ liveq dq vb vreg -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hi Ho He Hv Hi0 Hial Hiend Ho0 Hoal Hoend He0 Heal Heend Hvb. injection Hfr as <-.
  iIntros "[Hli Hci] [Hlo Hco] [Hle Hce] Hlv HK".
  step. step_global Hi. step. norm.
  check_read_dq "Hli" by (a2). iNext. iIntros "Hli".
  load_pointer_dq "Hli Hci Hlv" by (a2). iNext. iIntros "Hli Hci Hlv".
  step_global Hv. step. step. step. step. branch_as true.
  step. step_global Ho. step. norm.
  check_read_dq "Hlo" by (a2). iNext. iIntros "Hlo".
  load_pointer_dq "Hlo Hco Hlv" by (a2). iNext. iIntros "Hlo Hco Hlv".
  step_global Hv. step. step. step. step. step. step. branch_as true.
  step. step_global He. step. norm.
  check_read_dq "Hle" by (a2). iNext. iIntros "Hle".
  load_pointer_dq "Hle Hce Hlv" by (a2). iNext. iIntros "Hle Hce Hlv".
  step_global Hv. step. step. step. step. step. step. branch_as true.
  step. iApply wp_ret_void. iNext. iApply ("HK" with "[$Hli $Hci] [$Hlo $Hco] [$Hle $Hce] Hlv").
Qed.

(** ## The contract

    The instance below repackages the lemma as the contract that callers
    import, for any program in which the name runs the image's body. *)

(** Any program whose image defines the check with this body meets the
    check's contract. *)
#[global] Instance check_vtables_has_spec
    `{!Defines ge "glibc_vtables#check_stdfiles_vtables" start_check_vtables_fn} :
  HasSpec registry (os_wi w0) ge (TAtom "glibc_vtables#check_stdfiles_vtables") check_vtables_spec.
Proof using Type.
  intros [[[[[[[[fi fireg] fo] foreg] fe] fereg] vb] vreg] dq]. exists start_check_vtables_fn.
  split; [apply defines|]. split; [eexists; reflexivity|]. intros fr Φ Hfr.
  cbn [fs_pre fs_post fs_args check_vtables_spec].
  iIntros "(%H & Hi & Ho & He & Hv) HK".
  destruct H as ((Hgi & Hgo & Hge & Hgv & Hvb) & (Hi0 & Hial & Hiend) & (Ho0 & Hoal & Hoend) & (He0 & Heal & Heend)).
  iApply (wp_check_vtables with "Hi Ho He Hv"); try eassumption.
  iNext. iIntros "Hi Ho He Hv". iApply "HK". iFrame. done.
Qed.

End rules.
