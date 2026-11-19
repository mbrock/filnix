(** Main registers the close callback, prints hello and exits. This file
    proves those calls together from an initialized main-entry state.
    Every library call uses a proved rule for the linked function.
    Establishing that entry state is separate from this execution proof;
    in particular, the loader image alone is not its precondition. *)

From Glibc Require Fix.
From Glibc Require Import HiAtexit_hi_atexit.
From Glibc Require Import GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld OsRegistry FileInv WordString AtexitLogic ExitRun
  HiAtexitModule HiAtexitFns HiAtexitGe HiAtexitStdout
  AllocCall HiAtexitInitial HiAtexitExitEnv HiAtexitPuts HiAtexitExit.
From Glibc Require ExitRunTail LibioFlushInv.
Import ListNotations.
Open Scope Z_scope.
Import ExitRun ExitRunTail AtexitLogic OsWorld Fix.LG0 Fix.LG0.L LibioFlushInv FileInv.

(** This is main's body in the actual linked module. *)
Definition hi_main_fn : func := HiAtexit_hi_atexit.fn_main.

(** Main has no parameters in this fixture. *)
Definition hi_main_frame : frame := mkFrame hi_main_fn [] [] None (Enter (TAtom "start") None).

(** A call with no arguments starts this exact main body. *)
Lemma hi_main_call : call_frame hi_main_fn [] = Some hi_main_frame.
Proof. reflexivity. Qed.

(** The linked main symbol resolves to that body. *)
Lemma hi_find_main : find_fn hge (TAtom "main") = Some (Defined hi_main_fn).
Proof. vm_compute. reflexivity. Qed.

Section resources.
Context `{!gen_heapGS piece pval Σ}.

(** Main owns the initialized streams, thread, allocator and empty
    callback array. The string includes the aligned window strlen reads. *)
Definition hi_main_state (w0 : os_world) : iProp Σ :=
  vtables_ro hge 73504 (mkRegion 73504 75856 GlobalData Live) ∗
  single_ro hge 76240 (mkRegion 76240 76248 GlobalData Live) ∗
  tcb_cleanup_inv (ow_self w0) ∗
  live 73408 (mkRegion 73408 73416 GlobalData Live) ∗ pcell 73408 0 (mkPtr 72240 (Obj 72240)) ∗
  hi_stdout_before w0 70608 73504 (mkPtr 72240 (Obj 72240)) 0 None ∗
  malloc_call_state (DfracOwn 1) 68800 68992 65888 hi_mp_reg hi_tc_reg hi_dummy_reg ∗
  io_list_inv hge [mkPtr 71760 (Obj 71760); mkPtr 72240 (Obj 72240); mkPtr 72000 (Obj 72000)] ∗
  ([∗ list] g ∈ hi_exit_streams, stream_life g ∗ exit_stream false g) ∗
  word_string (DfracOwn 1) (mkPtr 65568 (Ro 65568)) [104; 101; 108; 108; 111] ∗
  exit_funcs_inv hi_exit_objs [] 0 ∗ exit_lock_free 76160 (mkRegion 76160 76176 GlobalData Live).

End resources.

(** Proof-mode searches do not expand the combined entry resources. *)
#[local] Hint Opaque hi_main_state hi_exit_callback_state hi_stdout_before hi_stdout_after
  single_ro vtables_ro io_list_inv tcb_cleanup_inv stream_life exit_stream malloc_call_state word_string
  exit_funcs_inv exit_lock_free : typeclass_instances.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world).

(** Execution uses the linked program and the post-start OS world. *)
Local Instance hi_main_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry hge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) hge.
Local Notation sexpr := (language.expr (nanofil_lang glibc_os_registry hge)).

(** Main is safe even when output or closing fails. The postcondition
    is arbitrary because exit, including the error callback path, ends
    the process rather than returning to main. *)
Lemma hi_main_wp Φ :
  ow_errno w0 = Some (mkPtr 70608 (Obj 70608)) -> ptr_addr (ow_self w0) <> 0 ->
  loop_env w0 hge hi_exit_objs ->
  exit_lock_env w0 hge 76160 (mkRegion 76160 76176 GlobalData Live) ->
  hi_main_state w0 -∗ WP (ERun hi_main_frame : sexpr) {{ Φ }}.
Proof using Type.
  intros Heb Hself Henv Hlock. pose proof Henv as (Hlay & Hgl & Hwi & _).
  assert (Hfns : exit_fns hge).
  { split; [exact (hi_find___new_exitfn _)|]. split; [exact (hi_find___internal_atexit _)|exact (hi_find___cxa_atexit _)]. }
  assert (Hclose : lookup (TAtom "hi_atexit#close_stdout_hi") (ge_globals hge) = Some hi_close_ptr)
    by (vm_compute; reflexivity).
  assert (Hstr : lookup (TAtom "hi_atexit#str.0") (ge_globals hge) = Some (mkPtr 65568 (Ro 65568)))
    by (vm_compute; reflexivity).
  rewrite /hi_main_state.
  iIntros "(#Hvt & #Hs & Htcb & Hso & Hsoc & Hout & HM & Hio & Hrest & Hstr & Hinv & Hlock)".
  unfold hi_main_frame. step. step_global Hclose.
  eapply step_wand; [eapply wp_call_bind; inst;
    [reflexivity | exact (hi_find_atexit _) | reflexivity] |].
  iApply (wp_glibc_atexit glibc_os_registry (os_wi w0) hge hi_exit_objs [] 0 hi_close_ptr with "Hinv");
    [exact Hlay | exact Hgl | exact Hwi | exact Hfns | cbn; lia | cbn; lia |].
  iIntros "Hinv". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. step_global Hstr.
  eapply step_wand; [eapply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ [WPtr (mkPtr 65568 (Ro 65568))]); inst;
    [reflexivity | exact (hi_find_puts _) | reflexivity] |].
  iApply (hi_puts w0 (DfracOwn 1) 68800 68992 65888 hi_mp_reg hi_tc_reg hi_dummy_reg
    with "Hvt Hs Hstr Hso Hsoc Hout HM");
    [vm_compute; reflexivity | vm_compute; reflexivity | reflexivity
    | vm_compute; reflexivity | reflexivity | cbn; lia | exact Heb | exact Hself |].
  iNext. iIntros (r Hr) "Hstr Hso Hsoc Hout HM".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  eapply step_wand; [eapply wp_call_bind; inst;
    [reflexivity | exact (hi_find_exit _) | reflexivity] |].
  iApply (hi_exit_after_puts w0 [104; 101; 108; 108; 111] with "Hinv Hlock [Htcb Hso Hsoc Hout Hio Hrest]");
    [discriminate | exact Heb | exact Henv | exact Hlock |].
  rewrite /hi_exit_callback_state. iFrame "Hvt Hs Htcb Hso Hsoc Hout Hio Hrest".
Qed.

End rules.
