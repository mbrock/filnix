(** Exit first runs the registered close callback and then cleans up
    stdin and stderr. This file composes those proved functions in the
    linked program. Its entry state explicitly requires an initialized
    thread and single-thread flag; it does not identify that state with
    the untouched loader image or prove process startup. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld OsRegistry FileInv AtexitLogic ExitRun ExitRunCode
  HiAtexitBase HiAtexitFns HiAtexitGe HiAtexitCloseIt HiAtexitCloseStdout
  HiAtexitStdout HiAtexitStdoutClose HiAtexitCleanup HiAtexitExitEnv.
Import ListNotations.
Open Scope Z_scope.
Import HGV.ER HGV.ER.XL.XT HGV.ER.XL.XT.AX HLG HLG.L
  HFL HFL.FI.

(** The remaining streams are stderr and stdin, in list order. *)
Definition hi_exit_streams : list ptr := [mkPtr 69328 (Obj 69328); mkPtr 69568 (Obj 69568)].

(** Atexit receives the actual linked close callback's function pointer. *)
Definition hi_close_ptr : ptr := mkPtr 65536 (Fn (TAtom "hi_atexit#close_stdout_hi")).

Section resources.
Context `{!gen_heapGS piece pval Σ}.

(** Cleanup owns the initialized thread and remaining streams, with
    no pending output in either stream. *)
Definition hi_exit_tail_state (w0 : os_world) : iProp Σ :=
  single_ro hge 73808 (mkRegion 73808 73816 GlobalData Live) ∗
  tcb_cleanup_inv (ow_self w0) ∗ io_list_inv hge hi_exit_streams ∗
  [∗ list] g ∈ hi_exit_streams, stream_life g ∗ exit_stream false g.

(** The callback additionally owns stdout after puts and its global
    pointer. The other streams keep their fields while stdout closes. *)
Definition hi_exit_callback_state (w0 : os_world) (s : list Z) : iProp Σ :=
  vtables_ro hge 71072 (mkRegion 71072 73424 GlobalData Live) ∗
  single_ro hge 73808 (mkRegion 73808 73816 GlobalData Live) ∗
  tcb_cleanup_inv (ow_self w0) ∗
  live 70976 (mkRegion 70976 70984 GlobalData Live) ∗ pcell 70976 0 (mkPtr 69808 (Obj 69808)) ∗
  hi_stdout_after w0 68176 71072 s (mkPtr 69808 (Obj 69808)) None ∗
  io_list_inv hge [mkPtr 69328 (Obj 69328); mkPtr 69808 (Obj 69808); mkPtr 69568 (Obj 69568)] ∗
  [∗ list] g ∈ hi_exit_streams, stream_life g ∗ exit_stream false g.

End resources.

(** Proof-mode searches leave the combined stream resources folded. *)
#[local] Hint Opaque hi_exit_tail_state hi_exit_callback_state
  single_ro vtables_ro io_list_inv tcb_cleanup_inv stream_life exit_stream : typeclass_instances.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world).

(** Exit runs in the linked program with the fixed post-start OS world. *)
Local Instance hi_exit_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry hge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) hge.
Local Notation sexpr := (language.expr (nanofil_lang glibc_os_registry hge)).

(** Closing stdout returns the resources for the remaining cleanup.
    Output errors may instead end the process; success is not assumed. *)
Lemma hi_exit_callback s : s <> [] -> ow_errno w0 = Some (mkPtr 68176 (Obj 68176)) ->
  hi_exit_callback_state w0 s -∗
  WP (ERun hi_close_frame : sexpr) {{ o, ⌜o = RetVoid⌝ ∗ hi_exit_tail_state w0 }}.
Proof.
  intros Hs Heb. rewrite /hi_exit_callback_state.
  iIntros "(Hvt & #Hs & Htcb & Hso & Hsoc & Hout & Hio & Hrest)".
  iDestruct (big_sepL_sep with "Hrest") as "[Hlives Hfields]".
  iApply (hi_stdout_after_close w0 s [mkPtr 69328 (Obj 69328)] [mkPtr 69568 (Obj 69568)]
    (mkPtr 69808 (Obj 69808)) 68176 71072 (mkRegion 71072 73424 GlobalData Live)
    73808 (mkRegion 73808 73816 GlobalData Live)
    (mkPtr 68672 (Fn (TAtom "glibc_genops#flush_cleanup"))) (mkPtr 69568 (Obj 69568))
    70976 (mkRegion 70976 70984 GlobalData Live)
    with "Hvt Hs Htcb Hso Hsoc Hout Hio Hlives");
    [exact Hs | vm_compute; reflexivity | reflexivity | cbn; lia
    | vm_compute; reflexivity | vm_compute; reflexivity | cbn; lia | cbn; lia
    | vm_compute; reflexivity | cbn; lia | exact Heb |].
  iNext. iIntros "Htcb Hio Hlives". iSplit; [done|].
  rewrite /hi_exit_tail_state. iFrame "Hs Htcb Hio".
  iApply big_sepL_sep. iFrame "Hlives Hfields".
Qed.

(** The linked handler has the calling convention that atexit expects. *)
Lemma hi_exit_handler s : s <> [] -> ow_errno w0 = Some (mkPtr 68176 (Obj 68176)) ->
  ⊢ exit_handler w0 hge 0 (hi_close_ptr, null, null)
    (hi_exit_callback_state w0 s) (hi_exit_tail_state w0).
Proof.
  intros Hs Heb.
  iApply (exit_handler_void w0 hge 0 hi_close_ptr null (TAtom "hi_atexit#close_stdout_hi")
    hi_close_fn hi_close_frame);
    [reflexivity | vm_compute; reflexivity | exact hi_find_close | cbn; lia
    | reflexivity | reflexivity | reflexivity | exact hi_close_call |].
  iApply hi_exit_callback; assumption.
Qed.

(** Exit runs the one registered callback and the actual glibc cleanup.
    The remaining premises describe the registration objects and OS
    world, not unproved call rules. *)
Lemma hi_exit_after_puts s Φ :
  s <> [] -> ow_errno w0 = Some (mkPtr 68176 (Obj 68176)) ->
  loop_env w0 hge hi_exit_objs ->
  exit_lock_env w0 hge 73728 (mkRegion 73728 73744 GlobalData Live) ->
  exit_funcs_inv hi_exit_objs [(hi_close_ptr, null, null)] 1 -∗
  exit_lock_free 73728 (mkRegion 73728 73744 GlobalData Live) -∗
  hi_exit_callback_state w0 s -∗
  WP (ERun (mkFrame glibc_exit [(TAtom "v0", WInt 0)] [] None (Enter (TAtom "start") None)) : sexpr) {{ Φ }}.
Proof.
  intros Hs Heb Henv Hlock. iIntros "Hinv Hlock HP".
  iApply (wp_glibc_exit w0 hge hi_exit_objs 73728 (mkRegion 73728 73744 GlobalData Live)
    [(hi_close_ptr, null, null)] 1 0 (hi_exit_callback_state w0 s)
    (fun n => match n with O => hi_exit_tail_state w0 | S _ => hi_exit_callback_state w0 s end)
    with "Hinv Hlock HP [] [] []");
    [exact Henv | exact Hlock | exact (hi_find___run_exit_handlers _) | | |].
  - iApply (HGV.dtors_rule_tls w0 hge (hi_find___GI___call_tls_dtors _)).
  - rewrite big_sepL_singleton. iApply hi_exit_handler; assumption.
  - rewrite /hi_exit_tail_state. iApply hi_cleanup_rule; [vm_compute; reflexivity|cbn; lia].
Qed.

End rules.
