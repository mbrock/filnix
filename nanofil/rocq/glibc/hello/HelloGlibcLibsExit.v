(** This file discharges Hello's call of glibc exit. The registered
    close_stdout callback is the caller's premise, but registration, dispatch,
    TLS destructors and final stream cleanup use their concrete proofs. *)

From Glibc Require Import Unit_stdlib_exit_os.
From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Machine
  ExternalCalls Pieces Heap Language Logic MemLogic.
From Glibc Require Import IRFrames HelloBodies.

From Glibc Require Import OsWorld OsRegistry AtexitLogic ExitRunTail ExitRun
  HelloGlibcDebts HelloGlibcLibsT HelloGlibcLibsCleanup.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Import LG0 LG0.L HelloGlibcDebts HelloGlibcDebts.SW.FI.ML.

Section libs.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (Hk : hello_link ge o) (Hos : hello_os_layout w0 o).
(** Collector safepoints preserve the concrete OS interpretation. *)
Local Instance exit_stable : SafepointStable (os_wi w0) :=
  SW.OW.os_wi_stable w0.
(** The call runs with the concrete glibc OS registry. *)
Local Instance exit_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.

(** The concrete object layout establishes all preservation premises of the loop. *)
Lemma hello_exit_env : ExitRunTail.loop_env w0 ge (ho_x o).
Proof using Type*.
  split; [exact (hk_exit_layout _ _ Hk)|]. split; [exact (hk_exit_globals _ _ Hk)|].
  split.
  - split; [|split]; refine (hello_os_write w0 o _ _ Hos _); cbn; tauto.
  - split; [|split; [|exact (hk_exit_soft _ _ Hk)]];
      refine (hello_os_write w0 o _ _ Hos _); cbn; tauto.
Qed.

(** The thread cookie and external symbol facts establish the recursive-lock contract. *)
Lemma hello_exit_lock_env : ExitRun.exit_lock_env w0 ge (ho_el o) (ho_elr o).
Proof using Type*.
  destruct (hk_el _ _ Hk) as (H0 & H8 & He & Hg).
  split; [exact H0|]. split; [exact H8|]. split; [exact He|]. split; [exact Hg|].
  split; [refine (hello_os_write w0 o _ _ Hos _); cbn; tauto|].
  split; [exact (proj1 Hos)|exact (hk_cookie _ _ Hk)].
Qed.

(** The compiled TLS destructor function returns immediately in this build. *)
Lemma hello_dtors (P : iProp Σ) : ⊢ ExitRun.dtors_rule w0 ge P P.
Proof using Hk.
  iIntros (f e ls lab rest j Ψ) "HP HK".
  iApply wp_call_bind; [reflexivity | exact (hk_dtors _ _ Hk) | reflexivity |]. iNext.
  iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
  iApply wp_ret_void. iNext. iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  iApply ("HK" with "HP").
Qed.

(** The concrete cleanup triple supplies the exit loop's cleanup call rule. *)
Lemma hello_cleanup : ⊢ ExitRunTail.cleanup_rule w0 ge (exit_io w0 ge o).
Proof using Hk.
  iIntros (f e ls lab d rest j Ψ) "HP HK".
  iApply (wp_call_fn w0 ge _ [] with "HP"); [exact (libs_cleanup w0 ge o Hk)|reflexivity|].
  iIntros (r) "(%n & %Hr & _)". destruct Hr as [-> Hn].
  iExists _. iSplit; [iPureIntro; cbn; rewrite Z.mod_small; [reflexivity|exact Hn]|].
  iNext. iApply "HK".
Qed.

(** Exit invokes the registered callback and never returns to main. *)
Lemma libs_exit (priv : iProp Σ) c n (S : iProp Σ) :
  fn_triple w0 ge (TAtom "close_stdout") [] (hello_ro ge o ∗ S ∗ priv ∗ names o)
    (fun r => ⌜r = RetVoid⌝ ∗ exit_io w0 ge o)%I ->
  fn_triple w0 ge (TAtom "exit") [WInt n]
    (hello_ro ge o ∗ S ∗ priv ∗ names o ∗
      (AtexitLogic.exit_funcs_inv (ho_x o) [(ho_cp o, null, null)] c ∗ ExitRun.exit_lock_free (ho_el o) (ho_elr o))) (fun _ => False)%I.
Proof using Hk Hos.
  intros Hclose. exists Unit_stdlib_exit_os.fn___GI_exit. split; [exact (hk_exit _ _ Hk)|]. split; [eexists; reflexivity|]. intros fr Φ Hfr.
  change (Some (mkFrame Unit_stdlib_exit_os.fn___GI_exit [(TAtom "v0", WInt n)] [] None (Enter (TAtom "start") None)) = Some fr)
    in Hfr. injection Hfr as <-.
  set (P := (hello_ro ge o ∗ S ∗ priv ∗ names o)%I).
  set (Q := fun i : nat => if Nat.eqb i 0 then exit_io w0 ge o else P).
  iIntros "(Hro & Hio & Hpv & Hnames & HX & Hl) _".
  iApply (ExitRun.wp_glibc_exit w0 ge (ho_x o) (ho_el o) (ho_elr o) [(ho_cp o, null, null)] c n P Q
    with "HX Hl [Hro Hio Hpv Hnames] [] [] []");
    [exact hello_exit_env | exact hello_exit_lock_env | exact (hk_run_exit _ _ Hk) | | | |].
  - iSplitL "Hro"; [iExact "Hro"|]. iSplitL "Hio"; [iExact "Hio"|]. iSplitL "Hpv"; [iExact "Hpv"|iExact "Hnames"].
  - cbn [Q]. iApply hello_dtors.
  - cbn [Q]. iSplitL; [|done].
    destruct (hk_cp _ _ Hk) as (Hcap & Hcheck & Haddr).
    iApply (ExitRun.exit_handler_void w0 ge _ (ho_cp o) null (TAtom "close_stdout") close_stdout_fn
      (invocation close_stdout_fn []) P (exit_io w0 ge o));
      [exact Hcap | exact Hcheck | exact (hk_close_stdout _ _ Hk) | lia | reflexivity | reflexivity |
       reflexivity | reflexivity |].
    destruct Hclose as (gf & Hgf & Hcall & Hspec).
    rewrite (hk_close_stdout _ _ Hk) in Hgf. injection Hgf as <-.
    iIntros "HP". iApply (Hspec _ _ eq_refl with "HP"). iIntros (r) "Hr". iExact "Hr".
  - iApply hello_cleanup.
Qed.
End libs.
