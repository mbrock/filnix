(** Main calls glibc to set the locale, print the greeting and close
    the streams on exit. This file collects those call proofs in
    [HelloLibs] for the private state that startup supplies. *)

From Glibc Require Import HelloObjects GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic MemLogic.
From Glibc Require Import HelloBodies.

From Glibc Require Import OsWorld OsRegistry AtexitLogic HelloGlibcDebts HelloGlibcLibsT
  HelloGlibcLibsStr HelloGlibcLibsName HelloGlibcLibsSys HelloGlibcLibsExit.
From Glibc Require ExitRun.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Import LG0 LG0.L HelloGlibcDebts HelloGlibcDebts.SW.FI.ML.

Section libs.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (Hk : hello_link ge o) (Hos : hello_os_layout w0 o).
Local Instance libs_stable : SafepointStable (os_wi w0) := os_wi_stable w0.
Local Instance libs_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.

(** Gnulib's `c: proper_name` returns its argument and touches nothing. *)
Lemma libs_proper_name : forall p,
  fn_triple w0 ge (TAtom "proper_name") [WPtr p] True (fun r => ⌜r = Ret (WPtr p)⌝)%I.
Proof using Hk.
  intros p. exists proper_name_fn. split; [exact (hk_proper_name _ _ Hk)|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr. injection Hfr as <-. iIntros "_ HK".
  iApply wp_enter; [vm_compute; reflexivity | reflexivity |]. iNext.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext. iApply "HK". done.
Qed.

(** The initially empty handler list becomes a one-callback list. *)
Lemma hello_libs (priv : iProp Σ) c (Ha : setlocale_all w0 ge o priv)
    (Hq : setlocale_query w0 ge o priv)
    (Hcl : close_stdout_narrow w0 ge o priv)
    (Hcw : close_stdout_wide w0 ge o priv)
    (Hm : mbsrtowcs w0 ge o priv)
    (Hw : wprintf_greeting w0 ge o priv)
    (Hp : HelloPrints w0 ge o priv) :
  HelloLibs w0 ge o priv
    (AtexitLogic.exit_funcs_inv (ho_x o) [] c ∗ ExitRun.exit_lock_free (ho_el o) (ho_elr o))%I
    (AtexitLogic.exit_funcs_inv (ho_x o) [(ho_cp o, null, null)] ((c + 1) mod 2 ^ 64) ∗ ExitRun.exit_lock_free (ho_el o) (ho_elr o))%I.
Proof using Hk Hos.
  constructor; [..| exact Ha | exact Hq | exact Hcl | exact Hcw | exact Hm | exact Hw | exact Hp].
  - exact (libs_mbszero w0 ge o Hk).
  - exact (libs_name w0 ge o Hk).
  - destruct (libs_atexit w0 ge o Hk Hos c) as (gf & Hg & Hcall & Hspec).
    exists gf. split; [exact Hg|]. split; [exact Hcall|]. intros fr Φ Hfr.
    iIntros "[HX Hl] HK". iApply (Hspec _ _ Hfr with "HX").
    iIntros (r) "(%k & %Hr & HX)". iApply "HK". iExists k. iSplit; [done|]. iFrame.
  - exact (libs_xmalloc w0 ge o Hk).
  - exact (libs_strlen w0 ge o Hk).
  - exact (libs_strncmp w0 ge o Hk).
  - exact (libs_errno w0 ge o Hk).
  - exact (libs_free w0 ge o Hk).
  - intros n S' Hc. exact (libs_exit w0 ge o Hk Hos priv ((c + 1) mod 2 ^ 64) n S' Hc).
  - exact libs_proper_name.
Qed.
End libs.
