(** This file constructs HelloLibs from the concrete library proofs.
    Only the close_stdout callback uses HelloCore; glibc registers and
    invokes that callback using its proved exit-handler machinery. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic MemLogic.
From Nanofil Require HelloVersion.
From Glibc Require Import OsWorld OsRegistry AtexitLogic HelloGlibcDebts HelloGlibcLibsT
  HelloGlibcMainLibsCalls HelloGlibcLibsSys HelloGlibcLibsCleanup HelloGlibcLibsExit.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** The interface exposes concrete exit resources and the completed record. *)
Module Type HelloMainLibsSig (D : HelloDebtsT) (AX : AtexitT).
Import LG0 LG0.L D D.SW.FI.ML.
(** The recursive exit lock starts unlocked, with no owner. *)
Definition exit_lock `{!gen_heapGS piece pval Σ} (o : hello_objs) : iProp Σ :=
  live (ho_el o) (ho_elr o) ∗ bytes (ho_el o) 0 [0; 0; 0; 0] ∗ bytes (ho_el o) 4 [0; 0; 0; 0] ∗
  pcell (ho_el o) 8 null.
(** The initially empty handler list becomes a one-callback list. The
    print calls and both cases of the close callback are proved elsewhere,
    from the image's code, and are passed in. *)
Parameter hello_libs : forall `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}
  (w0 : os_world) (ge : genv) (o : hello_objs), hello_link ge o -> hello_os_layout w0 o ->
  forall (debt : D.HelloCore w0 ge o) c, D.setlocale_query w0 ge o (D.hd_priv w0 ge o debt) ->
  D.close_stdout_narrow w0 ge o (D.hd_priv w0 ge o debt) ->
  D.close_stdout_wide w0 ge o (D.hd_priv w0 ge o debt) ->
  D.mbsrtowcs w0 ge o (D.hd_priv w0 ge o debt) ->
  D.wprintf_greeting w0 ge o (D.hd_priv w0 ge o debt) ->
  D.HelloPrints w0 ge o (D.hd_priv w0 ge o debt) ->
  D.HelloLibs w0 ge o (D.hd_priv w0 ge o debt)
    (AX.exit_funcs_inv (ho_x o) [] c ∗ exit_lock o)%I
    (AX.exit_funcs_inv (ho_x o) [(ho_cp o, null, null)] ((c + 1) mod 2 ^ 64) ∗ exit_lock o)%I.
End HelloMainLibsSig.

(** The implementation assembles the independently proved bridges. *)
Module HelloGlibcMainLibsOn (D : HelloDebtsT) (AX : AtexitT)
  : HelloMainLibsSig D AX.
(** The sealed call group supplies string and program-name calls. *)
Module C := HelloGlibcMainLibsCallsOn D.
(** The system bridge supplies allocation and registration. *)
Module SY := HelloGlibcLibsSysOn D AX.
(** The exit bridge invokes the callback and finishes cleanup. *)
Module EX := HelloGlibcLibsExitOn D AX.
Import LG0 LG0.L D D.SW.FI.ML.
(** The recursive exit lock starts unlocked, with no owner. *)
Definition exit_lock `{!gen_heapGS piece pval Σ} (o : hello_objs) : iProp Σ :=
  live (ho_el o) (ho_elr o) ∗ bytes (ho_el o) 0 [0; 0; 0; 0] ∗ bytes (ho_el o) 4 [0; 0; 0; 0] ∗
  pcell (ho_el o) 8 null.
Section libs.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (Hk : hello_link ge o) (Hos : hello_os_layout w0 o).
Local Instance libs_stable : SafepointStable (os_wi w0) := os_wi_stable w0.
Local Instance libs_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.

(** Gnulib's `c: proper_name` returns its argument and touches nothing. *)
Lemma libs_proper_name : forall p,
  D.fn_triple w0 ge (TAtom "proper_name") [WPtr p] True (fun r => ⌜r = Ret (WPtr p)⌝)%I.
Proof using Hk.
  intros p. exists HelloVersion.proper_name_fn. split; [exact (hk_proper_name _ _ Hk)|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr. injection Hfr as <-. iIntros "_ HK".
  iApply wp_enter; [vm_compute; reflexivity | reflexivity |]. iNext.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext. iApply "HK". done.
Qed.

(** The initially empty handler list becomes a one-callback list. *)
Lemma hello_libs (debt : D.HelloCore w0 ge o) c (Hq : D.setlocale_query w0 ge o (D.hd_priv w0 ge o debt))
    (Hcl : D.close_stdout_narrow w0 ge o (D.hd_priv w0 ge o debt))
    (Hcw : D.close_stdout_wide w0 ge o (D.hd_priv w0 ge o debt))
    (Hm : D.mbsrtowcs w0 ge o (D.hd_priv w0 ge o debt))
    (Hw : D.wprintf_greeting w0 ge o (D.hd_priv w0 ge o debt))
    (Hp : D.HelloPrints w0 ge o (D.hd_priv w0 ge o debt)) :
  D.HelloLibs w0 ge o (D.hd_priv w0 ge o debt)
    (AX.exit_funcs_inv (ho_x o) [] c ∗ exit_lock o)%I
    (AX.exit_funcs_inv (ho_x o) [(ho_cp o, null, null)] ((c + 1) mod 2 ^ 64) ∗ exit_lock o)%I.
Proof using Hk Hos.
  constructor; [..| exact Hq | exact Hcl | exact Hcw | exact Hm | exact Hw | exact Hp].
  - exact (C.ST.libs_mbszero w0 ge o Hk).
  - exact (C.NM.libs_name w0 ge o Hk).
  - destruct (SY.libs_atexit w0 ge o Hk Hos c) as (gf & Hg & Hcall & Hspec).
    exists gf. split; [exact Hg|]. split; [exact Hcall|]. intros fr Φ Hfr.
    iIntros "[HX Hl] HK". iApply (Hspec _ _ Hfr with "HX").
    iIntros (r) "(%k & %Hr & HX)". iApply "HK". iExists k. iSplit; [done|]. iFrame.
  - exact (SY.libs_xmalloc w0 ge o Hk).
  - exact (C.ST.libs_strlen w0 ge o Hk).
  - exact (C.ST.libs_strncmp w0 ge o Hk).
  - exact (C.ST.libs_errno w0 ge o Hk).
  - exact (SY.libs_free w0 ge o Hk).
  - intros n S' Hc. exact (EX.libs_exit w0 ge o Hk Hos debt ((c + 1) mod 2 ^ 64) n S' Hc).
  - exact libs_proper_name.
Qed.
End libs.
End HelloGlibcMainLibsOn.
