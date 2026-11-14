(** This file discharges Hello's allocation, deallocation and exit-handler
    registration calls. The proofs use the concrete OS world, so their
    interfaces require no separate world-preservation assumptions. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Machine
  ExternalCalls Pieces Heap Language Logic MemLogic HelloLeaf HelloJoin.
From Glibc Require Import OsWorld OsRegistry AllocLogic AtexitLogic
  HelloGlibcXmalloc HelloGlibcDebts HelloGlibcLibsT.
From Glibc Require AllocLogic AtexitLogic HelloGlibcXmalloc OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** The interface exposes the three proved triples. *)
Module Type HelloLibsSysSig (D : HelloDebtsT) (AX : AtexitT).
Import LG0 LG0.L D D.SW.FI.ML.
(** Allocation returns a positive fresh object rather than a null pointer. *)
Parameter libs_xmalloc : forall `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}
  (w0 : os_world) (ge : genv) (o : hello_objs), hello_link ge o -> forall n, 0 <= n < 2 ^ 64 ->
  D.fn_triple w0 ge (TAtom "xmalloc") [WInt n] (D.hello_ro ge o)
    (fun r => ∃ b, ⌜r = Ret (WPtr (mkPtr b (Obj b))) /\ 0 < b /\ b mod 16 = 0 /\
      b + req_extent (wreq n) <= 2 ^ 48⌝ ∗ obj b (wreq n))%I.
(** Deallocation consumes the heap object's live token. *)
Parameter libs_free : forall `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}
  (w0 : os_world) (ge : genv) (o : hello_objs), hello_link ge o -> forall b reg,
  r_kind reg = Heap -> b <> 0 ->
  D.fn_triple w0 ge (TAtom "free") [WPtr (mkPtr b (Obj b))] (live b reg) (fun r => ⌜r = RetVoid⌝)%I.
(** Registration appends Hello's callback to the initially empty list. *)
Parameter libs_atexit : forall `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}
  (w0 : os_world) (ge : genv) (o : hello_objs), hello_link ge o -> hello_os_layout w0 o -> forall c,
  D.fn_triple w0 ge (TAtom "atexit") [WPtr (ho_cp o)] (AX.exit_funcs_inv (ho_x o) [] c)
    (fun r => ∃ k, ⌜r = Ret (WInt k) /\ 0 <= k < 2 ^ 32⌝ ∗
      AX.exit_funcs_inv (ho_x o) [(ho_cp o, null, null)] ((c + 1) mod 2 ^ 64))%I.
(** Exit-state writes cannot change the registered errno object's kind. *)
Parameter libs_ignores : forall (w0 : os_world) (o : hello_objs), hello_os_layout w0 o -> forall b e,
  In b [xo_lock (ho_x o); xo_done (ho_x o); xo_called (ho_x o);
        xo_funcs (ho_x o); xo_init (ho_x o); ho_el o] -> AX.wi_ignores (os_wi w0) b e.
End HelloLibsSysSig.

(** The implementation uses the existing glibc proofs at the linked names. *)
Module HelloGlibcLibsSysOn (D : HelloDebtsT) (AX : AtexitT)
  : HelloLibsSysSig D AX.
(** Hello's allocation wrapper uses glibc's allocator. *)
Module XM := HelloGlibcXmalloc.
(** Registration uses the existing proof while exporting only its resources. *)
Module AR := AtexitLogic.
Import LG0 LG0.L D D.SW.FI.ML.
Section libs.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs).
(** The OS interpretation survives collector safepoints. *)
Local Instance sys_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** These calls run with the concrete glibc OS registry. *)
Local Instance sys_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.

(** Allocation returns a positive fresh object rather than a null pointer. *)
Lemma libs_xmalloc : hello_link ge o -> forall n, 0 <= n < 2 ^ 64 ->
  D.fn_triple w0 ge (TAtom "xmalloc") [WInt n] (D.hello_ro ge o)
    (fun r => ∃ b, ⌜r = Ret (WPtr (mkPtr b (Obj b))) /\ 0 < b /\ b mod 16 = 0 /\
      b + req_extent (wreq n) <= 2 ^ 48⌝ ∗ obj b (wreq n))%I.
Proof.
  intros Hk n Hn. exists xmalloc_fn. split; [exact (hk_xmalloc _ _ Hk)|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr.
  rewrite xmalloc_frame in Hfr. injection Hfr as <-.
  iIntros "Hro HK". iDestruct "Hro" as "(_ & _ & _ & _ & _ & _ & _ & Htc & _)".
  iApply (HelloGlibcXmalloc.wp_hello_xmalloc w0 glibc_os_registry ge n with "Htc");
    [exact Hn | exact (hk_malloc _ _ Hk) | exact (hk_mp _ _ Hk) | exact (hk_tc _ _ Hk) |
     exact (hk_malloc2 _ _ Hk) |].
  iNext. iIntros (b Hb) "Hobj _". iApply "HK". iExists b. iSplit; [done|iExact "Hobj"].
Qed.

(** Deallocation consumes the heap object's live token. *)
Lemma libs_free : hello_link ge o -> forall b reg, r_kind reg = Heap -> b <> 0 ->
  D.fn_triple w0 ge (TAtom "free") [WPtr (mkPtr b (Obj b))] (live b reg) (fun r => ⌜r = RetVoid⌝)%I.
Proof.
  intros Hk b reg Hheap Hb. exists free_fn. split; [exact (hk_free _ _ Hk)|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr.
  change (Some (mkFrame free_fn [(TAtom "v0", WPtr (mkPtr b (Obj b)))] [] None
    (Enter (TAtom "start") None)) = Some fr) in Hfr. injection Hfr as <-.
  destruct (hk_frees _ _ Hk) as (Hfree & Hfn & Hglobal). iIntros "Hl HK".
  iApply (AllocLogic.wp_glibc_free glibc_os_registry (os_wi w0) ge with "Hl");
    [exact Hfree | exact Hfn | exact Hglobal | exact Hheap | exact Hb |
     intros m wd h rs Hlive Hrs Hw; exact (os_wi_free w0 m wd h b reg rs Hheap Hlive Hrs Hw) |].
  iApply "HK". done.
Qed.

(** Exit-state writes cannot change the registered errno object's kind. *)
Lemma libs_ignores (w : os_world) (ob : hello_objs) : hello_os_layout w ob -> forall b e,
  In b [xo_lock (ho_x ob); xo_done (ho_x ob); xo_called (ho_x ob);
        xo_funcs (ho_x ob); xo_init (ho_x ob); ho_el ob] -> AX.wi_ignores (os_wi w) b e.
Proof.
  intros Hos b e Hb. exact (hello_os_write w ob b e Hos Hb).
Qed.

(** Registration appends Hello's callback to the initially empty list. *)
Lemma libs_atexit : hello_link ge o -> hello_os_layout w0 o -> forall c,
  D.fn_triple w0 ge (TAtom "atexit") [WPtr (ho_cp o)] (AX.exit_funcs_inv (ho_x o) [] c)
    (fun r => ∃ k, ⌜r = Ret (WInt k) /\ 0 <= k < 2 ^ 32⌝ ∗
      AX.exit_funcs_inv (ho_x o) [(ho_cp o, null, null)] ((c + 1) mod 2 ^ 64))%I.
Proof.
  intros Hk Hos c. exists atexit_fn. split; [exact (hk_atexit _ _ Hk)|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr.
  change (Some (mkFrame atexit_fn [(TAtom "v0", WPtr (ho_cp o))] [] None
    (Enter (TAtom "start") None)) = Some fr) in Hfr. injection Hfr as <-.
  iIntros "HX HK". iApply (AtexitLogic.wp_glibc_atexit glibc_os_registry (os_wi w0) ge with "HX");
    [exact (hk_exit_layout _ _ Hk) | exact (hk_exit_globals _ _ Hk) |
     split; [|split]; (apply (libs_ignores w0 o Hos); cbn; tauto) |
     exact (hk_exit_fns _ _ Hk) | cbn; lia | exact (proj2 (proj2 (hk_cp _ _ Hk))) |].
  iIntros "HX". iApply "HK". iExists 0. iSplit; [iPureIntro; split; [reflexivity|lia]|iExact "HX"].
Qed.
End libs.
End HelloGlibcLibsSysOn.
