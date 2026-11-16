(** A whole-program proof of a C program runs in phases. Startup code in
    glibc changes runtime state that the proof of `c: main` treats as
    fixed: it sets the thread cookie and registers the errno and dlerror
    handlers. Each phase is therefore proved under its own world
    interpretation, the predicate that a
    [[weakest-precondition]] in [Logic](Logic.v) carries alongside memory. This module
    proves that a proof under one interpretation also holds under another,
    as long as the two agree in every state where a [[ghost-state|ghost]]
    key holds a fixed value.

    ## Why one lemma suffices

    A proof of `c: main` should not have to be redone because startup ran
    first. Both phases run the same program with the same library
    contracts, so their program logics differ only in which world states
    they accept, the interpretation inside [heap_interp]. A Nanofil program
    never forks a thread, so every step of the first proof can be replayed
    under the second interpretation. The caller lends the ghost key and
    gets it back unchanged, so the key needs to be neither persistent nor
    final. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language ectx_language weakestpre.
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Machine
  ExternalCalls Pieces Heap Language Logic.

(** The functor [WiTransport] states the lemma over any Fil-C [[runtime]],
    so that the glibc proofs can apply it to their fixed logic instance. *)
Module WiTransport (R : Runtime) (LG : LogicSig R).
Import LG LG.L.

(** ## Transport between two interpretations

    The section fixes one registry, one global environment and two world
    interpretations. The lemma below then moves a weakest precondition
    from the first interpretation to the second. *)
Section transport.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world)) (ge : genv).
Context (wi1 wi2 : mem -> world -> gmap piece pval -> Prop).

Local Notation lexpr := (language.expr (nanofil_lang registry ge)).
Local Notation wp1 := (@wp _ _ _ _ (@wp' _ _ _ (nanofil_irisGS registry wi1 ge)) NotStuck ⊤).
Local Notation wp2 := (@wp _ _ _ _ (@wp' _ _ _ (nanofil_irisGS registry wi2 ge)) NotStuck ⊤).

(** A Nanofil step never forks a thread, so the list of forked
    expressions after every primitive step is empty. *)
Lemma prim_step_no_fork (e1 : lexpr) σ1 κ e2 σ2 efs :
  language.prim_step e1 σ1 κ e2 σ2 efs -> efs = [].
Proof. intros [K e1' e2' _ _ Hh]. destruct Hh; reflexivity. Qed.

(** A proof written for one phase of a program should carry over to a
    phase whose state checks agree with it. Here the key k holds v, and
    while it does, wi1 and wi2 accept the same states. A proof under wi1
    then runs under wi2, and the key comes back unchanged with every
    result. The proof is a Löb induction that looks the key up in the
    ghost heap before and after each step. *)
Lemma wp_wi_transport (k : piece) dq (v : pval) (e : lexpr) Φ :
  (forall m w h, h !! k = Some v -> wi2 m w h -> wi1 m w h) ->
  (forall m w h, h !! k = Some v -> wi1 m w h -> wi2 m w h) ->
  pointsto k dq v -∗ wp1 e Φ -∗ wp2 e (fun o => pointsto k dq v ∗ Φ o)%I.
Proof.
  intros H21 H12. iIntros "Hk H". iLöb as "IH" forall (e).
  rewrite !wp_unfold /wp_pre /=.
  destruct (to_val e) as [o|] eqn:Ev.
  - iMod "H". iModIntro. iFrame.
  - iIntros (σ ns κ κs nt) "Hσ".
    iDestruct "Hσ" as (h) "[Hh %Hf]". destruct Hf as (Ha & Hd & Hr & Hw).
    iDestruct (gen_heap_valid with "Hh Hk") as %Hl.
    iMod ("H" $! σ ns κ κs nt with "[Hh]") as "[%Hred H]".
    { iExists h. iFrame "Hh". iPureIntro. eauto. }
    iModIntro. iSplit; [done|].
    iIntros (e2 σ2 efs Hstep) "Hcred".
    pose proof (prim_step_no_fork _ _ _ _ _ _ Hstep) as ->.
    iMod ("H" $! e2 σ2 [] Hstep with "Hcred") as "H". iModIntro. iNext.
    iMod "H" as "H". iModIntro. iMod "H" as "(Hσ & H & _)".
    iDestruct "Hσ" as (h2) "[Hh %Hf]". destruct Hf as (Ha2 & Hd2 & Hr2 & Hw2).
    iDestruct (gen_heap_valid with "Hh Hk") as %Hl2.
    iModIntro. iSplitL "Hh".
    { iExists h2. iFrame "Hh". iPureIntro. eauto. }
    iSplitL; [|done]. iApply ("IH" with "Hk H").
Qed.

End transport.
End WiTransport.
