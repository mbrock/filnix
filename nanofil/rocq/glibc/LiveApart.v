(** A C program may compare two pointers that point into different
    objects. The file-backed buffer of `c: printf` does this: it asks
    whether the end of its window is the end of its own staging array,
    and the window may lie in the character buffer of the stream, which
    is another object. A proof about such a comparison needs to know
    that the two objects do not overlap in memory.

    The ownership of an object's bytes does not say this. A piece of
    memory is named by its object and an offset, not by an address, so
    two owned pieces of different objects could have the same address
    as far as the pieces say. The machine keeps the missing fact: its
    memory never has two [[live]] objects that overlap. This module
    brings that fact into a proof. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules Symbolic ExternalCalls ExternalMachine Transport Pieces Heap Language Logic.
From Glibc Require GlibcLogic.
From Glibc Require Import Fix.
Open Scope Z_scope.
Open Scope list_scope.

Module LG := LG0.
Module L := LG.L.
Import L LG GlibcLogic.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
Local Instance apart_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A running function may learn that two live objects are apart. The
    proof holds a share of the lifetime of each object, and it keeps
    both shares. The fact holds for two different objects: the end of
    one is at or below the start of the other. The rule takes no step
    of the program. It only looks at the machine's memory, which the
    logic lets a proof do while a function runs. *)
Lemma wp_live_apart dq dq' b reg b' reg' fr Φ :
  liveq dq b reg -∗ liveq dq' b' reg' -∗
  (⌜b <> b' -> r_end reg <= b' \/ r_end reg' <= b⌝ -∗ liveq dq b reg -∗ liveq dq' b' reg' -∗
   WP (ERun fr : gexpr) {{ Φ }}) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  iIntros "H1 H2 HK". iApply wp_unfold. rewrite /wp_pre.
  change (language.to_val (ERun fr : gexpr)) with (@None (language.val (nanofil_lang registry ge))).
  iIntros (σ ns κ κs nt) "Hσ". change (state_interp σ ns (κ ++ κs) nt) with (heap_interp wi σ).
  iDestruct (ptsq_facts with "Hσ H1") as %((Ha1 & _) & Hd & _).
  iDestruct (ptsq_facts with "Hσ H2") as %((Ha2 & _) & _).
  iSpecialize ("HK" with "[%] H1 H2"); [intros Hne; exact (Hd b reg b' reg' Ha1 Ha2 Hne)|].
  iEval (rewrite wp_unfold /wp_pre) in "HK".
  iEval (change (language.to_val (ERun fr : gexpr)) with (@None (language.val (nanofil_lang registry ge)))) in "HK".
  iApply ("HK" with "Hσ").
Qed.

End rules.
