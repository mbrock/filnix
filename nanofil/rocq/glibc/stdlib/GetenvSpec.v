(** The option parser calls getenv on a known name. Its caller supplies the
    resources for that name and receives them back when getenv returns. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String List.
From Nanofil Require Import Term Syntax Values Semantics Run Pieces Heap Language Logic ExternalCalls.
From Glibc Require Import Fix OsWorld.
Import ListNotations Fix.LG0 Fix.LG0.L.

Section named_rule.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Local Instance named_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A parser asks getenv about one linked name. Its loan must provide the
    memory needed for that name, rather than support arbitrary arguments. *)
Definition getenv_at_rule (G : iProp Σ) (p : ptr) : Prop :=
  forall f e ls l d args rest j Φ, map_option (arg_x ge e) args = Some [WPtr p] ->
  ⊢ G -∗ ▷ (∀ q, G -∗
    WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d P) (Global (TAtom "__GI_getenv")) args :: rest) j)) : gexpr) {{ Φ }}.

(** Extra resources travel beside the name's loan and return unchanged.
    This lets the parser carry the stack-size cell needed by its cutoff. *)
Lemma getenv_at_rule_sep (G R : iProp Σ) p :
  getenv_at_rule G p -> getenv_at_rule (G ∗ R) p.
Proof using Type.
  intros Hg f e ls l d args rest j Φ Hargs. iIntros "[HG HR] HK".
  iApply (Hg with "HG"); [exact Hargs|]. iNext. iIntros (q) "HG".
  iApply ("HK" with "[$HG $HR]").
Qed.
End named_rule.
