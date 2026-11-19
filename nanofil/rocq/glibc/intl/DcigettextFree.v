From Glibc Require Import GlibcProgram.
(** Glibc's message lookup frees the strings it allocated before it
    returns, and some of those slots hold null. The earlier proofs of the
    lookup asked the global environment to leave `c: free` to the model,
    which holds only in a program that does not link glibc's own free.
    Hello links that free, so this module states what the lookup needs
    from one call to free as a rule, and proves the rule both ways.

    A caller needs two answers from free. Freeing null leaves memory
    alone, and freeing a live heap object ends that object's life. The
    rule states both answers. One proof derives the rule from the model's
    built-in free, and the other runs glibc's captured `c: free`, which
    hands the object to the runtime's `c: zgc_free`. Both proofs show that
    the OS state stays valid after the object dies. *)
From Glibc Require Import GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld OsMemLogic OsExternals AllocLogic.
Import ListNotations.
Open Scope Z_scope.
Import Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld OsMemLogic.
Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** ## The rule for one call to free

    The lookup calls free with one pointer argument and ignores the
    result. Passing null must return without touching memory. Passing a
    live heap object must take the object's life and return. *)

(** A call to free on null returns and changes nothing that the caller
    owns. *)
Definition dci_free_null_rule : Prop := forall f e ls l v rest j Φ,
  arg_x ge e (Arg P v) = Some (WPtr null) ->
  ⊢ ▷ WP (ERun (mkFrame f e ls None (Exec l rest j)) : gexpr) {{ Φ }} -∗
    WP (ERun (mkFrame f e ls None (Exec l (Call CVoid (Global free_name) [Arg P v] :: rest) j)) : gexpr)
      {{ Φ }}.

(** A call to free on a live heap object b consumes b's life and
    returns. *)
Definition dci_free_live_rule : Prop := forall f e ls l v rest j b reg Φ,
  arg_x ge e (Arg P v) = Some (WPtr (mkPtr b (Obj b))) -> r_kind reg = Heap -> b <> 0 ->
  ⊢ live b reg -∗ ▷ WP (ERun (mkFrame f e ls None (Exec l rest j)) : gexpr) {{ Φ }} -∗
    WP (ERun (mkFrame f e ls None (Exec l (Call CVoid (Global free_name) [Arg P v] :: rest) j)) : gexpr)
      {{ Φ }}.

(** The lookup needs both cases. *)
Definition dci_free_rule : Prop := dci_free_null_rule /\ dci_free_live_rule.

(** ## The model's free

    Some programs have no free of their own. In such a program the
    machine frees memory itself, and it gives both answers. This proof
    covers that case, so the older statements about the lookup stay
    true. *)
Lemma dci_free_rule_heap : heap_fns ge -> dci_free_rule.
Proof using Type.
  intros (Hfh & Hff & Hfd & _). split.
  - intros f e ls l v rest j Φ Hx. iIntros "HK".
    iApply wp_free_null; [exact Hfh | exact Hff | exact Hfd | exact Hx | iExact "HK"].
  - intros f e ls l v rest j b reg Φ Hx Hk Hb. iIntros "Hl HK".
    iApply (wp_free with "Hl HK"); [exact Hfh | exact Hff | exact Hfd | exact Hx | exact Hk | exact Hb |].
    intros m wd h rs Hh Hrs Hw. exact (os_wi_free w0 m wd h b reg rs Hk Hh Hrs Hw).
Qed.

(** ## Glibc's free

    Hello defines free with glibc's own code, so a call to free there
    runs that code. The code passes its argument straight on to the
    runtime. The proof therefore needs the runtime to free heap objects,
    and it needs the program to leave the runtime's entry point
    undefined. *)
Lemma dci_free_rule_glibc `{!Defines ge "free" free_fn} :
  frees_heap (ge_free ge) -> find_fn ge zgc_free_name = None -> lookup zgc_free_name (ge_globals ge) = None ->
  dci_free_rule.
Proof using Type.
  intros Hfh Hzf Hzg. split.
  - intros f e ls l v rest j Φ Hx. iIntros "HK".
    iApply wp_call_bind; [cbn [map_option]; rewrite Hx; reflexivity | apply defines | reflexivity |]. iNext.
    iApply (AllocLogic.wp_glibc_free_null registry (os_wi w0) ge); [exact Hfh | exact Hzf | exact Hzg |].
    iExists _. iSplit; [iPureIntro; reflexivity | iExact "HK"].
  - intros f e ls l v rest j b reg Φ Hx Hk Hb. iIntros "Hl HK".
    iApply wp_call_bind; [cbn [map_option]; rewrite Hx; reflexivity | apply defines | reflexivity |]. iNext.
    iApply (AllocLogic.wp_glibc_free registry (os_wi w0) ge b reg with "Hl");
      [exact Hfh | exact Hzf | exact Hzg | exact Hk | exact Hb | |].
    + intros m wd h rs Hh Hrs Hw. exact (os_wi_free w0 m wd h b reg rs Hk Hh Hrs Hw).
    + iExists _. iSplit; [iPureIntro; reflexivity | iExact "HK"].
Qed.
End rules.

(** ## Controls

    A reader may ask why the rule has two proofs. The first works only
    when a program has no free of its own. The second works only when a
    program uses glibc's free. These checks show that no program does
    both. *)
Example dci_free_names : free_name = TAtom "free" /\ zgc_free_name = TAtom "zgc_free" /\ free_name <> zgc_free_name.
Proof. repeat split; discriminate. Qed.

(** A genv cannot leave free to the model and also bind glibc's free. *)
Lemma dci_free_premises_exclusive ge f :
  heap_fns ge -> find_fn ge free_name = Some (Defined f) -> False.
Proof. intros (_ & Hff & _) Hf. unfold free_name in Hf. rewrite Hff in Hf. discriminate. Qed.
