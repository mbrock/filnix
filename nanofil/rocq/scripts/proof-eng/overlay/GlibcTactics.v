(** Proving a glibc function requires following its instructions and checking
    that each memory access is allowed. This library supplies one set of
    tactics for those steps, using the existing [[separation-logic]] rules.
    The tactics keep the caller's named ownership facts available after each access. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  Machine Pieces Heap Language Logic MemLogic Symbolic ExternalCalls StepRules.
From Glibc Require Import Fix.
Import ListNotations LG0 LG0.L.
Open Scope Z_scope.

(** ## Applying rules without proof-mode search

    Each instruction rule describes the remaining computation after one step.
    These lemmas connect that description to the current proof context without
    searching through its ownership facts. *)

(** This lemma leaves the continuation of a rule that takes no resources. *)
Lemma step_wand {PROP : bi} (Δ : environments.envs PROP) (P Q : PROP) :
  (⊢ ▷ P -∗ Q) -> environments.envs_entails Δ P -> environments.envs_entails Δ Q.
Proof.
  rewrite environments.envs_entails_unseal. intros HW HΔ. etrans; [exact HΔ|].
  iIntros "H". iApply HW. iNext. iExact "H".
Qed.

(** This lemma leaves the continuation of a rule that takes one resource. *)
Lemma step_res1 {PROP : bi} (Δ : environments.envs PROP) (R R' P Q : PROP) :
  (⊢ R -∗ ▷ (R' -∗ P) -∗ Q) -> environments.envs_entails Δ (R' -∗ P) -> environments.envs_entails Δ (R -∗ Q).
Proof.
  rewrite environments.envs_entails_unseal. intros HW HΔ. etrans; [exact HΔ|].
  iIntros "H HR". iApply (HW with "HR"). iNext. iExact "H".
Qed.

(** This lemma leaves the continuation of a rule that takes two resources. *)
Lemma step_res2 {PROP : bi} (Δ : environments.envs PROP) (R1 R2 R1' R2' P Q : PROP) :
  (⊢ R1 -∗ R2 -∗ ▷ (R1' -∗ R2' -∗ P) -∗ Q) ->
  environments.envs_entails Δ (R1' -∗ R2' -∗ P) -> environments.envs_entails Δ (R1 -∗ R2 -∗ Q).
Proof.
  rewrite environments.envs_entails_unseal. intros HW HΔ. etrans; [exact HΔ|].
  iIntros "H HR1 HR2". iApply (HW with "HR1 HR2"). iNext. iExact "H".
Qed.

(** This lemma leaves the continuation of a rule that takes three resources. *)
Lemma step_res3 {PROP : bi} (Δ : environments.envs PROP) (R1 R2 R3 R1' R2' R3' P Q : PROP) :
  (⊢ R1 -∗ R2 -∗ R3 -∗ ▷ (R1' -∗ R2' -∗ R3' -∗ P) -∗ Q) ->
  environments.envs_entails Δ (R1' -∗ R2' -∗ R3' -∗ P) -> environments.envs_entails Δ (R1 -∗ R2 -∗ R3 -∗ Q).
Proof.
  rewrite environments.envs_entails_unseal. intros HW HΔ. etrans; [exact HΔ|].
  iIntros "H HR1 HR2 HR3". iApply (HW with "HR1 HR2 HR3"). iNext. iExact "H".
Qed.

(** ## Symbolic values and addresses

    A loop can read a variable whose value depends on earlier iterations.
    These helpers use the known facts about each [[temporary]] to prove
    address bounds, without knowing which C structure supplies an offset. *)

Create HintDb offs.

(** This lemma reads past an update to a different temporary. *)
Lemma lookup_put_miss {A : Type} k k' (v : A) e r :
  name_eqb k k' = false -> lookup k e = r -> lookup k (put k' v e) = r.
Proof. intros H <-. apply Symbolic.lookup_after_put_other. exact H. Qed.

(** This tactic reads updates first and then uses a hypothesis about the remaining environment. *)
Ltac lk_prove :=
  first [ apply Symbolic.lookup_after_put_same
        | eapply lookup_put_miss; [vm_compute; reflexivity | lk_prove]
        | eassumption ].

(** This tactic removes irrelevant hypotheses before invoking integer arithmetic. *)
Ltac clear_junk :=
  repeat match goal with
    H : ?T |- _ =>
      lazymatch T with
      | @eq Z _ _ => fail | Z.le _ _ => fail | Z.lt _ _ => fail | and (Z.le _ _) _ => fail
      | and (Z.lt _ _) _ => fail | not (@eq Z _ _) => fail
      | _ => clear H
      end
    end.

(** This tactic removes integer wrapping when the arithmetic hypotheses prove it unnecessary. *)
Ltac unwrap2 :=
  repeat match goal with
    | |- context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2 ^ 64)); [|lia]
    | |- context [?x mod 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616); [|lia]
    | |- context [?x mod 2 ^ 32] => rewrite (Z.mod_small x (2 ^ 32)); [|lia]
    | |- context [?x mod 4294967296] => rewrite (Z.mod_small x 4294967296); [|lia]
    end.

(** This tactic unfolds registered offsets and proves an address or alignment condition. *)
Ltac a2 := autounfold with offs;
  cbn [ptr_addr ptr_cap]; unfold raw_address; rewrite ?Z.add_0_r; clear_junk; unwrap2;
  first [lia | apply Z.mod_1_r | Z.div_mod_to_equations; lia].

(** This tactic recognizes an integer expression with no nested comparison. *)
Ltac innermost X :=
  lazymatch X with context [_ =? _] => fail | context [_ <? _] => fail | context [_ <=? _] => fail | _ => idtac end.

(** This tactic proves a branch condition by deciding its integer comparisons. *)
Ltac decide_ints :=
  unfold sign_extension; autounfold with offs; cbv zeta; unwrap2;
  repeat match goal with
    | |- context [?x =? ?y] => innermost x; innermost y; destruct (Z.eqb_spec x y); cbn [negb andb orb]
    | |- context [?x <? ?y] => innermost x; innermost y; destruct (Z.ltb_spec x y); cbn [negb andb orb]
    | |- context [?x <=? ?y] => innermost x; innermost y; destruct (Z.leb_spec x y); cbn [negb andb orb]
    end;
  first [reflexivity | exfalso; clear_junk; first [lia | Z.div_mod_to_equations; lia]].

(** ## Pure instructions

    Assignments, jumps and pointer arithmetic leave the program's memory unchanged.
    These tactics advance the current [[frame]] while keeping the ownership facts
    that later loads and stores will need. *)

(** This tactic fills the world-stability premise introduced by a rule. *)
Ltac inst := lazymatch goal with |- SafepointStable _ => exact _ | _ => idtac end.

(** This tactic reads a temporary through updates to an unknown environment. *)
Ltac vx :=
  first [reflexivity |
    cbn -[put];
    repeat match goal with
    | |- context [lookup ?k ?E] =>
        let H := fresh "Hlk" in assert (H : lookup k E = _) by lk_prove;
        rewrite H; clear H
    end; reflexivity].

(** This tactic finds the instruction in the goal rather than in a hypothesis. *)
Ltac at_of :=
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (_ (mkFrame _ _ _ _ ?a)) _) =>
      let a' := eval hnf in a in a'
  end.

(** This tactic applies a pure rule without changing hypotheses guarded by a later. *)
Ltac step_entailment result :=
  iStartProof;
  let a := at_of in
  lazymatch a with
  | Exec _ (Let _ _ _ _ :: _) _ =>
      eapply step_wand; [eapply wp_let; inst;
        [reflexivity | reflexivity | vx | intros ?; result] |]
  | Exec _ (Flight _ _ _ _ :: _) _ =>
      eapply step_wand; [eapply wp_flight; inst; [vx | reflexivity | vx] |]
  | Enter _ _ =>
      eapply step_wand; [eapply wp_enter; inst; [reflexivity | vx] |]; cbn [b_insts b_jump]
  | Exec _ [] (JGoto _) => eapply step_wand; [eapply wp_goto; inst |]
  | _ => fail "step: expected a pure let, flight, block entry, or goto"
  end.

(** A loop proof can assume its next iteration succeeds only after taking a step.
    This tactic makes such an assumption available by removing its outer [[later-modality]]. *)
Ltac step :=
  iStartProof;
  lazymatch goal with |- environments.envs_entails ?Delta _ =>
    lazymatch Delta with
    | context [environments.Esnoc _ _ (▷ _)%I] =>
        let a := at_of in
        lazymatch a with
        | Exec _ (Let _ _ _ _ :: _) _ =>
            iApply wp_let; [reflexivity | reflexivity | vx | intros ?; cbn; reflexivity | iNext]
        | Exec _ (Flight _ _ _ _ :: _) _ => iApply wp_flight; [vx | reflexivity | vx | iNext]
        | Enter _ _ => iApply wp_enter; [reflexivity | vx | iNext; cbn [b_insts b_jump]]
        | Exec _ [] (JGoto _) => iApply wp_goto; iNext
        end
    | _ => step_entailment ltac:(cbn; reflexivity)
    end
  end.

(** Some loop proofs rewrite an integer expression before simplifying it.
    This form preserves that expression so the caller's equation still matches. *)
Ltac step_symbolic := step_entailment ltac:(reflexivity).

(** This tactic stops before the first instruction that needs ownership or a decision. *)
Ltac steps := repeat step.

(** This tactic copies a global pointer whose binding is given by Hs. *)
Ltac step_global Hs :=
  eapply step_wand;
    [eapply wp_let; inst;
       [reflexivity | reflexivity | cbn [map2_option value_x]; rewrite Hs; reflexivity | intros ?; reflexivity] |].

(** This tactic reads a named temporary using the supplied lookup equation. *)
Ltac step_lookup n H :=
  eapply step_wand; [eapply wp_let; inst; [reflexivity | reflexivity |
    cbn [map2_option value_x]; repeat (rewrite (lookup_after_put_other _ (TAtom n)); [|reflexivity]);
    rewrite H; reflexivity | intros ?; reflexivity] |].

(** Naming a computed integer keeps repeated expressions small in a loop proof. *)
Section named_steps.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
Local Instance named_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** This rule exposes the integer result as a fresh name with its defining equation. *)
Lemma step_named_rule Δ f e ls l d k o args rest j classes xs X Φ :
  general_op o = true -> op_arg_classes o k = Some classes -> map2_option (value_x ge e) classes args = Some xs ->
  (forall m, op_res o k xs m = Some (OpRes (RVal (WInt X)) m)) ->
  (forall x, x = X -> environments.envs_entails Δ
    (WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }})) ->
  environments.envs_entails Δ
    (WP (ERun (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) : gexpr) {{ Φ }}).
Proof.
  intros Hgen Hclass Hvalues Hop Hnext. eapply step_wand.
  - eapply wp_let; eassumption.
  - exact (Hnext X eq_refl).
Qed.
End named_steps.

(** This tactic names an integer result and retains the equation used by later arithmetic. *)
Ltac step_named :=
  eapply step_named_rule; inst; [reflexivity | reflexivity | vx | intros ?; reflexivity |];
  let x := fresh "x" in let E := fresh "E" in intros x E.

(** This tactic leaves a branch condition symbolic for a later case split. *)
Ltac branch_symbolic :=
  iStartProof; eapply step_wand; [eapply wp_branch; inst; vx |].

(** This tactic computes a closed condition and follows its selected edge. *)
Ltac branch :=
  iStartProof;
  eapply step_wand; [eapply wp_branch; inst; vx |];
  lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
    let c' := eval vm_compute in c in change c with c' end; cbn [edge_label].

(** This tactic uses a supplied equation to decide which branch the program takes. *)
Ltac branch_rewrite E :=
  branch_symbolic; rewrite E;
  lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
    let c' := eval vm_compute in c in change c with c' end; cbn [edge_label].

(** This tactic proves the integer condition equals b before following its edge. *)
Ltac branch_as b :=
  iStartProof;
  eapply step_wand; [eapply wp_branch; inst; vx |];
  lazymatch goal with |- context [edge_label (if ?n =? 0 then _ else _)] =>
    let E := fresh "E" in assert (E : (n =? 0) = b) by decide_ints;
    rewrite E; clear E end; cbn [edge_label].

(** This tactic leaves one goal for each possible edge of an unknown condition. *)
Ltac branch_cases :=
  iStartProof;
  eapply step_wand; [eapply wp_branch; inst; vx |];
  lazymatch goal with |- context [edge_label (if ?n =? 0 then _ else _)] =>
    destruct (n =? 0) end; cbn [edge_label].

(** ## Memory instructions

    A load or store must access a live object within its bounds and at a valid alignment.
    These tactics prove those [[check]] conditions and preserve the ownership facts
    that later instructions need. *)

(** This tactic applies a rule that takes and returns one named resource. *)
Ltac rule1 H t := iRevert H; eapply step_res1; [t |]; iIntros H.

(** This tactic applies a rule that takes and returns two named resources. *)
Ltac rule2 H1 H2 t :=
  iRevert H2; iRevert H1; eapply step_res2; [t |]; iIntros H1; iIntros H2.

(** This tactic applies a rule that takes and returns three named resources. *)
Ltac rule3 H1 H2 H3 t :=
  iRevert H3; iRevert H2; iRevert H1; eapply step_res3; [t |];
  iIntros H1; iIntros H2; iIntros H3.

(** This tactic proves a check, half check, or renew using the object's life token. *)
Ltac check H :=
  iStartProof;
  let a := at_of in
  lazymatch a with
  | Exec _ (Let _ _ (Check _ _ _ _) _ :: _) _ =>
      rule1 H ltac:(eapply wp_check; inst; [reflexivity | vx | reflexivity | a2 | a2 | a2])
  | Exec _ (Let _ _ (HalfCheck _ _ _ _ _) _ :: _) _ =>
      rule1 H ltac:(eapply wp_half_check; inst;
        [reflexivity | vx | reflexivity | reflexivity | a2 | a2 | lia | a2 | a2])
  | Exec _ (Let _ _ (Renew _ _ _ _) _ :: _) _ =>
      rule1 H ltac:(eapply wp_renew; inst;
        [reflexivity | vx | reflexivity | reflexivity | a2 | a2 | a2])
  | _ => fail "check: expected a check, half check, or renew"
  end.

(** ## Concrete executions

    A proof on fixed input data can compute each updated environment instead of keeping symbolic expressions.
    These helpers preserve that convention without inspecting the abstract runtime implementation. *)

(** This tactic computes an equality's left side before instantiating its right side. *)
Ltac vm_eq :=
  match goal with |- ?l = ?r => let v := eval vm_compute in l in unify r v end;
  vm_compute; reflexivity.

(** This solver computes concrete instruction premises, rather than using symbolic arithmetic. *)
Ltac concrete_side :=
  lazymatch goal with
  | |- forall _ : mem, _ => intros ?; vm_eq
  | |- ptr_cap _ = _ \/ ptr_cap _ = _ => right; reflexivity
  | |- _ <= _ => vm_compute; congruence
  | |- _ = _ => vm_eq
  end.

(** This tactic replaces an environment with a computed equal environment. *)
Ltac replace_env e e' :=
  assert (Henv : e = e') by (vm_compute; reflexivity); try rewrite Henv; clear Henv.

(** This tactic computes only the values in the current frame's environment. *)
Ltac norm_env :=
  match goal with
  | |- context [mkFrame ?f ?e ?ls ?d ?pt] => let e' := eval vm_compute in e in replace_env e e'
  end.

(** This tactic advances a concrete execution and normalizes its updated environment. *)
Ltac concrete_step :=
  first
    [ iApply wp_let; [concrete_side | concrete_side | concrete_side | concrete_side | iNext; norm_env]
    | iApply wp_flight; [concrete_side | concrete_side | concrete_side | iNext; norm_env]
    | iApply wp_branch; [concrete_side | iNext; cbn [edge_label Z.eqb Pos.eqb]]
    | iApply wp_goto; iNext
    | iApply wp_enter; [concrete_side | concrete_side | iNext; norm_env; cbn [b_insts b_jump]] ].
