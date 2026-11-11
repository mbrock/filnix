(** A proof of a C loop describes the values and bounds that hold each
    time control reaches a particular instruction. This module computes
    one [[step]] under those assumptions without choosing concrete
    inputs, memory contents, or execution [[fuel]]. The resulting facts
    let [never_panics_by_invariant] prove that every reachable state
    avoids a safety failure.

    A proof need not know an input's exact value to decide every
    branch in the program. A known integer range may already determine
    a comparison; otherwise, the proof keeps both cases and their
    conditions. It records those values and bounds for named
    [[temporary|temporaries]] so that later instructions can use them.

    Instead of running the whole interpreter, a proof can also use one
    small rule for each instruction from [StepRules](StepRules.v).

    ## Keeping symbolic expressions small

    Computation must stop when an input remains unknown, so that known
    facts can still replace the expression. The following choices
    preserve arithmetic expressions that Rocq's arithmetic tactics can
    read rather than expand them into matches on integer bits.

    Unknown arithmetic should remain readable until a later assumption
    supplies the missing value, rather than expand into cases on bits.
    Each program file therefore sets `simpl nomatch`, since Rocq does
    not export that setting between modules. The reduction tactics
    likewise use `cbn` rather than `cbv` to leave unknown expressions
    intact.

    The model wraps integer results to their register [[class]], but a
    known range can make that wrap unnecessary. Otherwise, the tactic
    replaces a remainder by an unknown value with the proper bounds.
    It translates division into equations only when simpler arithmetic
    cannot finish the goal, and tries each wrap or comparison once. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Panics StepRules.
Import ListNotations.
Open Scope Z_scope.

(** ## Facts about an environment

    Assigning a temporary changes one environment entry and leaves the
    other names alone. The following facts describe those updates and
    record integer bounds that later steps can use. *)

(** Updating an environment changes the named entry but preserves every
    other lookup, as [lookup_after_put] states for [put]. *)
Lemma lookup_after_put : forall (A : Type) k k' (v : A) ps,
  lookup k (put k' v ps) = if name_eqb k k' then Some v else lookup k ps.
Proof.
  intros A k k' v ps. unfold put. simpl. destruct (name_eqb k k') eqn:E; [reflexivity|].
  induction ps as [|[k0 v0] ps IH]; simpl; [reflexivity|].
  destruct (name_eqb k' k0) eqn:E0; simpl.
  - apply term_eqb_eq in E0. subst k0. rewrite E. exact IH.
  - destruct (name_eqb k k0); [reflexivity | exact IH].
Qed.

(** Looking up the name just assigned returns its new value, as
    [lookup_after_put_same] states without assumptions about the old entry. *)
Lemma lookup_after_put_same : forall (A : Type) k (v : A) ps, lookup k (put k v ps) = Some v.
Proof. intros A k v ps. rewrite lookup_after_put, term_eqb_refl. reflexivity. Qed.

(** Looking up a different name returns its previous value, as
    [lookup_after_put_other] states when the names compare unequal. *)
Lemma lookup_after_put_other : forall (A : Type) k k' (v : A) ps,
  name_eqb k k' = false -> lookup k (put k' v ps) = lookup k ps.
Proof. intros A k k' v ps H. rewrite lookup_after_put, H. reflexivity. Qed.

(** Writing data bytes leaves every object's region entry unchanged,
    which [store_bytes_regions] uses to preserve facts about bounds. *)
Lemma store_bytes_regions : forall m a size x, m_regions (store_bytes m a size x) = m_regions m.
Proof. reflexivity. Qed.

(** A proof can describe an integer temporary by its range rather than
    its exact value. The assertion [int_at] records both the lookup and
    an arbitrary predicate on that integer. *)
Definition int_at (e : env) (x : name) (P : Z -> Prop) : Prop :=
  exists v, lookup x e = Some (WInt v) /\ P v.

(** Some temporary values need no bounds at all, so [any] accepts every
    integer without adding a condition to the proof. *)
Definition any (_ : Z) : Prop := True.

(** ## Arithmetic

    Pointer bounds and integer branches usually reduce to linear
    arithmetic once the proof supplies its known values. The following
    tactics handle remainders, discard unrelated memory facts, and keep
    expensive division reasoning out of easy goals. *)

(** The tactic [goal_divides] recognizes goals containing a remainder
    or quotient, where division equations may help the arithmetic solver. *)
Ltac goal_divides :=
  match goal with
  | |- context[_ mod _] => idtac
  | |- context[Z.rem _ _] => idtac
  | |- context[Z.quot _ _] => idtac
  | |- context[_ / _] => idtac
  end.

(** Many goals need only a remainder's bounds, not its relation to the
    original dividend. The tactic [mod_atoms] replaces remainders by
    variables between zero and their positive moduli, avoiding full
    division equations. *)
Ltac mod_atoms :=
  repeat match goal with
  | |- context[?x mod ?m] =>
      let H := fresh "Hmod" in pose proof (Z.mod_pos_bound x m eq_refl) as H;
      let r := fresh "r" in set (r := x mod m) in *; clearbody r
  | H0 : context[?x mod ?m] |- _ =>
      let H := fresh "Hmod" in pose proof (Z.mod_pos_bound x m eq_refl) as H;
      let r := fresh "r" in set (r := x mod m) in *; clearbody r
  end.

(** The tactic [arith] solves integer goals after removing environment
    lookups, memory facts, and bodies of local definitions. It tries
    linear arithmetic first, then remainder bounds, and finally full
    division equations when the goal contains division. Clearing local
    bodies avoids walking through a program's computed runs during
    every rewrite. *)
Ltac arith :=
  repeat match goal with
  | H : context[lookup _ _] |- _ => clear H
  | H : context[m_regions _] |- _ => clear H
  | H : context[m_bytes _] |- _ => clear H
  | H : _ |- _ => clearbody H
  end;
  try change (2 ^ 31) with 2147483648 in *; try change (2 ^ 32) with 4294967296 in *;
  try change (2 ^ 63) with 9223372036854775808 in *;
  try change (2 ^ 64) with 18446744073709551616 in *;
  first [ lia | mod_atoms; lia | goal_divides; Z.to_euclidean_division_equations; lia ].

(** Attempts to remove a wrap or decide a branch may fail legitimately
    because the input remains unknown. The tactic [arith_fast] omits
    division equations so that such attempts stay cheap. *)
Ltac arith_fast :=
  repeat match goal with
  | H : context[lookup _ _] |- _ => clear H
  | H : context[m_regions _] |- _ => clear H
  | H : context[m_bytes _] |- _ => clear H
  | H : _ |- _ => clearbody H
  end;
  try change (2 ^ 31) with 2147483648 in *; try change (2 ^ 32) with 4294967296 in *;
  try change (2 ^ 63) with 9223372036854775808 in *;
  try change (2 ^ 64) with 18446744073709551616 in *;
  first [ lia | mod_atoms; lia ].

(** The tactic [has_if] succeeds only when the supplied expression
    contains a conditional that may need deciding before further reduction. *)
Ltac has_if t := idtac; match t with context[if _ then _ else _] => idtac end.

(** The tactic [has_mod] succeeds only when the supplied expression
    contains a remainder that may need simplifying before further reduction. *)
Ltac has_mod t := idtac; match t with context[_ mod _] => idtac end.

(** The tactic [drop_wraps] simplifies the equation E from its innermost
    wraps outward, waiting for nested comparisons and remainders. It
    removes a wrap when arithmetic proves the value already fits;
    otherwise, it keeps only the remainder's bounds. It also converts
    signed remainders and quotients to Euclidean operations when their
    operands are nonnegative. *)
Ltac drop_wraps E :=
  repeat match type of E with
  | context[Z.rem ?x ?y] =>
      assert_fails (has_if x); assert_fails (has_mod x);
      rewrite (Z.rem_mod_nonneg x y) in E by (clear E; arith)
  | context[Z.quot ?x ?y] =>
      assert_fails (has_if x); assert_fails (has_mod x);
      rewrite (Z.quot_div_nonneg x y) in E by (clear E; arith)
  | context[?x mod ?m] =>
      assert_fails (has_if x); assert_fails (has_mod x);
      first [ rewrite (Z.mod_small x m) in E by (clear E; arith)
            | generalize (Z.mod_pos_bound x m eq_refl); revert E; generalize (x mod m);
              intros ? E ? ]
  end.

(** The tactic [decide_compares] simplifies integer comparisons in E
    whenever the current arithmetic facts determine their answers.
    Otherwise, it splits both cases and records the condition, waiting
    for any nested comparison to finish first. *)
Ltac decide_compares E :=
  repeat match type of E with
  | context[?a <? ?b] =>
      assert_fails (has_if a); assert_fails (has_if b);
      first [ rewrite (proj2 (Z.ltb_lt a b)) in E by (clear E; arith)
            | rewrite (proj2 (Z.ltb_ge a b)) in E by (clear E; arith)
            | revert E; destruct (Z.ltb_spec a b); intro E ]
  | context[?a <=? ?b] =>
      assert_fails (has_if a); assert_fails (has_if b);
      first [ rewrite (proj2 (Z.leb_le a b)) in E by (clear E; arith)
            | rewrite (proj2 (Z.leb_gt a b)) in E by (clear E; arith)
            | revert E; destruct (Z.leb_spec a b); intro E ]
  | context[?a =? ?b] =>
      assert_fails (has_if a); assert_fails (has_if b);
      first [ rewrite (proj2 (Z.eqb_eq a b)) in E by (clear E; arith)
            | rewrite (proj2 (Z.eqb_neq a b)) in E by (clear E; arith)
            | revert E; destruct (Z.eqb_spec a b); intro E ]
  end.

(** ## The step

    A symbolic step combines interpreter reduction with the values and
    bounds already known to the proof. The following tactics alternate
    these operations until they reach a result or need another fact. *)

(** The tactic [use_facts] replaces lookups in E with known temporary
    values, object regions, function blocks, and return classes.
    Function facts let the proof avoid carrying the entire function
    body through each step. *)
Ltac use_facts E :=
  repeat match goal with
  | H : lookup _ _ = Some _ |- _ => rewrite H in E
  | H : object_region _ (m_regions _) = Some _ |- _ => rewrite H in E
  | H : find_block _ (fn_blocks _) = _ |- _ => rewrite H in E
  | H : fn_ret _ = _ |- _ => rewrite H in E
  end.

(** The tactic [reduce] computes E as far as known facts and arithmetic
    permit while leaving byte loads and stores folded. It unfolds
    selected operations that get stuck on unknown values, then applies
    facts and simplifies wraps and comparisons until nothing changes. *)
Ltac reduce E :=
  repeat progress (
    cbn -[load_bytes store_bytes] in E; rewrite ?store_bytes_regions in E;
    try unfold sign_extension in E; try unfold raw_address in E; try unfold aligned_res in E;
    try unfold continue_at in E; try unfold with_point in E;
    try unfold int_load_res in E; try unfold access_res in E; try unfold cap_access_res in E;
    use_facts E; cbn [r_base r_end r_kind r_life ptr_addr ptr_cap] in E;
    drop_wraps E; decide_compares E).

(** Given an equation that names a step's result, [compute_step]
    reduces it through every branch left open by the assumptions. *)
Ltac compute_step E := reduce E.

(** ## Facts after a step

    After an instruction runs, the proof must establish its assertions
    for the next program point. The following tactics unpack old facts
    and follow environment updates or memory changes to prove the new
    ones. *)

(** The tactic [facts] unpacks conjunctions and existential witnesses
    in the assumptions, and splits disjunctions into separate proof cases. *)
Ltac facts :=
  repeat match goal with
  | H : True |- _ => clear H
  | H : _ /\ _ |- _ => destruct H
  | H : exists _, _ |- _ => destruct H
  | H : _ \/ _ |- _ => destruct H
  end.

(** The tactic [show_facts] proves assertions about the next state by
    following environment updates back to the known temporary values.
    It also preserves regions across byte stores, computes newly
    allocated regions, and proves integer ranges from assumptions or
    arithmetic. *)
Ltac show_facts :=
  unfold int_at, any;
  repeat match goal with
  | |- _ /\ _ => split
  | |- exists _, _ => eexists
  | |- True => exact I
  | |- _ \/ _ => first [left; solve [show_facts] | right; solve [show_facts]]
  | |- lookup _ (put _ _ _) = _ =>
      first [ rewrite lookup_after_put_same | rewrite lookup_after_put_other by reflexivity ]
  | H : lookup ?x ?e = _ |- lookup ?x ?e = _ => rewrite H; reflexivity
  | H : object_region ?b (m_regions ?m) = _ |- object_region ?b (m_regions ?m) = _ => rewrite H; reflexivity
  | |- context[m_regions (store_bytes _ _ _ _)] => rewrite store_bytes_regions
  | |- object_region _ _ = _ =>
      progress (cbn [c_mem allocated m_regions object_region r_base req_extent]; rewrite ?Z.eqb_refl)
  | |- Some _ = Some _ => reflexivity
  | |- @eq Z _ _ => reflexivity
  | |- _ <= _ => first [ assumption | arith ]
  | |- _ < _ => first [ assumption | arith ]
  | |- _ => progress cbv beta iota
  end.

(** ## The function, kept abstract

    Reducing a whole function body at every instruction repeats work
    that does not depend on the running state. A proof can instead
    compute each block once and refer to a small lookup fact. *)

(** A proof can compute a block once and save its lookup without
    exposing the whole function again. The tactic [block_fact] does
    this for an abstract function known to equal a concrete one. *)
Ltac block_fact f fn Hf l b H :=
  pose (b := find_block l (fn_blocks fn)); vm_compute in b;
  assert (H : find_block l (fn_blocks f) = b) by (rewrite Hf; reflexivity).

(** ## Applying instruction rules

    An instruction rule exposes only the values and checks needed for
    that instruction, rather than the whole interpreter. The following
    tactics choose the appropriate rule, prove its premises, and split
    any comparisons that the input facts leave undecided. *)

(** The tactic [use_facts_goal] replaces temporary lookups and object
    region lookups in the goal with values supplied by the assumptions. *)
Ltac use_facts_goal :=
  repeat match goal with
  | H : lookup _ _ = Some _ |- _ => rewrite H
  | H : object_region _ (m_regions _) = Some _ |- _ => rewrite H
  end.

(** The tactic [gen_env] gives an updated environment a fresh name
    while recording its new entry and preserving known lookups of other
    names. *)
Ltac gen_env :=
  repeat match goal with
  | |- context[put ?k ?v ?e] =>
      is_var e;
      let H := fresh "Hput" in
      assert (H : lookup k (put k v e) = Some v) by apply lookup_after_put_same;
      repeat match goal with
        | H' : lookup ?x e = Some ?w |- _ =>
            first [ assert (lookup x (put k v e) = Some w)
                      by (rewrite lookup_after_put_other; [exact H'|reflexivity])
                  | idtac ];
            clear H'
        end;
      let e' := fresh "e" in set (e' := put k v e) in *; clearbody e'; try clear e
  end.

(** The tactic [drop_wraps_goal] removes wraps that known bounds prove
    unnecessary and converts nonnegative signed division to Euclidean
    division. Unlike [drop_wraps], it leaves an unknown wrap intact
    rather than replacing it with a bounded variable. *)
Ltac drop_wraps_goal :=
  repeat match goal with
  | |- context[Z.rem ?x ?y] => assert_fails (has_if x); rewrite (Z.rem_mod_nonneg x y) by arith_fast
  | |- context[Z.quot ?x ?y] => assert_fails (has_if x); rewrite (Z.quot_div_nonneg x y) by arith_fast
  | |- context[?x mod ?m] => assert_fails (has_if x); rewrite (Z.mod_small x m) by arith_fast
  end.

(** The tactic [decide_compares_goal] resolves integer comparisons
    from the current arithmetic facts and leaves any undecided comparison
    in the goal. *)
Ltac decide_compares_goal :=
  repeat match goal with
  | |- context[?a <? ?b] =>
      assert_fails (has_if a); assert_fails (has_if b);
      first [ rewrite (proj2 (Z.ltb_lt a b)) by arith_fast | rewrite (proj2 (Z.ltb_ge a b)) by arith_fast ]
  | |- context[?a <=? ?b] =>
      assert_fails (has_if a); assert_fails (has_if b);
      first [ rewrite (proj2 (Z.leb_le a b)) by arith_fast | rewrite (proj2 (Z.leb_gt a b)) by arith_fast ]
  | |- context[?a =? ?b] =>
      assert_fails (has_if a); assert_fails (has_if b);
      first [ rewrite (proj2 (Z.eqb_eq a b)) by arith_fast | rewrite (proj2 (Z.eqb_neq a b)) by arith_fast ]
  end.

(** The tactic [split_compares] decides known comparisons and creates
    both proof cases for any comparison that remains unknown. It waits
    for nested comparisons and uses `case` to avoid traversing large
    local definitions in the context. *)
Ltac split_compares :=
  repeat (match goal with
          | |- context[?a <? ?b] =>
              assert_fails (has_if a); assert_fails (has_if b);
              first [ rewrite (proj2 (Z.ltb_lt a b)) by arith_fast | rewrite (proj2 (Z.ltb_ge a b)) by arith_fast
                    | case (Z.ltb_spec a b); intro ]
          | |- context[?a <=? ?b] =>
              assert_fails (has_if a); assert_fails (has_if b);
              first [ rewrite (proj2 (Z.leb_le a b)) by arith_fast | rewrite (proj2 (Z.leb_gt a b)) by arith_fast
                    | case (Z.leb_spec a b); intro ]
          | |- context[?a =? ?b] =>
              assert_fails (has_if a); assert_fails (has_if b);
              first [ rewrite (proj2 (Z.eqb_eq a b)) by arith_fast | rewrite (proj2 (Z.eqb_neq a b)) by arith_fast
                    | case (Z.eqb_spec a b); intro ]
          end; cbv beta iota).

(** A rule can leave its result unspecified until computation supplies
    the required value. The tactic [compute_premise] reduces the left
    side with known facts and unifies the right side with that result. *)
Ltac compute_premise :=
  repeat progress (cbn -[load_bytes store_bytes]; try unfold sign_extension;
                   use_facts_goal; cbn [ptr_addr ptr_cap]; drop_wraps_goal; decide_compares_goal);
  reflexivity.

(** The tactic [access_ok] proves a memory access valid from a known
    object region and arithmetic bounds on the address. It handles
    writable or read-only object [[capability|capabilities]] and proves
    the required alignment, including the trivial alignment of one. *)
Ltac access_ok :=
  cbn [ptr_addr ptr_cap]; unfold raw_address; drop_wraps_goal;
  match goal with
  | |- access_res _ _ (Obj _) _ _ _ = _ => eapply access_obj
  | |- access_res _ _ (Ro _) _ _ _ = _ => eapply access_ro_read
  end;
  first [ eassumption | apply Z.mod_1_r | cbn [r_end]; arith ].

(** The tactic [premise] discharges one instruction rule's requirement
    using a known lookup, a memory-operation lemma, or direct computation.
    Memory operations delegate their bounds and alignment checks to
    [access_ok], while ordinary expressions use [compute_premise]. *)
Ltac premise :=
  match goal with
  | |- general_op _ = true => reflexivity
  | |- op_arg_classes _ _ = _ => reflexivity
  | |- width_value_class _ = _ => reflexivity
  | |- find_block _ _ = _ => first [ eassumption | compute_premise ]
  | |- fn_ret _ = _ => first [ eassumption | compute_premise ]
  | |- invalidate_locals _ _ = _ => apply invalidate_none
  | |- _ <> _ => assumption
  | |- _ <= _ => first [ apply Z.leb_le; reflexivity | arith ]
  | |- op_res (Check _ _ _ _) _ _ _ = _ => apply op_check; access_ok
  | |- op_res (RawLoad LdL _) _ _ _ = _ => apply op_raw_load; access_ok
  | |- store_res Wl _ _ _ _ = _ => apply store_res_long; access_ok
  | |- _ = _ => compute_premise
  end.

(** The tactic [step_by_rule] chooses a forward rule for the current
    instruction or control-flow point in a frame that is not [[doomed]].
    It splits the fuel cases when entering a block and handles
    [[flight|flights]], stores, branches, allocations, and top-level
    returns. *)
Ltac step_by_rule :=
  match goal with
  | |- context[step _ (mkConfig (mkFrame _ _ _ None (Enter _ _)) _ _ ?fuel)] =>
      case (Z.eq_dec fuel 0); intro;
      [ match goal with H : fuel = 0 |- _ => rewrite H end; rewrite rule_out_of_fuel
      | erewrite rule_enter by premise ]
  | |- context[step _ (mkConfig (mkFrame _ _ _ None (Exec _ (Let _ _ (Alloc _) _ :: _) _)) _ _ _)] =>
      erewrite rule_alloc by premise
  | |- context[step _ (mkConfig (mkFrame _ _ _ None (Exec _ (Let _ _ _ _ :: _) _)) _ _ _)] =>
      erewrite rule_let by premise
  | |- context[step _ (mkConfig (mkFrame _ _ _ None (Exec _ (Flight _ _ _ _ :: _) _)) _ _ _)] =>
      erewrite rule_flight by premise
  | |- context[step _ (mkConfig (mkFrame _ _ _ None (Exec _ (RawStore _ _ _ _ :: _) _)) _ _ _)] =>
      erewrite rule_raw_store by premise
  | |- context[step _ (mkConfig (mkFrame _ _ _ None (Exec _ [] (JGoto _))) _ _ _)] =>
      rewrite rule_goto
  | |- context[step _ (mkConfig (mkFrame _ _ _ None (Exec _ [] (JBranch _ _ _))) _ _ _)] =>
      erewrite rule_branch by premise
  | |- context[step _ (mkConfig (mkFrame _ _ _ None (Exec _ [] (JRet _))) [] _ _)] =>
      erewrite rule_ret by premise; erewrite rule_return_top by premise
  end.

(** The tactic [take_step] applies the instruction rule, computes any
    jump target, and splits comparisons that remain undecided by the input
    facts. *)
Ltac take_step := step_by_rule; cbn [edge_label Z.eqb Pos.eqb]; split_compares.
