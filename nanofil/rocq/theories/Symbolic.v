(** Symbolic execution of the model's [[step]], for proofs that a
    program never panics from assertions at its points (Cycle.v).

    A program proof states what holds at each point of its function, as
    facts about the [[temporary|temporaries]] of the environment: the
    word a name holds, and a range for an integer. It then shows that
    one step from any configuration where the facts hold reaches a
    point where its facts hold, or ends without a failure (Panics.v's
    [never_panics_by_invariant]). That step is computed here with the
    environment, the memory and the [[fuel]] left abstract: the
    reduction stops where it needs a value it does not have, the facts
    supply it, and an integer comparison is decided by linear
    arithmetic over the facts' ranges, or split into its two answers
    when the facts do not decide it.

    ## Decisions

    | Decision | Why |
    |---|---|
    | integer arithmetic stays folded on an unknown (`simpl nomatch`, set by each program file, since Rocq exports no such setting) | unfolded, `65552 + x` becomes a match on the bits of x as deep as 65552 is long, which neither a fact nor arithmetic can read; on numbers it still computes |
    | the step is reduced by `cbn`, not `cbv` | `cbn` leaves a function stuck on an unknown value folded (`i mod 4294967296`, `lookup x e`), where a fact can be rewritten; `cbv` unfolds it into a term no fact matches, and does not finish on a remainder of a variable |
    | linear arithmetic decides comparisons, with remainders and quotients by constants turned into equations | the bounds a check compares are sums and multiples of the facts' integers; `lia` alone does not know `mod` or `rem` |
    | a remainder of a value proved in range is the value, and any other remainder an unknown in range | the model wraps every result to its [[class]]; where the facts bound it, the wrap is the identity, and dropping it keeps the terms small; where they do not, as for the input, the range is all a step needs, and each wrap or comparison is then tried once |
    | an undecided comparison is split, both answers kept | the input is unknown: the comparison with it goes either way, and the facts after it say which | *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Panics.
Import ListNotations.
Open Scope Z_scope.

(** ## Facts about an environment *)

(** Looking k up after [put] k' v answers v if k is k', and otherwise
    what it answered before. *)
Lemma lookup_after_put : forall (A : Type) k k' (v : A) ps,
  lookup k (put k' v ps) = if name_eqb k k' then Some v else lookup k ps.
Proof.
  intros A k k' v ps. unfold put. simpl. destruct (name_eqb k k') eqn:E; [reflexivity|].
  induction ps as [|[k0 v0] ps IH]; simpl; [reflexivity|].
  destruct (name_eqb k' k0) eqn:E0; simpl.
  - apply term_eqb_eq in E0. subst k0. rewrite E. exact IH.
  - destruct (name_eqb k k0); [reflexivity | exact IH].
Qed.

(** Looking k up after [put] k answers its new value. *)
Lemma lookup_after_put_same : forall (A : Type) k (v : A) ps, lookup k (put k v ps) = Some v.
Proof. intros A k v ps. rewrite lookup_after_put, term_eqb_refl. reflexivity. Qed.

(** Looking k up after [put] of another name answers what it answered
    before. *)
Lemma lookup_after_put_other : forall (A : Type) k k' (v : A) ps,
  name_eqb k k' = false -> lookup k (put k' v ps) = lookup k ps.
Proof. intros A k k' v ps H. rewrite lookup_after_put, H. reflexivity. Qed.

(** A store of bytes changes no object's region. *)
Lemma store_bytes_regions : forall m a size x, m_regions (store_bytes m a size x) = m_regions m.
Proof. reflexivity. Qed.

(** The name x holds an integer word of e that P allows. *)
Definition int_at (e : env) (x : name) (P : Z -> Prop) : Prop :=
  exists v, lookup x e = Some (WInt v) /\ P v.

(** Any integer. *)
Definition any (_ : Z) : Prop := True.

(** ## Arithmetic *)

(** The goal has a remainder or quotient in it. *)
Ltac goal_divides :=
  match goal with
  | |- context[_ mod _] => idtac
  | |- context[Z.rem _ _] => idtac
  | |- context[Z.quot _ _] => idtac
  | |- context[_ / _] => idtac
  end.

(** The arithmetic oracle: linear arithmetic over the integers, with
    the powers of two the model's classes use as numbers, and where
    the goal divides, with remainders and quotients by constants first
    turned into equations. Facts about environments and memory are set
    aside first; they say nothing arithmetic. *)
Ltac arith :=
  repeat match goal with
  | H : context[lookup _ _] |- _ => clear H
  | H : context[m_regions _] |- _ => clear H
  | H : context[m_bytes _] |- _ => clear H
  end;
  try change (2 ^ 31) with 2147483648 in *; try change (2 ^ 32) with 4294967296 in *;
  try change (2 ^ 63) with 9223372036854775808 in *;
  try change (2 ^ 64) with 18446744073709551616 in *;
  first [ lia | goal_divides; Z.to_euclidean_division_equations; lia ].

(** Fails unless the term t has an `if` in it. *)
Ltac has_if t := idtac; match t with context[if _ then _ else _] => idtac end.

(** Fails unless the term t has a remainder in it. *)
Ltac has_mod t := idtac; match t with context[_ mod _] => idtac end.

(** Drop the wraps in E, innermost first, once what each wraps holds
    no other wrap and no undecided comparison: a remainder or quotient
    of a nonnegative value is Euclid's, and a wrap that arithmetic over
    the context, without E, proves is the identity goes. A wrap it does
    not, of the input say, becomes an unknown known to lie between 0
    and the modulus. So each wrap is tried once. *)
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

(** Decide the integer comparisons in E: true or false where arithmetic
    over the context proves it, and otherwise split into its two
    answers at once, each kept as a fact, so that no comparison is
    tried twice. A comparison whose operands hold another comparison
    waits until that one is decided. *)
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

(** ## The step *)

(** Rewrite in E every fact in the context that names a temporary of an
    environment, the region of an object in a memory, or a block or the
    return class of the function, which a proof keeps abstract
    ([block_fact]) so that its whole body is not carried through every
    step. *)
Ltac use_facts E :=
  repeat match goal with
  | H : lookup _ _ = Some _ |- _ => rewrite H in E
  | H : object_region _ (m_regions _) = Some _ |- _ => rewrite H in E
  | H : find_block _ (fn_blocks _) = _ |- _ => rewrite H in E
  | H : fn_ret _ = _ |- _ => rewrite H in E
  end.

(** Reduce E as far as the facts and arithmetic allow: `cbn`, keeping
    a load's and a store's bytes folded, then the definitions `cbn` leaves folded
    (stuck on an unknown, such as an access check on the memory's
    regions, or building a record), the facts and the fields they
    supply, the wraps and the comparisons, until nothing changes. *)
Ltac reduce E :=
  repeat progress (
    cbn -[load_bytes store_bytes] in E; rewrite ?store_bytes_regions in E;
    try unfold sign_extension in E; try unfold raw_address in E; try unfold aligned_res in E;
    try unfold continue_at in E; try unfold with_point in E;
    try unfold int_load_res in E; try unfold access_res in E; try unfold cap_access_res in E;
    use_facts E; cbn [r_base r_end r_kind r_life ptr_addr ptr_cap] in E;
    drop_wraps E; decide_compares E).

(** Compute E, an equation r = step g c, to a result: reduce it, in
    every case of the comparisons the facts leave open. *)
Ltac compute_step E := reduce E.

(** ## Facts after a step *)

(** Take apart the facts in the context: conjunctions, existentials,
    and each case of a disjunction. *)
Ltac facts :=
  repeat match goal with
  | H : True |- _ => clear H
  | H : _ /\ _ |- _ => destruct H
  | H : exists _, _ |- _ => destruct H
  | H : _ \/ _ |- _ => destruct H
  end.

(** Prove a fact about the configuration after a step: look each name
    up through the step's [put]s to the facts before it, each object's
    region through the stores, which change none, and through a new
    object's, and the ranges by arithmetic. *)
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
  | |- _ <= _ => arith
  | |- _ < _ => arith
  | |- _ => progress cbv beta iota
  end.

(** ## The function, kept abstract *)

(** The block l of the function fn, computed once as b, and the fact H
    that the abstract f, equal to fn by Hf, has it: the step finds a
    block through H instead of reducing f's body. *)
Ltac block_fact f fn Hf l b H :=
  pose (b := find_block l (fn_blocks fn)); vm_compute in b;
  assert (H : find_block l (fn_blocks f) = b) by (rewrite Hf; reflexivity).
