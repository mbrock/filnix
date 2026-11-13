(** This module proves that the [[offset-interval|offset intervals]]
    computed by the [[validator]] accurately bound runtime integer
    values.
    [Campaign 3](../../../docs/formal.md#campaign-3-the-soundness-theorem)
    and [Offset intervals](../../../docs/rocq.md#offset-intervals)
    describe how interval bounds support pointer reuse.

    When a program adds an offset to a pointer, the validator bounds
    that integer offset by walking backward through the function's
    [[single-definition|single definitions]] with [offset_interval]. To
    prove that walk sound without reasoning about memo tables and depth
    limits at every step, we define a declarative relation [iv] with one
    constructor per operator clause. We then prove two facts: every
    interval returned by the validator is derivable in [iv], and every
    derivable interval holds of the runtime value whenever all walked
    single definitions still match their original computations.

    ## Decisions

    When a program adds several integer offsets together, the validator
    caches intermediate bounds in a memo table and stops at a fixed
    depth. Our declarative relation drops both the memo table and the
    depth limit, because soundness only needs each arithmetic rule to
    hold on its own. For multiplication, we name the scaled operand
    directly so induction never splits across a disjunction.

    A 64-bit pointer offset never wraps around like a 32-bit signed
    integer, so we check integer bounds modulo the operand's bit width.
    A narrow memory load always fits inside its target integer size
    after extension, regardless of what is in memory. Similarly, bitwise
    masks and narrow extensions bound their outputs regardless of their
    inputs, so their operands can be redefined later. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Values Memory Ops Semantics Machine Validate Dominance.
Import ListNotations.
Local Open Scope Z_scope.

(** Two classes k and k' that [class_eqb] finds equal are equal. *)
Lemma class_eqb_true : forall k k', class_eqb k k' = true -> k = k'.
Proof. intros k k' H. destruct k, k'; try discriminate H; reflexivity. Qed.

(** This tactic closes any clause that returns no interval and leaves
    the memo unchanged. *)
Ltac no_answer_now H Hm :=
  injection H as <- <-; split; [intros ? ? Hno; discriminate Hno | exact Hm].

(** [no_answer_now], for a clause that answers none whatever an operand is:
    it takes the operands apart until each case closes. *)
Ltac no_answer H Hm :=
  first [ no_answer_now H Hm
        | match goal with v : value |- _ => destruct v; cbn in H; no_answer H Hm end ].

(** This section fixes a function's single-definition map and defines
    the declarative interval relation over it. *)
Section Intervals.

(** The variable [once] holds the function's single-definition map as
    built by [single_definitions]. *)
Variable once : list (name * def).

(** A temporary name n is [defined] at [[class]] k by operation o and
    arguments args when its unique definition in the function is that
    `let` binding. *)
Definition defined (n : name) (k : class) (o : op) (args : list value) : Prop :=
  exists n', lookup n once = Some (DInst (Let n' k o args)) /\ name_eqb n' n = true.

(** The inductive relation [iv] captures every [[offset-interval|offset interval]]
    that the validator's bounded walk can derive. A judgment [iv v k lo hi]
    means that value v read at [[class]] k lies between lo and hi modulo
    the class width, with one constructor for each operator clause. *)
Inductive iv : value -> class -> Z -> Z -> Prop :=
| iv_const : forall c k x, signed_value k c = Some x -> iv (Const c) k x x
| iv_narrow : forall n k t args lo hi,
    defined n k (Ext t) args -> narrow_range t = Some (lo, hi) -> interval_fits k lo hi = true ->
    iv (Tmp n) k lo hi
| iv_sw : forall n k a lo hi,
    defined n k (Ext Sw) [a] -> iv a W lo hi -> interval_fits k lo hi = true -> iv (Tmp n) k lo hi
| iv_uw : forall n k a lo hi,
    defined n k (Ext Uw) [a] -> iv a W lo hi -> 0 <= lo -> interval_fits k lo hi = true ->
    iv (Tmp n) k lo hi
| iv_load : forall n k t off args lo hi,
    defined n k (RawLoad (LdNarrow t) off) args -> narrow_range t = Some (lo, hi) ->
    interval_fits k lo hi = true -> iv (Tmp n) k lo hi
| iv_copy : forall n k a lo hi,
    defined n k Copy [a] -> iv a k lo hi -> interval_fits k lo hi = true -> iv (Tmp n) k lo hi
| iv_and : forall n k a b c v,
    defined n k And [a; b] -> (a = Const c \/ b = Const c) -> signed_value k c = Some v -> 0 <= v ->
    interval_fits k 0 v = true -> iv (Tmp n) k 0 v
| iv_urem : forall n k a c bits,
    defined n k Urem [a; Const c] -> class_bits k = Some bits ->
    0 < c mod 2 ^ bits -> c mod 2 ^ bits <= 2 ^ (bits - 1) ->
    interval_fits k 0 (c mod 2 ^ bits - 1) = true -> iv (Tmp n) k 0 (c mod 2 ^ bits - 1)
| iv_shl : forall n k a s bits lo hi,
    defined n k Shl [a; Const s] -> class_bits k = Some bits -> 0 <= s -> s < bits ->
    iv a k lo hi -> interval_fits k (lo * 2 ^ s) (hi * 2 ^ s) = true ->
    iv (Tmp n) k (lo * 2 ^ s) (hi * 2 ^ s)
| iv_mul : forall n k args x c v lo0 hi0 lo hi,
    defined n k Mul args -> (args = [x; Const c] \/ args = [Const c; x]) -> iv x k lo0 hi0 ->
    signed_value k c = Some v ->
    (if 0 <=? v then (lo0 * v, hi0 * v) else (hi0 * v, lo0 * v)) = (lo, hi) ->
    interval_fits k lo hi = true -> iv (Tmp n) k lo hi
| iv_add : forall n k a b lo1 hi1 lo2 hi2,
    defined n k Add [a; b] -> iv a k lo1 hi1 -> iv b k lo2 hi2 ->
    interval_fits k (lo1 + lo2) (hi1 + hi2) = true -> iv (Tmp n) k (lo1 + lo2) (hi1 + hi2)
| iv_sub : forall n k a c v lo hi,
    defined n k Sub [a; Const c] -> signed_value k c = Some v -> iv a k lo hi ->
    interval_fits k (lo - v) (hi - v) = true -> iv (Tmp n) k (lo - v) (hi - v).

(** The validator caches previously computed intervals in a memo table
    to avoid re-walking shared expressions. A memo satisfies [memo_ok]
    when every cached interval is derivable in [iv]. *)
Definition memo_ok (m : memo) : Prop :=
  forall n k lo hi, memo_lookup n k m = Some (Some (lo, hi)) -> iv (Tmp n) k lo hi.

(** The empty memo is derived. *)
Lemma memo_ok_nil : memo_ok [].
Proof. intros n k lo hi E. discriminate E. Qed.

(** Caching a newly computed interval in the memo table preserves memo
    validity whenever the interval itself is derivable. *)
Lemma memo_ok_cons : forall n k r m,
  memo_ok m -> (forall lo hi, r = Some (lo, hi) -> iv (Tmp n) k lo hi) -> memo_ok (((n, k), r) :: m).
Proof.
  intros n k r m Hm Hr n' k' lo hi H. simpl in H.
  destruct (name_eqb n n' && class_eqb k k') eqn:E.
  - apply andb_true_iff in E as [E1 E2]. apply term_eqb_eq in E1. apply class_eqb_true in E2.
    subst n' k'. injection H as ->. exact (Hr _ _ eq_refl).
  - exact (Hm _ _ _ _ H).
Qed.

(** When an operator clause inspects its operand subexpressions, it
    calls a recursive helper to bound them. A helper satisfies [rec_ok]
    when every interval it returns is derivable and it keeps the memo
    table valid. *)
Definition rec_ok (rec : value -> class -> memo -> option (Z * Z) * memo) : Prop :=
  forall a k m r m', memo_ok m -> rec a k m = (r, m') ->
  (forall lo hi, r = Some (lo, hi) -> iv a k lo hi) /\ memo_ok m'.

(** Every operator clause in [op_interval] produces a derivable interval
    and preserves [memo_ok] whenever the operand callback satisfies
    [rec_ok] and the interval fits the class. *)
Lemma op_interval_ok : forall rec o args k m r m' n,
  rec_ok rec -> memo_ok m -> defined n k o args ->
  op_interval rec o args k m = (r, m') ->
  (forall lo hi, r = Some (lo, hi) -> interval_fits k lo hi = true -> iv (Tmp n) k lo hi) /\ memo_ok m'.
Proof.
  intros rec o args k m r m' n Hrec Hm Hd H.
  (* the cases where the op's operands' walks are the answer *)
  destruct o; simpl in H;
    try (no_answer H Hm).
  - (* add *)
    destruct args as [|a [|b [|c args]]]; cbn in H;
      try (no_answer H Hm).
    destruct (rec a k m) as [[[lo1 hi1]|] m1] eqn:Ea; destruct (Hrec _ _ _ _ _ Hm Ea) as [Ha Hm1].
    + destruct (rec b k m1) as [[[lo2 hi2]|] m2] eqn:Eb; destruct (Hrec _ _ _ _ _ Hm1 Eb) as [Hb Hm2].
      * injection H as <- <-. split; [|exact Hm2]. intros lo hi E Hf. injection E as <- <-.
        exact (iv_add _ _ _ _ _ _ _ _ Hd (Ha _ _ eq_refl) (Hb _ _ eq_refl) Hf).
      * injection H as <- <-. split; [intros lo hi E; discriminate E | exact Hm2].
    + injection H as <- <-. split; [intros lo hi E; discriminate E | exact Hm1].
  - (* sub *)
    destruct args as [|a [|b [|c args]]]; cbn in H;
      try (no_answer H Hm).
    destruct b as [nb | cb | gb]; cbn in H; try (no_answer H Hm).
    destruct (signed_value k cb) as [v|] eqn:Ev;
      [|no_answer H Hm].
    destruct (rec a k m) as [[[lo0 hi0]|] m1] eqn:Er; destruct (Hrec _ _ _ _ _ Hm Er) as [Hr Hm1].
    + injection H as <- <-. split; [|exact Hm1]. intros lo hi E Hf. injection E as <- <-.
      exact (iv_sub _ _ _ _ _ _ _ Hd Ev (Hr _ _ eq_refl) Hf).
    + injection H as <- <-. split; [intros lo hi E; discriminate E | exact Hm1].
  - (* mul *)
    assert (Hsc : forall x c r0 m0, (args = [x; Const c] \/ args = [Const c; x]) ->
              (match signed_value k c with
               | Some v => match rec x k m with
                           | (Some (lo, hi), m1) =>
                               (Some (if 0 <=? v then (lo * v, hi * v) else (hi * v, lo * v)), m1)
                           | r => r
                           end
               | None => (None, m)
               end) = (r0, m0) ->
              (forall lo hi, r0 = Some (lo, hi) -> interval_fits k lo hi = true -> iv (Tmp n) k lo hi) /\ memo_ok m0).
    { intros x c r0 m0 Ha E. destruct (signed_value k c) as [v|] eqn:Ev; [|no_answer_now E Hm].
      destruct (rec x k m) as [[[lo0 hi0]|] m1] eqn:Er; destruct (Hrec _ _ _ _ _ Hm Er) as [Hr Hm1];
        [|no_answer_now E Hm1].
      injection E as <- <-. split; [|exact Hm1]. intros lo hi E' Hf. injection E' as E'.
      exact (iv_mul _ _ _ _ _ _ _ _ _ _ Hd Ha (Hr _ _ eq_refl) Ev E' Hf). }
    destruct args as [|a [|b [|x args]]]; cbn in H;
      try (no_answer H Hm).
    destruct b as [nb | cb | gb]; destruct a as [na | ca | ga]; cbn in H;
      try (no_answer H Hm).
    + exact (Hsc _ ca _ _ (or_intror eq_refl) H).
    + exact (Hsc _ cb _ _ (or_introl eq_refl) H).
    + exact (Hsc _ cb _ _ (or_introl eq_refl) H).
    + exact (Hsc _ ca _ _ (or_intror eq_refl) H).
  - (* urem *)
    destruct args as [|a [|b [|c args]]]; cbn in H;
      try (no_answer H Hm).
    destruct b as [nb | cb | gb]; cbn in H; try (no_answer H Hm).
    destruct (class_bits k) as [bits|] eqn:Eb;
      [|no_answer H Hm].
    injection H as <- <-. split; [|exact Hm]. intros lo hi E Hf.
    destruct ((0 <? cb mod 2 ^ bits) && (cb mod 2 ^ bits <=? 2 ^ (bits - 1))) eqn:Ec; [|discriminate E].
    injection E as <- <-. apply andb_true_iff in Ec as [E1 E2]. apply Z.ltb_lt in E1. apply Z.leb_le in E2.
    exact (iv_urem _ _ _ _ _ Hd Eb E1 E2 Hf).
  - (* and *)
    assert (Hmask : forall c lo hi, (exists a b, args = [a; b] /\ (a = Const c \/ b = Const c)) ->
              (match signed_value k c with Some v => if 0 <=? v then Some (0, v) else None | None => None end)
                = Some (lo, hi) -> interval_fits k lo hi = true -> iv (Tmp n) k lo hi).
    { intros c lo hi (a & b & -> & Hc) E Hf. destruct (signed_value k c) as [v|] eqn:Ev; [|discriminate E].
      destruct (0 <=? v) eqn:Ez; [|discriminate E]. injection E as <- <-. apply Z.leb_le in Ez.
      exact (iv_and _ _ _ _ _ _ Hd Hc Ev Ez Hf). }
    destruct args as [|a [|b [|x args]]]; cbn in H;
      try (no_answer H Hm).
    (* ir.pl tries the right operand's mask first, then the left's. *)
    destruct a as [na | ca | ga]; destruct b as [nb | cb | gb]; cbn in H; try (no_answer H Hm).
    + destruct (signed_value k cb) as [vb|] eqn:Evb; [destruct (0 <=? vb) eqn:Ezb|]; cbn in H;
        [|no_answer H Hm|no_answer H Hm].
      injection H as <- <-. split; [|exact Hm]. intros lo hi E Hf.
      apply (Hmask cb lo hi (ex_intro _ _ (ex_intro _ _ (conj eq_refl (or_intror eq_refl))))); [|exact Hf].
      rewrite Evb, Ezb. exact E.
    + injection H as <- <-. split; [|exact Hm]. intros lo hi E Hf.
      exact (Hmask ca lo hi (ex_intro _ _ (ex_intro _ _ (conj eq_refl (or_introl eq_refl)))) E Hf).
    + destruct (signed_value k cb) as [vb|] eqn:Evb; [destruct (0 <=? vb) eqn:Ezb|]; cbn in H;
        injection H as <- <-; split; try exact Hm; intros lo hi E Hf.
      * apply (Hmask cb lo hi (ex_intro _ _ (ex_intro _ _ (conj eq_refl (or_intror eq_refl))))); [|exact Hf].
        rewrite Evb, Ezb. exact E.
      * exact (Hmask ca lo hi (ex_intro _ _ (ex_intro _ _ (conj eq_refl (or_introl eq_refl)))) E Hf).
      * exact (Hmask ca lo hi (ex_intro _ _ (ex_intro _ _ (conj eq_refl (or_introl eq_refl)))) E Hf).
    + injection H as <- <-. split; [|exact Hm]. intros lo hi E Hf.
      exact (Hmask ca lo hi (ex_intro _ _ (ex_intro _ _ (conj eq_refl (or_introl eq_refl)))) E Hf).
    + destruct (signed_value k cb) as [vb|] eqn:Evb; [destruct (0 <=? vb) eqn:Ezb|]; cbn in H;
        [|no_answer H Hm|no_answer H Hm].
      injection H as <- <-. split; [|exact Hm]. intros lo hi E Hf.
      apply (Hmask cb lo hi (ex_intro _ _ (ex_intro _ _ (conj eq_refl (or_intror eq_refl))))); [|exact Hf].
      rewrite Evb, Ezb. exact E.
  - (* shl *)
    destruct args as [|a [|b [|c args]]]; cbn in H;
      try (no_answer H Hm).
    destruct b as [nb | s | gb]; cbn in H; try (no_answer H Hm).
    destruct (class_bits k) as [bits|] eqn:Eb;
      [|no_answer H Hm].
    destruct ((0 <=? s) && (s <? bits)) eqn:Es;
      [|no_answer H Hm].
    apply andb_true_iff in Es as [Es1 Es2]. apply Z.leb_le in Es1. apply Z.ltb_lt in Es2.
    destruct (rec a k m) as [[[lo0 hi0]|] m1] eqn:Er.
    + destruct (Hrec _ _ _ _ _ Hm Er) as [Hr Hm1]. injection H as <- <-. split; [|exact Hm1].
      intros lo hi E Hf. injection E as <- <-.
      exact (iv_shl _ _ _ _ _ _ _ Hd Eb Es1 Es2 (Hr _ _ eq_refl) Hf).
    + destruct (Hrec _ _ _ _ _ Hm Er) as [_ Hm1]. injection H as <- <-.
      split; [intros lo hi E; discriminate E | exact Hm1].
  - (* copy *)
    destruct args as [|a [|a2 args]]; cbn in H;
      try (no_answer H Hm).
    destruct (Hrec _ _ _ _ _ Hm H) as [Hr Hm']. split; [|exact Hm']. intros lo hi E Hf.
    exact (iv_copy _ _ _ _ _ Hd (Hr _ _ E) Hf).
  - (* ext *)
    destruct (narrow_range t) as [[lo0 hi0]|] eqn:Et.
    + injection H as <- <-. split; [|exact Hm]. intros lo hi E Hf. injection E as <- <-.
      exact (iv_narrow _ _ _ _ _ _ Hd Et Hf).
    + destruct t; try discriminate Et; destruct args as [|a [|a2 args]];
        try (no_answer H Hm).
      * destruct (Hrec _ _ _ _ _ Hm H) as [Hr Hm']. split; [|exact Hm']. intros lo hi E Hf.
        exact (iv_sw _ _ _ _ _ Hd (Hr _ _ E) Hf).
      * destruct (rec a W m) as [[[lo0 hi0]|] m1] eqn:Er.
        -- destruct (Hrec _ _ _ _ _ Hm Er) as [Hr Hm1]. destruct (0 <=? lo0) eqn:El.
           ++ injection H as <- <-. split; [|exact Hm1]. intros lo hi E Hf. injection E as <- <-.
              apply Z.leb_le in El. exact (iv_uw _ _ _ _ _ Hd (Hr _ _ eq_refl) El Hf).
           ++ injection H as <- <-. split; [intros lo hi E; discriminate E | exact Hm1].
        -- injection H as <- <-. destruct (Hrec _ _ _ _ _ Hm Er) as [_ Hm1].
           split; [intros lo hi E; discriminate E | exact Hm1].
  - (* raw_load *)
    destruct t; try (no_answer H Hm).
    injection H as <- <-. split; [|exact Hm]. intros lo hi E Hf.
    exact (iv_load _ _ _ _ _ _ _ Hd E Hf).
Qed.

(** Bounding the recursion depth and caching intermediate answers cannot
    invent an unsound interval. Whatever fuel or depth remains, every
    bound returned by [oi] is derivable in [iv] and preserves memo
    validity. *)
Lemma oi_sound : forall fuel v k depth m r m',
  memo_ok m -> oi once fuel v k depth m = (r, m') ->
  (forall lo hi, r = Some (lo, hi) -> iv v k lo hi) /\ memo_ok m'.
Proof.
  induction fuel as [|f IH]; intros v k depth m r m' Hm H; destruct v as [n | c | g]; simpl in H.
  all: try (no_answer H Hm).
  all: try (destruct (signed_value k c) as [x|] eqn:Ex; injection H as <- <-; split;
            [intros lo hi E; injection E as <- <-; exact (iv_const _ _ _ Ex) | exact Hm
            |intros lo hi E; discriminate E | exact Hm]).
  - destruct (memo_lookup n k m) as [r0|] eqn:Em.
    + injection H as <- <-. split; [|exact Hm]. intros lo hi E. subst r0. exact (Hm _ _ _ _ Em).
    + injection H as <- <-. split; [intros lo hi E; discriminate E|].
      apply memo_ok_cons; [exact Hm | intros lo hi E; discriminate E].
  - destruct (memo_lookup n k m) as [r0|] eqn:Em.
    + injection H as <- <-. split; [|exact Hm]. intros lo hi E. subst r0. exact (Hm _ _ _ _ Em).
    + assert (Hrec : rec_ok (fun v k m => oi once f v k (depth + 1) m))
        by (intros a k' m0 r0 m1 Hm0 E; exact (IH _ _ _ _ _ _ Hm0 E)).
      assert (Hres : forall r0 m0,
                (if depth <? 32 then
                   match lookup n once with
                   | Some (DInst (Let n' k' o args)) =>
                       if name_eqb n' n && class_eqb k' k then
                         match op_interval (fun v k m => oi once f v k (depth + 1) m) o args k m with
                         | (Some (lo, hi), m1) => if interval_fits k lo hi then (Some (lo, hi), m1) else (None, m)
                         | (None, _) => (None, m)
                         end
                       else (None, m)
                   | _ => (None, m)
                   end
                 else (None, m)) = (r0, m0) ->
                (forall lo hi, r0 = Some (lo, hi) -> iv (Tmp n) k lo hi) /\ memo_ok m0).
      { intros r0 m0 E.
        destruct (depth <? 32); [|no_answer E Hm].
        destruct (lookup n once) as [[| ph | i]|] eqn:El;
          try (no_answer E Hm).
        destruct i as [n' k' o args | | | | | | | | ];
          try (no_answer E Hm).
        destruct (name_eqb n' n && class_eqb k' k) eqn:Ek;
          [|no_answer E Hm].
        apply andb_true_iff in Ek as [Ek1 Ek2]. apply class_eqb_true in Ek2. subst k'.
        assert (Hd : defined n k o args) by (exists n'; split; [exact El | exact Ek1]).
        destruct (op_interval _ o args k m) as [[[lo0 hi0]|] m1] eqn:Eo;
          destruct (op_interval_ok _ _ _ _ _ _ _ _ Hrec Hm Hd Eo) as [Ho Hm1].
        - destruct (interval_fits k lo0 hi0) eqn:Ef.
          + injection E as <- <-. split; [|exact Hm1]. intros lo hi E. injection E as <- <-.
            exact (Ho _ _ eq_refl Ef).
          + injection E as <- <-. split; [intros lo hi E; discriminate E | exact Hm].
        - injection E as <- <-. split; [intros lo hi E; discriminate E | exact Hm]. }
      match type of H with (let '(_, _) := ?x in _) = _ =>
        destruct x as [r0 m0] eqn:Ex end.
      injection H as <- <-. destruct (Hres _ _ eq_refl) as [Hr Hm0]. split; [exact Hr|].
      apply memo_ok_cons; [exact Hm0 | exact Hr].
Qed.

(** When the [[validator]] computes an integer bound for a pointer
    offset, that bound is guaranteed to be derivable in our declarative
    relation [iv]. Downstream proofs in [Chain] consume the validator's
    bounds through [offset_interval_iv]. *)
Theorem offset_interval_iv : forall v k lo hi,
  offset_interval once v k = Some (lo, hi) -> iv v k lo hi.
Proof.
  intros v k lo hi H. unfold offset_interval in H.
  destruct (oi once 33 v k 0 []) as [r m'] eqn:E. simpl in H. subst r.
  apply (oi_sound _ _ _ _ _ _ _ memo_ok_nil E). reflexivity.
Qed.

(** ## What an interval means on a run

    An interval bounds the runtime integer values that a program
    computes along an execution. Whenever each walked temporary holds
    the result computed from its operands, [iv_sound] shows that the
    derived interval holds of the runtime value. We abstract over the
    run-level invariant using a predicate ok that is closed under
    single-definition operands. *)

(** The predicate [let_holds] states that temporary n in environment e
    holds the value computed by operation o on its arguments in the
    defining environment e0. For a narrow load, it holds some extended
    value from that narrow type. *)
Definition let_holds (ge : genv) (e0 e : env) (n : name) (k : class) (o : op) (args : list value) : Prop :=
  match o with
  | RawLoad (LdNarrow t) _ => exists u x, extended t k u = Some x /\ lookup n e = Some x
  | _ => exists classes xs x, op_arg_classes o k = Some classes /\
           map2_option (value_x ge e0) classes args = Some xs /\ alu o k xs = Some x /\
           lookup n e = Some x
  end.

(** Only integer arithmetic, extensions, and narrow loads produce bounds
    in an interval derivation. The predicate [iv_op] identifies those
    supported operations. *)
Definition iv_op (o : op) : bool :=
  match o with
  | Ext _ | RawLoad (LdNarrow _) _ | Copy | And | Urem | Shl | Mul | Add | Sub => true
  | _ => false
  end.

(** A value v satisfies [in_iv] at integer [[class]] k in environment e
    when it evaluates to a word congruent to some integer x between lo
    and hi modulo the class width. *)
Definition in_iv (ge : genv) (e : env) (k : class) (v : value) (lo hi : Z) : Prop :=
  exists bits u x, class_bits k = Some bits /\ value_x ge e k v = Some (WInt u) /\
    lo <= x <= hi /\ u = x mod 2 ^ bits.

(** ### Arithmetic *)

(** An interval that fits the class k ([interval_fits]) is of an integer
    class: k has a bit width bits, and its modulus is 2^bits, which is
    positive. *)
Lemma fits_bits : forall k lo hi, interval_fits k lo hi = true ->
  exists bits, class_bits k = Some bits /\ modulus k = Some (2 ^ bits) /\ 0 < 2 ^ bits.
Proof. intros k lo hi H. destruct k; try discriminate H; eexists; (split; [reflexivity | split; [reflexivity | lia]]). Qed.

(** The signed value x of the constant c at a class of width bits
    ([signed_value]) is congruent to c modulo 2^bits and lies in the signed
    range of that width. *)
Lemma signed_value_mod : forall k c x bits, signed_value k c = Some x -> class_bits k = Some bits ->
  x mod 2 ^ bits = c mod 2 ^ bits /\ - 2 ^ (bits - 1) <= x < 2 ^ (bits - 1).
Proof.
  intros k c x bits H Hb. unfold signed_value in H. rewrite Hb in H. simpl in H. injection H as <-.
  assert (Hp : 2 ^ bits = 2 * 2 ^ (bits - 1) /\ 0 < 2 ^ (bits - 1)).
  { destruct k; try discriminate Hb; injection Hb as <-; simpl; lia. }
  pose proof (Z.mod_pos_bound c (2 ^ bits) ltac:(lia)).
  destruct (2 ^ (bits - 1) <=? c mod 2 ^ bits) eqn:E; [apply Z.leb_le in E | apply Z.leb_gt in E]; split; try lia.
  - replace (c mod 2 ^ bits - 2 ^ bits) with (c mod 2 ^ bits + (-1) * 2 ^ bits) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_mod. lia.
  - apply Z.mod_mod. lia.
Qed.

(** A constant's signed value fits its class ([interval_fits]) as an
    interval of one point. *)
Lemma signed_value_fits : forall k c x, signed_value k c = Some x -> interval_fits k x x = true.
Proof.
  intros k c x H. destruct k; try (unfold signed_value in H; discriminate H); [|reflexivity].
  destruct (signed_value_mod _ _ _ _ H eq_refl) as [_ Hr]. simpl. apply andb_true_iff.
  split; [apply Z.leb_le | apply Z.leb_le]; lia.
Qed.

(** Every interval derived ([iv]) fits its class ([interval_fits]). *)
Lemma iv_fits : forall v k lo hi, iv v k lo hi -> interval_fits k lo hi = true.
Proof. intros v k lo hi H. destruct H; try assumption. exact (signed_value_fits _ _ _ H). Qed.

(** Sign-extending u from the modulus m = 2h ([sign_extension]) gives at
    least -h and less than h. *)
Lemma sign_extension_range : forall m h u, 0 < h -> m = 2 * h -> - h <= sign_extension m h u < h.
Proof.
  intros m h u Hh Hm. unfold sign_extension. pose proof (Z.mod_pos_bound u m ltac:(lia)).
  destruct (h <=? u mod m) eqn:E; [apply Z.leb_le in E | apply Z.leb_gt in E]; lia.
Qed.

(** Extending any integer from a narrow type t produces a value inside
    t's [narrow_range], so narrow extensions and narrow loads are bounded
    regardless of the underlying value. *)
Lemma narrow_extension : forall t lo hi x, narrow_range t = Some (lo, hi) -> lo <= extension t x <= hi.
Proof.
  intros t lo hi x H. destruct t; simpl in H; try discriminate H; injection H as <- <-; simpl.
  - pose proof (sign_extension_range 65536 32768 x ltac:(lia) ltac:(lia)). lia.
  - pose proof (Z.mod_pos_bound x 65536 ltac:(lia)). lia.
  - pose proof (sign_extension_range 256 128 x ltac:(lia) ltac:(lia)). lia.
  - pose proof (Z.mod_pos_bound x 256 ltac:(lia)). lia.
Qed.

(** A sign-extended word is the signed value it holds: a signed 32-bit x,
    taken modulo 2^32 and sign-extended, is x again. *)
Lemma sign_extension_mod : forall x, - 2 ^ 31 <= x < 2 ^ 31 ->
  sign_extension (2 ^ 32) (2 ^ 31) (x mod 2 ^ 32) = x.
Proof.
  intros x Hx. unfold sign_extension. rewrite Z.mod_mod by lia.
  destruct (Z_lt_le_dec x 0).
  - replace (x mod 2 ^ 32) with (x + 2 ^ 32).
    + rewrite (proj2 (Z.leb_le _ _)) by lia. lia.
    + apply Z.mod_unique with (-1); lia.
  - rewrite Z.mod_small by lia. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
Qed.

(** The bitwise and of two nonnegative integers x and y lies from 0 to y: a
    nonnegative mask bounds an `and`. *)
Lemma land_le : forall x y, 0 <= x -> 0 <= y -> 0 <= Z.land x y <= y.
Proof.
  intros x y Hx Hy. split; [apply Z.land_nonneg; auto|].
  apply (Z.ldiff_le _ _ Hy). apply Z.bits_inj'. intros i Hi.
  rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit x i), (Z.testbit y i); reflexivity.
Qed.

(** A temporary n holding the integer w, read at an integer class of width
    bits, reads as w modulo 2^bits. *)
Lemma read_tmp : forall ge e k n w bits, class_bits k = Some bits -> lookup n e = Some (WInt w) ->
  value_x ge e k (Tmp n) = Some (WInt (w mod 2 ^ bits)).
Proof. intros ge e k n w bits Hb H. simpl. rewrite H. destruct k; try discriminate Hb; injection Hb as <-; reflexivity. Qed.

(** Any operand that reads as an integer u at an integer class of width bits
    has u at least 0 and below 2^bits. *)
Lemma value_int_range : forall ge e k v u bits, class_bits k = Some bits -> value_x ge e k v = Some (WInt u) ->
  0 <= u < 2 ^ bits.
Proof.
  intros ge e k v u bits Hb H. destruct k; try discriminate Hb; injection Hb as <-;
    destruct v as [n | c | g]; simpl in H.
  all: try (destruct (lookup n e) as [[w| |]|]; simpl in H; try discriminate H; injection H as <-;
            apply Z.mod_pos_bound; lia).
  all: try (injection H as <-; apply Z.mod_pos_bound; lia).
  all: destruct (lookup g (ge_globals ge)); discriminate H.
Qed.

(** When a temporary holds integer w, it satisfies [in_iv] between lo
    and hi if some integer in that range equals w modulo the class
    width. *)
Lemma in_iv_tmp : forall ge e k n w bits x lo hi,
  class_bits k = Some bits -> lookup n e = Some (WInt w) -> w mod 2 ^ bits = x mod 2 ^ bits ->
  lo <= x <= hi -> in_iv ge e k (Tmp n) lo hi.
Proof. intros ge e k n w bits x lo hi Hb H Hw Hx. exists bits, (w mod 2 ^ bits), x. rewrite (read_tmp _ _ _ _ _ _ Hb H). auto. Qed.

(** A constant c read at an integer class of width bits reads as c modulo
    2^bits. *)
Lemma const_read : forall ge e k c bits, class_bits k = Some bits ->
  value_x ge e k (Const c) = Some (WInt (c mod 2 ^ bits)).
Proof. intros ge e k c bits Hb. destruct k; try discriminate Hb; injection Hb as <-; reflexivity. Qed.

(** [map2_option] over two two-element lists succeeds only when f succeeds
    on each pair, and gives the two results. *)
Lemma map2_two : forall (X Y W : Type) (f : X -> Y -> option W) k1 k2 a b xs,
  map2_option f [k1; k2] [a; b] = Some xs -> exists x y, f k1 a = Some x /\ f k2 b = Some y /\ xs = [x; y].
Proof.
  intros X Y W f k1 k2 a b xs H. simpl in H.
  destruct (f k1 a) as [x|]; [|discriminate H]. destruct (f k2 b) as [y|]; [|discriminate H].
  injection H as <-. eauto.
Qed.

(** ### The theorem *)

(** To prove interval soundness in one runtime state, we parameterize
    over a predicate ok naming the temporaries that still match their
    definitions. [Chain] instantiates ok with dominance at the frame's
    current point. *)
Section Sound.

(** This section fixes the global environment ge, the current frame
    environment e, and the predicate ok of valid temporaries. *)
Variables (ge : genv) (e : env) (ok : name -> Prop).

(** Every valid temporary defined by an arithmetic or load instruction
    must still hold the result computed when that instruction ran, and
    every single-definition operand it used must still match its value
    in the current environment. *)
Hypothesis Hok : forall n k o args, defined n k o args -> iv_op o = true -> class_bits k <> None -> ok n ->
  exists e0, let_holds ge e0 e n k o args /\
    forall a, In (Tmp a) args -> once_has once a = true -> ok a /\ lookup a e0 = lookup a e.

(** A temporary n with a derived interval has a single definition: every
    [iv] constructor for a name rests on [defined]. *)
Lemma iv_once : forall v k lo hi, iv v k lo hi -> forall n, v = Tmp n -> once_has once n = true.
Proof.
  intros v k lo hi H n E. destruct H; try discriminate E; injection E as ->;
    match goal with Hd : defined _ _ _ _ |- _ => destruct Hd as (n' & Hl & _) end;
    unfold once_has; rewrite Hl; reflexivity.
Qed.

(** When an arithmetic instruction reuses an earlier operand, that
    operand must still hold the same value in the current environment.
    Any operand with a derived interval that satisfies ok reads
    identically in e0 and e across every integer class. *)
Lemma walked : forall e0 args a k' lo hi,
  (forall a, In (Tmp a) args -> once_has once a = true -> ok a /\ lookup a e0 = lookup a e) ->
  In a args -> iv a k' lo hi ->
  (forall n, a = Tmp n -> ok n) /\ forall k'', value_x ge e0 k'' a = value_x ge e k'' a.
Proof.
  intros e0 args a k' lo hi Ha Hin Hiv.
  assert (Hag : forall n, a = Tmp n -> ok n /\ lookup n e0 = lookup n e)
    by (intros n E; subst a; exact (Ha _ Hin (iv_once _ _ _ _ Hiv _ eq_refl))).
  split; [intros n E; exact (proj1 (Hag _ E))|].
  intros k''. destruct a as [n | c | g]; simpl; [rewrite (proj2 (Hag _ eq_refl)) | |]; reflexivity.
Qed.

(** Takes apart every `match` in the statement of H, discarding the cases
    that make H contradictory. *)
Ltac opens H :=
  repeat match type of H with
         | context [match ?x with _ => _ end] => destruct x eqn:?; cbv beta iota zeta in H; try discriminate H
         end; try discriminate H.

(** Whenever the [[validator]] derives an integer bound for a value, the
    runtime value in environment e lies within that bound modulo its
    class width, provided any temporary involved is valid under ok. *)
Theorem iv_sound : forall v k lo hi, iv v k lo hi -> (forall n, v = Tmp n -> ok n) -> in_iv ge e k v lo hi.
Proof.
  intros v k lo hi H. induction H; intros Hv.
  - (* a constant *)
    assert (Hb : exists bits, class_bits k = Some bits)
      by (destruct k; try discriminate H; eexists; reflexivity).
    destruct Hb as [bits Hb]. destruct (signed_value_mod _ _ _ _ H Hb) as [Hm _].
    exists bits, (c mod 2 ^ bits), x. rewrite (const_read _ _ _ _ _ Hb). auto with zarith.
  - (* ext to a narrow type *)
    destruct (fits_bits _ _ _ H1) as (bits & Hb & Hm & Hp). destruct (Hok _ _ _ _ H eq_refl ltac:(congruence) (Hv _ eq_refl)) as (e0 & Hl & _).
    destruct Hl as (cls & xs & x & Hc & Hx & Ha & Hn). simpl in Hc. injection Hc as <-.
    destruct args as [|a [|a' args]]; simpl in Hx; opens Hx; injection Hx as <-; simpl in Ha; opens Ha.
    injection Hm as ->. injection Ha as <-.
    match type of Hn with lookup _ _ = Some (WInt (extension t ?y mod _)) =>
      apply (in_iv_tmp _ _ _ _ _ _ (extension t y) _ _ Hb Hn) end;
      [apply Z.mod_mod; lia | exact (narrow_extension _ _ _ _ H0)].
  - (* ext(sw) *)
    destruct (fits_bits _ _ _ H1) as (bits & Hb & Hm & Hp). destruct (Hok _ _ _ _ H eq_refl ltac:(congruence) (Hv _ eq_refl)) as (e0 & Hl & Ha').
    destruct (walked _ _ _ _ _ _ Ha' (or_introl eq_refl) H0) as [Hoka Hra].
    destruct (IHiv Hoka) as (b32 & ua & xa & Hb32 & Hua & Hxa & ->).
    simpl in Hb32. injection Hb32 as <-. pose proof (iv_fits _ _ _ _ H0) as Hf. simpl in Hf.
    apply andb_true_iff in Hf as [Hf1 Hf2]. apply Z.leb_le in Hf1. apply Z.leb_le in Hf2.
    destruct Hl as (cls & xs & x & Hc & Hx & Ha & Hn). simpl in Hc. injection Hc as <-.
    simpl in Hx. rewrite Hra, Hua in Hx. injection Hx as <-. simpl in Ha. rewrite Hm in Ha. injection Ha as <-.
    apply (in_iv_tmp _ _ _ _ _ _ xa _ _ Hb Hn); [|lia]. rewrite Z.mod_mod by lia. f_equal.
    apply sign_extension_mod. lia.
  - (* ext(uw) *)
    destruct (fits_bits _ _ _ H2) as (bits & Hb & Hm & Hp). destruct (Hok _ _ _ _ H eq_refl ltac:(congruence) (Hv _ eq_refl)) as (e0 & Hl & Ha').
    destruct (walked _ _ _ _ _ _ Ha' (or_introl eq_refl) H0) as [Hoka Hra].
    destruct (IHiv Hoka) as (b32 & ua & xa & Hb32 & Hua & Hxa & ->).
    simpl in Hb32. injection Hb32 as <-. pose proof (iv_fits _ _ _ _ H0) as Hf. simpl in Hf.
    apply andb_true_iff in Hf as [Hf1 Hf2]. apply Z.leb_le in Hf1. apply Z.leb_le in Hf2.
    destruct Hl as (cls & xs & x & Hc & Hx & Ha & Hn). simpl in Hc. injection Hc as <-.
    simpl in Hx. rewrite Hra, Hua in Hx. injection Hx as <-. simpl in Ha. rewrite Hm in Ha. injection Ha as <-.
    apply (in_iv_tmp _ _ _ _ _ _ xa _ _ Hb Hn); [|lia]. rewrite Z.mod_mod by lia. f_equal. simpl.
    rewrite Z.mod_mod by lia. apply Z.mod_small. lia.
  - (* a narrow load *)
    destruct (fits_bits _ _ _ H1) as (bits & Hb & Hm & Hp). destruct (Hok _ _ _ _ H eq_refl ltac:(congruence) (Hv _ eq_refl)) as (e0 & Hl & _).
    destruct Hl as (u & x & Hx & Hn). unfold extended in Hx. rewrite Hm in Hx. injection Hx as <-.
    apply (in_iv_tmp _ _ _ _ _ _ (extension t u) _ _ Hb Hn); [apply Z.mod_mod; lia | exact (narrow_extension _ _ _ _ H0)].
  - (* copy *)
    destruct (fits_bits _ _ _ H1) as (bits & Hb & Hm & Hp). destruct (Hok _ _ _ _ H eq_refl ltac:(congruence) (Hv _ eq_refl)) as (e0 & Hl & Ha').
    destruct (walked _ _ _ _ _ _ Ha' (or_introl eq_refl) H0) as [Hoka Hra].
    destruct (IHiv Hoka) as (b' & ua & xa & Hb' & Hua & Hxa & ->).
    rewrite Hb in Hb'. injection Hb' as <-.
    destruct Hl as (cls & xs & x & Hc & Hx & Ha & Hn). simpl in Hc. injection Hc as <-.
    simpl in Hx. rewrite Hra, Hua in Hx. injection Hx as <-. simpl in Ha. injection Ha as <-.
    apply (in_iv_tmp _ _ _ _ _ _ xa _ _ Hb Hn); [apply Z.mod_mod; lia | exact Hxa].
  - (* and with a mask *)
    destruct (fits_bits _ _ _ H3) as (bits & Hb & Hm & Hp). destruct (Hok _ _ _ _ H eq_refl ltac:(congruence) (Hv _ eq_refl)) as (e0 & Hl & _).
    destruct (signed_value_mod _ _ _ _ H1 Hb) as [Hcv Hr].
    assert (Hh : 2 ^ bits = 2 * 2 ^ (bits - 1)) by (destruct k; try discriminate Hb; injection Hb as <-; reflexivity).
    assert (Hcu : c mod 2 ^ bits = v) by (rewrite <- Hcv; apply Z.mod_small; lia).
    destruct Hl as (cls & xs & x & Hc & Hx & Ha & Hn). simpl in Hc. injection Hc as <-.
    destruct (map2_two _ _ _ _ _ _ _ _ _ Hx) as (xa & xb & Ea & Eb & ->).
    destruct xa as [ya| |]; destruct xb as [yb| |]; simpl in Ha; try discriminate Ha. injection Ha as <-.
    pose proof (value_int_range _ _ _ _ _ _ Hb Ea). pose proof (value_int_range _ _ _ _ _ _ Hb Eb).
    assert (Hy : ya = v \/ yb = v).
    { destruct H0 as [-> | ->]; [left | right].
      - rewrite (const_read _ _ _ _ _ Hb) in Ea. injection Ea as <-. exact Hcu.
      - rewrite (const_read _ _ _ _ _ Hb) in Eb. injection Eb as <-. exact Hcu. }
    assert (Hland : 0 <= Z.land ya yb <= v)
      by (destruct Hy as [-> | ->]; [rewrite Z.land_comm|]; apply land_le; lia).
    apply (in_iv_tmp _ _ _ _ _ _ (Z.land ya yb) _ _ Hb Hn); [reflexivity | lia].
  - (* urem by a constant *)
    destruct (fits_bits _ _ _ H3) as (bits' & Hb' & Hm & Hp). rewrite H0 in Hb'. injection Hb' as <-.
    destruct (Hok _ _ _ _ H eq_refl ltac:(congruence) (Hv _ eq_refl)) as (e0 & Hl & _).
    destruct Hl as (cls & xs & x & Hc & Hx & Ha & Hn). simpl in Hc. injection Hc as <-.
    destruct (map2_two _ _ _ _ _ _ _ _ _ Hx) as (xa & xb & Ea & Eb & ->).
    rewrite (const_read _ _ _ _ _ H0) in Eb. injection Eb as <-.
    destruct xa as [ya| |]; simpl in Ha; try discriminate Ha. injection Ha as <-.
    pose proof (value_int_range _ _ _ _ _ _ H0 Ea). pose proof (Z.mod_pos_bound ya (c mod 2 ^ bits) H1).
    unfold unsigned_division in Hn. rewrite (proj2 (Z.eqb_neq _ _)) in Hn by lia.
    apply (in_iv_tmp _ _ _ _ _ _ (ya mod (c mod 2 ^ bits)) _ _ H0 Hn); [reflexivity | lia].
  - (* shl by a constant *)
    destruct (fits_bits _ _ _ H4) as (bits' & Hb' & Hm & Hp). rewrite H0 in Hb'. injection Hb' as <-.
    destruct (Hok _ _ _ _ H eq_refl ltac:(congruence) (Hv _ eq_refl)) as (e0 & Hl & Ha').
    destruct (walked _ _ _ _ _ _ Ha' (or_introl eq_refl) H3) as [Hoka Hra].
    destruct (IHiv Hoka) as (b' & ua & xa & Hb' & Hua & Hxa & ->).
    rewrite H0 in Hb'. injection Hb' as <-.
    destruct Hl as (cls & xs & x & Hc & Hx & Ha & Hn). simpl in Hc. injection Hc as <-.
    assert (Hbits : bits = 32 \/ bits = 64) by (destruct k; try discriminate H0; injection H0 as <-; auto).
    simpl in Hx. rewrite Hra, Hua in Hx. simpl in Hx. injection Hx as <-.
    simpl in Ha. unfold shift_factor in Ha. rewrite H0 in Ha. simpl in Ha. rewrite Hm in Ha. injection Ha as <-.
    change (Z.pow_pos 2 32) with (2 ^ 32) in Hn.
    rewrite (Z.mod_small s (2 ^ 32)) in Hn by (destruct Hbits; subst; lia).
    rewrite (Z.mod_small s bits) in Hn by lia.
    apply (in_iv_tmp _ _ _ _ _ _ (xa * 2 ^ s) _ _ H0 Hn).
    + rewrite Z.mod_mod by lia. apply Z.mul_mod_idemp_l. lia.
    + assert (0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia). nia.
  - (* mul by a constant *)
    destruct (fits_bits _ _ _ H4) as (bits & Hb & Hm & Hp). destruct (Hok _ _ _ _ H eq_refl ltac:(congruence) (Hv _ eq_refl)) as (e0 & Hl & Ha').
    destruct (signed_value_mod _ _ _ _ H2 Hb) as [Hcv _].
    assert (Hin : In x args) by (destruct H0 as [-> | ->]; simpl; auto).
    destruct (walked _ _ _ _ _ _ Ha' Hin H1) as [Hoka Hra].
    destruct (IHiv Hoka) as (b' & ua & xa & Hb' & Hua & Hxa & ->). rewrite Hb in Hb'. injection Hb' as <-.
    destruct Hl as (cls & xs & y & Hc & Hy & Ha & Hn). simpl in Hc. injection Hc as <-.
    assert (Hprod : (lo0 <= hi0 -> lo <= xa * v <= hi))
      by (intros _; destruct (0 <=? v) eqn:Ez; [apply Z.leb_le in Ez | apply Z.leb_gt in Ez];
          injection H3 as <- <-; nia).
    destruct H0 as [-> | ->]; destruct (map2_two _ _ _ _ _ _ _ _ _ Hy) as (y1 & y2 & E1 & E2 & ->).
    + rewrite Hra, Hua in E1. injection E1 as <-. rewrite (const_read _ _ _ _ _ Hb) in E2. injection E2 as <-.
      simpl in Ha. rewrite Hm in Ha. injection Ha as <-.
      apply (in_iv_tmp _ _ _ _ _ _ (xa * v) _ _ Hb Hn); [|apply Hprod; lia].
      rewrite Z.mod_mod by lia. rewrite <- Hcv. rewrite <- Z.mul_mod by lia. reflexivity.
    + rewrite Hra, Hua in E2. injection E2 as <-. rewrite (const_read _ _ _ _ _ Hb) in E1. injection E1 as <-.
      simpl in Ha. rewrite Hm in Ha. injection Ha as <-.
      apply (in_iv_tmp _ _ _ _ _ _ (xa * v) _ _ Hb Hn); [|apply Hprod; lia].
      rewrite Z.mod_mod by lia. rewrite <- Hcv, (Z.mul_comm xa). rewrite <- Z.mul_mod by lia. reflexivity.
  - (* add *)
    destruct (fits_bits _ _ _ H2) as (bits & Hb & Hm & Hp). destruct (Hok _ _ _ _ H eq_refl ltac:(congruence) (Hv _ eq_refl)) as (e0 & Hl & Ha').
    destruct (walked _ _ _ _ _ _ Ha' (or_introl eq_refl) H0) as [Hoka Hra].
    destruct (walked _ _ _ _ _ _ Ha' (or_intror (or_introl eq_refl)) H1) as [Hokb Hrb].
    destruct (IHiv1 Hoka) as (b1 & ua & xa & Hb1 & Hua & Hxa & ->).
    destruct (IHiv2 Hokb) as (b2 & ub & xb & Hb2 & Hub & Hxb & ->).
    rewrite Hb in Hb1, Hb2. injection Hb1 as <-. injection Hb2 as <-.
    destruct Hl as (cls & xs & x & Hc & Hx & Ha & Hn).
    assert (Hcl : cls = [k; k]) by (destruct k; try discriminate Hb; simpl in Hc; injection Hc as <-; reflexivity).
    subst cls. simpl in Hx. rewrite Hra, Hrb, Hua, Hub in Hx. injection Hx as <-. simpl in Ha. rewrite Hm in Ha. injection Ha as <-.
    apply (in_iv_tmp _ _ _ _ _ _ (xa + xb) _ _ Hb Hn); [|lia].
    rewrite Z.mod_mod by lia. rewrite <- Z.add_mod by lia. reflexivity.
  - (* sub a constant *)
    destruct (fits_bits _ _ _ H2) as (bits & Hb & Hm & Hp). destruct (Hok _ _ _ _ H eq_refl ltac:(congruence) (Hv _ eq_refl)) as (e0 & Hl & Ha').
    destruct (signed_value_mod _ _ _ _ H0 Hb) as [Hcv _].
    destruct (walked _ _ _ _ _ _ Ha' (or_introl eq_refl) H1) as [Hoka Hra].
    destruct (IHiv Hoka) as (b' & ua & xa & Hb' & Hua & Hxa & ->).
    rewrite Hb in Hb'. injection Hb' as <-.
    destruct Hl as (cls & xs & x & Hc & Hx & Ha & Hn).
    assert (Hcl : cls = [k; k]) by (destruct k; try discriminate Hb; simpl in Hc; injection Hc as <-; reflexivity).
    subst cls. destruct (map2_two _ _ _ _ _ _ _ _ _ Hx) as (y1 & y2 & E1 & E2 & ->).
    rewrite Hra, Hua in E1. injection E1 as <-. rewrite (const_read _ _ _ _ _ Hb) in E2. injection E2 as <-.
    simpl in Ha. rewrite Hm in Ha. injection Ha as <-.
    apply (in_iv_tmp _ _ _ _ _ _ (xa - v) _ _ Hb Hn); [|lia].
    rewrite Z.mod_mod by lia. rewrite <- Hcv. rewrite <- Zminus_mod. reflexivity.
Qed.

End Sound.

End Intervals.
