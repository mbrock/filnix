(** The simplifier rewrites ground operation terms before the interpreter sees
    them. We read each operand at the class the operation expects and compare
    the resulting words. For a pointer, word equality includes its [[capability]]. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Maps Values Ops Semantics.
From Backend Require Import Pizlonate Escape.
From Opt Require Import OptIr Simplify OptAluProof.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Unset Lia Cache.

(** ## Operand evaluation

    An operation supplies a class for each operand. Evaluation fails when a
    term cannot be decoded or the interpreter cannot read its value. *)

(** The interpreter reads a decoded operand at its requested class. *)
Definition eval_val (ge : genv) (e : env) (kt v : term) : option word :=
  let* k := opt_class kt in
  let* a := opt_value v in
  Semantics.value_x ge e k a.

(** The operand list must have exactly as many entries as the class list. *)
Fixpoint eval_args (ge : genv) (e : env) (ks args : list term) : option (list word) :=
  match ks, args with
  | [], [] => Some []
  | k :: ks', a :: args' =>
      let* x := eval_val ge e k a in
      let* xs := eval_args ge e ks' args' in Some (x :: xs)
  | _, _ => None
  end.

(** Addition and subtraction use the interpreter's pointer arithmetic at the
    pointer class. The ALU handles the other decoded operations. *)
Definition run_op (o : Syntax.op) (k : class) (xs : list word) : option word :=
  match o with
  | Add | Sub => Ops.additive_res k o xs
  | _ => Ops.alu o k xs
  end.

(** Ground operations select their operand classes before reading the frame. *)
Definition eval_op (ge : genv) (e : env) (kt op : term) (args : list term)
    (filc : bool) : option word :=
  let* k := opt_class kt in
  let* o := opt_op op in
  let* ks := op_arg_classes op kt filc in
  let* xs := eval_args ge e ks args in run_op o k xs.

(** A replacement can name a value directly or compute one more operation. *)
Definition eval_simp_res (ge : genv) (e : env) (kt : term) (filc : bool)
    (r : simp_res) : option word :=
  match r with
  | SimpVal v => eval_val ge e kt v
  | SimpOp op args => eval_op ge e kt op args filc
  end.

(** ## Operation tables

    Swapping operands changes the order of a comparison. Complementing the
    condition instead reverses its truth value. *)

Ltac split_atoms H :=
  repeat match type of H with
  | context [if String.eqb ?a ?b then _ else _] =>
      let E := fresh in destruct (String.eqb a b) eqn:E;
      [apply String.eqb_eq in E; subst; cbv beta iota zeta in H |]
  end.

Ltac choose_atom H :=
  repeat rewrite orb_true_iff in H;
  repeat match type of H with
  | _ \/ _ => destruct H as [H | H]
  end; apply String.eqb_eq in H; subst.

(** Both arithmetic entry points agree after swapping commutative operands. *)
Theorem commutative_op_sound op k x y o :
  commutative_op op = true -> Syntax.int_class k = true -> opt_op op = Some o ->
  Ops.alu o k [WInt x; WInt y] = Ops.alu o k [WInt y; WInt x] /\
  (o = Add -> Ops.additive_res k o [WInt x; WInt y] =
              Ops.additive_res k o [WInt y; WInt x]).
Proof.
  intros H I D. destruct op as [|a| |]; try discriminate H.
  cbn [commutative_op] in H. choose_atom H;
    inversion D; subst; destruct k; try discriminate I; split;
    intros; try discriminate; cbn [Ops.alu Ops.additive_res];
    first [rewrite Z.add_comm | rewrite Z.mul_comm | rewrite Z.land_comm |
           rewrite Z.lor_comm | rewrite Z.lxor_comm]; reflexivity.
Qed.

(** Mirroring a condition preserves the bit returned for reversed operands. *)
Theorem mirrored_cond_sound c c1 ck k x y :
  mirrored_cond c = Some c1 -> opt_class ck = Some k -> Syntax.int_class k = true ->
  exists cn c1n, opt_cond c = Some cn /\ opt_cond c1 = Some c1n /\
    Ops.cond_bit c1n k y x = Ops.cond_bit cn k x y.
Proof.
  intros H D I. destruct c as [|a| |]; try discriminate H.
  cbn [mirrored_cond] in H.
  destruct (String.eqb a "eq" || String.eqb a "ne") eqn:E.
  - apply orb_true_iff in E as [E|E]; apply String.eqb_eq in E; subst;
      inversion H; subst; do 2 eexists; repeat split; cbn [Ops.cond_bit];
      rewrite Z.eqb_sym; reflexivity.
  - split_atoms H; try discriminate H; inversion H; subst;
      do 2 eexists; repeat split; destruct k; try discriminate I; reflexivity.
Qed.

(** Negating a condition changes either comparison bit into its complement. *)
Theorem negated_cond_sound c c1 ck k x y :
  negated_cond c = Some c1 -> opt_class ck = Some k -> Syntax.int_class k = true ->
  exists cn c1n, opt_cond c = Some cn /\ opt_cond c1 = Some c1n /\
    forall b, Ops.cond_bit cn k x y = Some b -> Ops.cond_bit c1n k x y = Some (1 - b).
Proof.
  intros H D I. destruct c as [|a| |]; try discriminate H.
  cbn [negated_cond] in H. split_atoms H; try discriminate H; inversion H; subst;
    do 2 eexists; repeat split; intros b B; destruct k; try discriminate I;
    cbn [Ops.cond_bit Ops.signed Syntax.modulus Syntax.half_modulus] in *;
    repeat match goal with
    | H : context [if ?test then _ else _] |- _ => destruct test eqn:? in H
    | |- context [if ?test then _ else _] => destruct test eqn:?
    end; simpl in B; inversion B; subst; try reflexivity;
    repeat match goal with
    | H : (_ <? _) = _ |- _ => first [apply Z.ltb_lt in H | apply Z.ltb_ge in H]
    | H : (_ <=? _) = _ |- _ => first [apply Z.leb_le in H | apply Z.leb_gt in H]
    end; lia.
Qed.

(** The highest set bit survives in the predecessor unless it was the only
    set bit of the original number. *)
Lemma single_bit_value v :
  0 < v -> Z.land v (v - 1) = 0 -> v = 2 ^ Z.log2 v.
Proof.
  intros V H. pose proof (Z.log2_spec v V) as R.
  destruct (Z.eq_dec v (2 ^ Z.log2 v)); auto.
  assert (L : Z.log2 (v - 1) = Z.log2 v).
  { apply Z.log2_unique; [apply Z.log2_nonneg | lia]. }
  pose proof (Z.pow_pos_nonneg 2 (Z.log2 v) ltac:(lia) (Z.log2_nonneg v)).
  pose proof (Z.bit_log2 (v - 1) ltac:(lia)) as B.
  rewrite L in B. apply (f_equal (fun z => Z.testbit z (Z.log2 v))) in H.
  cbn beta in H. rewrite Z.land_spec, Z.bit_log2, B, Z.testbit_0_l in H by lia.
  discriminate.
Qed.

(** Each right shift consumes one bit of the exponent and increments the count. *)
Lemma log2_steps_power fuel s acc :
  0 <= s <= Z.of_nat fuel -> log2_steps fuel (2 ^ s) acc = acc + s.
Proof.
  revert s acc. induction fuel as [|f IH]; intros s acc H;
    destruct (Z.eq_dec s 0) as [->|N]; try (change (acc = acc + 0); ring).
  - lia.
  - cbn [log2_steps]. assert (T : (2 ^ s <=? 1) = false).
    { apply Z.leb_gt. change (2 ^ 0 < 2 ^ s). apply Z.pow_lt_mono_r; lia. }
    rewrite T.
    replace s with (Z.succ (s - 1)) at 1 by lia.
    rewrite Z.pow_succ_r by lia. rewrite Z.shiftr_div_pow2 by lia.
    change (2 ^ 1) with 2. rewrite Z.mul_comm, Z.div_mul by lia.
    rewrite IH by lia. ring.
Qed.

(** The exponent returned for a modular constant identifies its only set bit
    and fits within the class width. *)
Theorem power_of_two_spec kt k bits m n s :
  opt_class kt = Some k -> Syntax.int_class k = true ->
  Syntax.class_bits k = Some bits -> Syntax.modulus k = Some m ->
  power_of_two kt n = Some s -> 0 <= s < bits /\ n mod m = 2 ^ s.
Proof.
  intros D I B M. unfold power_of_two. rewrite (class_modulus_agree _ _ D), M.
  set (v := n mod m). cbn beta iota.
  destruct ((0 <? v) && (Z.land v (v - 1) =? 0)) eqn:E; try discriminate.
  apply andb_true_iff in E as [V E]. apply Z.ltb_lt in V. apply Z.eqb_eq in E.
  pose proof (single_bit_value v V E) as P.
  assert (R : 0 <= Z.log2 v < bits /\ bits <= 64).
  { destruct k; try discriminate I; inversion B; inversion M; subst; split;
      try lia; split; try apply Z.log2_nonneg;
      apply Z.log2_lt_pow2; try lia; subst v; apply Z.mod_pos_bound; lia. }
  intro H. assert (C : log2_steps 64 v 0 = Z.log2 v).
  { rewrite P at 1. rewrite log2_steps_power by (change (0 <= Z.log2 v <= 64); lia). reflexivity. }
  rewrite C in H. inversion H. tauto.
Qed.

(** ## Narrow integer values

    An extension reads the low word of its operand even when it produces a
    long result. Signed narrow values must therefore survive the intervening
    reduction modulo the word size. *)

(** Every accepted pair of narrow types preserves the first extension after
    the interpreter reads its low word. *)
Theorem narrow_fits_sound t0 t :
  narrow_fits t0 t = true ->
  exists n0 n, opt_narrow t0 = Some n0 /\ opt_narrow t = Some n /\
    forall x k m, Syntax.int_class k = true -> Syntax.modulus k = Some m ->
      Ops.extension n (Ops.extension n0 x mod 2 ^ 32) mod m = Ops.extension n0 x mod m.
Proof.
  intros H. destruct t0 as [|a| |], t as [|b| |]; try discriminate H.
  cbn [narrow_fits] in H. split_atoms H; try discriminate H; choose_atom H;
    do 2 eexists; repeat split; intros x k m I M; f_equal;
    cbn [Ops.extension]; unfold Ops.sign_extension;
    change (2 ^ 32) with 4294967296 in *; change (2 ^ 31) with 2147483648 in *;
    repeat match goal with
    | |- context [x mod ?m0] =>
        let B := fresh "bits" in let V := fresh in
        pose proof (Z.mod_pos_bound x m0 ltac:(lia)) as V;
        remember (x mod m0) as B in *; clear Heqbits
    end;
    repeat match goal with
    | |- context [if ?a <=? ?b then _ else _] =>
        let E := fresh in destruct (a <=? b) eqn:E; [apply Z.leb_le in E | apply Z.leb_gt in E]
    end;
    repeat rewrite Z.mod_mod_divide in * by
      (match goal with |- (?d | ?n) => exists (n / d); reflexivity end);
    repeat rewrite Z.mod_small in * by lia;
    try match goal with
    | |- context [?z mod ?d] =>
        let V := fresh in assert (V : z mod d = z + d) by
          (symmetry; apply Z.mod_unique_pos with (q := -1); lia);
        rewrite V in *
    end; lia.
Qed.

(** Every narrow type represents both boolean values exactly. *)
Theorem boolean_ext_sound t n k m x :
  opt_narrow t = Some n -> Syntax.int_class k = true -> Syntax.modulus k = Some m ->
  (x = 0 \/ x = 1) -> Ops.extension n x mod m = x.
Proof.
  intros D I M [->| ->]; destruct k; try discriminate I;
    inversion M; subst; destruct n; reflexivity.
Qed.

(** ## Integer identities

    Constants enter the interpreter modulo their operand class. In particular,
    a shift reads a word-sized count even when it shifts a long integer. *)

Local Notation "'lit' n" := (TApp "const" [TInt n]) (at level 10).
Local Notation kw := (TAtom "w").
Local Notation kl := (TAtom "l").
Local Notation kp := (TAtom "p").

(** A successful literal test recovers the complete operand term. *)
Lemma literal_shape v n : const_int v = Some n -> v = lit n.
Proof.
  destruct v as [| |f [|[z| | |] [|b bs]]|]; cbn [const_int]; try discriminate.
  destruct (String.eqb f "const") eqn:F; try discriminate.
  apply String.eqb_eq in F. intros H. inversion H. subst. reflexivity.
Qed.

(** A successful temporary lookup recovers the complete operand term. *)
Lemma temp_shape v t : tmp_name v = [t] -> v = tmp t.
Proof.
  destruct v as [| |f [|a [|b bs]]|]; cbn [tmp_name]; try discriminate.
  destruct (String.eqb f "tmp") eqn:F; try discriminate.
  apply String.eqb_eq in F. intros H. inversion H. subst. reflexivity.
Qed.

(** Reading an integer at either width produces a reduced bit pattern. *)
Lemma integer_value_range ge e kt v x k m :
  opt_class kt = Some k -> Syntax.int_class k = true -> Syntax.modulus k = Some m ->
  eval_val ge e kt v = Some (WInt x) -> 0 <= x < m.
Proof.
  intros D I M. unfold eval_val. rewrite D.
  destruct (opt_value v) as [[t|n|g]|]; try discriminate;
    cbn [value_x]; destruct k; try discriminate I; inversion M; subst;
    repeat match goal with
    | |- context [lookup ?a ?l] => destruct (lookup a l) as [v0|]; try discriminate
    | v0 : word |- _ => destruct v0; try discriminate
    end; intro H; inversion H; subst; apply Z.mod_pos_bound; lia.
Qed.

(** Each entry in the boolean table reads as the same boolean bit at either
    integer width. *)
Definition bools_ok (ge : genv) (e : env) (bools : nmap (list (term * term))) :=
  forall b eqs, nm_find b bools = Some eqs ->
  exists z, (z = 0 \/ z = 1) /\ forall kt, is_int_class kt = true ->
    eval_val ge e kt (tmp b) = Some (WInt z).

(** The boolean test also accepts the two integer literals. *)
Lemma boolean_value ge e kt v bools x :
  bools_ok ge e bools -> is_int_class kt = true -> is_boolean bools v = true ->
  eval_val ge e kt v = Some (WInt x) -> x = 0 \/ x = 1.
Proof.
  intros B I. unfold is_boolean.
  destruct (const_int v) as [n|] eqn:C.
  - apply literal_shape in C. subst. rewrite orb_true_iff, !Z.eqb_eq.
    intros [->| ->]; apply is_int_class_iff in I as [->| ->];
      intro H; inversion H; auto.
  - destruct (tmp_name v) as [|t [|a rest]] eqn:T; try discriminate.
    apply temp_shape in T. subst. unfold nm_mem.
    destruct (nm_find t bools) as [eqs|] eqn:F; try discriminate.
    destruct (B t eqs F) as [z [Z V]]. rewrite (V kt I). congruence || intuition congruence.
Qed.

(** Reading a word-sized shift count and reducing it again preserves its
    residue for both shift widths. *)
Lemma word_shift_count n b :
  (b = 32 \/ b = 64) -> (n mod (2 ^ 32)) mod b = n mod b.
Proof.
  intros [->| ->]; apply Z.mod_mod_divide;
    [exists 134217728 | exists 67108864]; reflexivity.
Qed.

(** A mask with its low bits set keeps exactly the residue at that width. *)
Lemma low_mask x s : 0 <= s -> Z.land x (2 ^ s - 1) = x mod (2 ^ s).
Proof. intro H. change (Z.land x (Z.pred (2 ^ s)) = x mod (2 ^ s)). rewrite <- Z.ones_equiv. apply Z.land_ones. exact H. Qed.

Ltac decode_ops :=
  cbv [eval_simp_res eval_op op_arg_classes op_kind eval_args opt_op opt_class
       is_atom String.eqb Ascii.eqb Bool.eqb orb andb
       run_op Ops.alu Ops.additive_res Syntax.modulus Syntax.class_bits
       Syntax.half_modulus Ops.shift_factor Ops.signed_division Ops.signed
       Ops.unsigned_division] in *.

(** Integer literals are reduced at the width chosen by the operation. *)
Lemma eval_literal ge e kt k n m :
  opt_class kt = Some k -> Syntax.modulus k = Some m -> k <> P ->
  eval_val ge e kt (lit n) = Some (WInt (n mod m)).
Proof.
  intros D M N. unfold eval_val. rewrite D. cbn [opt_value value_x].
  change (match Syntax.modulus k with
          | Some d => match k with P => Some (WPtr (mkPtr (n mod d) CNone))
                               | _ => Some (WInt (n mod d)) end
          | None => None end = Some (WInt (n mod m))).
  rewrite M. destruct k; congruence.
Qed.

Ltac literals :=
  repeat first [
    rewrite (eval_literal _ _ kw W _ (2 ^ 32)) in * by (reflexivity || discriminate)
  | rewrite (eval_literal _ _ kl L _ (2 ^ 64)) in * by (reflexivity || discriminate) ].

Ltac bit_ranges :=
  repeat match goal with
  | H : eval_val ?g ?e kw ?v = Some (WInt ?x) |- _ =>
      lazymatch goal with
      | B : 0 <= x < 2 ^ 32 |- _ => fail
      | _ => pose proof (integer_value_range g e kw v x W (2 ^ 32) eq_refl eq_refl eq_refl H)
      end
  | H : eval_val ?g ?e kl ?v = Some (WInt ?x) |- _ =>
      lazymatch goal with
      | B : 0 <= x < 2 ^ 64 |- _ => fail
      | _ => pose proof (integer_value_range g e kl v x L (2 ^ 64) eq_refl eq_refl eq_refl H)
      end
  end.

Ltac read_words H :=
  repeat match type of H with
  | context [eval_val ?g ?e ?k ?v] =>
      let V := fresh "V" in destruct (eval_val g e k v) as [[?|?|? ?]|] eqn:V;
      cbv beta iota zeta in H |- *; try discriminate H
  end.

Ltac guards H :=
  repeat lazymatch type of H with
  | (if ?b then _ else _) = _ =>
      let E := fresh "guard" in destruct b eqn:E; [|clear E]; try discriminate H
  end.

Ltac guard_facts :=
  repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_true_iff in H; destruct H
  | H : (_ || _) = true |- _ => apply orb_true_iff in H; destruct H
  | H : String.eqb _ _ = true |- _ => apply String.eqb_eq in H; subst
  | H : term_eqb _ _ = true |- _ => apply term_eqb_eq in H; subst
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  end.

Ltac class_numbers :=
  cbv [is_zero_mod is_one_mod class_modulus OptIr.class_bits String.eqb
       Ascii.eqb Bool.eqb orb andb] in *;
  guard_facts.

Ltac use_power :=
  match goal with
  | H : power_of_two kw ?n = Some ?s |- _ =>
      destruct (power_of_two_spec kw W 32 (2 ^ 32) n s eq_refl eq_refl eq_refl eq_refl H)
  | H : power_of_two kl ?n = Some ?s |- _ =>
      destruct (power_of_two_spec kl L 64 (2 ^ 64) n s eq_refl eq_refl eq_refl eq_refl H)
  end.

Ltac identity_semantics R V :=
  injection R as <-; decode_ops; literals; read_words V; bit_ranges;
  try use_power; class_numbers;
  repeat rewrite word_shift_count in * by auto;
  repeat match goal with H : ?a mod ?m = _ |- _ => progress rewrite H in V end;
  cbv beta iota zeta in V |- *;
  try reflexivity; try assumption.

(** Each identity that fires preserves the original integer word, including
    shifts and masks introduced for a power-of-two divisor. *)
Theorem apply_identity_sound ge e kt op args bools res filc w :
  bools_ok ge e bools -> is_int_class kt = true ->
  apply_identity op kt args bools = Some res -> eval_op ge e kt op args filc = Some w ->
  eval_simp_res ge e kt filc res = Some w.
Proof.
  intros B I R V. destruct op as [|a| |]; try discriminate R.
  destruct args as [|x [|y [|z rest]]]; try discriminate R.
  cbn [apply_identity] in R. destruct (const_int y) as [n|] eqn:C.
  - apply literal_shape in C. subst y. guards R;
      try match type of R with
      | context [power_of_two kt n] => destruct (power_of_two kt n) eqn:P;
          try discriminate R; guards R
      end; guard_facts; apply is_int_class_iff in I as [->| ->];
      identity_semantics R V.
    all: change 4294967296 with (2 ^ 32) in *;
      change 18446744073709551616 with (2 ^ 64) in *;
      repeat match goal with H : ?a mod ?m = _ |- _ => progress rewrite H in V end;
      try subst n;
      try match goal with H : ?n mod ?m = 2 ^ ?s |- _ =>
        pose proof (Z.mod_pos_bound n m ltac:(lia));
        pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia));
        try rewrite (proj2 (Z.eqb_neq (2 ^ s) 0) ltac:(lia)) in V;
        try rewrite Z.shiftl_1_l by lia
      end;
      change (2 ^ 0) with 1 in *;
      try change (Ops.sign_extension (2 ^ 32) (2 ^ 31) 1) with 1 in V;
      try change (Ops.sign_extension (2 ^ 64) (2 ^ 63) 1) with 1 in V;
      cbn [Z.eqb] in V;
      rewrite ?Z.lor_0_r, ?Z.lxor_0_r, ?Z.land_0_r, ?Z.add_0_r, ?Z.sub_0_r,
        ?Z.mul_1_r, ?Z.mul_0_r, ?Z.div_1_r, ?Z.quot_1_r in V;
      unfold Ops.sign_extension in V;
      repeat rewrite Z.mod_small in V by lia;
      repeat match type of V with
      | context [if ?a <=? ?b then _ else _] => destruct (a <=? b) eqn:?
      end;
      try rewrite Zminus_mod_idemp_l in V;
      try match type of V with context [(?z - ?m) mod ?m] =>
        replace ((z - m) mod m) with z in V by
          (apply Z.mod_unique_pos with (q := -1); lia) end;
      repeat rewrite Z.mod_small in * by lia;
      try rewrite low_mask in * by lia;
      repeat rewrite Z.mod_small in * by lia;
      try exact V; try (inversion V; subst; reflexivity).
    all: repeat match goal with H : 0 <= ?a < ?m |- _ =>
      progress rewrite (Z.mod_small a m H) in * end; try exact V.
    all: match goal with H : is_boolean _ _ = true, E : eval_val _ _ ?k _ = _ |- _ =>
      destruct (boolean_value ge e k x bools n0 B eq_refl H E) as [->| ->]; exact V end.
  - destruct (tmp_name x) as [|tx [|u us]] eqn:X; try discriminate R.
    destruct (tmp_name y) as [|ty [|u us]] eqn:Y; try discriminate R.
    apply temp_shape in X. apply temp_shape in Y. subst x y.
    guards R; guard_facts; apply is_int_class_iff in I as [->| ->];
      injection R as <-; decode_ops; literals; read_words V;
      rewrite ?Z.sub_diag, ?Z.lxor_nilpotent, ?Z.land_diag, ?Z.lor_diag in V; exact V.
Qed.

(** ## Additive cancellation

    A recorded sum or difference explains the value of a temporary in its
    defining class. Pointer arithmetic takes its offset at long class and
    carries the [[capability]] of the left operand through every step. *)

(** The right operand of pointer arithmetic holds a long integer offset. *)
Definition offset_class k := if is_atom "p" k then kl else k.

(** A canonical address survives reduction modulo the pointer width. This
    includes global pointers because adding zero to a global at address
    [2 ^ 64] produces address zero, while reading the global returns [2 ^ 64]. *)
Definition addresses_ok ge e :=
  forall v p, eval_val ge e kp v = Some (WPtr p) -> 0 <= ptr_addr p < 2 ^ 64.

(** Each arithmetic entry names its defining operation and agrees with that
    operation whenever the interpreter reads the temporary. *)
Definition arith_ok ge e defs filc :=
  forall t k op a b, nm_find t (sd_arith defs) = Some (k, op, a, b) ->
    (k = kp \/ is_int_class k = true) /\ (op = TAtom "add" \/ op = TAtom "sub") /\
    eval_val ge e k (tmp t) = eval_op ge e k op [a; b] filc.

Ltac arithmetic_classes K :=
  destruct K as [->|K]; [|apply is_int_class_iff in K as [->| ->]].

Ltac cancel_tests R :=
  guards R; guard_facts; injection R as <-.

Ltac erase_inner_mods :=
  repeat first [rewrite Z.add_mod_idemp_l by lia | rewrite Z.add_mod_idemp_r by lia |
                rewrite Zminus_mod_idemp_l | rewrite Zminus_mod_idemp_r |
                rewrite Z.mod_mod by lia].

Ltac ring_residue :=
  erase_inner_mods;
  first [reflexivity | apply f_equal2; [ring | reflexivity] |
    match goal with
    | B : 0 <= ?x < ?m |- ?x = _ mod ?m =>
        rewrite <- (Z.mod_small x m B) at 1; apply f_equal2; [ring|reflexivity]
    end].

Ltac solve_word_equality :=
  first [reflexivity | apply f_equal; apply f_equal; ring_residue |
    apply f_equal; apply f_equal; f_equal; ring_residue].

Ltac expand_definitions V :=
  repeat match goal with
  | H : eval_val ?g ?e ?k ?a = _ |- _ => progress rewrite H in V
  end.

Ltac cancel_evaluate V :=
  cbv [offset_class is_atom String.eqb Ascii.eqb Bool.eqb] in *;
  decode_ops; expand_definitions V; literals; read_words V;
  injection V as <-; solve_word_equality.

(** Pair cancellation removes a common term from two recorded expressions.
    The definition of the offset is read at long class when the base is a pointer. *)
Theorem cancel_pair_sound ge e k aop a1 a2 op bop b1 b2 a b res filc w :
  (k = kp \/ is_int_class k = true) ->
  (aop = TAtom "add" \/ aop = TAtom "sub") ->
  (op = TAtom "add" \/ op = TAtom "sub") ->
  (bop = TAtom "add" \/ bop = TAtom "sub") ->
  eval_val ge e k a = eval_op ge e k aop [a1; a2] filc ->
  eval_val ge e (offset_class k) b = eval_op ge e (offset_class k) bop [b1; b2] filc ->
  cancel_pair k aop a1 a2 op bop b1 b2 = Some res ->
  eval_op ge e k op [a; b] filc = Some w -> eval_simp_res ge e k filc res = Some w.
Proof.
  intros K A O B Ea Eb R V. arithmetic_classes K; destruct A as [->| ->],
    O as [->| ->], B as [->| ->];
    unfold cancel_pair in R;
    cbv [is_atom is_int_class String.eqb Ascii.eqb Bool.eqb andb orb] in R;
    try discriminate R; cancel_tests R.
  all: cancel_evaluate V.
Qed.

(** A canonical base word can be returned directly when its net offset is zero. *)
Ltac base_range :=
  bit_ranges;
  try match goal with A : addresses_ok ?g ?e, H : eval_val ?g ?e kp ?v = Some (WPtr ?p) |- _ =>
    is_var p; pose proof (A _ _ H); destruct p as [addr cap0] end.

(** Right cancellation uses only integer identities. Pointer operations always
    retain their base on the left. *)
Theorem cancel_right_sound ge e k op a bop b1 b2 b res filc w :
  is_int_class k = true -> (op = TAtom "add" \/ op = TAtom "sub") ->
  (bop = TAtom "add" \/ bop = TAtom "sub") ->
  eval_val ge e k b = eval_op ge e k bop [b1; b2] filc ->
  cancel_right op a bop b1 b2 = Some res -> eval_op ge e k op [a; b] filc = Some w ->
  eval_simp_res ge e k filc res = Some w.
Proof.
  intros K O B Eb R V. apply is_int_class_iff in K as [->| ->];
    destruct O as [->| ->], B as [->| ->]; unfold cancel_right in R;
    cbv [is_atom String.eqb Ascii.eqb Bool.eqb andb] in R;
    try discriminate R; cancel_tests R; decode_ops; expand_definitions V;
    read_words V; base_range; injection V as <-; solve_word_equality.
Qed.

(** Choosing a short signed literal preserves the residue of the combined
    offset. Both signs use the same modulus as the enclosing operation. *)
Lemma combine_offsets m base u v :
  0 < m -> 0 <= base < m ->
  let d := (u + v) mod m in
  ((base + u) mod m + v) mod m =
    (if d =? 0 then base else
     if d <? Z.shiftr m 1 then (base + d) mod m else (base - (m - d)) mod m).
Proof.
  intros M B d. rewrite Z.add_mod_idemp_l by lia.
  replace (base + u + v) with (base + (u + v)) by ring.
  rewrite <- Z.add_mod_idemp_r by lia. fold d.
  destruct (d =? 0) eqn:E.
  - apply Z.eqb_eq in E. rewrite E, Z.add_0_r, Z.mod_small by lia. reflexivity.
  - destruct (d <? Z.shiftr m 1); [reflexivity|].
    replace (base - (m - d)) with (base + d + (-1) * m) by ring.
    rewrite Z.mod_add by lia. reflexivity.
Qed.

(** Each additive opcode gives its literal offset a sign before combination. *)
Definition signed_offset op n := if is_atom "add" op then n else -n.

(** Equal successful results carry equal values. *)
Lemma some_value {T : Type} (x y : T) : Some x = Some y -> x = y.
Proof. congruence. Qed.

(** Two adjacent literal offsets can be represented by their common residue
    or by the shorter subtraction chosen by the simplifier. *)
Lemma cancel_constants_sound ge e k aop op a base u v res filc w :
  addresses_ok ge e -> (k = kp \/ is_int_class k = true) ->
  (aop = TAtom "add" \/ aop = TAtom "sub") ->
  (op = TAtom "add" \/ op = TAtom "sub") ->
  eval_val ge e k a = eval_op ge e k aop [base; lit u] filc ->
  (let* m := arith_modulus k in
   let d := (signed_offset aop u + signed_offset op v) mod m in
   if d =? 0 then Some (SimpVal base) else
   if d <? Z.shiftr m 1 then Some (SimpOp (TAtom "add") [base; lit d])
   else Some (SimpOp (TAtom "sub") [base; lit (m - d)])) = Some res ->
  eval_op ge e k op [a; lit v] filc = Some w -> eval_simp_res ge e k filc res = Some w.
Proof.
  intros A K L O Ea R V. arithmetic_classes K; destruct L as [->| ->], O as [->| ->];
    cbv [arith_modulus class_modulus signed_offset is_atom String.eqb Ascii.eqb Bool.eqb orb] in R;
    change 4294967296 with (2 ^ 32) in R; change 18446744073709551616 with (2 ^ 64) in R;
    lazymatch type of R with
    | context [(?u1 + ?v1) mod ?m] =>
      let F := fresh "offset" in
      pose proof (combine_offsets m) as F;
      destruct (((u1 + v1) mod m) =? 0) eqn:Zr;
      [|destruct (((u1 + v1) mod m) <? Z.shiftr m 1) eqn:Sr];
      apply some_value in R; subst res; decode_ops; expand_definitions V; literals; read_words V; base_range;
      match goal with B : 0 <= ?b < ?m0 |- _ =>
        first [is_var b | lazymatch b with ptr_addr (mkPtr _ _) => idtac end];
        specialize (F b u1 v1 ltac:(lia) B)
      end;
      cbv zeta in F; rewrite Zr in F; try rewrite Sr in F;
      apply some_value in V; subst w; cbn [ptr_addr ptr_cap] in *;
      apply f_equal; apply f_equal; try match goal with |- mkPtr _ _ = mkPtr _ _ => f_equal end;
      lazymatch type of F with
      | _ = ?rhs => transitivity rhs; [ring_residue | rewrite <- F at 1;
          repeat match goal with
          | |- context [(?x + ?z mod ?m) mod ?m] =>
              is_var z; rewrite (Z.add_mod_idemp_r x z m) by lia
          | |- context [(?x - ?z mod ?m) mod ?m] =>
              is_var z; rewrite (Zminus_mod_idemp_r x z m)
          end; ring_residue]
      end
    end.
Qed.

(** Atom recognition fixes the whole ground term. *)
Lemma atom_shape s t : is_atom s t = true -> t = TAtom s.
Proof.
  destruct t as [|a| |]; try discriminate. cbn [is_atom].
  intros H. apply String.eqb_eq in H. congruence.
Qed.

(** Left cancellation can recover the base itself, merge literal offsets, or
    consult a second definition for the offset. *)
Theorem cancel_left_sound ge e k aop a1 a2 op b defs a res filc w :
  addresses_ok ge e -> arith_ok ge e defs filc -> (k = kp \/ is_int_class k = true) ->
  (aop = TAtom "add" \/ aop = TAtom "sub") -> (op = TAtom "add" \/ op = TAtom "sub") ->
  eval_val ge e k a = eval_op ge e k aop [a1; a2] filc ->
  cancel_left k aop a1 a2 op b defs = Some res ->
  eval_op ge e k op [a; b] filc = Some w -> eval_simp_res ge e k filc res = Some w.
Proof.
  intros A D K L O Ea R V. unfold cancel_left in R. guards R.
  all: try (lazymatch type of R with Some _ = _ => idtac end;
    guard_facts; apply some_value in R; subst res; arithmetic_classes K;
    destruct L as [->| ->], O as [->| ->]; try discriminate;
    decode_ops; expand_definitions V; read_words V; base_range; apply some_value in V; subst w;
    cbn [ptr_addr ptr_cap] in *; solve_word_equality).
  destruct (const_int a2) as [u|] eqn:U; destruct (const_int b) as [v|] eqn:C.
  1: { apply literal_shape in U. apply literal_shape in C. subst.
       exact (cancel_constants_sound ge e k aop op a a1 u v res filc w A K L O Ea R V). }
  all: destruct (tmp_name b) as [|bt [|z rest]] eqn:T; try discriminate R;
    apply temp_shape in T; subst b;
    destruct (nm_find bt (sd_arith defs)) as [[[[bk bop] b1] b2]|] eqn:F; try discriminate R;
    fold (offset_class k) in R;
    destruct (term_eqb bk (offset_class k)) eqn:E;
    try discriminate R;
    apply term_eqb_eq in E; subst bk; destruct (D _ _ _ _ _ F) as [_ [B Eb]];
    exact (cancel_pair_sound ge e k aop a1 a2 op bop b1 b2 a (tmp bt) res filc w K L O B Ea Eb R V).
Qed.

(** The arithmetic dispatcher consults a left definition first. It may use a
    right definition when the enclosing operation has integer class. *)
Theorem cancel_arith_sound ge e k op args defs filc res w :
  addresses_ok ge e -> arith_ok ge e defs filc ->
  cancel_arith k op args defs = Some res -> eval_op ge e k op args filc = Some w ->
  eval_simp_res ge e k filc res = Some w.
Proof.
  intros A D R V. unfold cancel_arith in R.
  destruct (is_atom "p" k || is_int_class k) eqn:K; try discriminate R.
  destruct (is_atom "add" op || is_atom "sub" op) eqn:O; try discriminate R.
  apply orb_true_iff in K. apply orb_true_iff in O.
  assert (K' : k = kp \/ is_int_class k = true) by (destruct K; auto using atom_shape).
  assert (O' : op = TAtom "add" \/ op = TAtom "sub") by (destruct O; auto using atom_shape).
  destruct args as [|a [|b [|z rest]]]; try discriminate R.
  cbv beta iota zeta in R.
  lazymatch type of R with context [match ?left_side with Some _ => Some _ | None => _ end] =>
    destruct left_side as [r|] eqn:Left end.
  - apply some_value in R. subst r.
    destruct (tmp_name a) as [|t [|i is_]] eqn:T; try discriminate Left.
    apply temp_shape in T. subst a.
    destruct (nm_find t (sd_arith defs)) as [[[[ak aop] a1] a2]|] eqn:F; try discriminate Left.
    destruct (term_eqb ak k) eqn:E; try discriminate Left.
    apply term_eqb_eq in E. subst ak. destruct (D _ _ _ _ _ F) as [_ [L Ea]].
    exact (cancel_left_sound ge e k aop a1 a2 op b defs (tmp t) res filc w A D K' L O' Ea Left V).
  - destruct (is_int_class k) eqn:I; try discriminate R.
    destruct (tmp_name b) as [|t [|i is_]] eqn:T; try discriminate R.
    apply temp_shape in T. subst b.
    destruct (nm_find t (sd_arith defs)) as [[[[bk bop] b1] b2]|] eqn:F; try discriminate R.
    destruct (term_eqb bk k) eqn:E; try discriminate R.
    apply term_eqb_eq in E. subst bk. destruct (D _ _ _ _ _ F) as [_ [L Eb]].
    exact (cancel_right_sound ge e k op a bop b1 b2 (tmp t) res filc w I O' L Eb R V).
Qed.

(** A cancelled pointer expression returns the original address and the exact
    [[capability]], including the identity and access rights of its object. *)
Corollary cancel_arith_preserves_ptr_cap ge e op args defs filc res p :
  addresses_ok ge e -> arith_ok ge e defs filc ->
  cancel_arith kp op args defs = Some res -> eval_op ge e kp op args filc = Some (WPtr p) ->
  exists q, eval_simp_res ge e kp filc res = Some (WPtr q) /\
    ptr_addr q = ptr_addr p /\ ptr_cap q = ptr_cap p.
Proof.
  intros A D R V. exists p. repeat split.
  exact (cancel_arith_sound ge e kp op args defs filc res (WPtr p) A D R V).
Qed.

(** ## Integer comparisons

    Comparisons read both arguments at the comparison class. The raw ALU
    returns their truth bit independently of the result class. *)

(** A comparison term carries its condition and its operand class. *)
Definition cmp (c ck : term) := TApp "cmp" [c; ck].

(** A binary comparison reads two integer words and returns the comparison bit. *)
Lemma eval_cmp_equation ge e kt c ck a b f :
  eval_op ge e kt (cmp c ck) [a; b] f =
  (let* k := opt_class kt in let* cn := opt_cond c in let* kn := opt_class ck in
   let* x := eval_val ge e ck a in let* y := eval_val ge e ck b in
   Ops.alu (Cmp cn kn) k [x; y]).
Proof.
  unfold cmp, eval_op. destruct (opt_class kt); [|reflexivity].
  cbn [opt_op]. destruct (opt_cond c); [|reflexivity]. destruct (opt_class ck); [|reflexivity].
  assert (Q : op_arg_classes (TApp "cmp" [c; ck]) kt f = Some [ck; ck]) by reflexivity.
  rewrite Q.
  cbn [eval_args]. destruct (eval_val ge e ck a), (eval_val ge e ck b); reflexivity.
Qed.

(** A successful comparison identifies both input words and its output bit. *)
Lemma eval_cmp_inv ge e kt c ck a b f w :
  eval_op ge e kt (cmp c ck) [a; b] f = Some w ->
  exists k cn kn x y z, opt_class kt = Some k /\ opt_cond c = Some cn /\
    opt_class ck = Some kn /\ eval_val ge e ck a = Some (WInt x) /\
    eval_val ge e ck b = Some (WInt y) /\ Ops.cond_bit cn kn x y = Some z /\ w = WInt z.
Proof.
  rewrite eval_cmp_equation. destruct (opt_class kt), (opt_cond c), (opt_class ck);
    try discriminate. destruct (eval_val ge e ck a) as [[x|p|cc sz]|];
    try discriminate; destruct (eval_val ge e ck b) as [[y|p'|cc' sz']|]; try discriminate;
    cbn [Ops.alu]; destruct (Ops.cond_bit c1 c2 x y) eqn:F; try discriminate;
    intros H; apply some_value in H; subst; do 6 eexists; repeat split; eauto.
Qed.

(** A successful read and a comparison bit suffice to evaluate a comparison. *)
Lemma eval_cmp_intro ge e kt c ck a b f k cn kn x y z :
  opt_class kt = Some k -> opt_cond c = Some cn -> opt_class ck = Some kn ->
  eval_val ge e ck a = Some (WInt x) -> eval_val ge e ck b = Some (WInt y) ->
  Ops.cond_bit cn kn x y = Some z -> eval_op ge e kt (cmp c ck) [a; b] f = Some (WInt z).
Proof.
  intros K C D X Y Z. rewrite eval_cmp_equation, K, C, D, X, Y. cbn [Ops.alu].
  rewrite Z. reflexivity.
Qed.

(** Translation by a common residue is injective on reduced operands. *)
Lemma translation_eqb m x y d :
  0 < m -> 0 <= x < m -> 0 <= y < m ->
  ((x + d) mod m =? (y + d) mod m) = (x =? y).
Proof.
  intros M X Y. destruct (x =? y) eqn:E.
  - apply Z.eqb_eq in E. subst. apply Z.eqb_refl.
  - apply Z.eqb_neq in E. apply Z.eqb_neq. intros H. apply E.
    apply (f_equal (fun z => (z - d) mod m)) in H. cbn beta in H.
    rewrite !Zminus_mod_idemp_l in H.
    replace (x + d - d) with x in H by ring. replace (y + d - d) with y in H by ring.
    rewrite (Z.mod_small _ _ X), (Z.mod_small _ _ Y) in H. exact H.
Qed.

(** Equality and inequality are unchanged when a common offset is cancelled
    on both sides of an integer comparison. *)
Theorem cancel_cmp_sound ge e kt c ck args defs filc args1 w :
  (c = TAtom "eq" \/ c = TAtom "ne") -> is_int_class ck = true -> arith_ok ge e defs filc ->
  cancel_cmp c ck args defs = Some args1 -> eval_op ge e kt (cmp c ck) args filc = Some w ->
  eval_op ge e kt (cmp c ck) args1 filc = Some w.
Proof.
  intros C I D R V. unfold cancel_cmp in R.
  assert (G : negb (is_atom "eq" c || is_atom "ne" c) = false)
    by (destruct C as [->| ->]; reflexivity).
  rewrite G in R. destruct args as [|a [|b [|z rest]]]; try discriminate R.
  destruct (tmp_name a) as [|at_ [|u us]] eqn:A; try discriminate R.
  destruct (tmp_name b) as [|bt [|u us]] eqn:B; try discriminate R.
  apply temp_shape in A. apply temp_shape in B. subst a b.
  destruct (nm_find at_ (sd_arith defs)) as [[[[ak aop] a1] a2]|] eqn:Fa; try discriminate R.
  destruct (nm_find bt (sd_arith defs)) as [[[[bk bop] b1] b2]|] eqn:Fb; try discriminate R.
  destruct (term_eqb ak ck && term_eqb bk ck && term_eqb aop bop) eqn:E; try discriminate R.
  guard_facts. destruct (D _ _ _ _ _ Fa) as [_ [O Ea]]. destruct (D _ _ _ _ _ Fb) as [_ [_ Eb]].
  destruct (opt_class kt) as [rk|] eqn:K; [|unfold eval_op in V; rewrite K in V; discriminate].
  destruct O as [->| ->]; cbv [is_atom String.eqb Ascii.eqb Bool.eqb andb] in R;
    guards R; try discriminate R; guard_facts; apply some_value in R; subst args1;
    destruct C as [->| ->]; apply is_int_class_iff in I as [->| ->];
    rewrite eval_cmp_equation, K in V |- *; clear K;
    cbn [opt_cond opt_int_cond opt_class] in V |- *;
    decode_ops; expand_definitions V; read_words V; bit_ranges;
    cbv [opt_cond opt_int_cond String.eqb Ascii.eqb Bool.eqb Ops.cond_bit] in V |- *;
    try match type of V with context [(?x - ?d) mod ?m =? (?y - ?d) mod ?m] =>
      replace (x - d) with (x + -d) in V by ring;
      replace (y - d) with (y + -d) in V by ring end;
    repeat match goal with
    | V : context [(?x + ?d) mod ?m =? (?y + ?d) mod ?m] |- _ =>
        rewrite (translation_eqb m x y d) in V by lia
    | V : context [(?d + ?x) mod ?m =? (?d + ?y) mod ?m] |- _ =>
        rewrite (Z.add_comm d x), (Z.add_comm d y) in V
    | V : context [(?d + ?x) mod ?m =? (?y + ?d) mod ?m] |- _ =>
        rewrite (Z.add_comm d x) in V
    | V : context [(?x + ?d) mod ?m =? (?d + ?y) mod ?m] |- _ =>
        rewrite (Z.add_comm d y) in V
    end; exact V.
Qed.

(** A class admits boolean literals when zero and one both decode as integer
    words. Pointer literals instead produce pointer words. *)
Definition bit_class kt :=
  exists k m, opt_class kt = Some k /\ Syntax.modulus k = Some m /\ k <> P /\ 1 < m.

(** Either integer class represents both boolean literals. *)
Lemma int_bit_class kt : is_int_class kt = true -> bit_class kt.
Proof.
  intro I. apply is_int_class_iff in I as [->| ->]; unfold bit_class;
    [exists W, (2 ^ 32) | exists L, (2 ^ 64)]; repeat split; try discriminate; lia.
Qed.

(** Reading a boolean literal at an admissible class preserves its bit. *)
Lemma eval_bit ge e kt z : bit_class kt -> (z = 0 \/ z = 1) ->
  eval_val ge e kt (lit z) = Some (WInt z).
Proof.
  intros [k [m [D [M [N B]]]]] Z. rewrite (eval_literal _ _ _ _ _ _ D M N).
  rewrite Z.mod_small by lia. reflexivity.
Qed.

(** The class table records the class at which the frame holds each temporary. *)
Definition classes_ok ge e (classes : nmap term) :=
  forall t kt, nm_find t classes = Some kt ->
    exists w, lookup t e = Some w /\ eval_val ge e kt (tmp t) = Some w.

(** The frame stores the same bit for a recorded boolean and every temporary
    in its equivalence list. Each of these names has a declared integer class. *)
Definition equivs_ok ge e (classes : nmap term) (bools : nmap (list (term * term))) :=
  forall b eqs z, nm_find b bools = Some eqs -> eval_val ge e kw (tmp b) = Some (WInt z) ->
    forall t, (t = b \/ exists tag, In (tag, t) eqs) ->
      exists kt, nm_find t classes = Some kt /\ is_int_class kt = true /\
        lookup t e = Some (WInt z).

(** A comparison fact explains the recorded temporary. A narrow fact describes
    its extended value at the declared width and the low word read by another extension. *)
Definition defs_ok ge e (classes : nmap term) defs filc :=
  forall t fact kt, nm_find t (sd_main defs) = Some fact -> nm_find t classes = Some kt ->
  match fact with
  | DefCmp c ck a b => is_int_class ck = true /\
      eval_val ge e kt (tmp t) = eval_op ge e kt (cmp c ck) [a; b] filc
  | DefNarrow ty => exists n k m x, opt_narrow ty = Some n /\ opt_class kt = Some k /\
      Syntax.int_class k = true /\ Syntax.modulus k = Some m /\
      eval_val ge e kt (tmp t) = Some (WInt (Ops.extension n x mod m)) /\
      eval_val ge e kw (tmp t) = Some (WInt (Ops.extension n x mod 2 ^ 32))
  | DefNot _ => True
  end.

(** The representative search returns a list member whose declared class
    matches the requested result class. *)
Lemma same_class_member classes k ps t :
  same_class_temp classes k ps = Some t ->
  (exists tag, In (tag, t) ps) /\ nm_find t classes = Some k.
Proof.
  induction ps as [|[tag a] rest IH]; cbn [same_class_temp]; try discriminate.
  destruct (nm_find a classes) as [ka|] eqn:F.
  - destruct (term_eqb ka k) eqn:E.
    + intros H. apply some_value in H. apply term_eqb_eq in E. subst.
      split; [exists tag; left; reflexivity | exact F].
    + intros H. destruct (IH H) as [[u U] Q]. split; [exists u; right; exact U | exact Q].
  - intros H. destruct (IH H) as [[u U] Q]. split; [exists u; right; exact U | exact Q].
Qed.

(** Comparing a temporary to itself returns one for equality and non-strict
    order. Every other successful integer condition returns zero. *)
Lemma self_comparison c cn k x z :
  opt_cond c = Some cn -> Syntax.int_class k = true -> Ops.cond_bit cn k x x = Some z ->
  z = (if is_atom "eq" c || is_atom "ule" c || is_atom "uge" c ||
          is_atom "sle" c || is_atom "sge" c then 1 else 0).
Proof.
  intros D I V. destruct c as [|s| |]; try discriminate D.
  unfold opt_cond in D. destruct (opt_int_cond (TAtom s)) eqn:N.
  - apply some_value in D. subst cn. unfold opt_int_cond in N. split_atoms N;
      try discriminate N; apply some_value in N; subst;
      cbn [Ops.cond_bit] in V; try destruct (Ops.signed k x); try discriminate V;
      rewrite ?Z.eqb_refl, ?Z.ltb_irrefl, ?Z.leb_refl in V; inversion V; reflexivity.
  - split_atoms D; try discriminate D; apply some_value in D; subst; discriminate.
Qed.

(** The search for a negated comparison returns a fact attached to one of
    the candidate temporaries. *)
Lemma find_negation_member defs ps res :
  (let fix find_cmp (qs : list (term * term)) :=
     match qs with
     | [] => None
     | (_, t) :: rest =>
         match nm_find t (sd_main defs) with
         | Some (DefCmp c ck a b) =>
             let* c1 := negated_cond c in Some (SimpOp (cmp c1 ck) [a; b])
         | _ => find_cmp rest
         end
     end in find_cmp ps) = Some res ->
  exists tag t c c1 ck a b, In (tag, t) ps /\ nm_find t (sd_main defs) = Some (DefCmp c ck a b) /\
    negated_cond c = Some c1 /\ res = SimpOp (cmp c1 ck) [a; b].
Proof.
  induction ps as [|[tag t] rest IH]; cbn; try discriminate.
  destruct (nm_find t (sd_main defs)) as [[c ck a b|u|ty]|] eqn:D.
  - destruct (negated_cond c) as [c1|] eqn:N; try discriminate.
    intro H. apply some_value in H. subst. do 7 eexists. split; [left; reflexivity|]. eauto.
  - intros H. destruct (IH H) as (q & u' & c & c1 & ck & a & b & H1 & H2).
    do 7 eexists. split; [right; exact H1 | exact H2].
  - intros H. destruct (IH H) as (q & u' & c & c1 & ck & a & b & H1 & H2).
    do 7 eexists. split; [right; exact H1 | exact H2].
  - intros H. destruct (IH H) as (q & u' & c & c1 & ck & a & b & H1 & H2).
    do 7 eexists. split; [right; exact H1 | exact H2].
Qed.

(** The zero and one guards identify the residue read by the comparison. *)
Lemma residue_guards ck k m n :
  opt_class ck = Some k -> Syntax.modulus k = Some m ->
  (is_zero_mod ck n = true -> n mod m = 0) /\
  (is_one_mod ck n = true -> n mod m = 1).
Proof.
  intros K M. unfold is_zero_mod, is_one_mod. rewrite (class_modulus_agree _ _ K), M.
  split; apply Z.eqb_eq.
Qed.

(** Testing a boolean against zero or one either copies the bit or complements
    it, according to the condition and the reduced literal. *)
Lemma boolean_truth_bit c ck k cn m n x z :
  opt_class ck = Some k -> Syntax.modulus k = Some m -> opt_cond c = Some cn ->
  (x = 0 \/ x = 1) -> Ops.cond_bit cn k x (n mod m) = Some z ->
  (((is_atom "ne" c && is_zero_mod ck n) || (is_atom "eq" c && is_one_mod ck n)) = true ->
     z = x) /\
  (((is_atom "eq" c && is_zero_mod ck n) || (is_atom "ne" c && is_one_mod ck n)) = true ->
     z = 1 - x).
Proof.
  intros K M C B V. destruct (residue_guards _ _ _ n K M) as [Zero One].
  split; intro H; apply orb_true_iff in H as [H|H]; apply andb_true_iff in H as [H N];
    apply atom_shape in H; subst c; apply some_value in C; subst cn;
    first [rewrite (Zero N) in V | rewrite (One N) in V];
    destruct B as [->| ->]; inversion V; reflexivity.
Qed.

(** Negating a stored comparison computes the complement of its temporary
    even when the new result uses another class. *)
Lemma negate_recorded_cmp ge e classes defs filc kt rk t tk c c1 ck a b z :
  defs_ok ge e classes defs filc -> opt_class kt = Some rk ->
  nm_find t classes = Some tk -> nm_find t (sd_main defs) = Some (DefCmp c ck a b) ->
  eval_val ge e tk (tmp t) = Some (WInt z) -> negated_cond c = Some c1 ->
  eval_op ge e kt (cmp c1 ck) [a; b] filc = Some (WInt (1 - z)).
Proof.
  intros D K T F B N. destruct (D _ _ _ F T) as [I E]. rewrite E in B.
  destruct (eval_cmp_inv _ _ _ _ _ _ _ _ _ B) as (k0 & cn & kn & x & y & z0 & Q & C & A & X & Y & V & Z).
  injection Z as <-.
  destruct (opt_class_int _ I) as [kn' [A' J]]. rewrite A in A'. apply some_value in A'. subst kn'.
  destruct (negated_cond_sound _ _ _ _ x y N A J) as [cn0 [cn1 [H [H1 H2]]]].
  rewrite C in H. apply some_value in H. subst cn0.
  eapply eval_cmp_intro; eauto.
Qed.

(** A declared operand reads the word that the frame stores under its name. *)
Lemma declared_word ge e classes t kt w :
  classes_ok ge e classes -> nm_find t classes = Some kt -> lookup t e = Some w ->
  eval_val ge e kt (tmp t) = Some w.
Proof.
  intros Cl F L. destruct (Cl _ _ F) as [v [V Read]]. rewrite L in V.
  apply some_value in V. subst v. exact Read.
Qed.

(** Every member of a boolean's candidate list has the same bit at its declared class. *)
Lemma boolean_candidates ge e classes bools kt b eqs x :
  classes_ok ge e classes -> equivs_ok ge e classes bools -> nm_find b bools = Some eqs ->
  eval_val ge e kw (tmp b) = Some (WInt x) ->
  forall tag t, In (tag, t) ((kt, b) :: eqs) ->
    exists tk, nm_find t classes = Some tk /\ is_int_class tk = true /\
      eval_val ge e tk (tmp t) = Some (WInt x).
Proof.
  intros Cl E F B tag t H.
  assert (Member : t = b \/ exists u, In (u, t) eqs).
  { destruct H as [H|H]; [left; congruence | right; exists tag; exact H]. }
  destruct (E _ _ _ F B _ Member) as [tk [T [I L]]]. exists tk.
  repeat split; auto. exact (declared_word _ _ _ _ _ _ Cl T L).
Qed.

(** When a rewrite replaces an integer bit by its own literal, the result
    class must read that literal as an integer. This condition also admits
    unchecked comparisons that produce another operation or a temporary. *)
Definition bit_result kt res w :=
  forall z, res = SimpVal (lit z) -> w = WInt z -> (z = 0 \/ z = 1) -> bit_class kt.

(** Boolean comparison rewrites preserve their bit whenever the result class
    can represent a literal bit. The raw ALU also accepts a pointer result
    class, where replacing an integer bit with a literal would change its word constructor. *)
Theorem boolean_cmp_sound ge e kt c ck args classes bools defs filc res w :
  is_int_class ck = true -> bit_result kt res w -> classes_ok ge e classes ->
  bools_ok ge e bools -> equivs_ok ge e classes bools -> defs_ok ge e classes defs filc ->
  boolean_cmp c ck kt args classes bools defs = Some res ->
  eval_op ge e kt (cmp c ck) args filc = Some w -> eval_simp_res ge e kt filc res = Some w.
Proof.
  intros I Bit Cl B E D R V. destruct args as [|a [|b [|u us]]]; try discriminate R.
  destruct (eval_cmp_inv _ _ _ _ _ _ _ _ _ V) as (rk & cn & kn & x & y & z & K & C & J & X & Y & Z & ->).
  destruct (opt_class_int _ I) as [kn' [J' Int]]. rewrite J in J'. apply some_value in J'. subst kn'.
  destruct (int_class_bits_modulus _ Int) as (width & m & _ & M & _).
  unfold boolean_cmp in R.
  destruct (tmp_name a) as [|ta [|u us]] eqn:Ta;
    try (destruct (tmp_name b) as [|tb [|v vs]] eqn:Tb).
  all: try (lazymatch type of R with context [term_eqb ?ta ?tb] =>
    destruct (term_eqb ta tb) eqn:Et; try discriminate R;
    apply term_eqb_eq in Et; subst tb; apply temp_shape in Ta; apply temp_shape in Tb;
    subst a b; rewrite X in Y; injection Y as <-;
    pose proof (self_comparison _ _ _ _ _ C Int Z) as S; subst z;
    apply some_value in R; subst res; cbn [eval_simp_res]; destruct (_ || _); apply eval_bit; unfold bit_result in Bit; eauto end).
  all: destruct (const_int b) as [n|] eqn:N; try discriminate R;
    apply literal_shape in N; subst b;
    rewrite (eval_literal _ _ _ _ _ _ J M ltac:(destruct kn; discriminate || congruence)) in Y;
    injection Y as <-; destruct (residue_guards _ _ _ n J M) as [Zero One];
    guards R.
  all: try (lazymatch type of R with Some _ = _ => idtac end;
    guard_facts; match goal with H : is_atom _ ?cd = true, G : is_zero_mod _ _ = true |- _ =>
      apply atom_shape in H; subst c; rewrite (Zero G) in Z end;
    apply some_value in C; subst cn; apply some_value in R; subst res;
    cbn [Ops.cond_bit] in Z;
    pose proof (integer_value_range _ _ _ _ _ _ _ J Int M X);
    first [rewrite (proj2 (Z.ltb_ge x 0) ltac:(lia)) in Z |
           rewrite (proj2 (Z.leb_le 0 x) ltac:(lia)) in Z];
    apply some_value in Z; subst z; cbn [eval_simp_res]; apply eval_bit; unfold bit_result in Bit; eauto).
  all: try discriminate R;
    destruct (nm_find ta bools) as [eqs|] eqn:F; try discriminate R;
    apply temp_shape in Ta; subst a;
    destruct (B _ _ F) as [z0 [Bool Reads]]; rewrite (Reads ck I) in X; injection X as <-;
    pose proof (boolean_candidates ge e classes bools kt ta eqs z0 Cl E F (Reads kw eq_refl)) as Members;
    destruct (boolean_truth_bit _ _ _ _ _ _ _ _ J M C Bool Z) as [Copy Neg];
    destruct (_ || _) eqn:G in R.
  all: try (destruct (same_class_temp classes kt ((kt, ta) :: eqs)) as [t|] eqn:S;
    try discriminate R; apply some_value in R; subst res;
    destruct (same_class_member _ _ _ _ S) as [[tag H] T];
    destruct (Members _ _ H) as [tk [T' [_ Val]]]; rewrite T in T'; injection T' as <-;
    rewrite (Copy G); exact Val).
  all: destruct (_ || _) eqn:G' in R; try discriminate R;
    apply (find_negation_member defs ((kt, ta) :: eqs) res) in R as (tag & t & c0 & c1 & ck0 & a0 & b0 & H & Fact & N & ->);
    destruct (Members _ _ H) as [tk [T [_ Val]]]; rewrite (Neg G');
    eapply negate_recorded_cmp; eassumption.
Qed.

(** ## Single steps and recursive simplification

    The fuel limits recursive rewrites after a swap or a cancellation. Each
    step passes the same word to the next step, so exhausting fuel preserves
    the last operation exactly. *)

(** The environment relates the simplifier's tables to the current frame.
    Canonical pointer addresses include both temporary and global operands. *)
Record simp_env_ok ge e classes bools defs filc : Prop := {
  simp_addresses : addresses_ok ge e;
  simp_classes : classes_ok ge e classes;
  simp_bools : bools_ok ge e bools;
  simp_equivs : equivs_ok ge e classes bools;
  simp_defs_valid : defs_ok ge e classes defs filc;
  simp_arith : arith_ok ge e defs filc
}.

(** A copy returns the word read at its result class. *)
Lemma copy_value ge e kt v f : eval_op ge e kt (TAtom "copy") [v] f = eval_val ge e kt v.
Proof.
  unfold eval_op. destruct (opt_class kt) eqn:K.
  - change (op_arg_classes (TAtom "copy") kt f) with (Some [kt]).
    cbn [eval_args]. destruct (eval_val ge e kt v); reflexivity.
  - unfold eval_val. rewrite K. reflexivity.
Qed.

(** Adding or subtracting a multiple of the address modulus returns the same
    canonical pointer, including its original capability. *)
Lemma pointer_zero_sound ge e op args f w :
  addresses_ok ge e -> (op = TAtom "add" \/ op = TAtom "sub") ->
  (match args with [_; y] =>
     match const_int y with Some n => is_zero_mod kl n | None => false end
   | _ => false end) = true ->
  eval_op ge e kp op args f = Some w ->
  eval_simp_res ge e kp f
    (match args with [x; _] => SimpVal x | _ => SimpOp op args end) = Some w.
Proof.
  intros A O R V. destruct args as [|x [|y [|u us]]]; try discriminate R.
  destruct (const_int y) as [n|] eqn:N; try discriminate R. apply literal_shape in N. subst y.
  apply (proj1 (residue_guards kl L (2 ^ 64) n eq_refl eq_refl)) in R.
  destruct O as [->| ->]; decode_ops; literals; rewrite R in V; read_words V;
    base_range; cbn [ptr_addr ptr_cap] in *; rewrite ?Z.add_0_r, ?Z.sub_0_r, Z.mod_small in V by lia;
    exact V.
Qed.

(** A foldable operation with an integer result reads all of its literal
    operands at integer classes. *)
Lemma fold_arg_classes op kt f ks :
  is_int_class kt = true -> foldable_op op = true -> op_arg_classes op kt f = Some ks ->
  Forall (fun ak => is_int_class ak = true) ks.
Proof.
  intros I F A. unfold foldable_op in F. unfold op_arg_classes in A.
  destruct (op_kind op) as [kind|]; try discriminate A. destruct kind; try discriminate F;
    try (apply some_value in A; subst; repeat constructor; assumption).
  - apply is_int_class_iff in I as [->| ->]; inversion A; repeat constructor.
  - destruct op as [| |tag [|c [|ck [|q qs]]]|]; try discriminate F.
    inversion A; subst. repeat constructor; exact F.
Qed.

(** The numeric folding pass and the interpreter read the same reduced
    integer words from a list of literals. *)
Lemma eval_arg_numbers ge e ks args xs :
  Forall (fun ak => is_int_class ak = true) ks -> arg_numbers ks args = Some xs ->
  eval_args ge e ks args = Some (map WInt xs).
Proof.
  revert args xs. induction ks as [|k ks IH]; intros [|a rest] xs F N;
    cbn [arg_numbers] in N; try discriminate N.
  - apply some_value in N. subst. reflexivity.
  - inversion F as [|h t I T]; subst. destruct (const_int a) as [n|] eqn:A; try discriminate N.
    destruct (class_modulus k) as [m|] eqn:M; try discriminate N.
    destruct (arg_numbers ks rest) as [ys|] eqn:Y; try discriminate N.
    apply some_value in N. subst xs. apply literal_shape in A. subst a.
    destruct (opt_class_int _ I) as [kn [K J]]. rewrite (class_modulus_agree _ _ K) in M.
    cbn [eval_args]. rewrite (eval_literal _ _ _ _ _ _ K M ltac:(destruct kn; discriminate)),
      (IH _ _ T Y). reflexivity.
Qed.

(** At integer class the additive evaluator delegates to the ALU. *)
Lemma run_integer o k ws : Syntax.int_class k = true -> run_op o k ws = Ops.alu o k ws.
Proof. destruct k; try discriminate; destruct o; reflexivity. Qed.

(** Constant folding reads the same arguments as the interpreter and returns
    a literal that already lies within the result width. *)
Lemma folded_sound ge e kt op args f ks xs n w :
  is_int_class kt = true -> foldable_op op = true -> op_arg_classes op kt f = Some ks ->
  arg_numbers ks args = Some xs -> eval_alu op kt xs = Some n ->
  eval_op ge e kt op args f = Some w -> eval_val ge e kt (lit n) = Some w.
Proof.
  intros I F A N R V. destruct (opt_class_int _ I) as [k [K J]].
  destruct (int_class_bits_modulus _ J) as (b & m & _ & M & _).
  destruct (eval_alu_sound _ _ f _ _ _ _ K J M (arg_numbers_in_range _ _ _ _ _ _ A N) R)
    as [o [O [Value Range]]].
  unfold eval_op in V. rewrite K, O, A, (eval_arg_numbers ge e ks args xs (fold_arg_classes _ _ _ _ I F A) N),
    (run_integer _ _ _ J), Value in V.
  rewrite (eval_literal _ _ _ _ _ _ K M ltac:(destruct k; discriminate)), Z.mod_small by exact Range. exact V.
Qed.

(** Swapping a commutative integer operation preserves evaluation of the two operands. *)
Lemma commute_values ge e kt op a b f w :
  is_int_class kt = true -> commutative_op op = true ->
  eval_op ge e kt op [a; b] f = Some w -> eval_op ge e kt op [b; a] f = Some w.
Proof.
  intros I C V. destruct op as [|s| |]; try discriminate C.
  cbn [commutative_op] in C. choose_atom C; apply is_int_class_iff in I as [->| ->];
    decode_ops; read_words V;
    first [rewrite Z.add_comm | rewrite Z.mul_comm | rewrite Z.land_comm |
           rewrite Z.lor_comm | rewrite Z.lxor_comm]; exact V.
Qed.

(** Mirroring a comparison exchanges the input words and retains the original bit. *)
Lemma mirror_values ge e kt c ck a b c1 f w :
  is_int_class ck = true -> mirrored_cond c = Some c1 ->
  eval_op ge e kt (cmp c ck) [a; b] f = Some w -> eval_op ge e kt (cmp c1 ck) [b; a] f = Some w.
Proof.
  intros I H V. destruct (eval_cmp_inv _ _ _ _ _ _ _ _ _ V) as (k & cn & kn & x & y & z & K & C & D & X & Y & Z & ->).
  destruct (opt_class_int _ I) as [kn' [D' J]]. rewrite D in D'; injection D' as <-.
  destruct (mirrored_cond_sound _ _ _ _ x y H D J) as [c0 [c1n [C0 [C1 B]]]].
  rewrite C in C0. injection C0 as <-. eapply eval_cmp_intro; eauto. rewrite B. exact Z.
Qed.

(** A successful narrow extension reads the low word of its operand. *)
Lemma extension_read ge e kt ty v f w :
  eval_op ge e kt (TApp "ext" [ty]) [v] f = Some w ->
  exists n k m x, opt_narrow ty = Some n /\ opt_class kt = Some k /\ Syntax.modulus k = Some m /\
    eval_val ge e kw v = Some (WInt x) /\ w = WInt (Ops.extension n x mod m).
Proof.
  unfold eval_op. destruct (opt_class kt) as [k|] eqn:K; try discriminate.
  destruct ty as [|s| |]; try discriminate.
  destruct (String.eqb s "s") eqn:S; [apply String.eqb_eq in S; subst; discriminate|].
  destruct (String.eqb s "d") eqn:D; [apply String.eqb_eq in D; subst; discriminate|].
  change (opt_op (TApp "ext" [TAtom s])) with
    (if String.eqb s "s" then Some (ExtF Single) else if String.eqb s "d" then Some (ExtF Double)
     else let* n := opt_narrow (TAtom s) in Some (Ext n)).
  rewrite S, D. destruct (opt_narrow (TAtom s)) as [n|] eqn:N; try discriminate.
  assert (A : op_arg_classes (TApp "ext" [TAtom s]) kt f = Some [kw]).
  { unfold opt_narrow in N. split_atoms N; try discriminate; reflexivity. }
  rewrite A. cbn [eval_args]. destruct (eval_val ge e kw v) as [[x|p|cc sz]|]; try discriminate.
  cbn [run_op Ops.alu]. destruct (Syntax.modulus k) as [m|] eqn:M; try discriminate.
  intros V. apply some_value in V. subst w. exists n, k, m, x. repeat split; eauto.
Qed.

(** A second extension of a boolean can reuse the equivalent temporary at
    the requested width. Both operands read the same zero or one. *)
Lemma extend_boolean ge e kt ty b eqs t classes bools filc w :
  classes_ok ge e classes -> bools_ok ge e bools -> equivs_ok ge e classes bools -> nm_find b bools = Some eqs ->
  same_class_temp classes kt eqs = Some t ->
  eval_op ge e kt (TApp "ext" [ty]) [tmp b] filc = Some w ->
  eval_val ge e kt (tmp t) = Some w.
Proof.
  intros Cl B E F S V. destruct (extension_read _ _ _ _ _ _ _ V) as (n & k & m & x & N & K & M & X & ->).
  destruct (B _ _ F) as [z [Bool Reads]]. rewrite (Reads kw eq_refl) in X. injection X as <-.
  destruct (same_class_member _ _ _ _ S) as [[tag H] T].
  destruct (E _ _ _ F (Reads kw eq_refl) t (or_intror (ex_intro _ tag H))) as [tk [T' [I Val]]].
  rewrite T in T'. injection T' as <-. apply (declared_word _ _ _ _ _ _ Cl T) in Val.
  destruct (opt_class_int _ I) as [kn [Q J]].
  rewrite K in Q. injection Q as <-. rewrite (boolean_ext_sound _ _ _ _ _ N J M Bool). exact Val.
Qed.

(** A fitting narrow fact explains both the stored result and the low word
    read by the next extension. *)
Lemma extend_narrow ge e classes defs filc kt ty t0 b w :
  defs_ok ge e classes defs filc -> nm_find b (sd_main defs) = Some (DefNarrow t0) ->
  nm_find b classes = Some kt -> narrow_fits t0 ty = true ->
  eval_op ge e kt (TApp "ext" [ty]) [tmp b] filc = Some w -> eval_val ge e kt (tmp b) = Some w.
Proof.
  intros D F C Fit V. destruct (D _ _ _ F C) as (n0 & k & m & x & N0 & K & I & M & Val & Low).
  destruct (extension_read _ _ _ _ _ _ _ V) as (n & kn & mn & y & N & K' & M' & Y & ->).
  rewrite K in K'; injection K' as <-. rewrite M in M'; injection M' as <-.
  rewrite Low in Y; injection Y as <-.
  destruct (narrow_fits_sound _ _ Fit) as (n0' & n' & H & H' & Preserve).
  rewrite N0 in H; injection H as <-. rewrite N in H'; injection H' as <-.
  rewrite Val. f_equal. f_equal. symmetry. exact (Preserve x k m I M).
Qed.

(** A comparison instruction declares a result class that can store a truth
    bit. Other instructions satisfy this syntactic condition automatically. *)
Definition cmp_result_class kt op :=
  forall c ck, op = cmp c ck -> bit_class kt.

(** Integer cancellation has an integer result class. A successful pointer
    cancellation starts with pointer arithmetic and therefore returns a pointer. *)
Lemma cancellation_bit_result ge e kt op args defs filc r w :
  cancel_arith kt op args defs = Some r -> eval_op ge e kt op args filc = Some w ->
  forall replacement, bit_result kt replacement w.
Proof.
  intros R V replacement z Literal Word Bit. subst w. unfold cancel_arith in R.
  destruct (is_atom "p" kt || is_int_class kt) eqn:K; try discriminate R.
  destruct (is_atom "add" op || is_atom "sub" op) eqn:O; try discriminate R.
  apply orb_true_iff in K as [K|I]; [|exact (int_bit_class _ I)].
  apply atom_shape in K. subst kt. apply orb_true_iff in O as [O|O];
    apply atom_shape in O; subst op; destruct args as [|a [|b [|t ts]]];
    try discriminate R; decode_ops; read_words V; discriminate V.
Qed.

Ltac stage_result R S r :=
  lazymatch type of R with
  | (match ?test with Some _ => _ | None => _ end) = _ =>
      destruct test as [r|] eqn:S
  end.

(** Simplifying an operation preserves its word at every fuel limit. For
    unchecked operations the literal-bit condition records exactly when the
    result class can represent a returned comparison bit. *)
Theorem simplified_sound ge e classes bools defs filc :
  simp_env_ok ge e classes bools defs filc ->
  forall fuel kt op args w,
    eval_op ge e kt op args filc = Some w ->
    (bit_result kt (simplified fuel kt op args classes filc bools defs) w \/ cmp_result_class kt op) ->
    eval_simp_res ge e kt filc (simplified fuel kt op args classes filc bools defs) = Some w.
Proof.
  intros [A Cl B E D Ar] fuel. induction fuel as [|fuel IH]; intros kt op args w V Bit.
  - exact V.
  - remember (simplified (S fuel) kt op args classes filc bools defs) as res eqn:R.
    symmetry in R. cbn [simplified] in R.
    destruct (is_atom "copy" op) eqn:C.
    + apply atom_shape in C. subst op. destruct args as [|v [|u us]]; try (subst res; exact V).
      rewrite copy_value in V. destruct v as [n|s|g vs|q]; try (subst res; exact V).
      destruct vs as [|t [|u us]]; try (subst res; exact V).
      destruct (String.eqb g "global"); subst res; cbn [eval_simp_res]; auto.
      rewrite copy_value. exact V.
      destruct v as [| |g [|t [|q qs]]|]; subst res; exact V.
    + lazymatch type of R with (if ?test then _ else _) = _ => destruct test eqn:P end.
      * apply andb_true_iff in P as [H Z]. apply andb_true_iff in H as [K O].
        apply atom_shape in K. subst kt. apply orb_true_iff in O as [O|O];
          apply atom_shape in O; subst op; subst res; eapply pointer_zero_sound; eauto.
      * stage_result R Fold r.
        -- subst res. destruct (is_int_class kt && foldable_op op && forallb is_const_term args) eqn:G;
             try discriminate Fold. apply andb_true_iff in G as [G _]. apply andb_true_iff in G as [I F].
           destruct (op_arg_classes op kt filc) as [ks|] eqn:Ks; try discriminate Fold.
           destruct (arg_numbers ks args) as [xs|] eqn:X; try discriminate Fold.
           destruct (eval_alu op kt xs) as [n|] eqn:N; try discriminate Fold.
           apply some_value in Fold; subst r. exact (folded_sound _ _ _ _ _ _ _ _ _ _ I F Ks X N V).
        -- stage_result R Comm r.
           ++ subst res. destruct (is_int_class kt && commutative_op op) eqn:G; try discriminate Comm.
              apply andb_true_iff in G as [I O]. destruct args as [|a [|b [|u us]]]; try discriminate Comm.
              destruct (is_const_term a && negb (is_const_term b)); try discriminate Comm.
              apply some_value in Comm. subst r. apply IH; [eapply commute_values; eassumption | exact Bit].
           ++ stage_result R Mirror r.
              ** subst res. destruct op as [| |g [|c [|ck [|u us]]]|]; try discriminate Mirror.
                 destruct args as [|a [|b [|u us]]]; try discriminate Mirror.
                 destruct (String.eqb g "cmp" && is_int_class ck && is_const_term a && negb (is_const_term b))
                   eqn:G; try discriminate Mirror.
                 apply andb_true_iff in G as [G _]. apply andb_true_iff in G as [G _].
                 apply andb_true_iff in G as [G I]. apply String.eqb_eq in G. subst g.
                 destruct (mirrored_cond c) as [c1|] eqn:M; try discriminate Mirror.
                 apply some_value in Mirror; subst r. apply IH;
                   [exact (mirror_values _ _ _ _ _ _ _ _ _ _ I M V) |].
                 destruct Bit as [Bit|Class]; [left; exact Bit|right].
                 intros q qk _. exact (Class c ck eq_refl).
              ** stage_result R Identity r.
                 { subst res. destruct (is_int_class kt) eqn:I; try discriminate Identity.
                   exact (apply_identity_sound _ _ _ _ _ _ _ _ _ B I Identity V). }
                 destruct (cancel_arith kt op args defs) as [[v|op1 args1]|] eqn:Cancel.
                 { subst res. exact (cancel_arith_sound _ _ _ _ _ _ _ _ _ A Ar Cancel V). }
                 { subst res. apply IH; [exact (cancel_arith_sound _ _ _ _ _ _ _ _ _ A Ar Cancel V) |].
                   left. exact (cancellation_bit_result _ _ _ _ _ _ _ _ _ Cancel V _). }
                 stage_result R Compare r.
                 { subst res. destruct op as [| |g [|c [|ck [|u us]]]|]; try discriminate Compare.
                   destruct (String.eqb g "cmp" && is_int_class ck) eqn:G; try discriminate Compare.
                   apply andb_true_iff in G as [G I]. apply String.eqb_eq in G. subst g.
                   destruct (boolean_cmp c ck kt args classes bools defs) as [r0|] eqn:BC.
                   - apply some_value in Compare. subst r.
                     assert (Q : bit_result kt r0 w).
                     { destruct Bit as [Q|Class]; [exact Q|]. intros z R Wd Bool. exact (Class c ck eq_refl). }
                     exact (boolean_cmp_sound _ _ _ _ _ _ _ _ _ _ _ _ I Q Cl B E D BC V).
                   - destruct (cancel_cmp c ck args defs) as [args1|] eqn:CC; try discriminate Compare.
                     apply some_value in Compare; subst r. apply IH; [|exact Bit].
                     assert (GC : c = TAtom "eq" \/ c = TAtom "ne").
                     { unfold cancel_cmp in CC. destruct (is_atom "eq" c || is_atom "ne" c) eqn:G;
                         try discriminate CC. apply orb_true_iff in G as [Q|Q]; auto using atom_shape. }
                     exact (cancel_cmp_sound _ _ _ _ _ _ _ _ _ _ GC I Ar CC V). }
                 destruct op as [| |g [|ty [|u us]]|]; try (subst res; exact V).
                 destruct args as [|v [|u us]]; try (subst res; exact V).
                 destruct (String.eqb g "ext") eqn:G; [apply String.eqb_eq in G; subst g|subst res; exact V].
                 destruct (tmp_name v) as [|b [|t ts]] eqn:T; try (subst res; exact V).
                 apply temp_shape in T; subst v. stage_result R BoolExt r.
                 { subst res. destruct (nm_find b bools) as [eqs|] eqn:F; try discriminate BoolExt.
                   destruct (same_class_temp classes kt eqs) as [t|] eqn:S; try discriminate BoolExt.
                   apply some_value in BoolExt; subst r. eapply extend_boolean; eassumption. }
                 destruct (nm_find b (sd_main defs)) as [[c ck a d|u|t0]|] eqn:F; try (subst res; exact V).
                 destruct (nm_find b classes) as [kb|] eqn:Ck; try (subst res; exact V).
                 destruct (narrow_fits t0 ty && term_eqb kb kt) eqn:G; [|subst res; exact V].
                 apply andb_true_iff in G as [N G]. apply term_eqb_eq in G; subst kb res.
                 eapply extend_narrow; eassumption.
Qed.

(** Evaluating a literal as an integer word requires a numeric result class.
    Every such class represents both zero and one. *)
Lemma literal_requires_bit_class ge e kt z :
  eval_val ge e kt (lit z) = Some (WInt z) -> bit_class kt.
Proof.
  unfold eval_val. destruct (opt_class kt) as [k|] eqn:K; try discriminate.
  destruct k; try discriminate; intros H; unfold bit_class.
  all: eexists; eexists; split; [exact K|]; repeat split; try discriminate; lia.
Qed.

(** The literal-bit condition is necessary as well as sufficient for successful
    source evaluations. It imposes no condition when the replacement is another operation. *)
Corollary simplified_sound_iff ge e classes bools defs filc fuel kt op args w :
  simp_env_ok ge e classes bools defs filc -> eval_op ge e kt op args filc = Some w ->
  let r := simplified fuel kt op args classes filc bools defs in
  eval_simp_res ge e kt filc r = Some w <-> bit_result kt r w.
Proof.
  intros Env V r. split.
  - intros R z Literal Word Bit. rewrite Literal, Word in R.
    exact (literal_requires_bit_class _ _ _ _ R).
  - intro Bit. exact (simplified_sound _ _ _ _ _ _ Env fuel kt op args w V (or_introl Bit)).
Qed.

(** A caller can discharge the result condition from the source instruction
    alone. Only comparisons need a class that can store a literal bit. *)
Corollary simplified_typed_sound ge e classes bools defs filc fuel kt op args w :
  simp_env_ok ge e classes bools defs filc -> cmp_result_class kt op ->
  eval_op ge e kt op args filc = Some w ->
  eval_simp_res ge e kt filc (simplified fuel kt op args classes filc bools defs) = Some w.
Proof.
  intros Env Class V. exact (simplified_sound _ _ _ _ _ _ Env fuel kt op args w V (or_intror Class)).
Qed.

(** Integer-result instructions satisfy the master theorem directly. *)
Corollary simplified_integer_sound ge e classes bools defs filc fuel kt op args w :
  simp_env_ok ge e classes bools defs filc -> is_int_class kt = true ->
  eval_op ge e kt op args filc = Some w ->
  eval_simp_res ge e kt filc (simplified fuel kt op args classes filc bools defs) = Some w.
Proof.
  intros Env I V. apply (simplified_sound _ _ _ _ _ _ Env fuel kt op args w V).
  left. intros z R Wd B. exact (int_bit_class _ I).
Qed.

(** A pointer-valued source cannot trigger the literal-bit exception. *)
Corollary simplified_pointer_sound ge e classes bools defs filc fuel kt op args p :
  simp_env_ok ge e classes bools defs filc -> eval_op ge e kt op args filc = Some (WPtr p) ->
  eval_simp_res ge e kt filc (simplified fuel kt op args classes filc bools defs) = Some (WPtr p).
Proof.
  intros Env V. apply (simplified_sound _ _ _ _ _ _ Env fuel kt op args (WPtr p) V).
  left. intros z R Wd. discriminate Wd.
Qed.

(** An unchecked comparison can request a pointer result even though the ALU
    returns an integer. With empty fact tables, the simplifier replaces a
    self-comparison by a literal that evaluates to a pointer instead. *)
Example unchecked_comparison_changes_word f :
  let ge := mkGenv [] [] (fun _ _ => None) in
  let t := TAtom "b" in let args := [tmp t; tmp t] in let e := [(t, WInt 0)] in
  simp_env_ok ge e nm_empty nm_empty empty_defs f /\
  eval_op ge e kp (cmp (TAtom "eq") kw) args f = Some (WInt 1) /\
  eval_simp_res ge e kp f (simplified 1 kp (cmp (TAtom "eq") kw) args nm_empty f nm_empty empty_defs)
    = Some (WPtr (mkPtr 1 CNone)).
Proof.
  cbv zeta. split; [|split; reflexivity]. constructor.
  - intros v p V. unfold eval_val in V. destruct (opt_value v) as [[t|n|g]|]; try discriminate.
    + cbn [value_x lookup] in V.
      destruct (name_eqb t (TAtom "b")); discriminate.
    + apply some_value in V. injection V as <-. apply Z.mod_pos_bound. lia.
    + inversion V. subst. cbn [ptr_addr]. lia.
  - intros t k H. rewrite nm_find_empty in H. discriminate.
  - intros t eqs H. rewrite nm_find_empty in H. discriminate.
  - intros t eqs z H. rewrite nm_find_empty in H. discriminate.
  - intros t fact kt H. discriminate H.
  - intros t kt op a b H. discriminate H.
Qed.
