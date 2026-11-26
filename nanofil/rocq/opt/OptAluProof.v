(** This module connects the middle-end optimizer's shared operation tables in
    [OptIr] to the core formal operational semantics in [Nanofil.Syntax],
    [Nanofil.Values], and [Nanofil.Ops]. Every integer constant-folding
    evaluation performed by [OptIr.eval_alu] is proved to produce an
    already-reduced integer word that agrees identically with [Nanofil.Ops.alu]
    and [Nanofil.Ops.additive_res].

    It also certifies the purity contract used by value numbering and dead-code
    elimination in [Simplify]: every operation accepted by [Simplify.pure_op]
    never traps, never faults as unchecked, never allocates, and never reads or
    modifies memory, returning either an immediate value or, exclusively for
    floating-point-to-integer conversions, undefined behavior. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics.
From Backend Require Import Pizlonate Escape.
From Opt Require Import OptIr Simplify.
Import ListNotations.
Local Open Scope Z_scope.

(** ## Syntax decoding bridge

    The optimizer operates on ground [term] trees, whereas [Nanofil.Ops]
    evaluates typed [Syntax.class], [Syntax.narrow], [Syntax.cond], and
    [Syntax.op] constructors. The decoders below match the model's transport
    representation without importing the runtime axiom signature. *)

(** Decoding a ground class atom returns the corresponding [Syntax.class]
    constructor. *)
Definition opt_class (t : term) : option class :=
  match t with
  | TAtom a =>
      if String.eqb a "w" then Some W
      else if String.eqb a "l" then Some L
      else if String.eqb a "p" then Some P
      else if String.eqb a "a" then Some A
      else if String.eqb a "f" then Some F
      else if String.eqb a "s" then Some Single
      else if String.eqb a "d" then Some Double
      else if String.eqb a "x" then Some Extended
      else None
  | _ => None
  end.

(** Decoding a narrow integer type atom returns the corresponding
    [Syntax.narrow] constructor. *)
Definition opt_narrow (t : term) : option narrow :=
  match t with
  | TAtom a =>
      if String.eqb a "sw" then Some Sw
      else if String.eqb a "uw" then Some Uw
      else if String.eqb a "sh" then Some Sh
      else if String.eqb a "uh" then Some Uh
      else if String.eqb a "sb" then Some Sb
      else if String.eqb a "ub" then Some Ub
      else None
  | _ => None
  end.

(** Decoding an integer comparison condition atom returns the corresponding
    [Syntax.cond] constructor. *)
Definition opt_int_cond (t : term) : option cond :=
  match t with
  | TAtom a =>
      if String.eqb a "eq" then Some Eq
      else if String.eqb a "ne" then Some Ne
      else if String.eqb a "sle" then Some Sle
      else if String.eqb a "slt" then Some Slt
      else if String.eqb a "sge" then Some Sge
      else if String.eqb a "sgt" then Some Sgt
      else if String.eqb a "ule" then Some Ule
      else if String.eqb a "ult" then Some Ult
      else if String.eqb a "uge" then Some Uge
      else if String.eqb a "ugt" then Some Ugt
      else None
  | _ => None
  end.

(** Decoding any comparison condition atom handles both integer and
    floating-point relational operators. *)
Definition opt_cond (t : term) : option cond :=
  match opt_int_cond t with
  | Some c => Some c
  | None =>
      match t with
      | TAtom a =>
          if String.eqb a "le" then Some Le
          else if String.eqb a "lt" then Some Lt
          else if String.eqb a "ge" then Some Ge
          else if String.eqb a "gt" then Some Gt
          else if String.eqb a "o" then Some Ord
          else if String.eqb a "uo" then Some Unord
          else None
      | _ => None
      end
  end.

(** Decoding a ground operation term covers every pure and arithmetic operation
    handled by the optimizer. *)
Definition opt_op (t : term) : option op :=
  match t with
  | TAtom a =>
      if String.eqb a "add" then Some Add
      else if String.eqb a "sub" then Some Sub
      else if String.eqb a "mul" then Some Mul
      else if String.eqb a "div" then Some Div
      else if String.eqb a "udiv" then Some Udiv
      else if String.eqb a "rem" then Some Rem
      else if String.eqb a "urem" then Some Urem
      else if String.eqb a "and" then Some And
      else if String.eqb a "or" then Some Or
      else if String.eqb a "xor" then Some Xor
      else if String.eqb a "sar" then Some Sar
      else if String.eqb a "shr" then Some Shr
      else if String.eqb a "shl" then Some Shl
      else if String.eqb a "neg" then Some Neg
      else if String.eqb a "copy" then Some Copy
      else if String.eqb a "select" then Some Select
      else if String.eqb a "ptoi" then Some Ptoi
      else if String.eqb a "itop" then Some Itop
      else if String.eqb a "truncd" then Some Truncd
      else if String.eqb a "truncx" then Some Truncx
      else if String.eqb a "stosi" then Some (FloatToInt Single Signed)
      else if String.eqb a "stoui" then Some (FloatToInt Single Unsigned)
      else if String.eqb a "dtosi" then Some (FloatToInt Double Signed)
      else if String.eqb a "dtoui" then Some (FloatToInt Double Unsigned)
      else if String.eqb a "xtosi" then Some (FloatToInt Extended Signed)
      else if String.eqb a "xtoui" then Some (FloatToInt Extended Unsigned)
      else if String.eqb a "swtof" then Some (IntToFloat W Signed)
      else if String.eqb a "uwtof" then Some (IntToFloat W Unsigned)
      else if String.eqb a "sltof" then Some (IntToFloat L Signed)
      else if String.eqb a "ultof" then Some (IntToFloat L Unsigned)
      else if String.eqb a "cast" then Some Cast
      else if String.eqb a "sqrt" then Some Sqrt
      else None
  | TApp f xs =>
      if String.eqb f "cmp" then
        match xs with
        | [c; ck] =>
            let* c' := opt_cond c in
            let* ck' := opt_class ck in
            Some (Cmp c' ck')
        | _ => None
        end
      else if String.eqb f "ext" then
        match xs with
        | [TAtom a] =>
            if String.eqb a "s" then Some (ExtF Single)
            else if String.eqb a "d" then Some (ExtF Double)
            else let* n' := opt_narrow (TAtom a) in Some (Ext n')
        | _ => None
        end
      else None
  | _ => None
  end.

(** Decoding an operand term produces a typed [Syntax.value] for temporaries,
    integer constants, and global symbols. *)
Definition opt_value (t : term) : option value :=
  match t with
  | TApp f [n] =>
      if String.eqb f "tmp" then Some (Tmp n)
      else if String.eqb f "global" then Some (Global n)
      else if String.eqb f "const" then
        match n with TInt z => Some (Const z) | _ => None end
      else None
  | _ => None
  end.

(** ## Bit-width and table agreement

    Before proving ALU equivalence, we establish that [OptIr]'s bit-width,
    modulus, sign-threshold, extension, shift-factor, and condition-bit
    functions coincide with [Nanofil.Syntax] and [Nanofil.Ops], and that
    bitwise operations preserve unsigned power-of-two bounds. *)

(** Recognizing an integer class atom via [OptIr.is_int_class] characterizes
    exactly the atoms `"w"` and `"l"`. *)
Lemma is_int_class_iff : forall kt,
  OptIr.is_int_class kt = true <-> kt = TAtom "w" \/ kt = TAtom "l".
Proof.
  intros kt. unfold OptIr.is_int_class, is_atom.
  destruct kt as [|a| |].
  - split; [discriminate | intros [H|H]; discriminate].
  - rewrite orb_true_iff, !String.eqb_eq. split.
    + intros [<- | <-]; [left | right]; reflexivity.
    + intros [H|H]; injection H as ->; [left | right]; reflexivity.
  - split; [discriminate | intros [H|H]; discriminate].
  - split; [discriminate | intros [H|H]; discriminate].
Qed.

(** Every class accepted by [OptIr.is_int_class] decodes to [W] or [L]. *)
Lemma opt_class_int : forall kt,
  OptIr.is_int_class kt = true ->
  exists k, opt_class kt = Some k /\ Syntax.int_class k = true.
Proof.
  intros kt H. apply is_int_class_iff in H as [-> | ->].
  - exists W. split; reflexivity.
  - exists L. split; reflexivity.
Qed.

(** The optimizer's [OptIr.class_bits] agrees with [Syntax.class_bits] on
    integer classes. *)
Lemma class_bits_agree : forall kt k,
  opt_class kt = Some k ->
  Syntax.int_class k = true ->
  OptIr.class_bits kt = Syntax.class_bits k.
Proof.
  intros kt k Hc Hi. destruct kt as [|a| |]; try discriminate Hc.
  simpl in Hc.
  destruct (String.eqb a "w") eqn:Ew;
    [apply String.eqb_eq in Ew; subst; injection Hc as <-; reflexivity |].
  destruct (String.eqb a "l") eqn:El;
    [apply String.eqb_eq in El; subst; injection Hc as <-; reflexivity |].
  destruct (String.eqb a "p") eqn:Ep;
    [injection Hc as <-; discriminate Hi |].
  destruct (String.eqb a "a") eqn:Ea;
    [injection Hc as <-; discriminate Hi |].
  destruct (String.eqb a "f") eqn:Ef;
    [injection Hc as <-; discriminate Hi |].
  destruct (String.eqb a "s") eqn:Es;
    [injection Hc as <-; discriminate Hi |].
  destruct (String.eqb a "d") eqn:Ed;
    [injection Hc as <-; discriminate Hi |].
  destruct (String.eqb a "x") eqn:Ex;
    [injection Hc as <-; discriminate Hi | discriminate Hc].
Qed.

(** The optimizer's [OptIr.class_modulus] agrees with [Syntax.modulus] on every
    decoded register class. *)
Lemma class_modulus_agree : forall kt k,
  opt_class kt = Some k ->
  OptIr.class_modulus kt = Syntax.modulus k.
Proof.
  intros kt k Hc. destruct kt as [|a| |]; try discriminate Hc.
  simpl in Hc.
  destruct (String.eqb a "w") eqn:Ew;
    [apply String.eqb_eq in Ew; subst; injection Hc as <-; reflexivity |].
  destruct (String.eqb a "l") eqn:El;
    [apply String.eqb_eq in El; subst; injection Hc as <-; reflexivity |].
  destruct (String.eqb a "p") eqn:Ep;
    [apply String.eqb_eq in Ep; subst; injection Hc as <-; reflexivity |].
  destruct (String.eqb a "a") eqn:Ea;
    [apply String.eqb_eq in Ea; subst; injection Hc as <-; reflexivity |].
  destruct (String.eqb a "f") eqn:Ef;
    [apply String.eqb_eq in Ef; subst; injection Hc as <-; reflexivity |].
  destruct (String.eqb a "s") eqn:Es;
    [apply String.eqb_eq in Es; subst; injection Hc as <-; reflexivity |].
  destruct (String.eqb a "d") eqn:Ed;
    [apply String.eqb_eq in Ed; subst; injection Hc as <-; reflexivity |].
  destruct (String.eqb a "x") eqn:Ex;
    [apply String.eqb_eq in Ex; subst; injection Hc as <-;
     simpl; f_equal; vm_compute; reflexivity | discriminate Hc].
Qed.

(** Any term whose [OptIr.class_modulus] succeeds decodes via [opt_class] to a
    class with the same modulus. *)
Lemma class_modulus_some_decode : forall kt m,
  OptIr.class_modulus kt = Some m ->
  exists k, opt_class kt = Some k /\ Syntax.modulus k = Some m /\ 0 < m.
Proof.
  intros kt m Hm. destruct kt as [|a| |]; try discriminate Hm.
  simpl in Hm.
  destruct (String.eqb a "w") eqn:Ew;
    [apply String.eqb_eq in Ew; subst; injection Hm as <-;
     exists W; repeat split; try reflexivity; lia |].
  destruct (String.eqb a "s") eqn:Es;
    [apply String.eqb_eq in Es; subst; injection Hm as <-;
     exists Single; repeat split; try reflexivity; lia |].
  destruct (String.eqb a "l") eqn:El;
    [apply String.eqb_eq in El; subst; injection Hm as <-;
     exists L; repeat split; try reflexivity; lia |].
  destruct (String.eqb a "p") eqn:Ep;
    [apply String.eqb_eq in Ep; subst; injection Hm as <-;
     exists P; repeat split; try reflexivity; lia |].
  destruct (String.eqb a "d") eqn:Ed;
    [apply String.eqb_eq in Ed; subst; injection Hm as <-;
     exists Double; repeat split; try reflexivity; lia |].
  destruct (String.eqb a "x") eqn:Ex;
    [apply String.eqb_eq in Ex; subst; injection Hm as <-;
     exists Extended; split; [reflexivity | split; [f_equal; vm_compute; reflexivity | vm_compute; reflexivity]]
    | discriminate Hm].
Qed.

(** The optimizer's [OptIr.class_half_modulus] agrees with [Syntax.half_modulus]
    on every decoded class. *)
Lemma class_half_modulus_agree : forall kt k,
  opt_class kt = Some k ->
  OptIr.class_half_modulus kt = Syntax.half_modulus k.
Proof.
  intros kt k Hc. destruct kt as [|a| |]; try discriminate Hc.
  simpl in Hc.
  destruct (String.eqb a "w") eqn:Ew;
    [apply String.eqb_eq in Ew; subst; injection Hc as <-; reflexivity |].
  destruct (String.eqb a "l") eqn:El;
    [apply String.eqb_eq in El; subst; injection Hc as <-; reflexivity |].
  destruct (String.eqb a "p") eqn:Ep;
    [apply String.eqb_eq in Ep; subst; injection Hc as <-; reflexivity |].
  destruct (String.eqb a "a") eqn:Ea;
    [apply String.eqb_eq in Ea; subst; injection Hc as <-; reflexivity |].
  destruct (String.eqb a "f") eqn:Ef;
    [apply String.eqb_eq in Ef; subst; injection Hc as <-; reflexivity |].
  destruct (String.eqb a "s") eqn:Es;
    [apply String.eqb_eq in Es; subst; injection Hc as <-; reflexivity |].
  destruct (String.eqb a "d") eqn:Ed;
    [apply String.eqb_eq in Ed; subst; injection Hc as <-; reflexivity |].
  destruct (String.eqb a "x") eqn:Ex;
    [apply String.eqb_eq in Ex; subst; injection Hc as <-; reflexivity | discriminate Hc].
Qed.

(** Two's-complement sign extension in [OptIr] is definitionally identical to
    [Ops.sign_extension]. *)
Lemma sign_extension_agree : forall m h u,
  OptIr.sign_extension m h u = Ops.sign_extension m h u.
Proof. reflexivity. Qed.

(** Signed integer decoding in [OptIr.signed_val] matches [Ops.signed] on every
    decoded class. *)
Lemma signed_val_agree : forall kt k u,
  opt_class kt = Some k ->
  OptIr.signed_val kt u = Ops.signed k u.
Proof.
  intros kt k u Hc. unfold OptIr.signed_val, Ops.signed.
  rewrite (class_modulus_agree kt k Hc), (class_half_modulus_agree kt k Hc).
  reflexivity.
Qed.

(** Narrow integer extension in [OptIr.extension_val] succeeds precisely on
    valid narrow type atoms and matches [Ops.extension]. *)
Lemma extension_val_agree : forall t x s,
  OptIr.extension_val t x = Some s ->
  exists nt, opt_narrow (TAtom t) = Some nt /\ s = Ops.extension nt x.
Proof.
  intros t x s H. unfold OptIr.extension_val in H.
  destruct (String.eqb t "sb") eqn:E1;
    [apply String.eqb_eq in E1; subst; injection H as <-; exists Sb; split; reflexivity |].
  destruct (String.eqb t "ub") eqn:E2;
    [apply String.eqb_eq in E2; subst; injection H as <-; exists Ub; split; reflexivity |].
  destruct (String.eqb t "sh") eqn:E3;
    [apply String.eqb_eq in E3; subst; injection H as <-; exists Sh; split; reflexivity |].
  destruct (String.eqb t "uh") eqn:E4;
    [apply String.eqb_eq in E4; subst; injection H as <-; exists Uh; split; reflexivity |].
  destruct (String.eqb t "sw") eqn:E5;
    [apply String.eqb_eq in E5; subst; injection H as <-; exists Sw; split; reflexivity |].
  destruct (String.eqb t "uw") eqn:E6;
    [apply String.eqb_eq in E6; subst; injection H as <-; exists Uw; split; reflexivity |].
  discriminate H.
Qed.

(** Shift-factor computation in [OptIr.shift_factor] matches [Ops.shift_factor]
    on integer classes and always yields a positive power of two. *)
Lemma shift_factor_agree : forall kt k y,
  opt_class kt = Some k ->
  Syntax.int_class k = true ->
  OptIr.shift_factor kt y = Ops.shift_factor k y.
Proof.
  intros kt k y Hc Hi. unfold OptIr.shift_factor, Ops.shift_factor.
  rewrite (class_bits_agree kt k Hc Hi).
  destruct k; try discriminate Hi; simpl; f_equal;
    rewrite Z.shiftl_1_l; reflexivity.
Qed.

(** Evaluating a condition bit in [OptIr.cond_bit] agrees with [Ops.cond_bit]
    for every decoded integer comparison class and produces zero or one. *)
Lemma cond_bit_agree : forall c ck ckn x y r,
  opt_class ck = Some ckn ->
  OptIr.cond_bit c ck x y = Some r ->
  exists cn,
    opt_cond (TAtom c) = Some cn /\
    Ops.cond_bit cn ckn x y = Some r /\
    (r = 0 \/ r = 1).
Proof.
  intros c ck ckn x y r Hck Hcb. unfold OptIr.cond_bit in Hcb.
  destruct (String.eqb c "eq") eqn:E1;
    [apply String.eqb_eq in E1; subst; injection Hcb as <-;
     exists Eq; repeat split; try reflexivity; destruct (x =? y); auto |].
  destruct (String.eqb c "ne") eqn:E2;
    [apply String.eqb_eq in E2; subst; injection Hcb as <-;
     exists Ne; repeat split; try reflexivity; destruct (x =? y); auto |].
  destruct (String.eqb c "ult") eqn:E3;
    [apply String.eqb_eq in E3; subst; injection Hcb as <-;
     exists Ult; repeat split; try reflexivity; destruct (x <? y); auto |].
  destruct (String.eqb c "ule") eqn:E4;
    [apply String.eqb_eq in E4; subst; injection Hcb as <-;
     exists Ule; repeat split; try reflexivity; destruct (x <=? y); auto |].
  destruct (String.eqb c "ugt") eqn:E5;
    [apply String.eqb_eq in E5; subst; injection Hcb as <-;
     exists Ugt; repeat split; try reflexivity; destruct (y <? x); auto |].
  destruct (String.eqb c "uge") eqn:E6;
    [apply String.eqb_eq in E6; subst; injection Hcb as <-;
     exists Uge; repeat split; try reflexivity; destruct (y <=? x); auto |].
  rewrite (signed_val_agree ck ckn x Hck) in Hcb.
  rewrite (signed_val_agree ck ckn y Hck) in Hcb.
  destruct (Ops.signed ckn x) as [sx|] eqn:Hsx; [| discriminate Hcb].
  destruct (Ops.signed ckn y) as [sy|] eqn:Hsy; [| discriminate Hcb].
  destruct (String.eqb c "slt") eqn:E7;
    [apply String.eqb_eq in E7; subst; injection Hcb as <-;
     exists Slt; simpl; rewrite Hsx, Hsy; repeat split; try reflexivity;
     destruct (sx <? sy); auto |].
  destruct (String.eqb c "sle") eqn:E8;
    [apply String.eqb_eq in E8; subst; injection Hcb as <-;
     exists Sle; simpl; rewrite Hsx, Hsy; repeat split; try reflexivity;
     destruct (sx <=? sy); auto |].
  destruct (String.eqb c "sgt") eqn:E9;
    [apply String.eqb_eq in E9; subst; injection Hcb as <-;
     exists Sgt; simpl; rewrite Hsx, Hsy; repeat split; try reflexivity;
     destruct (sy <? sx); auto |].
  destruct (String.eqb c "sge") eqn:E10;
    [apply String.eqb_eq in E10; subst; injection Hcb as <-;
     exists Sge; simpl; rewrite Hsx, Hsy; repeat split; try reflexivity;
     destruct (sy <=? sx); auto |].
  discriminate Hcb.
Qed.

(** Any nonnegative integer below two to the [b] has all bits at positions
    [b] and above equal to `false`. *)
Lemma testbit_above_pow2 : forall x b i,
  0 <= x < 2 ^ b -> 0 <= b -> b <= i -> Z.testbit x i = false.
Proof.
  intros x b i [Hx0 Hxb] Hb Hi.
  destruct (Z.eq_dec x 0) as [-> | Hnz].
  - apply Z.testbit_0_l.
  - apply Z.bits_above_log2; [lia |].
    assert (Hlog : Z.log2 x < b) by (apply Z.log2_lt_pow2; lia).
    lia.
Qed.

(** Any nonnegative integer whose bits at positions [b] and above are all
    `false` lies strictly below two to the [b]. *)
Lemma lt_pow2_of_testbit : forall r b,
  0 <= r -> 0 <= b ->
  (forall i, b <= i -> Z.testbit r i = false) ->
  r < 2 ^ b.
Proof.
  intros r b Hr0 Hb Hbits.
  destruct (Z.eq_dec r 0) as [-> | Hnz].
  - apply Z.pow_pos_nonneg; lia.
  - destruct (Z_lt_ge_dec r (2 ^ b)) as [Hlt | Hge]; [exact Hlt |].
    assert (Hlog : b <= Z.log2 r) by (apply Z.log2_le_pow2; lia).
    pose proof (Hbits (Z.log2 r) Hlog) as Hfalse.
    pose proof (Z.bit_log2 r ltac:(lia)) as Htrue.
    congruence.
Qed.

(** Bitwise conjunction preserves unsigned power-of-two bounds. *)
Lemma land_bound_pow2 : forall x y b,
  0 <= b -> 0 <= x < 2 ^ b -> 0 <= y < 2 ^ b ->
  0 <= Z.land x y < 2 ^ b.
Proof.
  intros x y b Hb Hx Hy. split.
  - apply Z.land_nonneg. left. lia.
  - apply lt_pow2_of_testbit; [apply Z.land_nonneg; left; lia | exact Hb |].
    intros i Hi. rewrite Z.land_spec.
    rewrite (testbit_above_pow2 x b i Hx Hb Hi). reflexivity.
Qed.

(** Bitwise disjunction preserves unsigned power-of-two bounds. *)
Lemma lor_bound_pow2 : forall x y b,
  0 <= b -> 0 <= x < 2 ^ b -> 0 <= y < 2 ^ b ->
  0 <= Z.lor x y < 2 ^ b.
Proof.
  intros x y b Hb Hx Hy. split.
  - apply Z.lor_nonneg. lia.
  - apply lt_pow2_of_testbit; [apply Z.lor_nonneg; lia | exact Hb |].
    intros i Hi. rewrite Z.lor_spec.
    rewrite (testbit_above_pow2 x b i Hx Hb Hi), (testbit_above_pow2 y b i Hy Hb Hi).
    reflexivity.
Qed.

(** Bitwise exclusive disjunction preserves unsigned power-of-two bounds. *)
Lemma lxor_bound_pow2 : forall x y b,
  0 <= b -> 0 <= x < 2 ^ b -> 0 <= y < 2 ^ b ->
  0 <= Z.lxor x y < 2 ^ b.
Proof.
  intros x y b Hb Hx Hy. split.
  - apply Z.lxor_nonneg. lia.
  - apply lt_pow2_of_testbit; [apply Z.lxor_nonneg; lia | exact Hb |].
    intros i Hi. rewrite Z.lxor_spec.
    rewrite (testbit_above_pow2 x b i Hx Hb Hi), (testbit_above_pow2 y b i Hy Hb Hi).
    reflexivity.
Qed.

(** Reducing constant operands via [Simplify.arg_numbers] ensures that every
    reduced integer lies strictly within its class modulus. *)
Lemma arg_numbers_bounds : forall ks args xs,
  Simplify.arg_numbers ks args = Some xs ->
  Forall2 (fun k x => exists m, OptIr.class_modulus k = Some m /\ 0 <= x < m) ks xs.
Proof.
  induction ks as [|k ks IH]; intros [|a args] xs H; simpl in H; try discriminate H.
  - injection H as <-. constructor.
  - destruct (const_int a) as [n|]; [| discriminate H].
    destruct (OptIr.class_modulus k) as [m|] eqn:Hm; [| discriminate H].
    destruct (Simplify.arg_numbers ks args) as [rest|] eqn:Hrest; [| discriminate H].
    injection H as <-. constructor.
    + exists m. split; [exact Hm |].
      destruct (class_modulus_some_decode k m Hm) as (_ & _ & _ & Hpos).
      apply Z.mod_pos_bound. exact Hpos.
    + exact (IH args rest Hrest).
Qed.

(** ## Exact ALU equivalence

    The main theorem [eval_alu_sound] proves that whenever [OptIr.eval_alu]
    folds an integer operation on operands reduced to their class moduli, the
    resulting integer is already reduced modulo the result class and equals
    [Nanofil.Ops.alu] on the corresponding [WInt] words. *)

(** Helper stating that every operand matches the range of its expected
    argument class. *)
Definition args_in_range (op kt : term) (filc : bool) (xs : list Z) : Prop :=
  exists arg_ks,
    OptIr.op_arg_classes op kt filc = Some arg_ks /\
    Forall2 (fun ak x => exists m, OptIr.class_modulus ak = Some m /\ 0 <= x < m) arg_ks xs.

(** Constant arguments reduced by [Simplify.arg_numbers] satisfy
    [args_in_range]. *)
Lemma arg_numbers_in_range : forall op kt filc arg_ks args xs,
  OptIr.op_arg_classes op kt filc = Some arg_ks ->
  Simplify.arg_numbers arg_ks args = Some xs ->
  args_in_range op kt filc xs.
Proof.
  intros op kt filc arg_ks args xs Hks Hnums.
  exists arg_ks. split; [exact Hks | apply arg_numbers_bounds with (args := args); exact Hnums].
Qed.

(** Extracting the bit width and modulus of an integer class shows that the
    modulus equals two to the bit width. *)
Lemma int_class_bits_modulus : forall k,
  Syntax.int_class k = true ->
  exists b m,
    Syntax.class_bits k = Some b /\
    Syntax.modulus k = Some m /\
    0 < b /\ m = 2 ^ b /\ 0 < m.
Proof.
  intros k Hk. destruct k; try discriminate Hk.
  - exists 32, (2 ^ 32). repeat split; try reflexivity; lia.
  - exists 64, (2 ^ 64). repeat split; try reflexivity; lia.
Qed.

(** Evaluating any integer operation through [OptIr.eval_alu] at integer class
    [kt] produces a reduced result matching [Nanofil.Ops.alu] exactly. *)
Theorem eval_alu_sound : forall op kt filc xs r k m,
  opt_class kt = Some k ->
  Syntax.int_class k = true ->
  Syntax.modulus k = Some m ->
  args_in_range op kt filc xs ->
  OptIr.eval_alu op kt xs = Some r ->
  exists o,
    opt_op op = Some o /\
    Ops.alu o k (map WInt xs) = Some (WInt r) /\
    0 <= r < m.
Proof.
  intros op kt filc xs r k m Hkt Hik Hm Hrng Heval.
  pose proof (class_modulus_agree kt k Hkt) as Hmod_eq.
  rewrite Hm in Hmod_eq.
  destruct (int_class_bits_modulus k Hik) as (bits & m' & Hbits & Hm' & Hbits_pos & Hm_pow & Hm_pos).
  rewrite Hm in Hm'. injection Hm' as <-.
  destruct Hrng as (arg_ks & Harg_ks & Hbounds).
  destruct op as [| a | f args |]; try discriminate Heval.
  - (* Atomic integer operations *)
    simpl in Heval.
    destruct (String.eqb a "add") eqn:Eadd.
    { apply String.eqb_eq in Eadd. subst a.
      destruct xs as [|x [|y [|]]]; try discriminate Heval.
      rewrite Hmod_eq in Heval. injection Heval as <-.
      exists Add. split; [reflexivity | split; [simpl; rewrite Hm; reflexivity | apply Z.mod_pos_bound; exact Hm_pos]]. }
    destruct (String.eqb a "sub") eqn:Esub.
    { apply String.eqb_eq in Esub. subst a.
      destruct xs as [|x [|y [|]]]; try discriminate Heval.
      rewrite Hmod_eq in Heval. injection Heval as <-.
      exists Sub. split; [reflexivity | split; [simpl; rewrite Hm; reflexivity | apply Z.mod_pos_bound; exact Hm_pos]]. }
    destruct (String.eqb a "mul") eqn:Emul.
    { apply String.eqb_eq in Emul. subst a.
      destruct xs as [|x [|y [|]]]; try discriminate Heval.
      rewrite Hmod_eq in Heval. injection Heval as <-.
      exists Mul. split; [reflexivity | split; [simpl; rewrite Hm; reflexivity | apply Z.mod_pos_bound; exact Hm_pos]]. }
    destruct (String.eqb a "neg") eqn:Eneg.
    { apply String.eqb_eq in Eneg. subst a.
      destruct xs as [|x [|]]; try discriminate Heval.
      rewrite Hmod_eq in Heval. injection Heval as <-.
      exists Neg. split; [reflexivity | split; [simpl; rewrite Hm; reflexivity | apply Z.mod_pos_bound; exact Hm_pos]]. }
    destruct (String.eqb a "copy") eqn:Ecopy.
    { apply String.eqb_eq in Ecopy. subst a.
      destruct xs as [|x [|]]; try discriminate Heval.
      injection Heval as <-.
      simpl in Harg_ks. injection Harg_ks as <-.
      inversion Hbounds as [|? ? ? ? [mx [Hmx Hxb]] _]; subst.
      rewrite Hmod_eq in Hmx. injection Hmx as <-.
      exists Copy. split; [reflexivity | split; [reflexivity | exact Hxb]]. }
    destruct (String.eqb a "select") eqn:Esel.
    { apply String.eqb_eq in Esel. subst a.
      destruct xs as [|c [|x [|y [|]]]]; try discriminate Heval.
      injection Heval as <-.
      simpl in Harg_ks. injection Harg_ks as <-.
      inversion Hbounds as [|? ? ? ? _ Hrest1]; subst.
      inversion Hrest1 as [|? ? ? ? [mx [Hmx Hxb]] Hrest2]; subst.
      inversion Hrest2 as [|? ? ? ? [my [Hmy Hyb]] _]; subst.
      rewrite Hmod_eq in Hmx, Hmy. injection Hmx as <-. injection Hmy as <-.
      exists Select. split; [reflexivity | split; [reflexivity |]].
      destruct (c =? 0); [exact Hyb | exact Hxb]. }
    destruct (String.eqb a "and") eqn:Eand.
    { apply String.eqb_eq in Eand. subst a.
      destruct xs as [|x [|y [|]]]; try discriminate Heval.
      injection Heval as <-.
      simpl in Harg_ks. injection Harg_ks as <-.
      inversion Hbounds as [|? ? ? ? [mx [Hmx Hxb]] Hrest]; subst.
      inversion Hrest as [|? ? ? ? [my [Hmy Hyb]] _]; subst.
      rewrite Hmod_eq in Hmx, Hmy. injection Hmx as <-. injection Hmy as <-.
      exists And. split; [reflexivity | split; [reflexivity |]].
      apply land_bound_pow2; [lia | exact Hxb | exact Hyb]. }
    destruct (String.eqb a "or") eqn:Eor.
    { apply String.eqb_eq in Eor. subst a.
      destruct xs as [|x [|y [|]]]; try discriminate Heval.
      injection Heval as <-.
      simpl in Harg_ks. injection Harg_ks as <-.
      inversion Hbounds as [|? ? ? ? [mx [Hmx Hxb]] Hrest]; subst.
      inversion Hrest as [|? ? ? ? [my [Hmy Hyb]] _]; subst.
      rewrite Hmod_eq in Hmx, Hmy. injection Hmx as <-. injection Hmy as <-.
      exists Or. split; [reflexivity | split; [reflexivity |]].
      apply lor_bound_pow2; [lia | exact Hxb | exact Hyb]. }
    destruct (String.eqb a "xor") eqn:Exor.
    { apply String.eqb_eq in Exor. subst a.
      destruct xs as [|x [|y [|]]]; try discriminate Heval.
      injection Heval as <-.
      simpl in Harg_ks. injection Harg_ks as <-.
      inversion Hbounds as [|? ? ? ? [mx [Hmx Hxb]] Hrest]; subst.
      inversion Hrest as [|? ? ? ? [my [Hmy Hyb]] _]; subst.
      rewrite Hmod_eq in Hmx, Hmy. injection Hmx as <-. injection Hmy as <-.
      exists Xor. split; [reflexivity | split; [reflexivity |]].
      apply lxor_bound_pow2; [lia | exact Hxb | exact Hyb]. }
    destruct (String.eqb a "udiv") eqn:Eudiv.
    { apply String.eqb_eq in Eudiv. subst a.
      destruct xs as [|x [|y [|]]]; try discriminate Heval.
      injection Heval as <-.
      simpl in Harg_ks. injection Harg_ks as <-.
      inversion Hbounds as [|? ? ? ? [mx [Hmx Hxb]] Hrest]; subst.
      inversion Hrest as [|? ? ? ? [my [Hmy Hyb]] _]; subst.
      rewrite Hmod_eq in Hmx, Hmy. injection Hmx as <-. injection Hmy as <-.
      exists Udiv. split; [reflexivity |].
      simpl. unfold Ops.unsigned_division.
      destruct (y =? 0) eqn:Ey0.
      - split; [reflexivity | lia].
      - apply Z.eqb_neq in Ey0.
        rewrite Z.quot_div_nonneg by lia.
        split; [reflexivity |].
        split; [apply Z.div_pos; lia |].
        pose proof (Z.div_le_upper_bound x y x ltac:(lia) ltac:(nia)). lia. }
    destruct (String.eqb a "urem") eqn:Eurem.
    { apply String.eqb_eq in Eurem. subst a.
      destruct xs as [|x [|y [|]]]; try discriminate Heval.
      injection Heval as <-.
      simpl in Harg_ks. injection Harg_ks as <-.
      inversion Hbounds as [|? ? ? ? [mx [Hmx Hxb]] Hrest]; subst.
      inversion Hrest as [|? ? ? ? [my [Hmy Hyb]] _]; subst.
      rewrite Hmod_eq in Hmx, Hmy. injection Hmx as <-. injection Hmy as <-.
      exists Urem. split; [reflexivity |].
      simpl. unfold Ops.unsigned_division.
      destruct (y =? 0) eqn:Ey0.
      - split; [reflexivity | lia].
      - apply Z.eqb_neq in Ey0.
        split; [reflexivity |].
        pose proof (Z.mod_pos_bound x y ltac:(lia)). lia. }
    destruct (String.eqb a "div") eqn:Ediv.
    { apply String.eqb_eq in Ediv. subst a.
      destruct xs as [|x [|y [|]]]; try discriminate Heval.
      rewrite (signed_val_agree kt k x Hkt), (signed_val_agree kt k y Hkt) in Heval.
      destruct (Ops.signed k x) as [sx|] eqn:Hsx; [| discriminate Heval].
      destruct (Ops.signed k y) as [sy|] eqn:Hsy; [| discriminate Heval].
      exists Div. split; [reflexivity |].
      simpl. unfold Ops.signed_division. rewrite Hsx, Hsy, Hm.
      destruct (sy =? 0) eqn:Esy0.
      - injection Heval as <-. split; [reflexivity | lia].
      - rewrite Hmod_eq in Heval. injection Heval as <-.
        split; [reflexivity | apply Z.mod_pos_bound; exact Hm_pos]. }
    destruct (String.eqb a "rem") eqn:Erem.
    { apply String.eqb_eq in Erem. subst a.
      destruct xs as [|x [|y [|]]]; try discriminate Heval.
      rewrite (signed_val_agree kt k x Hkt), (signed_val_agree kt k y Hkt) in Heval.
      destruct (Ops.signed k x) as [sx|] eqn:Hsx; [| discriminate Heval].
      destruct (Ops.signed k y) as [sy|] eqn:Hsy; [| discriminate Heval].
      exists Rem. split; [reflexivity |].
      simpl. unfold Ops.signed_division. rewrite Hsx, Hsy, Hm.
      destruct (sy =? 0) eqn:Esy0.
      - injection Heval as <-. split; [reflexivity | lia].
      - rewrite Hmod_eq in Heval. injection Heval as <-.
        split; [reflexivity | apply Z.mod_pos_bound; exact Hm_pos]. }
    destruct (String.eqb a "shl") eqn:Eshl.
    { apply String.eqb_eq in Eshl. subst a.
      destruct xs as [|x [|y [|]]]; try discriminate Heval.
      rewrite (shift_factor_agree kt k y Hkt Hik), Hmod_eq in Heval.
      destruct (Ops.shift_factor k y) as [p|] eqn:Hp; [| discriminate Heval].
      injection Heval as <-.
      exists Shl. split; [reflexivity |].
      simpl. rewrite Hp, Hm.
      split; [reflexivity | apply Z.mod_pos_bound; exact Hm_pos]. }
    destruct (String.eqb a "shr") eqn:Eshr.
    { apply String.eqb_eq in Eshr. subst a.
      destruct xs as [|x [|y [|]]]; try discriminate Heval.
      rewrite (shift_factor_agree kt k y Hkt Hik) in Heval.
      destruct (Ops.shift_factor k y) as [p|] eqn:Hp; [| discriminate Heval].
      injection Heval as <-.
      simpl in Harg_ks. injection Harg_ks as <-.
      inversion Hbounds as [|? ? ? ? [mx [Hmx Hxb]] _]; subst.
      rewrite Hmod_eq in Hmx. injection Hmx as <-.
      unfold Ops.shift_factor in Hp. rewrite Hbits in Hp. injection Hp as <-.
      assert (Hp_pos : 0 < 2 ^ (y mod bits)).
      { apply Z.pow_pos_nonneg; [lia |].
        pose proof (Z.mod_pos_bound y bits Hbits_pos). lia. }
      exists Shr. split; [reflexivity |].
      simpl. unfold Ops.shift_factor. rewrite Hbits.
      rewrite Z.quot_div_nonneg by lia.
      split; [reflexivity |].
      split; [apply Z.div_pos; lia |].
      pose proof (Z.div_le_upper_bound x (2 ^ (y mod bits)) x ltac:(lia) ltac:(nia)). lia. }
    destruct (String.eqb a "sar") eqn:Esar.
    { apply String.eqb_eq in Esar. subst a.
      destruct xs as [|x [|y [|]]]; try discriminate Heval.
      rewrite (shift_factor_agree kt k y Hkt Hik), (signed_val_agree kt k x Hkt), Hmod_eq in Heval.
      destruct (Ops.shift_factor k y) as [p|] eqn:Hp; [| discriminate Heval].
      destruct (Ops.signed k x) as [sx|] eqn:Hsx; [| discriminate Heval].
      injection Heval as <-.
      exists Sar. split; [reflexivity |].
      simpl. rewrite Hp, Hsx, Hm.
      split; [reflexivity | apply Z.mod_pos_bound; exact Hm_pos]. }
    discriminate Heval.
  - (* Compound integer operations: ext and cmp *)
    simpl in Heval.
    destruct (String.eqb f "ext") eqn:Eext.
    { apply String.eqb_eq in Eext. subst f.
      destruct args as [|[|t| |][|]]; try discriminate Heval.
      destruct xs as [|x [|]]; try discriminate Heval.
      destruct (OptIr.extension_val t x) as [s|] eqn:Hext; [| discriminate Heval].
      rewrite Hmod_eq in Heval. injection Heval as <-.
      destruct (extension_val_agree t x s Hext) as (nt & Hnt & ->).
      exists (Ext nt). split.
      - simpl.
        destruct (String.eqb t "s") eqn:Es; [apply String.eqb_eq in Es; subst; discriminate Hnt |].
        destruct (String.eqb t "d") eqn:Ed; [apply String.eqb_eq in Ed; subst; discriminate Hnt |].
        destruct nt; simpl in Hnt;
          destruct (String.eqb t "sw") eqn:Esw; try (apply String.eqb_eq in Esw; subst; reflexivity);
          destruct (String.eqb t "uw") eqn:Euw; try (apply String.eqb_eq in Euw; subst; reflexivity);
          destruct (String.eqb t "sh") eqn:Esh; try (apply String.eqb_eq in Esh; subst; reflexivity);
          destruct (String.eqb t "uh") eqn:Euh; try (apply String.eqb_eq in Euh; subst; reflexivity);
          destruct (String.eqb t "sb") eqn:Esb; try (apply String.eqb_eq in Esb; subst; reflexivity);
          destruct (String.eqb t "ub") eqn:Eub; try (apply String.eqb_eq in Eub; subst; reflexivity);
          discriminate Hnt.
      - simpl. rewrite Hm. split; [reflexivity | apply Z.mod_pos_bound; exact Hm_pos]. }
    destruct (String.eqb f "cmp") eqn:Ecmp.
    { apply String.eqb_eq in Ecmp. subst f.
      destruct args as [|[|c| |][|ck [|]]]; try discriminate Heval.
      destruct xs as [|x [|y [|]]]; try discriminate Heval.
      simpl in Harg_ks. injection Harg_ks as <-.
      inversion Hbounds as [|? ? ? ? [mck [Hmck _]] _]; subst.
      destruct (class_modulus_some_decode ck mck Hmck) as (ckn & Hckn & _ & _).
      destruct (cond_bit_agree c ck ckn x y r Hckn Heval) as (cn & Hcn & Hcb & Hr01).
      exists (Cmp cn ckn). split.
      - simpl. rewrite Hcn, Hckn. reflexivity.
      - simpl. rewrite Hcb. split; [reflexivity |].
        destruct k; try discriminate Hik; simpl in Hbits; injection Hbits as <-; lia. }
    discriminate Heval.
Qed.

(** At integer classes, [OptIr.eval_alu] for `add` and `sub` also agrees with
    [Nanofil.Ops.additive_res]. *)
Corollary eval_alu_additive_sound : forall op kt filc xs r k m,
  (op = TAtom "add" \/ op = TAtom "sub") ->
  opt_class kt = Some k ->
  Syntax.int_class k = true ->
  Syntax.modulus k = Some m ->
  args_in_range op kt filc xs ->
  OptIr.eval_alu op kt xs = Some r ->
  exists o,
    opt_op op = Some o /\
    Ops.additive_res k o (map WInt xs) = Some (WInt r) /\
    0 <= r < m.
Proof.
  intros op kt filc xs r k m Hop Hkt Hik Hm Hrng Heval.
  destruct (eval_alu_sound op kt filc xs r k m Hkt Hik Hm Hrng Heval) as (o & Ho & Halu & Hrb).
  exists o. split; [exact Ho | split; [| exact Hrb]].
  destruct k; try discriminate Hik; simpl; exact Halu.
Qed.

(** ## Pure-operation semantics

    Both dead-code elimination and dominator-tree value numbering in [Simplify]
    rely on [Simplify.pure_op]. We prove directly against [Nanofil.Ops.op_res]
    that every pure operation leaves memory untouched, never traps, never
    faults as unchecked, and evaluates identically in any two memory states. *)

(** Classifying which decoded operations can satisfy [Simplify.pure_op]
    rules out allocations, memory loads, checks, compare-and-exchange,
    variadic argument extraction, and `setjmp`. *)
Lemma pure_op_cases : forall op o,
  Simplify.pure_op op = true ->
  opt_op op = Some o ->
  match o with
  | Add | Sub | Mul | And | Or | Xor | Sar | Shr | Shl | Neg | Copy | Select
  | Ptoi | Itop | Cmp _ _ | Ext _ | ExtF _ | Truncd | Truncx | Sqrt
  | IntToFloat _ _ | FloatToInt _ _ | Cast => True
  | _ => False
  end.
Proof.
  intros op o Hpure Hop.
  destruct op as [| a | f args |]; try discriminate Hop.
  - unfold opt_op in Hop. cbn iota in Hop.
    repeat (match type of Hop with
            | context [String.eqb a ?s] =>
                let E := fresh "E" in
                destruct (String.eqb a s) eqn:E;
                [apply String.eqb_eq in E; subst a;
                 vm_compute in Hop; injection Hop as <-;
                 first [exact I | vm_compute in Hpure; discriminate Hpure]
                | cbn iota in Hop]
            end).
    discriminate Hop.
  - unfold opt_op in Hop. cbn iota in Hop.
    destruct (String.eqb f "cmp") eqn:Ecmp; cbn iota in Hop.
    + destruct args as [|c [|ck [|]]]; try discriminate Hop.
      destruct (opt_cond c), (opt_class ck); try discriminate Hop.
      injection Hop as <-. exact I.
    + destruct (String.eqb f "ext") eqn:Eext; cbn iota in Hop; [| discriminate Hop].
      destruct args as [|[|ta| |] [|]]; try discriminate Hop.
      destruct (String.eqb ta "s"); cbn iota in Hop; [injection Hop as <-; exact I |].
      destruct (String.eqb ta "d"); cbn iota in Hop; [injection Hop as <-; exact I |].
      destruct (opt_narrow (TAtom ta)) as [nt|];
        [injection Hop as <-; exact I | discriminate Hop].
Qed.

(** Every pure operation evaluated through [Nanofil.Ops.op_res] leaves memory
    unchanged and never traps, faults as unchecked, or allocates. Only
    [FloatToInt] can report undefined behavior via [OpUB]. *)
Theorem pure_op_no_trap_no_mem : forall op o k xs m out,
  Simplify.pure_op op = true ->
  opt_op op = Some o ->
  Ops.op_res o k xs m = Some out ->
  (exists w, out = OpRes (RVal w) m) \/
  (exists fk sg why, o = FloatToInt fk sg /\ out = OpUB why).
Proof.
  intros op o k xs m out Hpure Hop Hres.
  pose proof (pure_op_cases op o Hpure Hop) as Hcase.
  destruct o; try contradiction Hcase; unfold Ops.op_res in Hres.
  - (* Add *)
    destruct (Ops.fmt_of k) as [f|].
    + destruct (Ops.float_arithmetic Add f xs) as [r|]; try discriminate Hres.
      injection Hres as <-. left. eexists. reflexivity.
    + unfold Ops.op_res_int in Hres.
      destruct (Ops.additive_res k Add xs) as [w|]; try discriminate Hres.
      injection Hres as <-. left. eexists. reflexivity.
  - (* Sub *)
    destruct (Ops.fmt_of k) as [f|].
    + destruct (Ops.float_arithmetic Sub f xs) as [r|]; try discriminate Hres.
      injection Hres as <-. left. eexists. reflexivity.
    + unfold Ops.op_res_int in Hres.
      destruct (Ops.additive_res k Sub xs) as [w|]; try discriminate Hres.
      injection Hres as <-. left. eexists. reflexivity.
  - (* Mul *)
    destruct (Ops.fmt_of k) as [f|].
    + destruct (Ops.float_arithmetic Mul f xs) as [r|]; try discriminate Hres.
      injection Hres as <-. left. eexists. reflexivity.
    + unfold Ops.op_res_int in Hres.
      destruct (Ops.alu Mul k xs) as [w|]; try discriminate Hres.
      injection Hres as <-. left. eexists. reflexivity.
  - (* And *)
    destruct (Ops.fmt_of k); unfold Ops.op_res_int in Hres;
      destruct (Ops.alu And k xs) as [w|]; try discriminate Hres;
      injection Hres as <-; left; eexists; reflexivity.
  - (* Or *)
    destruct (Ops.fmt_of k); unfold Ops.op_res_int in Hres;
      destruct (Ops.alu Or k xs) as [w|]; try discriminate Hres;
      injection Hres as <-; left; eexists; reflexivity.
  - (* Xor *)
    destruct (Ops.fmt_of k); unfold Ops.op_res_int in Hres;
      destruct (Ops.alu Xor k xs) as [w|]; try discriminate Hres;
      injection Hres as <-; left; eexists; reflexivity.
  - (* Sar *)
    destruct (Ops.fmt_of k); unfold Ops.op_res_int in Hres;
      destruct (Ops.alu Sar k xs) as [w|]; try discriminate Hres;
      injection Hres as <-; left; eexists; reflexivity.
  - (* Shr *)
    destruct (Ops.fmt_of k); unfold Ops.op_res_int in Hres;
      destruct (Ops.alu Shr k xs) as [w|]; try discriminate Hres;
      injection Hres as <-; left; eexists; reflexivity.
  - (* Shl *)
    destruct (Ops.fmt_of k); unfold Ops.op_res_int in Hres;
      destruct (Ops.alu Shl k xs) as [w|]; try discriminate Hres;
      injection Hres as <-; left; eexists; reflexivity.
  - (* Neg *)
    destruct (Ops.fmt_of k) as [f|].
    + destruct (Ops.float_arithmetic Neg f xs) as [r|]; try discriminate Hres.
      injection Hres as <-. left. eexists. reflexivity.
    + unfold Ops.op_res_int in Hres.
      destruct (Ops.alu Neg k xs) as [w|]; try discriminate Hres.
      injection Hres as <-. left. eexists. reflexivity.
  - (* Copy *)
    destruct (Ops.fmt_of k) as [f|].
    + destruct (Ops.float_arithmetic Copy f xs) as [r|]; try discriminate Hres.
      injection Hres as <-. left. eexists. reflexivity.
    + unfold Ops.op_res_int in Hres.
      destruct (Ops.alu Copy k xs) as [w|]; try discriminate Hres.
      injection Hres as <-. left. eexists. reflexivity.
  - (* Ptoi *)
    destruct (Ops.fmt_of k); unfold Ops.op_res_int in Hres;
      destruct (Ops.alu Ptoi k xs) as [w|]; try discriminate Hres;
      injection Hres as <-; left; eexists; reflexivity.
  - (* Itop *)
    destruct (Ops.fmt_of k); unfold Ops.op_res_int in Hres;
      destruct (Ops.alu Itop k xs) as [w|]; try discriminate Hres;
      injection Hres as <-; left; eexists; reflexivity.
  - (* Select *)
    destruct (Ops.fmt_of k); unfold Ops.op_res_int in Hres;
      destruct (Ops.alu Select k xs) as [w|]; try discriminate Hres;
      injection Hres as <-; left; eexists; reflexivity.
  - (* Cmp *)
    destruct (Ops.fmt_of k), xs as [|[n1| |][|[n2| |][|]]];
      try (destruct (Ops.fmt_of k0); try discriminate Hres;
           [injection Hres as <-; left; eexists; reflexivity
           | unfold Ops.op_res_int in Hres;
             destruct (Ops.alu (Cmp c k0) k _); try discriminate Hres;
             injection Hres as <-; left; eexists; reflexivity]).
    all: destruct (Ops.fmt_of k0); try discriminate Hres;
         unfold Ops.op_res_int in Hres;
         destruct (Ops.alu (Cmp c k0) k _); try discriminate Hres;
         injection Hres as <-; left; eexists; reflexivity.
  - (* Ext *)
    destruct (Ops.fmt_of k); unfold Ops.op_res_int in Hres;
      destruct (Ops.alu (Ext t) k xs) as [w|]; try discriminate Hres;
      injection Hres as <-; left; eexists; reflexivity.
  - (* ExtF *)
    destruct (Ops.fmt_of k), xs as [|[n| |][|]]; try discriminate Hres;
      destruct (Ops.float_convert (ExtF k0) k n) as [r|]; try discriminate Hres;
      injection Hres as <-; left; eexists; reflexivity.
  - (* Truncd *)
    destruct (Ops.fmt_of k), xs as [|[n| |][|]]; try discriminate Hres;
      destruct (Ops.float_convert Truncd k n) as [r|]; try discriminate Hres;
      injection Hres as <-; left; eexists; reflexivity.
  - (* Truncx *)
    destruct (Ops.fmt_of k), xs as [|[n| |][|]]; try discriminate Hres;
      destruct (Ops.float_convert Truncx k n) as [r|]; try discriminate Hres;
      injection Hres as <-; left; eexists; reflexivity.
  - (* FloatToInt *)
    destruct (Ops.fmt_of k), xs as [|[n| |][|]]; try discriminate Hres;
      destruct (Ops.fmt_of k0) as [from|]; try discriminate Hres;
      unfold Ops.float_integer in Hres;
      destruct (Syntax.modulus k) as [mk|]; try discriminate Hres;
      destruct sg; destruct (Ieee.ieee_to_int from n) as [z|];
      try (injection Hres as <-; right; exists k0, Signed, (TAtom "float_conversion"); split; reflexivity);
      try (injection Hres as <-; right; exists k0, Unsigned, (TAtom "float_conversion"); split; reflexivity);
      try (destruct ((- (mk / 2) <=? z) && (z <=? mk / 2 - 1));
           injection Hres as <-;
           [left; eexists; reflexivity
           | right; exists k0, Signed, (TAtom "float_conversion"); split; reflexivity]);
      try (destruct ((0 <=? z) && (z <=? mk - 1));
           injection Hres as <-;
           [left; eexists; reflexivity
           | right; exists k0, Unsigned, (TAtom "float_conversion"); split; reflexivity]).
  - (* IntToFloat *)
    destruct (Ops.fmt_of k) as [f|], xs as [|[n| |][|]]; try discriminate Hres;
      destruct (Ops.integer_source k0 sg n) as [z|]; try discriminate Hres;
      injection Hres as <-; left; eexists; reflexivity.
  - (* Cast *)
    destruct (Ops.fmt_of k), xs as [|[n| |][|]]; try discriminate Hres;
      injection Hres as <-; left; eexists; reflexivity.
  - (* Sqrt *)
    destruct (Ops.fmt_of k), xs as [|[n| |][|]]; try discriminate Hres;
      destruct (Ops.float_convert Sqrt k n) as [r|]; try discriminate Hres;
      injection Hres as <-; left; eexists; reflexivity.
Qed.

(** Every pure operation is completely independent of the memory state: if it
    produces a value [w] in memory [m1], it produces the exact same value [w]
    in any other memory [m2], justifying dominator-tree value numbering across
    intervening memory writes and calls. *)
Theorem pure_op_mem_independent : forall op o k xs m1 m2 w,
  Simplify.pure_op op = true ->
  opt_op op = Some o ->
  Ops.op_res o k xs m1 = Some (OpRes (RVal w) m1) ->
  Ops.op_res o k xs m2 = Some (OpRes (RVal w) m2).
Proof.
  intros op o k xs m1 m2 w Hpure Hop Hres.
  pose proof (pure_op_cases op o Hpure Hop) as Hcase.
  destruct o; try contradiction Hcase; unfold Ops.op_res in *.
  - destruct (Ops.fmt_of k) as [f|].
    + destruct (Ops.float_arithmetic Add f xs); congruence.
    + unfold Ops.op_res_int in *. destruct (Ops.additive_res k Add xs); congruence.
  - destruct (Ops.fmt_of k) as [f|].
    + destruct (Ops.float_arithmetic Sub f xs); congruence.
    + unfold Ops.op_res_int in *. destruct (Ops.additive_res k Sub xs); congruence.
  - destruct (Ops.fmt_of k) as [f|].
    + destruct (Ops.float_arithmetic Mul f xs); congruence.
    + unfold Ops.op_res_int in *. destruct (Ops.alu Mul k xs); congruence.
  - destruct (Ops.fmt_of k); unfold Ops.op_res_int in *; destruct (Ops.alu And k xs); congruence.
  - destruct (Ops.fmt_of k); unfold Ops.op_res_int in *; destruct (Ops.alu Or k xs); congruence.
  - destruct (Ops.fmt_of k); unfold Ops.op_res_int in *; destruct (Ops.alu Xor k xs); congruence.
  - destruct (Ops.fmt_of k); unfold Ops.op_res_int in *; destruct (Ops.alu Sar k xs); congruence.
  - destruct (Ops.fmt_of k); unfold Ops.op_res_int in *; destruct (Ops.alu Shr k xs); congruence.
  - destruct (Ops.fmt_of k); unfold Ops.op_res_int in *; destruct (Ops.alu Shl k xs); congruence.
  - destruct (Ops.fmt_of k) as [f|].
    + destruct (Ops.float_arithmetic Neg f xs); congruence.
    + unfold Ops.op_res_int in *. destruct (Ops.alu Neg k xs); congruence.
  - destruct (Ops.fmt_of k) as [f|].
    + destruct (Ops.float_arithmetic Copy f xs); congruence.
    + unfold Ops.op_res_int in *. destruct (Ops.alu Copy k xs); congruence.
  - destruct (Ops.fmt_of k); unfold Ops.op_res_int in *; destruct (Ops.alu Ptoi k xs); congruence.
  - destruct (Ops.fmt_of k); unfold Ops.op_res_int in *; destruct (Ops.alu Itop k xs); congruence.
  - destruct (Ops.fmt_of k); unfold Ops.op_res_int in *; destruct (Ops.alu Select k xs); congruence.
  - destruct (Ops.fmt_of k), xs as [|[n1| |][|[n2| |][|]]];
      destruct (Ops.fmt_of k0); unfold Ops.op_res_int in *;
      try (destruct (Ops.alu (Cmp c k0) k _)); congruence.
  - destruct (Ops.fmt_of k); unfold Ops.op_res_int in *; destruct (Ops.alu (Ext t) k xs); congruence.
  - destruct (Ops.fmt_of k), xs as [|[n| |][|]]; try discriminate Hres;
      destruct (Ops.float_convert (ExtF k0) k n); congruence.
  - destruct (Ops.fmt_of k), xs as [|[n| |][|]]; try discriminate Hres;
      destruct (Ops.float_convert Truncd k n); congruence.
  - destruct (Ops.fmt_of k), xs as [|[n| |][|]]; try discriminate Hres;
      destruct (Ops.float_convert Truncx k n); congruence.
  - destruct (Ops.fmt_of k), xs as [|[n| |][|]]; try discriminate Hres;
      destruct (Ops.fmt_of k0) as [from|]; try discriminate Hres;
      unfold Ops.float_integer in *;
      destruct (Syntax.modulus k) as [mk|]; try discriminate Hres;
      destruct sg, (Ieee.ieee_to_int from n); try congruence;
      try (destruct ((- (mk / 2) <=? z) && (z <=? mk / 2 - 1)); congruence);
      try (destruct ((0 <=? z) && (z <=? mk - 1)); congruence).
  - destruct (Ops.fmt_of k) as [f|], xs as [|[n| |][|]]; try discriminate Hres;
      destruct (Ops.integer_source k0 sg n); congruence.
  - destruct (Ops.fmt_of k), xs as [|[n| |][|]]; unfold Ops.op_res_int in *; congruence.
  - destruct (Ops.fmt_of k), xs as [|[n| |][|]]; try discriminate Hres;
      destruct (Ops.float_convert Sqrt k n); congruence.
Qed.
