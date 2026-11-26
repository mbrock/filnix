(** The simplifier uses integer ranges to recognize addresses that differ by a
    constant. These proofs interpret its facts in the current environment and
    track the [[capability]] along with the address of each pointer. *)

From Stdlib Require Import String ZArith Znumtheory List Bool Lia.
From Nanofil Require Import Term Maps Syntax Values Memory Ops Semantics.
From Backend Require Import Order Pizlonate Escape.
From Opt Require Import OptIr Simplify OptAluProof.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** ## Signed ranges

    A word stores the residue of an integer modulo its width. A signed range
    describes the integer that the machine recovers from that residue. *)

Local Notation M32 := 4294967296.
Local Notation M64 := 18446744073709551616.
Local Notation H32 := 2147483648.

(** A signed word recovers any integer between the two signed limits. *)
Lemma signed_word_roundtrip z :
  -2147483648 <= z <= 2147483647 ->
  Ops.extension Sw (z mod M32) = z.
Proof.
  intro H. change (Ops.sign_extension M32 H32 (z mod M32) = z).
  unfold Ops.sign_extension. rewrite Z.mod_mod by lia.
  destruct (Z_lt_ge_dec z 0).
  - replace (z mod M32) with (z + M32).
    + destruct (Z.leb_spec H32 (z + M32)); lia.
    + apply Z.mod_unique with (-1); lia.
  - rewrite Z.mod_small by lia.
    destruct (Z.leb_spec H32 z); lia.
Qed.

(** Byte and halfword extensions produce exactly representable signed words. *)
Theorem narrow_range_sound t lo hi :
  Simplify.narrow_range t = Some (lo, hi) ->
  exists nt, opt_narrow t = Some nt /\ -2147483648 <= lo /\ hi <= 2147483647 /\
    forall x, let u := Ops.extension nt x mod 2 ^ 32 in
      0 <= u < 2 ^ 32 /\ Ops.signed W u = Some (Ops.extension nt x) /\
      lo <= Ops.extension nt x <= hi.
Proof.
  destruct t as [|a| |]; try discriminate. cbn [narrow_range].
  repeat match goal with
  | |- context [if String.eqb ?a ?b then _ else _] =>
      let E := fresh in destruct (String.eqb a b) eqn:E; [apply String.eqb_eq in E; subst a|]
  end; try discriminate; intro E; injection E as <- <-.
  all: eexists; split; [reflexivity|].
  all: split; [lia|]; split; [lia|]; intro x; split; [apply Z.mod_pos_bound; lia|].
  all: match goal with
  | |- _ /\ ?P => assert (R : P) by
      (cbn [Ops.extension]; unfold Ops.sign_extension;
       repeat match goal with
       | |- context [?v mod ?m] => pose proof (Z.mod_pos_bound v m ltac:(lia));
          remember (v mod m) as u; clear Hequ
       | |- context [if ?h <=? ?u then _ else _] => destruct (Z.leb_spec h u)
       end; lia)
  end.
  all: split; [unfold Ops.signed; cbn [modulus half_modulus]; f_equal; apply signed_word_roundtrip; lia|exact R].
Qed.

(** A logical shift removes at least one high bit from a word whenever its
    reduced count is positive. *)
Theorem offset_facts_shr_range_sound (x n : Z) :
  0 <= x < 2 ^ 32 -> 0 < n mod 32 ->
  let s := n mod 32 in let hi := Z.shiftl 1 (32 - s) - 1 in
  let r := x / 2 ^ s in 0 <= r <= hi /\ hi <= 2147483647 /\ Ops.signed W r = Some r.
Proof.
  intros X S. pose proof (Z.mod_pos_bound n 32 ltac:(lia)).
  set (s := n mod 32) in *. cbn zeta.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mul_1_l.
  assert (P : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  assert (Q : x / 2 ^ s < 2 ^ (32 - s)).
  { apply Z.div_lt_upper_bound; [lia|].
    rewrite <- Z.pow_add_r by lia. replace (s + (32 - s)) with 32 by lia. lia. }
  assert (R : 2 ^ (32 - s) <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ (32 - s) <= H32) in R.
  pose proof (Z.div_pos x (2 ^ s) ltac:(lia) ltac:(lia)).
  repeat split; try lia. unfold Ops.signed; cbn [modulus half_modulus]; f_equal.
  change (Ops.sign_extension M32 H32 (x / 2 ^ s) = x / 2 ^ s).
  unfold Ops.sign_extension. rewrite Z.mod_small by lia.
  destruct (Z.leb_spec H32 (x / 2 ^ s)); lia.
Qed.

(** Masking a nonnegative integer can only clear bits of the mask. *)
Lemma land_bounded_by_mask x m :
  0 <= x -> 0 <= m -> 0 <= Z.land x m <= m.
Proof.
  intros X M. rewrite <- (Z2N.id x X), <- (Z2N.id m M), <- N2Z.inj_land.
  split; [apply N2Z.is_nonneg|]. apply N2Z.inj_le. apply N.land_le_r.
Qed.

(** A mask below the sign bit bounds the signed value of the result. *)
Theorem offset_facts_and_range_sound (x n : Z) :
  0 <= x < 2 ^ 32 -> let m := n mod M32 in m < H32 ->
  0 <= Z.land x m <= m /\ m <= 2147483647 /\
  Ops.signed W (Z.land x m) = Some (Z.land x m).
Proof.
  intros X m M. assert (B : 0 <= m < M32) by (apply Z.mod_pos_bound; lia).
  pose proof (land_bounded_by_mask x m ltac:(lia) ltac:(lia)).
  repeat split; try lia. unfold Ops.signed; cbn [modulus half_modulus]; f_equal. change (Ops.sign_extension M32 H32 (Z.land x m) = Z.land x m).
  unfold Ops.sign_extension. rewrite Z.mod_small by lia. destruct (Z.leb_spec H32 (Z.land x m)); lia.
Qed.

(** Addition and subtraction store their offsets as unsigned word residues. *)
Theorem offset_facts_wsum_sound (y n : Z) :
  (y + n) mod M32 = (y + n mod M32) mod M32 /\
  (y - n) mod M32 = (y + (-n) mod M32) mod M32 /\
  0 <= n mod M32 < M32 /\ 0 <= (-n) mod M32 < M32.
Proof.
  rewrite !Zplus_mod_idemp_r. replace (y - n) with (y + - n) by ring.
  repeat split; try reflexivity; apply Z.mod_pos_bound; lia.
Qed.

(** ## Widening a word sum

    The unsigned check rules out a carry beyond bit 31. The signed check
    instead bounds the sum of the two signed representatives. *)

(** An unsigned extension distributes over addition within the word range. *)
Theorem ext_uw_nowrap_sound y sy lo hi c b :
  0 <= y < 2 ^ 32 -> Ops.signed W y = Some sy ->
  0 <= lo -> lo <= sy <= hi -> hi <= 2147483647 ->
  0 <= c < 2 ^ 32 -> hi + c <= 4294967295 -> b = (y + c) mod 2 ^ 32 ->
  Ops.extension Uw b mod 2 ^ 64 = (Ops.extension Uw y + c) mod 2 ^ 64.
Proof.
  intros Y E L R U C S ->. change (0 <= y < M32) in Y.
  change (Some (Ops.sign_extension M32 H32 y) = Some sy) in E. injection E as <-.
  unfold Ops.sign_extension in R. rewrite Z.mod_small in R by lia.
  destruct (Z.leb_spec H32 y); [lia|].
  cbn [Ops.extension]. change (0 <= c < M32) in C.
  change (((y+c) mod M32 mod M32) mod M64 = (y mod M32 + c) mod M64).
  rewrite Z.mod_mod by lia. rewrite (Z.mod_small y) by lia. rewrite Z.mod_small with (a:=y+c) by lia.
  reflexivity.
Qed.

(** A signed extension distributes over addition when both endpoints fit. *)
Theorem ext_sw_nowrap_sound y sy lo hi c0 b :
  0 <= y < 2 ^ 32 -> Ops.signed W y = Some sy -> lo <= sy <= hi ->
  0 <= c0 < 2 ^ 32 ->
  let s := if H32 <=? c0 then c0 - M32 else c0 in
  -2147483648 <= lo + s /\ hi + s <= 2147483647 ->
  b = (y + c0) mod 2 ^ 32 ->
  Ops.extension Sw b mod 2 ^ 64 = (Ops.extension Sw y + s mod 2 ^ 64) mod 2 ^ 64.
Proof.
  intros Y E R C s B ->. change (Some (Ops.extension Sw y) = Some sy) in E.
  assert (V : Ops.extension Sw y = sy) by congruence. clear E.
  rewrite V, Zplus_mod_idemp_r. f_equal.
  replace ((y + c0) mod 2 ^ 32) with ((sy + s) mod M32).
  - apply signed_word_roundtrip. lia.
  - change (0 <= y < M32) in Y. change (Ops.sign_extension M32 H32 y = sy) in V.
    unfold Ops.sign_extension in V. rewrite Z.mod_small in V by lia.
    subst sy. unfold s. destruct (H32 <=? y), (H32 <=? c0);
      try reflexivity;
      match goal with |- ?a mod _ = _ =>
        first [replace a with (y+c0 + -2*M32) by ring |
               replace a with (y+c0 + -1*M32) by ring] end;
      rewrite Z.mod_add by lia; reflexivity.
Qed.

(** ## Linear keys and their operands

    A linear key describes the part of an offset that can vary at run time.
    Each table entry relates that key or a word range to a value in the
    current environment. *)

(** An operand takes its value at the class chosen by the instruction. *)
Definition operand ge e k v :=
  let* a := opt_value v in value_x ge e k a.

(** The arithmetic evaluator reads each argument at its core operand class. *)
Definition eval_arith ge e k op args :=
  let* o := opt_op op in
  let* ks := Syntax.op_arg_classes o k in
  let* xs := map2_option (operand ge e) ks args in
  match o with
  | Add | Sub => Ops.additive_res k o xs
  | _ => Ops.alu o k xs
  end.

(** A temporary contributes its stored integer before operand truncation. *)
Definition read_int (e : env) t :=
  match lookup t e with Some (WInt x) => Some x | _ => None end.

(** The key computes an integer expression whose residue supplies the variable
    part of an address. An extension reads the low word of its operand. *)
Fixpoint eval_lin_key (e : env) (key : term) : option Z :=
  match key with
  | TApp f [t] => if String.eqb f "v" then read_int e t else None
  | TApp f [k; a] =>
      if String.eqb f "ext" then
        let* nt := opt_narrow k in let* x := read_int e a in
        match nt with Uw | Sw => Some (Ops.extension nt x) | _ => None end
      else match a with
      | TInt n =>
          let* v := eval_lin_key e k in
          if String.eqb f "shl" then Some (Z.shiftl v n)
          else if String.eqb f "mul" then Some (v * n) else None
      | _ => None
      end
  | _ => None
  end.

(** A range bounds the signed interpretation of the low word of a temporary. *)
Definition range_holds e t lo hi :=
  exists x sy, read_int e t = Some x /\ Ops.signed W (x mod M32) = Some sy /\
    lo <= sy <= hi /\ hi <= 2147483647.

(** The four tables describe linear offsets, signed intervals, narrow
    definitions, and sums that wrap at the word boundary. *)
Record lin_defs_ok (e : env) (defs : simp_defs) : Prop := {
  lin_entry : forall t key c, nm_find t (sd_lin defs) = Some (key,c) ->
    exists x v, read_int e t = Some x /\ eval_lin_key e key = Some v /\
      0 <= c < M64 /\ x mod M64 = (v+c) mod M64;
  range_entry : forall t lo hi, nm_find t (sd_range defs) = Some (lo,hi) ->
    range_holds e t lo hi;
  narrow_entry : forall t ty lo hi, nm_find t (sd_main defs) = Some (DefNarrow ty) ->
    narrow_range ty = Some (lo,hi) -> range_holds e t lo hi;
  sum_entry : forall t y c, nm_find t (sd_wsum defs) = Some (y,c) ->
    exists x b, read_int e y = Some x /\ read_int e t = Some b /\
      0 <= c < M32 /\ b mod M32 = (x mod M32 + c) mod M32
}.

(** The range lookup can consult either the explicit interval or the narrow
    type attached to a definition. *)
Lemma range_of_sound e defs t lo hi :
  lin_defs_ok e defs -> range_of defs t = Some (lo,hi) -> range_holds e t lo hi.
Proof.
  intros D. unfold range_of. destruct (nm_find t (sd_range defs)) eqn:R.
  - intro E. rewrite E in R. eapply range_entry; eauto.
  - destruct (nm_find t (sd_main defs)) as [[c k a b|b|ty]|] eqn:N; try discriminate.
    eapply narrow_entry; eauto.
Qed.

(** A temporary with no linear entry serves as its own key with offset zero. *)
Lemma lin_of_sound e defs t key c x :
  lin_defs_ok e defs -> read_int e t = Some x -> lin_of defs t = (key,c) ->
  0 <= c < M64 /\ exists v, eval_lin_key e key = Some v /\ x mod M64 = (v+c) mod M64.
Proof.
  intros D V. unfold lin_of. destruct (nm_find t (sd_lin defs)) as [[k n]|] eqn:E.
  - intro H. injection H as -> ->.
    destruct (lin_entry _ _ D _ _ _ E) as (u & v & U & K & B & F).
    rewrite V in U. injection U as <-. split; [exact B|]. exists v. auto.
  - intro H. injection H as <- <-. split; [lia|]. exists x. rewrite Z.add_0_r. split; [exact V|reflexivity].
Qed.

(** The temporary recognizer returns the unique name in a temporary operand. *)
Lemma tmp_name_inv v t : tmp_name v = [t] -> v = tmp t.
Proof.
  destruct v as [| |f [|a [|b xs]]|]; try discriminate.
  cbn [tmp_name]. destruct (String.eqb f "tmp") eqn:E; try discriminate.
  apply String.eqb_eq in E. subst. intro H. injection H as ->. reflexivity.
Qed.

(** The constant recognizer returns the literal stored in the operand. *)
Lemma const_int_inv v n : const_int v = Some n -> v = TApp "const" [TInt n].
Proof.
  destruct v as [| |f [|a xs]|]; try discriminate.
  destruct a; try discriminate. destruct xs; try discriminate. cbn [const_int].
  destruct (String.eqb f "const") eqn:E; try discriminate.
  apply String.eqb_eq in E. subst. intro H. injection H as ->. reflexivity.
Qed.

(** The low six shift bits survive truncation to a word. *)
Lemma shift_count_word n : n mod M32 mod 64 = n mod 64.
Proof. symmetry. apply Zmod_div_mod; try lia. exists 67108864. reflexivity. Qed.

Ltac reduce_arith :=
  cbn [eval_arith opt_op opt_narrow Syntax.op_arg_classes map2_option operand opt_value
       value_x word_at_class Ops.additive_res Ops.alu Ops.shift_factor
       modulus Syntax.class_bits tmp String.eqb Ascii.eqb Bool.eqb].

Ltac strip_mod :=
  repeat first [rewrite Zplus_mod_idemp_l | rewrite Zplus_mod_idemp_r |
    rewrite Zminus_mod_idemp_l | rewrite Zminus_mod_idemp_r |
    rewrite Zmult_mod_idemp_l | rewrite Zmult_mod_idemp_r | rewrite Z.mod_mod by lia].

(** Each binary linear operation distributes its action over the variable
    part and the constant part of the input. *)
Lemma lin_binary_sound ge e defs a t n key c r :
  lin_defs_ok e defs ->
  lin_op (TAtom a) [tmp t; TApp "const" [TInt n]] defs = Some (key,c) ->
  eval_arith ge e L (TAtom a) [tmp t; TApp "const" [TInt n]] = Some (WInt r) ->
  0 <= c < M64 /\ exists v, eval_lin_key e key = Some v /\ r = (v+c) mod M64.
Proof.
  intros D. cbn [lin_op tmp_name const_int tmp String.eqb Ascii.eqb Bool.eqb].
  destruct (lin_of defs t) as [k d] eqn:F.
  repeat match goal with
  | |- context [if String.eqb ?u ?s then _ else _] =>
      let E := fresh in destruct (String.eqb u s) eqn:E;
        [apply String.eqb_eq in E; subst u|]
  end; try discriminate.
  all: try (destruct (0 <? n mod 64) eqn:S; [|discriminate]).
  all: intro Form; injection Form as <- <-; reduce_arith;
    destruct (lookup t e) as [[x|p|cap size]|] eqn:X; try discriminate.
  all: intro Run; injection Run as <-.
  all: assert (V : read_int e t = Some x) by (unfold read_int; rewrite X; reflexivity).
  all: destruct (lin_of_sound _ _ _ _ _ _ D V F) as (B & v & K & R).
  all: split; [apply Z.mod_pos_bound; lia|].
  all: change (Z.pow_pos 2 64) with M64; change (Z.pow_pos 2 32) with M32.
  - exists v. split; [exact K|].
    rewrite R. strip_mod. f_equal. ring.
  - exists v. split; [exact K|].
    rewrite R. strip_mod. f_equal. ring.
  - exists (Z.shiftl v (n mod 64)). split.
    + cbn [eval_lin_key String.eqb Ascii.eqb Bool.eqb]. rewrite K. reflexivity.
    + pose proof (Z.mod_pos_bound n 64 ltac:(lia)).
      rewrite shift_count_word, R, !Z.shiftl_mul_pow2 by lia.
      strip_mod. f_equal. ring.
  - exists (v * (n mod M64)). split.
    + cbn [eval_lin_key String.eqb Ascii.eqb Bool.eqb]. rewrite K. reflexivity.
    + rewrite R.
      rewrite Zmult_mod_idemp_l, Zplus_mod_idemp_r. f_equal. ring.
Qed.

(** Widening an unsigned or signed sum uses the recorded interval exactly
    when the corresponding overflow check succeeds. *)
Lemma lin_extension_sound ge e defs ty b key c r :
  lin_defs_ok e defs ->
  lin_op (TApp "ext" [ty]) [tmp b] defs = Some (key,c) ->
  eval_arith ge e L (TApp "ext" [ty]) [tmp b] = Some (WInt r) ->
  0 <= c < M64 /\ exists v, eval_lin_key e key = Some v /\ r = (v+c) mod M64.
Proof.
  intro D. destruct ty as [|a| |]; try discriminate.
  cbn [lin_op tmp tmp_name is_atom].
  destruct (String.eqb "uw" a) eqn:U;
    [apply String.eqb_eq in U; subst a|
     destruct (String.eqb "sw" a) eqn:S; [apply String.eqb_eq in S; subst a|discriminate]].
  all: intros F Run; revert Run; reduce_arith;
    destruct (lookup b e) as [[x|p|cap size]|] eqn:X; try discriminate;
    intro Run; injection Run as <-.
  all: assert (V : read_int e b = Some x) by (unfold read_int; rewrite X; reflexivity).
  all: cbn [String.eqb Ascii.eqb Bool.eqb] in F.
  all: destruct (nm_find b (sd_wsum defs)) as [[y d]|] eqn:Sum;
    try (destruct (range_of defs y) as [[lo hi]|] eqn:Range);
    repeat match type of F with context [if ?test && ?test' then _ else _] =>
      destruct (test && test') eqn:Guard end.
  all: injection F as <- <-.
  all: try (split; [lia|]; eexists; split;
    [cbn [eval_lin_key opt_narrow String.eqb Ascii.eqb Bool.eqb]; rewrite V; reflexivity|
     rewrite Z.add_0_r; f_equal; cbn [Ops.extension]; unfold Ops.sign_extension; change (Z.pow_pos 2 32) with M32;
       change (2^32) with M32; rewrite Z.mod_mod by lia; reflexivity]).
  all: destruct (sum_entry _ _ D _ _ _ Sum) as (u & z & Y & Zx & C & B);
    rewrite V in Zx; injection Zx as <-;
    destruct (range_of_sound _ _ _ _ _ D Range) as (q & sy & Q & Sg & R & Hi);
    rewrite Y in Q; injection Q as <-; apply andb_true_iff in Guard;
    destruct Guard as [Low High]; apply Z.leb_le in Low; apply Z.leb_le in High.
  - split; [lia|]. exists (Ops.extension Uw u). split.
    + cbn [eval_lin_key opt_narrow String.eqb Ascii.eqb Bool.eqb]. rewrite Y. reflexivity.
    + change (Ops.extension Uw (x mod M32) mod M64 = (Ops.extension Uw u + d) mod M64).
      replace (Ops.extension Uw u) with (Ops.extension Uw (u mod M32))
        by (cbn [Ops.extension]; change (2^32) with M32; apply Z.mod_mod; lia).
      eapply ext_uw_nowrap_sound; eauto; apply Z.mod_pos_bound; lia.
  - split; [apply Z.mod_pos_bound; lia|]. exists (Ops.extension Sw u). split.
    + cbn [eval_lin_key opt_narrow String.eqb Ascii.eqb Bool.eqb]. rewrite Y. reflexivity.
    + replace (Ops.extension Sw u) with (Ops.extension Sw (u mod M32)) by
        (cbn [Ops.extension]; unfold Ops.sign_extension; change (2^32) with M32;
         rewrite Z.mod_mod by lia; reflexivity).
      eapply ext_sw_nowrap_sound; eauto; first [apply Z.mod_pos_bound; lia|split; assumption].
Qed.

(** Every recognized linear operation evaluates to the residue of its key plus
    its stored offset. The offset itself is a canonical 64-bit residue. *)
Theorem lin_op_sound ge e defs op args key c r :
  lin_defs_ok e defs -> lin_op op args defs = Some (key,c) ->
  eval_arith ge e L op args = Some (WInt r) ->
  0 <= c < M64 /\ exists v, eval_lin_key e key = Some v /\ r = (v+c) mod M64.
Proof.
  intro D. destruct op as [|a|f ts|]; try discriminate.
  - destruct args as [|v [|vn [|extra rest]]]; try discriminate.
    cbn [lin_op]. destruct (tmp_name v) as [|t [|u us]] eqn:T; try discriminate.
    destruct (const_int vn) as [n|] eqn:N; try discriminate.
    apply tmp_name_inv in T. apply const_int_inv in N. subst v vn.
    apply (lin_binary_sound _ _ _ _ _ _ _ _ _ D).
  - destruct ts as [|ty [|u us]]; try discriminate.
    destruct args as [|v [|u us]]; try discriminate. cbn [lin_op].
    destruct (String.eqb f "ext") eqn:F; try discriminate.
    destruct (tmp_name v) as [|b [|u us]] eqn:T; try discriminate.
    apply String.eqb_eq in F. apply tmp_name_inv in T. subst.
    apply (lin_extension_sound _ _ _ _ _ _ _ _ D).
Qed.

(** A fresh binding preserves every successful integer read. *)
Lemma read_int_fresh e d w t x :
  lookup d e = None -> read_int e t = Some x -> read_int (put d w e) t = Some x.
Proof.
  intros Fresh. unfold read_int. rewrite lookup_put_name.
  destruct (name_eqb t d) eqn:E; [apply term_eqb_eq in E; subst; rewrite Fresh|];
    congruence.
Qed.

(** Evaluating a key reads only names already present in the environment. *)
Lemma key_fresh e d w : lookup d e = None -> forall key v,
  eval_lin_key e key = Some v -> eval_lin_key (put d w e) key = Some v.
Proof.
  intro Fresh. fix IH 1. intros key v.
  destruct key as [| |f [|k [|a [|u us]]]|]; try discriminate.
  - cbn [eval_lin_key]. destruct (String.eqb f "v"); try discriminate.
    apply read_int_fresh; assumption.
  - cbn [eval_lin_key]. destruct (String.eqb f "ext").
    + destruct (opt_narrow k) as [nt|]; try discriminate.
      destruct (read_int e a) eqn:E; try discriminate.
      rewrite (read_int_fresh _ _ _ _ _ Fresh E). trivial.
    + destruct a; try discriminate. destruct (eval_lin_key e k) eqn:E; try discriminate.
      rewrite (IH _ _ E). trivial.
Qed.

(** All existing facts survive the binding of a fresh SSA destination. *)
Lemma defs_fresh e defs d w : lookup d e = None -> lin_defs_ok e defs ->
  lin_defs_ok (put d w e) defs.
Proof.
  intros F D. constructor.
  - intros t k c H. destruct (lin_entry _ _ D _ _ _ H) as (x & v & X & K & C & E).
    exists x, v. repeat split; eauto using read_int_fresh, key_fresh; lia.
  - intros t lo hi H. destruct (range_entry _ _ D _ _ _ H) as (x & s & X & S & R).
    exists x, s. split; eauto using read_int_fresh.
  - intros t ty lo hi H N. destruct (narrow_entry _ _ D _ _ _ _ H N) as (x & s & X & S & R).
    exists x, s. split; eauto using read_int_fresh.
  - intros t y c H. destruct (sum_entry _ _ D _ _ _ H) as (x & b & X & B & C & E).
    exists x, b. repeat split; eauto using read_int_fresh; lia.
Qed.

(** An integer read at word class always yields a canonical word residue. *)
Lemma operand_word_bound ge e v x :
  operand ge e W v = Some (WInt x) -> 0 <= x < M32.
Proof.
  unfold operand. destruct (opt_value v) as [[t|n|g]|]; try discriminate;
    cbn [value_x modulus].
  - destruct (lookup t e) as [[u|p|c s]|]; try discriminate.
    intro H. injection H as <-. apply Z.mod_pos_bound; lia.
  - intro H. injection H as <-. apply Z.mod_pos_bound; lia.
  - destruct (lookup g (ge_globals ge)); discriminate.
Qed.

Ltac keep_entries D :=
  constructor; cbn [sd_lin sd_range sd_wsum sd_main];
    first [apply (lin_entry _ _ D) | apply (range_entry _ _ D) |
           apply (narrow_entry _ _ D) | apply (sum_entry _ _ D) | idtac].

Ltac added_entry D :=
  let t := fresh "dest" in let u := fresh "first" in let v := fresh "second" in
  intros t u v H; rewrite nm_find_add in H;
  destruct (name_eqb t _) eqn:Same;
    [apply term_eqb_eq in Same; subst t; injection H as <- <- |
     first [eapply lin_entry | eapply range_entry | eapply sum_entry]; eauto].

(** Recording an evaluated instruction preserves all four tables. Freshness
    ensures that the destination cannot change any operand used by an old fact. *)
Theorem offset_facts_preserves_lin_defs_ok ge e defs d kt k op args w :
  lin_defs_ok e defs -> lookup d e = None -> opt_class kt = Some k ->
  eval_arith ge e k op args = Some w ->
  lin_defs_ok (put d w e) (offset_facts d kt op args defs).
Proof.
  intros D Fresh Class Run. pose proof (defs_fresh _ _ _ w Fresh D) as Old.
  unfold offset_facts. destruct (is_atom "l" kt) eqn:L.
  - destruct kt; try discriminate. apply String.eqb_eq in L. subst.
    injection Class as <-. destruct (lin_op op args defs) as [[key c]|] eqn:Form; [|exact Old].
    assert (Int : exists r, w = WInt r).
    { unfold eval_arith in Run. destruct (opt_op op) as [o|] eqn:Decode; try discriminate.
      destruct (Syntax.op_arg_classes o Syntax.L) as [ks|]; try discriminate.
      destruct (map2_option (operand ge e) ks args) as [xs|]; try discriminate.
      destruct op as [|a|f ts|]; try discriminate;
        destruct args as [|v [|vn [|u us]]]; try discriminate.
      all: cbn [lin_op] in Form.
      all: repeat match type of Form with
      | context [match ?x with _ => _ end] => destruct x eqn:?; try discriminate
      end.
      all: repeat match goal with E : String.eqb _ _ = true |- _ =>
        apply String.eqb_eq in E; subst end.
      all: repeat match goal with E : is_atom _ ?ty = true |- _ => destruct ty; try discriminate;
        apply String.eqb_eq in E; subst end.
      all: cbn [opt_op opt_narrow String.eqb Ascii.eqb Bool.eqb] in Decode;
        injection Decode as <-; destruct xs as [|[x| |] [|[y| |] [|extra tail]]]; try discriminate;
        cbn [Ops.additive_res Ops.alu modulus Ops.shift_factor Syntax.class_bits] in Run;
        injection Run as <-; eauto. }
    destruct Int as [r ->]. destruct (lin_op_sound _ _ _ _ _ _ _ _ D Form Run)
      as (C & v & K & E).
    keep_entries Old. added_entry Old. exists r, v.
    split; [unfold read_int; rewrite lookup_put_name, term_eqb_refl; reflexivity|].
    split; [eapply key_fresh; eauto|]. split; [exact C|]. rewrite E, Z.mod_mod by lia. reflexivity.
  - destruct (is_atom "w" kt) eqn:Wc; [|exact Old].
    destruct kt; try discriminate. apply String.eqb_eq in Wc. subst. injection Class as <-.
    destruct op as [|a| |]; try exact Old.
    destruct args as [|v [|vn [|u us]]]; try exact Old.
    destruct (const_int vn) as [n|] eqn:N; [|exact Old]. apply const_int_inv in N. subst vn.
    destruct (String.eqb a "shr") eqn:Sh.
    + destruct (0 <? n mod 32) eqn:S; [|exact Old]. apply String.eqb_eq in Sh. subst a.
      revert Run. reduce_arith. destruct (operand ge e W v) as [[x|p|cap size]|] eqn:V;
        try discriminate. intro Run. injection Run as <-.
      pose proof (operand_word_bound _ _ _ _ V) as X.
      apply Z.ltb_lt in S. destruct (offset_facts_shr_range_sound _ _ X S) as (R & Hi & Signed).
      keep_entries Old. added_entry Old.
      change (Z.pow_pos 2 32) with M32 in *.
      assert (Count : n mod M32 mod 32 = n mod 32) by
        (symmetry; apply Zmod_div_mod; try lia; exists 134217728; reflexivity).
      rewrite Count. exists (x / 2 ^ (n mod 32)), (x / 2 ^ (n mod 32)).
      split; [unfold read_int; rewrite lookup_put_name, term_eqb_refl; reflexivity|].
      rewrite Z.mod_small by lia. auto.
    + destruct (String.eqb a "and") eqn:And.
      * destruct (n mod M32 <? H32) eqn:M; [|exact Old]. apply String.eqb_eq in And. subst a.
        revert Run. reduce_arith. destruct (operand ge e W v) as [[x|p|cap size]|] eqn:V;
          try discriminate. intro Run. injection Run as <-.
        pose proof (operand_word_bound _ _ _ _ V) as X. apply Z.ltb_lt in M.
        destruct (offset_facts_and_range_sound _ _ X M) as (R & Hi & Signed).
        keep_entries Old. added_entry Old. set (z := Z.land x (n mod M32)) in *.
        exists z, z. split; [unfold read_int; rewrite lookup_put_name, term_eqb_refl; reflexivity|].
        rewrite Z.mod_small by lia. auto.
      * destruct (String.eqb a "add") eqn:Add;
          [apply String.eqb_eq in Add; subst a|
           destruct (String.eqb a "sub") eqn:Sub; [apply String.eqb_eq in Sub; subst a|exact Old]].
        all: destruct (tmp_name v) as [|y [|u us]] eqn:T; try exact Old;
          apply tmp_name_inv in T; subst v; revert Run; reduce_arith;
          destruct (lookup y e) as [[x|p|cap size]|] eqn:Y; try discriminate; intro Run; injection Run as <-.
        all: keep_entries Old; added_entry Old; eexists x, _;
          split; [eapply read_int_fresh; [exact Fresh|unfold read_int; rewrite Y; reflexivity]|];
          split; [unfold read_int; rewrite lookup_put_name, term_eqb_refl; reflexivity|];
          split; [apply Z.mod_pos_bound; lia|]; change (Z.pow_pos 2 32) with M32;
          strip_mod; f_equal; ring.
Qed.

(** ## Value numbering and address rebasing

    Value numbering sorts operands only for commutative integer operations.
    An address anchor also records the block, the base pointer, and the
    variable part of the offset. *)

(** Equal keys identify the same class and operation and agree on the
    operand list after any permitted sorting. *)
Theorem numbered_key_sound kt op args lbl kt' op' args' lbl' key1 key2 :
  numbered_key kt op args lbl = Some key1 ->
  numbered_key kt' op' args' lbl' = Some key2 -> key1 = key2 ->
  kt = kt' /\ op = op' /\ (args = args' \/
    (commutative_op op = true /\ is_int_class kt = true /\
     msort term_compare args = msort term_compare args')).
Proof.
  unfold numbered_key. destruct (pure_op op && negb (is_atom "copy" op)); try discriminate.
  destruct (pure_op op' && negb (is_atom "copy" op')); try discriminate.
  intros E F. injection E as <-. injection F as <-. intro H. injection H as -> -> H.
  split; [reflexivity|]. split; [reflexivity|].
  destruct (is_atom "p" kt' && existsb is_const_term args),
    (is_atom "p" kt' && existsb is_const_term args') in H; try discriminate;
    injection H as H.
  all: destruct (commutative_op op' && is_int_class kt') eqn:C; [right|left; exact H].
  all: apply andb_true_iff in C; tauto.
Qed.

(** Sorting two operands can only exchange their positions. *)
Lemma numbered_pair_order a b a' b' :
  msort term_compare [a;b] = msort term_compare [a';b'] ->
  (a = a' /\ b = b') \/ (a = b' /\ b = a').
Proof.
  cbn [msort fold_left push_run merge_runs merge length Nat.add merge_steps].
  destruct (term_compare a b), (term_compare a' b'); cbn [merge_steps length Nat.add];
    intro H; injection H as H1 H2; auto.
Qed.

(** The integer evaluator returns the same word for either order of a
    commutative pair, including when an operand has the wrong word shape. *)
Lemma commutative_alu op o k x y :
  commutative_op op = true -> opt_op op = Some o ->
  Ops.alu o k [x;y] = Ops.alu o k [y;x].
Proof.
  destruct op as [|a| |]; try discriminate. cbn [commutative_op].
  intro C. repeat rewrite orb_true_iff in C.
  repeat match goal with H : _ \/ _ |- _ => destruct H end;
    match goal with E : String.eqb _ _ = true |- _ => apply String.eqb_eq in E; subst a end;
    intro E; injection E as <-;
    destruct x as [x| |], y as [y| |]; try reflexivity; cbn [Ops.alu];
    first [rewrite Z.add_comm | rewrite Z.mul_comm | rewrite Z.land_comm |
           rewrite Z.lor_comm | rewrite Z.lxor_comm]; reflexivity.
Qed.

(** Equal binary keys give the same arithmetic result when the evaluator
    reads both original operand lists. The keys can identify different
    operand orders only when the operation permits the exchange. *)
Corollary numbered_pair_sound ge e kt kt' op op' a b a' b' lbl lbl' key k :
  numbered_key kt op [a;b] lbl = Some key ->
  numbered_key kt' op' [a';b'] lbl' = Some key ->
  opt_class kt = Some k ->
  ((a = a' /\ b = b') \/ (a = b' /\ b = a')) /\
  eval_arith ge e k op [a;b] = eval_arith ge e k op' [a';b'].
Proof.
  intros K K' Class.
  destruct (numbered_key_sound _ _ _ _ _ _ _ _ _ _ K K' eq_refl)
    as (_ & <- & [Same | (Comm & Int & Sorted)]).
  - injection Same as -> ->. auto.
  - destruct (numbered_pair_order _ _ _ _ Sorted) as [[-> ->]|[-> ->]]; [auto|].
    split; [auto|]. apply is_int_class_iff in Int.
    destruct op as [|s| |]; try discriminate. cbn [commutative_op] in Comm.
    repeat rewrite orb_true_iff in Comm.
    repeat match goal with H : _ \/ _ |- _ => destruct H end;
      match goal with E : String.eqb _ _ = true |- _ => apply String.eqb_eq in E; subst s end;
      subst kt; injection Class as <-; unfold eval_arith;
      cbn [opt_op Syntax.op_arg_classes map2_option String.eqb Ascii.eqb Bool.eqb];
      match goal with |- context [operand ge e ?k a'] =>
        destruct (operand ge e k a'), (operand ge e k b') end; try reflexivity;
      match type of K with numbered_key _ ?op _ _ = _ =>
        apply (commutative_alu op); reflexivity end.
Qed.

(** The core evaluator supplies the semantics of pure operations, including
    floating-point arithmetic and conversions. *)
Definition eval_pure ge e k op args m :=
  let* o := opt_op op in let* ks := Syntax.op_arg_classes o k in
  let* xs := map2_option (operand ge e) ks args in Ops.op_res o k xs m.

(** Moving along an address family changes its address and carries the
    exact Fil-C [[capability]] of the original pointer. *)
Definition family_ptr pw v c :=
  mkPtr ((ptr_addr pw + v + c) mod M64) (ptr_cap pw).

(** Every numbered expression has the stored result in the current
    environment. Each anchor names a pointer in the stated address family. *)
Record avail_ok ge e lbl avail : Prop := {
  numbered_entry : forall kt k op args key d,
    opt_class kt = Some k -> numbered_key kt op args lbl = Some key ->
    nm_find key (sa_num avail) = Some d ->
    exists w, lookup d e = Some w /\
      forall m, eval_pure ge e k op args m = Some (OpRes (RVal w) m);
  anchor_entry : forall p key b c0,
    nm_find (TApp "based" [lbl;p;key]) (sa_based avail) = Some (b,c0) ->
    exists pw v, lookup p e = Some (WPtr pw) /\ eval_lin_key e key = Some v /\
      lookup b e = Some (WPtr (family_ptr pw v c0))
}.

(** A pointer arithmetic hit in the numbering table yields the computed word. *)
Lemma numbered_pointer_hit ge e lbl avail op args target d :
  avail_ok ge e lbl avail -> (op = TAtom "add" \/ op = TAtom "sub") ->
  (let* key := numbered_key (TAtom "p") op args lbl in nm_find key (sa_num avail)) = Some d ->
  eval_arith ge e P op args = Some target -> lookup d e = Some target.
Proof.
  intros A Kind. destruct (numbered_key (TAtom "p") op args lbl) eqn:K; try discriminate.
  intros Hit Run. destruct (numbered_entry _ _ _ _ A (TAtom "p") P _ _ _ _ eq_refl K Hit) as (w & V & All).
  specialize (All (mkMem (fun _ => 0) [] (fun _ => CNone))).
  destruct Kind as [-> | ->]; unfold eval_pure in All; unfold eval_arith in Run;
    cbn [opt_op Syntax.op_arg_classes String.eqb Ascii.eqb Bool.eqb] in All, Run;
    destruct (map2_option (operand ge e) [P;L] args) as [xs|]; try discriminate;
    destruct xs as [|[x|p|] [|[y| |] [|u us]]]; try discriminate;
    injection Run as <-; injection All as <-; exact V.
Qed.

(** A forward distance and its backward complement reach the same residue. *)
Lemma anchor_distance a c0 c :
  let dist := (c-c0) mod M64 in
  ((a+c0) mod M64 + dist) mod M64 = (a+c) mod M64 /\
  ((a+c0) mod M64 - (M64-dist) mod M64) mod M64 = (a+c) mod M64.
Proof.
  cbn zeta. split.
  - strip_mod. f_equal. ring.
  - rewrite Zminus_mod_idemp_r, Zminus_mod_idemp_l.
    replace (a+c0-(M64-(c-c0) mod M64)) with ((a+c0+(c-c0) mod M64) + (-1)*M64) by ring.
    rewrite Z.mod_add by lia. strip_mod. f_equal. ring.
Qed.

(** Reusing a numbered result, returning an anchor, and emitting a new
    pointer operation all preserve the address and the original capability.
    The offset operand must hold an integer when the source executes. *)
Theorem rebased_op_sound ge e lbl avail classes defs p t pw x bk c :
  avail_ok ge e lbl avail -> lin_defs_ok e defs ->
  lookup p e = Some (WPtr pw) -> read_int e t = Some x ->
  based_addr (TAtom "p") (TAtom "add") [tmp p;tmp t] lbl classes defs = Some (bk,c) ->
  exists key v, bk = TApp "based" [lbl;p;key] /\ eval_lin_key e key = Some v /\
    match rebased_op (TAtom "p") (TAtom "add") [tmp p;tmp t] lbl (Some (bk,c)) avail with
    | FoundSame d => lookup d e = Some (WPtr (family_ptr pw v c))
    | FoundOp op args => eval_arith ge e P op args = Some (WPtr (family_ptr pw v c))
    end.
Proof.
  intros A D Pval X.
  unfold based_addr. change (is_atom "p" (TAtom "p") && is_atom "add" (TAtom "add")) with true.
  change (tmp_name (tmp p)) with [p]. change (tmp_name (tmp t)) with [t]. cbn iota.
  destruct (nm_find t classes) as [kt|]; try discriminate.
  destruct (is_atom "l" kt); try discriminate.
  destruct (lin_of defs t) as [key n] eqn:F. intro B. injection B as <- <-.
  destruct (lin_of_sound _ _ _ _ _ _ D X F) as (C & v & V & Form).
  exists key, v. split; [reflexivity|]. split; [exact V|].
  assert (Source : eval_arith ge e P (TAtom "add") [tmp p;tmp t] = Some (WPtr (family_ptr pw v n))).
  { unfold read_int in X. destruct (lookup t e) as [[z| |]|] eqn:T; try discriminate.
    injection X as <-. reduce_arith. rewrite Pval, T. unfold family_ptr.
    change (2^64) with M64. rewrite Form. strip_mod. rewrite Z.add_assoc. reflexivity. }
  unfold rebased_op.
  destruct (let* k := numbered_key (TAtom "p") (TAtom "add") [tmp p;tmp t] lbl in
            nm_find k (sa_num avail)) eqn:Hit.
  - eapply (numbered_pointer_hit ge e lbl avail (TAtom "add") [tmp p;tmp t]); [exact A| |exact Hit|exact Source]. auto.
  - cbv beta iota zeta. match goal with |- context [match ?entry with Some _ => _ | None => _ end] =>
      destruct entry as [[b c0]|] eqn:Anchor end; [|exact Source].
    destruct (anchor_entry _ _ _ _ A _ _ _ _ Anchor) as (q & u & Q & U & Addr).
    rewrite Pval in Q. injection Q as <-. rewrite V in U. injection U as <-.
    destruct (anchor_distance (ptr_addr pw + v) c0 n) as [Forward Backward].
    set (dist := (n-c0) mod M64) in *. destruct (dist =? 0) eqn:Zero.
    + apply Z.eqb_eq in Zero. rewrite Zero, Z.add_0_r, Z.mod_mod in Forward by lia.
      unfold family_ptr in *. rewrite Forward in Addr. exact Addr.
    + destruct (dist <? 9223372036854775808).
      * assert (Run : eval_arith ge e P (TAtom "add") [tmp b; TApp "const" [TInt dist]] =
            Some (WPtr (family_ptr pw v n))).
        { reduce_arith. rewrite Addr. unfold family_ptr. cbn [ptr_addr ptr_cap].
          change (2^64) with M64. rewrite Zplus_mod_idemp_r, Forward. reflexivity. }
        destruct (let* k := numbered_key (TAtom "p") (TAtom "add")
          [tmp b; TApp "const" [TInt dist]] lbl in nm_find k (sa_num avail)) eqn:New;
          [eapply (numbered_pointer_hit ge e lbl avail (TAtom "add") [tmp b; TApp "const" [TInt dist]]); [exact A| |exact New|exact Run]; auto|exact Run].
      * assert (Run : eval_arith ge e P (TAtom "sub") [tmp b; TApp "const" [TInt (M64-dist)]] =
            Some (WPtr (family_ptr pw v n))).
        { reduce_arith. rewrite Addr. unfold family_ptr. cbn [ptr_addr ptr_cap].
          change (2^64) with M64. rewrite Backward. reflexivity. }
        destruct (let* k := numbered_key (TAtom "p") (TAtom "sub")
          [tmp b; TApp "const" [TInt (M64-dist)]] lbl in nm_find k (sa_num avail)) eqn:New;
          [eapply (numbered_pointer_hit ge e lbl avail (TAtom "sub") [tmp b; TApp "const" [TInt (M64-dist)]]); [exact A| |exact New|exact Run]; auto|exact Run].
Qed.

(** ## Boolean values

    A branch can use a temporary as a boolean when its stored word is zero
    or one. Integer extension preserves both words, whereas floating-point
    widening interprets their bits in the source format. *)

(** Each name in the boolean table holds one of the two integer words. *)
Definition bools_ok (e : env) (bools : nmap (list (term * term))) :=
  forall t eqs, nm_find t bools = Some eqs ->
    lookup t e = Some (WInt 0) \/ lookup t e = Some (WInt 1).

(** Whenever a recognized boolean operand supplies an integer word, the
    operand class preserves its value of zero or one. *)
Lemma boolean_operand ge e bools v k x :
  bools_ok e bools -> is_boolean bools v = true ->
  operand ge e k v = Some (WInt x) -> x = 0 \/ x = 1.
Proof.
  intros B. unfold is_boolean. destruct (const_int v) as [n|] eqn:N.
  - apply const_int_inv in N. subst. intro E. apply orb_true_iff in E.
    destruct E as [E|E]; apply Z.eqb_eq in E; subst; destruct k; intro X;
      try discriminate; injection X as <-; auto.
  - destruct (tmp_name v) as [|t [|u us]] eqn:T; try discriminate.
    apply tmp_name_inv in T. subst v. unfold nm_mem.
    destruct (nm_find t bools) eqn:F; try discriminate. intros _.
    destruct (B _ _ F) as [X|X]; destruct k;
      cbn [operand opt_value tmp String.eqb Ascii.eqb Bool.eqb value_x]; rewrite X;
      intro E; injection E as <-; auto.
Qed.

(** Both integer and floating-point comparisons return a bit on success. *)
Lemma comparison_bit c ck k xs m w :
  Ops.op_res (Cmp c ck) k xs m = Some (OpRes (RVal w) m) ->
  w = WInt 0 \/ w = WInt 1.
Proof.
  destruct xs as [|[a| |] [|[b| |] [|u us]]]; cbn [Ops.op_res];
    destruct (fmt_of ck) as [f|]; try discriminate.
  - intro E. injection E as <-. unfold float_compare.
    destruct (fcond_of c) as [fc|]; [|auto]. unfold Ieee.ieee_compare.
    destruct (Ieee.decode f a), (Ieee.decode f b).
    match goal with |- context [if ?b then 1 else 0] => destruct b; auto end.
  - cbn [op_res_int Ops.alu]. destruct c; cbn [Ops.cond_bit]; try discriminate;
      repeat match goal with
      | |- context [Ops.signed ck ?z] => destruct (Ops.signed ck z)
      | |- context [if ?b then 1 else 0] => destruct b
      end; intro E; try discriminate; injection E as <-; auto.
Qed.

(** Each successful comparison, narrow integer extension, or recognized
    bitwise operation returns a boolean. The floating-point widening case
    requires an exclusion because it can change the representation of one. *)
Theorem bool_result_sound ge e bools op args eqs k m w :
  bools_ok e bools -> (forall fk, opt_op op = Some (ExtF fk) -> fmt_of k = None) ->
  bool_result op args bools = Some eqs ->
  eval_pure ge e k op args m = Some (OpRes (RVal w) m) ->
  w = WInt 0 \/ w = WInt 1.
Proof.
  intros B K. destruct op as [|a|f ts|]; try discriminate.
  - cbn [bool_result]. destruct args as [|v [|u [|extra rest]]]; try
      (rewrite andb_false_r; destruct (String.eqb a "and" || String.eqb a "or" || String.eqb a "xor"); discriminate).
    destruct (String.eqb a "and" && match const_int u with Some n => n =? 1 | None => false end) eqn:Mask.
    + apply andb_true_iff in Mask. destruct Mask as [A N]. apply String.eqb_eq in A. subst a.
      destruct (const_int u) as [n|] eqn:U; try discriminate. apply Z.eqb_eq in N. subst n.
      apply const_int_inv in U. subst u. intros _. unfold eval_pure.
      destruct k; cbn [opt_op String.eqb Ascii.eqb Bool.eqb Syntax.op_arg_classes map2_option];
        match goal with |- context [operand ge e ?k v] => destruct (operand ge e k v) as [[x| |]|] eqn:X end; try discriminate;
        change (Some (OpRes (RVal (WInt (Z.land x 1))) m) = Some (OpRes (RVal w) m) -> w = WInt 0 \/ w = WInt 1);
        intro E; injection E as <-; replace 1 with (Z.ones 1) by reflexivity;
        rewrite Z.land_ones by lia; change (2^1) with 2; change (Z.ones 1) with 1.
      all: pose proof (Z.mod_pos_bound x 2 ltac:(lia)); destruct (Z.eq_dec (x mod 2) 0) as [->|N];
        [left; reflexivity|right; f_equal; lia].
    + destruct (String.eqb a "and" || String.eqb a "or" || String.eqb a "xor") eqn:A; try discriminate.
      destruct (is_boolean bools v && is_boolean bools u) eqn:Both; try discriminate.
      apply andb_true_iff in Both. destruct Both as [V U].
      repeat rewrite orb_true_iff in A. destruct A as [[A|A]|A]; apply String.eqb_eq in A;
        subst a; intros _; unfold eval_pure;
        cbn [opt_op Syntax.op_arg_classes map2_option String.eqb Ascii.eqb Bool.eqb];
        destruct (operand ge e k v) as [[x| |]|] eqn:X; try discriminate;
        destruct (operand ge e k u) as [[y| |]|] eqn:Y; try discriminate;
        destruct (boolean_operand _ _ _ _ _ _ B V X) as [-> | ->];
        destruct (boolean_operand _ _ _ _ _ _ B U Y) as [-> | ->];
        intro E; injection E as <-; auto.
  - destruct ts as [|ty [|ck [|u us]]]; try discriminate.
    + cbn [bool_result]. destruct (String.eqb f "ext") eqn:F; try discriminate.
      destruct args as [|v [|u us]]; try discriminate. destruct (tmp_name v) as [|t [|u us]] eqn:T; try discriminate.
      apply String.eqb_eq in F. apply tmp_name_inv in T. subst f v.
      intro Hit. destruct (B _ _ Hit) as [X|X]; unfold eval_pure;
        destruct ty as [|a| |]; try discriminate;
        cbn [opt_op String.eqb Ascii.eqb Bool.eqb];
        destruct (String.eqb a "s") eqn:S; try (apply String.eqb_eq in S; subst a);
        try (destruct (String.eqb a "d") eqn:J; [apply String.eqb_eq in J; subst a|]);
        try (destruct (opt_narrow (TAtom a)) as [nt|] eqn:N; [destruct nt|discriminate]);
        cbn [Syntax.op_arg_classes map2_option operand opt_value tmp value_x String.eqb Ascii.eqb Bool.eqb];
        rewrite X.
      all: try (match goal with |- context [op_res (ExtF ?fk) _ _ _] =>
        specialize (K fk eq_refl); destruct k; discriminate end).
      all: destruct k; intro E; try discriminate; injection E as <-; auto.
    + cbn [bool_result]. destruct (String.eqb f "cmp") eqn:F; try discriminate.
      apply String.eqb_eq in F. subst. intros _. unfold eval_pure.
      cbn [opt_op String.eqb Ascii.eqb Bool.eqb].
      destruct (opt_cond ty), (opt_class ck); try discriminate.
      cbn [Syntax.op_arg_classes]. destruct (map2_option (operand ge e) [c0;c0] args) eqn:X;
        try discriminate. apply comparison_bit.
Qed.

(** Widening the single-precision bit pattern one supplies a counterexample
    when the result class is allowed to be double precision. *)
Lemma bool_result_float_counterexample :
  let t := TAtom "x" in let bs := nm_add t ([] : list (term * term)) nm_empty in
  let e := [(t,WInt 1)] in
  bools_ok e bs /\
  bool_result (TApp "ext" [TAtom "s"]) [tmp t] bs = Some [] /\
  forall ge m, eval_pure ge e Double (TApp "ext" [TAtom "s"]) [tmp t] m =
    Some (OpRes (RVal (WInt 3936146074321813504)) m).
Proof.
  cbn zeta. split.
  - intros t eqs. rewrite nm_find_add, nm_find_empty.
    destruct (name_eqb t (TAtom "x")) eqn:T; try discriminate.
    apply term_eqb_eq in T. subst. auto.
  - split; reflexivity.
Qed.

(** ## Branches and returns

    A branch reads its condition at word class before it chooses an edge.
    Returns read each operand at the class in the function signature, so
    substitution must preserve the whole word, including any capability. *)

(** A terminator chooses an edge or supplies the words for a return. *)
Inductive jump_value :=
| JumpEdge (target : term)
| JumpReturn (result : word)
| JumpReturns (results : list word).

(** Jump evaluation performs the operand reads and edge selection of
    [jump_step]. An edge retains its complete target, including a poll marker. *)
Definition eval_jump ge e rt j : option jump_value :=
  match j with
  | TApp "branch" [v;t1;t2] =>
      match operand ge e W v with
      | Some (WInt n) => Some (JumpEdge (if n =? 0 then t2 else t1))
      | _ => None
      end
  | TApp "goto" [t] => Some (JumpEdge t)
  | TApp "ret" [v] =>
      match rt with RClass k => let* w := operand ge e k v in Some (JumpReturn w) | _ => None end
  | TApp "rets" [TList vs] =>
      match rt with RTuple ks => let* ws := map2_option (operand ge e) ks vs in Some (JumpReturns ws) | _ => None end
  | _ => None
  end.

(** A replacement preserves the operand's value at each use class. *)
Definition reps_ok ge e (reps : nmap term) :=
  forall t v k, nm_find t reps = Some v -> operand ge e k v = operand ge e k (tmp t).

(** A negation entry relates the stored word to the complement of a boolean. *)
Definition not_defs_ok (e : env) defs :=
  forall t b n, nm_find t (sd_main defs) = Some (DefNot b) ->
    lookup b e = Some (WInt n) -> (n = 0 \/ n = 1) ->
    lookup t e = Some (WInt (if n =? 0 then 1 else 0)).

(** Substituting a recorded value preserves the complete operand read. *)
Lemma subst_operand ge e reps k v :
  reps_ok ge e reps -> operand ge e k (subst_val reps v) = operand ge e k v.
Proof.
  intro R. unfold subst_val. destruct (tmp_name v) as [|t [|u us]] eqn:T; try reflexivity.
  destruct (nm_find t reps) eqn:F; try reflexivity. apply tmp_name_inv in T. subst. eauto.
Qed.

(** Substituting a tuple preserves its values and any failure to match its arity. *)
Lemma subst_tuple ge e reps ks vs :
  reps_ok ge e reps ->
  map2_option (operand ge e) ks (map (subst_val reps) vs) = map2_option (operand ge e) ks vs.
Proof.
  intro R. revert vs. induction ks as [|k ks IH]; intros [|v vs]; try reflexivity.
  cbn [map map2_option]. rewrite subst_operand, IH by assumption. reflexivity.
Qed.

(** Eliminating a same-target branch requires that its condition has a word
    value. All other folds also preserve failed operand reads. *)
Definition same_target_ready ge e j :=
  match j with
  | TApp "branch" [v;t1;t2] => t1 = t2 -> exists n, operand ge e W v = Some (WInt n)
  | _ => True
  end.

(** Folding a jump preserves its destination or its complete return value.
    The fold flag records a change to the graph and plays no role in evaluation. *)
Theorem fold_jump_sound ge e rt reps bools defs f0 j0 j1 f1 :
  reps_ok ge e reps -> bools_ok e bools -> not_defs_ok e defs ->
  same_target_ready ge e j0 -> fold_jump reps bools defs f0 j0 = (j1,f1) ->
  eval_jump ge e rt j1 = eval_jump ge e rt j0.
Proof.
  intros R B N Ready. unfold fold_jump.
  destruct j0 as [z|a|f xs|ts]; try (intro E; injection E as <- <-; reflexivity).
  destruct (String.eqb f "branch") eqn:Br.
  - apply String.eqb_eq in Br. subst f.
    destruct xs as [|v [|t1 [|t2 [|u us]]]]; try (intro E; injection E as <- <-; reflexivity).
    pose proof (subst_operand ge e reps W v R) as Sub.
    set (v' := subst_val reps v) in *. destruct (const_int v') as [n|] eqn:C.
    + apply const_int_inv in C. rewrite C in Sub. intro E. injection E as <- <-.
      cbn [eval_jump]. rewrite <- Sub.
      change (operand ge e W (TApp "const" [TInt n])) with (Some (WInt (n mod M32))).
      cbv beta iota zeta. destruct (n mod M32 =? 0); reflexivity.
    + destruct (term_eqb t1 t2) eqn:Same.
      * apply term_eqb_eq in Same. subst t2. destruct (Ready eq_refl) as [n V].
        intro E. injection E as <- <-. cbn [eval_jump]. rewrite V. destruct (n =? 0); reflexivity.
      * assert (Unchanged : eval_jump ge e rt (TApp "branch" [v';t1;t2]) =
            eval_jump ge e rt (TApp "branch" [v;t1;t2])) by (cbn [eval_jump]; rewrite Sub; reflexivity).
        destruct (tmp_name v') as [|t [|u us]] eqn:T;
          try (intro E; injection E as <- <-; exact Unchanged).
        destruct (nm_find t (sd_main defs)) as [[c ck a b|b|ty]|] eqn:F;
          try (intro E; injection E as <- <-; exact Unchanged).
        unfold nm_mem. destruct (nm_find b bools) eqn:Bit;
          [|intro E; injection E as <- <-; exact Unchanged].
        apply tmp_name_inv in T. rewrite T in Sub. intro E. injection E as <- <-.
        cbn [eval_jump]. rewrite <- Sub. destruct (B _ _ Bit) as [X|X];
          pose proof (N _ _ _ F X ltac:(auto)) as Y;
          cbn [operand opt_value tmp value_x String.eqb Ascii.eqb Bool.eqb]; rewrite X,Y; reflexivity.
  - destruct (String.eqb f "ret") eqn:Ret.
    + apply String.eqb_eq in Ret. subst f. destruct xs as [|v [|u us]]; intro E; injection E as <- <-;
        try reflexivity. destruct rt; try reflexivity. cbn [eval_jump]. rewrite subst_operand by assumption. reflexivity.
    + destruct (String.eqb f "rets") eqn:Rets; [|intro E; injection E as <- <-; reflexivity].
      apply String.eqb_eq in Rets. subst f.
      destruct xs as [|v [|u us]]; try (intro E; injection E as <- <-; reflexivity).
      all: destruct v; intro E; injection E as <- <-; try reflexivity.
      destruct rt; try reflexivity. cbn [eval_jump]. rewrite subst_tuple by assumption. reflexivity.
Qed.

(** An unbound condition makes the original branch fail even when its two
    targets agree. The folded jump reaches the shared target directly. *)
Lemma fold_jump_unbound_counterexample ge rt :
  let t := TAtom "target" in let j := TApp "branch" [tmp (TAtom "missing");t;t] in
  eval_jump ge [] rt j = None /\
  eval_jump ge [] rt (fst (fold_jump nm_empty nm_empty empty_defs false j)) = Some (JumpEdge t).
Proof. split; reflexivity. Qed.
