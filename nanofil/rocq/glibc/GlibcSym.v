(** A block proof today steps one instruction at a time, and at every
    load or check the author names the ownership facts the rule needs
    and proves the same address arithmetic again. This module replaces
    that work for straight-line code with a symbolic executor written
    as an ordinary Rocq function. The function reads a description of
    the environment and of the owned memory, runs every instruction of
    a block, and returns what holds at the block's end together with
    the arithmetic conditions it could not settle itself.

    One theorem, [sym_sound], states that the function's answer is a
    valid proof step: if the conditions hold and the description was
    true of the real state, the block's [[weakest-precondition]] holds.
    The theorem is proved once from the existing instruction rules, so
    running the executor inside a proof costs one computation instead
    of a tactic step per instruction.

    Unknown pointer addresses and integer values need not prevent execution.
    The executor keeps expressions for them and stores their actual values
    separately, in a valuation. It uses only the memory permissions named
    by the caller and preserves the others, as [[separation-logic]] permits. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  Machine Pieces Heap Language Logic MemLogic ExternalCalls StepRules.
From Nanofil Require Validate WordBits Interval.
From Glibc Require Import Fix GlibcTactics.
Module sym_ML := MemLogicOn R LG0.
Import ListNotations LG0 LG0.L.
Open Scope Z_scope.

(** Narrow cells own exactly the bytes used by the corresponding load. *)
Definition sym_bytes (n : narrow) (x : Z) : list Z :=
  le_bytes x (Z.to_nat (fst (narrow_type n))).

(** Decoding a narrow cell recovers its low bits even when the supplied integer is out of range. *)
Lemma sym_bytes_decode n x :
  of_bytes (sym_bytes n x) = x mod 2 ^ (8 * fst (narrow_type n)).
Proof.
  pose proof (WordBits.low_step x 0 ltac:(lia)) as H0.
  pose proof (WordBits.low_step x 1 ltac:(lia)) as H1.
  pose proof (WordBits.low_step x 2 ltac:(lia)) as H2.
  pose proof (WordBits.low_step x 3 ltac:(lia)) as H3.
  change (x mod 256 = x mod 1 + 1 * byte_of x 0) in H0.
  change (x mod 65536 = x mod 256 + 256 * byte_of x 1) in H1.
  change (x mod 16777216 = x mod 65536 + 65536 * byte_of x 2) in H2.
  change (x mod 4294967296 = x mod 16777216 + 16777216 * byte_of x 3) in H3.
  rewrite Z.mod_1_r in H0.
  destruct n;
    first [change (byte_of x 0 + 256 * (byte_of x 1 + 256 *
              (byte_of x 2 + 256 * (byte_of x 3 + 256 * 0))) = x mod 4294967296) |
           change (byte_of x 0 + 256 * (byte_of x 1 + 256 * 0) = x mod 65536) |
           change (byte_of x 0 + 256 * 0 = x mod 256)]; lia.
Qed.

(** Flag calculations combine bits without changing their register width. *)
Inductive bitop := BAnd | BOr | BXor.

(** Each flag operation has the same integer meaning as its machine instruction. *)
Definition bitden (o : bitop) : Z -> Z -> Z :=
  match o with BAnd => Z.land | BOr => Z.lor | BXor => Z.lxor end.

(** Shifts distinguish arithmetic right shift from logical right shift and left shift. *)
Inductive shiftop := SArith | SRight | SLeft.

(** Shift counts wrap at the register width, as they do in the machine's arithmetic evaluator. *)
Definition shiftden (o : shiftop) (k : class) (x y : Z) : Z :=
  match shift_factor k y, modulus k, signed k x with
  | Some p, Some m, Some sx =>
      match o with SArith => (sx / p) mod m | SRight => x / p | SLeft => (x * p) mod m end
  | _, _, _ => 0
  end.

(** Extending a value bounds it by the signed or unsigned width of its source type. *)
Definition sym_ext_range (n : narrow) : Z * Z :=
  match n with
  | Sb => (-128, 127) | Ub => (0, 255)
  | Sh => (-32768, 32767) | Uh => (0, 65535)
  | Sw => (-2 ^ 31, 2 ^ 31 - 1) | Uw => (0, 2 ^ 32 - 1)
  end.

(** These bounds hold for every input, including negative integers and values wider than the source type. *)
Lemma sym_ext_range_sound n x :
  fst (sym_ext_range n) <= extension n x <= snd (sym_ext_range n).
Proof.
  destruct n; cbn [sym_ext_range extension fst snd];
    first [match goal with |- context [sign_extension ?m ?h x] =>
      pose proof (Interval.sign_extension_range m h x ltac:(lia) ltac:(lia)) end |
      match goal with |- context [x mod ?m] =>
      pose proof (Z.mod_pos_bound x m ltac:(lia)) end]; lia.
Qed.

(** ## Symbolic integers, capabilities and words

    A block may add an offset to a pointer whose address is unknown.
    The executor records the addition as an expression rather than
    requiring a concrete result. The valuation supplies the unknown values. *)

(** An integer expression is built from constants, integer variables,
    the address of a pointer variable, the end of a region variable,
    sums, differences, remainders by a constant, comparisons, bit operations,
    extensions and shifts. The
    comparison [ZCmp] c k a b is one when a and b of class k satisfy c,
    and zero otherwise, as the IR's `cmp` instruction computes. *)
Inductive zexp : Type :=
  | ZK (z : Z)
  | ZV (n : nat)
  | ZAddr (n : nat)
  | ZEnd (n : nat)
  | ZAdd (a b : zexp)
  | ZSub (a b : zexp)
  | ZMod (a : zexp) (m : Z)
  | ZCmp (c : cond) (k : class) (a b : zexp)
  | ZBits (o : bitop) (a b : zexp)
  | ZExt (n : narrow) (a : zexp)
  | ZShift (o : shiftop) (k : class) (a b : zexp).

(** A capability identifies a writable or read-only object by its base address.
    It can also be absent or supplied by a pointer variable. *)
Inductive scap : Type :=
  | SCNone
  | SCObj (b : zexp)
  | SCRo (b : zexp)
  | SCOf (n : nat).

(** A symbolic word is an integer or a pointer made of an address and
    a capability. A pointer variable p is described as [SWPtr] with
    address [ZAddr] and capability [SCOf] of the same number. *)
Inductive sword : Type :=
  | SWInt (x : zexp)
  | SWPtr (a : zexp) (c : scap).

(** The valuation gives the integer variables, the pointer variables
    and the region variables their values in the proof. *)
Record valuation : Type := mkVal { vz : list Z; vp : list ptr; vr : list region }.

(** Evaluation gives an integer expression its value. A variable outside the
    valuation reads as zero, and so does a comparison whose class the
    model rejects; the executor never produces either. *)
Fixpoint zden (ρ : valuation) (x : zexp) : Z :=
  match x with
  | ZK z => z
  | ZV n => nth n (vz ρ) 0
  | ZAddr n => match nth_error (vp ρ) n with Some p => ptr_addr p | None => 0 end
  | ZEnd n => match nth_error (vr ρ) n with Some r => r_end r | None => 0 end
  | ZAdd a b => zden ρ a + zden ρ b
  | ZSub a b => zden ρ a - zden ρ b
  | ZMod a m => zden ρ a mod m
  | ZCmp c k a b => match cond_bit c k (zden ρ a) (zden ρ b) with Some v => v | None => 0 end
  | ZBits o a b => bitden o (zden ρ a) (zden ρ b)
  | ZExt n a => extension n (zden ρ a)
  | ZShift o k a b => shiftden o k (zden ρ a) (zden ρ b)
  end.

(** Evaluation replaces a symbolic capability's variables with their values. *)
Definition cden (ρ : valuation) (c : scap) : cap :=
  match c with
  | SCNone => CNone
  | SCObj b => Obj (zden ρ b)
  | SCRo b => Ro (zden ρ b)
  | SCOf n => match nth_error (vp ρ) n with Some p => ptr_cap p | None => CNone end
  end.

(** Evaluation reconstructs the integer or pointer described by a symbolic word. *)
Definition wden (ρ : valuation) (w : sword) : word :=
  match w with
  | SWInt x => WInt (zden ρ x)
  | SWPtr a c => WPtr (mkPtr (zden ρ a) (cden ρ c))
  end.

(** ## What the executor may assume

    The executor removes a wrap such as x mod 2^64 when it knows that
    x already lies in range, and it treats two capabilities as equal
    when the proof says they are. These facts come from the proof's
    hypotheses, and [sym_sound] asks for them to hold. *)

(** A bound says that lo ≤ x < hi for the integer expression x. *)
Record bound : Type := mkBound { bd_exp : zexp; bd_lo : Z; bd_hi : Z }.

(** The facts are a list of bounds and a list of capability equations. *)
Record facts : Type := mkFacts { f_bounds : list bound; f_caps : list (scap * scap) }.

(** The facts hold under ρ when every bound and every equation does. *)
Definition facts_hold (ρ : valuation) (fs : facts) : Prop :=
  Forall (fun bd => bd_lo bd <= zden ρ (bd_exp bd) < bd_hi bd) (f_bounds fs) /\
  Forall (fun ce => cden ρ (fst ce) = cden ρ (snd ce)) (f_caps fs).

(** ## The environment

    The executor tracks known temporary values and records each assignment
    in instruction order. Applying those assignments to the original
    environment produces the same [put] calls as the step tactics. *)

(** A symbolic environment lists the known temporaries with their values. *)
Definition senv : Type := list (name * sword).

(** A real environment e matches se under ρ when every listed
    temporary has the listed value in e. Other temporaries may hold
    anything. *)
Definition env_models (ρ : valuation) (se : senv) (e : env) : Prop :=
  Forall (fun nw => lookup (fst nw) e = Some (wden ρ (snd nw))) se.

(** The environment after a block applies its assignments, the first
    one innermost. *)
Definition apply_ups (ρ : valuation) (ups : list (name * sword)) (e : env) : env :=
  fold_left (fun e u => put (fst u) (wden ρ (snd u)) e) ups e.

(** ## Owned memory

    A load needs permission to read its cell, and a store needs permission
    to change it. The caller supplies those permissions as atoms, which
    describe the owned cells and the objects that remain alive. *)

(** An atom describes an object lifetime, an integer cell, a pointer cell,
    or the lifetime of a loaded pointer's target. Cell atoms record a
    base address and offset; lifetime atoms refer to a numbered region. *)
Inductive atom : Type :=
  | ALive (b : zexp) (r : nat)
  | ACell (b o v : zexp)
  | APCell (b o a : zexp) (c : scap)
  | ALiveCap (c : scap) (r : nat)
  | ANarrow (n : narrow) (b o v : zexp).

(** ## What the executor returns

    The executor runs until the block's jump, or until an instruction
    it cannot handle. It returns the state at that point, the
    conditions it left for the proof, and how the block continues. *)

(** The proof must establish an inequality or equation between
    integer expressions, or the world condition of a store, which says
    that the external world's interpretation survives writing the new
    value. A store of an integer cell carries its old and new values,
    and a store of a pointer cell its old and new pointers. *)
Inductive ob : Type :=
  | OLe (a b : zexp)
  | OLt (a b : zexp)
  | OEq (a b : zexp)
  | OStoreW (b o : zexp) (r : nat) (old new : zexp)
  | OStoreP (b o : zexp) (r : nat) (old new : sword).

(** A stop reason explains why execution stopped before the block's jump. Each
    reason names what was missing, in terms an author can act on: the
    lifetime of object b, the cell at b plus o, the target lifetime of
    a loaded pointer, a capability that is not a known object, a
    temporary the executor does not know, or an instruction outside
    the executor's fragment. *)
Inductive stop_reason : Type :=
  | NoLive (b : zexp)
  | NoCell (b o : zexp)
  | NoLiveCap (c : scap)
  | NotObject (c : scap)
  | UnknownTmp (n : name)
  | Unsupported (i : inst)
  (** The block ends in a return or trap, which the step tactics handle. *)
  | UnsupportedJump (j : jump)
  | NotYet.

(** An assignment changes a temporary, and a store changes a cell.
    The state tracks both changes and collects conditions that the caller must prove. *)
Record sstate : Type := mkSState {
  st_env : senv; st_ups : list (name * sword); st_heap : list atom; st_obs : list ob }.

(** Execution either reaches a goto or branch, or stops at an unsupported instruction.
    A stopped execution returns the instructions and jump that remain to be handled. *)
Inductive leaf : Type :=
  | LGoto (t : target) (s : sstate)
  | LBranch (c : zexp) (t1 t2 : target) (s : sstate)
  | LStop (why : stop_reason) (rest : list inst) (j : jump) (s : sstate).

(** ## Removing redundant integer wraps

    Arithmetic instructions wrap their results even when the proof already
    places those results in range. The executor propagates closed intervals
    through sums and differences before deciding whether to keep a wrap. *)

(** Comparisons with the same condition have the same interpretation. *)
Definition sym_cond_eqb (c d : cond) : bool :=
  match c, d with
  | Eq, Eq | Ne, Ne | Ult, Ult | Ule, Ule | Ugt, Ugt | Uge, Uge
  | Slt, Slt | Sle, Sle | Sgt, Sgt | Sge, Sge
  | Le, Le | Lt, Lt | Ge, Ge | Gt, Gt | Ord, Ord | Unord, Unord => true
  | _, _ => false
  end.

(** This comparison recognizes identical expressions without inspecting their valuations. *)
Fixpoint zsame (a b : zexp) : bool :=
  match a, b with
  | ZK x, ZK y => Z.eqb x y
  | ZV x, ZV y | ZAddr x, ZAddr y | ZEnd x, ZEnd y => Nat.eqb x y
  | ZAdd a b, ZAdd c d | ZSub a b, ZSub c d => zsame a c && zsame b d
  | ZMod a m, ZMod b n => zsame a b && Z.eqb m n
  | ZCmp c k a b, ZCmp d l x y =>
      sym_cond_eqb c d && class_eqb k l && zsame a x && zsame b y
  | ZBits o a b, ZBits p c d =>
      (match o, p with BAnd, BAnd | BOr, BOr | BXor, BXor => true | _, _ => false end)
      && zsame a c && zsame b d
  | ZExt n a, ZExt m b =>
      (match n, m with Sb, Sb | Ub, Ub | Sh, Sh | Uh, Uh | Sw, Sw | Uw, Uw => true | _, _ => false end)
      && zsame a b
  | ZShift o k a b, ZShift p l c d =>
      (match o, p with SArith, SArith | SRight, SRight | SLeft, SLeft => true | _, _ => false end)
      && class_eqb k l && zsame a c && zsame b d
  | _, _ => false
  end.

(** Matching expression syntax justifies replacing either expression in a proof. *)
Lemma zsame_sound a b : zsame a b = true -> a = b.
Proof.
  revert b. induction a; destruct b; cbn; intros H; try discriminate;
    repeat match goal with H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?] end;
    try match goal with H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H end;
    try match goal with H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H end;
    try solve [f_equal; auto].
  - assert (c = c0) by (destruct c, c0; discriminate || reflexivity).
    assert (k = k0) by (destruct k, k0; discriminate || reflexivity).
    subst. f_equal; auto.
  - destruct o, o0; try discriminate; f_equal; auto.
  - destruct n, n0; try discriminate; f_equal; auto.
  - destruct o, o0; try discriminate;
      assert (k = k0) by (destruct k, k0; discriminate || reflexivity);
      subst; f_equal; auto.
Qed.

(** A recorded bound supplies an inclusive interval for its expression. *)
Fixpoint known_range (bs : list bound) (x : zexp) : option (Z * Z) :=
  match bs with
  | [] => None
  | b :: bs => if zsame x (bd_exp b) then Some (bd_lo b, bd_hi b - 1)
               else known_range bs x
  end.

(** Interval propagation uses only integer arithmetic and recorded bounds. *)
Fixpoint zrange (fs : facts) (x : zexp) : option (Z * Z) :=
  match known_range (f_bounds fs) x with
  | Some r => Some r
  | None =>
      match x with
      | ZK z => Some (z, z)
      | ZAdd a b =>
          match zrange fs a, zrange fs b with
          | Some (lo, hi), Some (lo', hi') => Some (lo + lo', hi + hi')
          | _, _ => None
          end
      | ZSub a b =>
          match zrange fs a, zrange fs b with
          | Some (lo, hi), Some (lo', hi') => Some (lo - hi', hi - lo')
          | _, _ => None
          end
      | ZMod _ m => if 0 <? m then Some (0, m - 1) else None
      | ZExt n _ => Some (sym_ext_range n)
      | ZBits BAnd a b =>
          match zrange fs a, zrange fs b with
          | Some (lo, hi), Some (lo', hi') =>
              if (0 <=? lo) && (0 <=? lo') then Some (0, hi') else None
          | _, _ => None
          end
      | _ => None
      end
  end.

(** A wrap disappears only when the entire inferred interval fits its modulus. *)
Definition zwrap (fs : facts) (x : zexp) (m : Z) : zexp :=
  match x with
  | ZK z => ZK (z mod m)
  | _ =>
      match zrange fs x with
      | Some (lo, hi) => if (0 <=? lo) && (hi <? m) then x else ZMod x m
      | None => ZMod x m
      end
  end.

(** The bounds supplied by the caller justify every recorded interval. *)
Lemma known_range_sound ρ bs x lo hi :
  Forall (fun bd => bd_lo bd <= zden ρ (bd_exp bd) < bd_hi bd) bs ->
  known_range bs x = Some (lo, hi) -> lo <= zden ρ x <= hi.
Proof.
  intros H. induction H as [|b bs Hb Hbs IH]; cbn; [discriminate|].
  destruct (zsame x (bd_exp b)) eqn:E.
  - apply zsame_sound in E. subst x. intros H. inversion H; subst. lia.
  - exact IH.
Qed.

(** Propagating an interval preserves both bounds on the expression's value. *)
Lemma zrange_sound ρ fs x lo hi : facts_hold ρ fs ->
  zrange fs x = Some (lo, hi) -> lo <= zden ρ x <= hi.
Proof.
  intros [Hbs Hcs]. revert lo hi. induction x; intros lo hi;
    cbn [zrange]; destruct (known_range (f_bounds fs) _) as [[a b]|] eqn:E;
    try solve [intros H; inversion H; subst; eapply known_range_sound; eauto];
    try discriminate.
  - intros H. inversion H; subst. cbn. lia.
  - destruct (zrange fs x1) as [[a b]|] eqn:E1; [|discriminate].
    destruct (zrange fs x2) as [[c d]|] eqn:E2; [|discriminate].
    intros H. inversion H; subst. specialize (IHx1 _ _ eq_refl).
    specialize (IHx2 _ _ eq_refl). cbn. lia.
  - destruct (zrange fs x1) as [[a b]|] eqn:E1; [|discriminate].
    destruct (zrange fs x2) as [[c d]|] eqn:E2; [|discriminate].
    intros H. inversion H; subst. specialize (IHx1 _ _ eq_refl).
    specialize (IHx2 _ _ eq_refl). cbn. lia.
  - destruct (0 <? m) eqn:Em; [|discriminate].
    apply Z.ltb_lt in Em. intros H. inversion H; subst.
    pose proof (Z.mod_pos_bound (zden ρ x) m Em). cbn. lia.
  - destruct o; try discriminate.
    destruct (zrange fs x1) as [[a b]|] eqn:E1; [|discriminate].
    destruct (zrange fs x2) as [[c d]|] eqn:E2; [|discriminate].
    destruct ((0 <=? a) && (0 <=? c)) eqn:En; [|discriminate].
    apply andb_true_iff in En as [Ha Hc]. apply Z.leb_le in Ha. apply Z.leb_le in Hc.
    intros H. injection H as <- <-. specialize (IHx1 _ _ eq_refl).
    specialize (IHx2 _ _ eq_refl). cbn [zden bitden].
    pose proof (Interval.land_le (zden ρ x1) (zden ρ x2) ltac:(lia) ltac:(lia)). lia.
  - intros H. pose proof (sym_ext_range_sound n (zden ρ x)).
    destruct n; inversion H; subst; exact H0.
Qed.

(** Removing a redundant wrap does not change the represented integer. *)
Lemma zwrap_sound ρ fs x m : facts_hold ρ fs ->
  zden ρ (zwrap fs x m) = zden ρ x mod m.
Proof.
  intros Hfs. unfold zwrap. destruct x; try reflexivity;
    destruct (zrange fs _) as [[lo hi]|] eqn:E; try reflexivity;
    destruct ((0 <=? lo) && (hi <? m)) eqn:H; try reflexivity;
    apply andb_true_iff in H as [Hl Hh]; apply Z.leb_le in Hl; apply Z.ltb_lt in Hh;
    symmetry; apply Z.mod_small; pose proof (zrange_sound _ _ _ _ _ Hfs E); lia.
Qed.

(** Same-width extensions keep only the source bits; other extensions retain their signed or unsigned interpretation. *)
Definition zextend (fs : facts) (n : narrow) (x : zexp) (m : Z) : zexp :=
  if m =? 2 ^ (8 * fst (narrow_type n)) then zwrap fs x m
  else zwrap fs (ZExt n x) m.

(** Sign extension leaves the source bits unchanged when the result has the same width. *)
Lemma extension_mod_width n x :
  extension n x mod 2 ^ (8 * fst (narrow_type n)) = x mod 2 ^ (8 * fst (narrow_type n)).
Proof.
  destruct n; cbn [extension narrow_type fst];
    try (unfold sign_extension; match goal with |- context [if ?b then _ else _] => destruct b end);
    try rewrite Zminus_mod;
    rewrite ?Z_mod_same_full ?Z.sub_0_r;
    repeat (rewrite Z.mod_mod; [|lia]); reflexivity.
Qed.

(** Removing a same-width extension preserves the result of the machine instruction. *)
Lemma zextend_sound ρ fs n x m : facts_hold ρ fs ->
  zden ρ (zextend fs n x m) = extension n (zden ρ x) mod m.
Proof.
  intros Hfs. unfold zextend. destruct (m =? 2 ^ (8 * fst (narrow_type n))) eqn:E.
  - apply Z.eqb_eq in E. subst m. rewrite (zwrap_sound _ _ _ _ Hfs) extension_mod_width. reflexivity.
  - rewrite (zwrap_sound _ _ _ _ Hfs). reflexivity.
Qed.

(** Nested expressions lose redundant wraps before their addresses are compared. *)
Fixpoint zclean (fs : facts) (x : zexp) : zexp :=
  match x with
  | ZAdd a b => ZAdd (zclean fs a) (zclean fs b)
  | ZSub a b => ZSub (zclean fs a) (zclean fs b)
  | ZMod a m => zwrap fs (zclean fs a) m
  | ZCmp c k a b =>
      let a' := zclean fs a in let b' := zclean fs b in
      match a', b' with
      | ZK x, ZK y =>
          match cond_bit c k x y with Some v => ZK v | None => ZCmp c k a' b' end
      | _, _ => ZCmp c k a' b'
      end
  | ZBits o a b => ZBits o (zclean fs a) (zclean fs b)
  | ZExt n a => ZExt n (zclean fs a)
  | ZShift o k a b => ZShift o k (zclean fs a) (zclean fs b)
  | _ => x
  end.

(** Cleaning an address preserves the value used by the instruction rules. *)
Lemma zclean_sound ρ fs x : facts_hold ρ fs -> zden ρ (zclean fs x) = zden ρ x.
Proof.
  intros Hfs. induction x; cbn [zclean]; try reflexivity.
  - cbn. now rewrite IHx1 IHx2.
  - cbn. now rewrite IHx1 IHx2.
  - rewrite zwrap_sound; [cbn; now rewrite IHx|exact Hfs].
  - destruct (zclean fs x1); destruct (zclean fs x2);
      cbn in IHx1, IHx2; cbn [zden]; rewrite <- IHx1, <- IHx2;
      try reflexivity. destruct (cond_bit c k z z0) eqn:E; cbn [zden]; rewrite ?E; reflexivity.
  - cbn. now rewrite IHx1 IHx2.
  - cbn. now rewrite IHx.
  - cbn. now rewrite IHx1 IHx2.
Qed.

(** A linear form records one coefficient for each non-additive expression. *)
Fixpoint lin_insert (x : zexp) (k : Z) (xs : list (zexp * Z)) : list (zexp * Z) :=
  match xs with
  | [] => [(x, k)]
  | (y, n) :: ys => if zsame x y then (y, k + n) :: ys else (y, n) :: lin_insert x k ys
  end.

(** Sums and differences contribute signed coefficients to the same linear form. *)
Fixpoint lin_acc (x : zexp) (k : Z) (xs : list (zexp * Z)) : list (zexp * Z) :=
  match x with
  | ZK z => lin_insert (ZK 1) (k * z) xs
  | ZAdd a b => lin_acc b k (lin_acc a k xs)
  | ZSub a b => lin_acc b (-k) (lin_acc a k xs)
  | _ => lin_insert x k xs
  end.

(** Two addresses match when their difference has no nonzero coefficient. *)
Definition zlinear_eqb (fs : facts) (a b : zexp) : bool :=
  forallb (fun x => Z.eqb (snd x) 0)
    (lin_acc (ZSub (zclean fs a) (zclean fs b)) 1 []).

(** The value of a linear form is the sum of its weighted expressions. *)
Fixpoint lin_den (ρ : valuation) (xs : list (zexp * Z)) : Z :=
  match xs with [] => 0 | (x, k) :: xs => k * zden ρ x + lin_den ρ xs end.

(** Combining coefficients preserves the sum represented by a linear form. *)
Lemma lin_insert_sound ρ x k xs :
  lin_den ρ (lin_insert x k xs) = k * zden ρ x + lin_den ρ xs.
Proof.
  induction xs as [|[y n] ys IH]; cbn; [lia|].
  destruct (zsame x y) eqn:E; cbn.
  - apply zsame_sound in E. subst. ring.
  - rewrite IH. ring.
Qed.

(** Flattening addition and subtraction preserves the represented integer. *)
Lemma lin_acc_sound ρ x k xs :
  lin_den ρ (lin_acc x k xs) = k * zden ρ x + lin_den ρ xs.
Proof.
  revert k xs. induction x; intros k' xs; cbn [lin_acc];
    rewrite ?lin_insert_sound ?IHx1 ?IHx2 ?IHx1; cbn [zden]; ring.
Qed.

(** A successful linear comparison justifies using the same owned cell. *)
Lemma zlinear_eqb_sound ρ fs a b : facts_hold ρ fs ->
  zlinear_eqb fs a b = true -> zden ρ a = zden ρ b.
Proof.
  intros Hfs H. unfold zlinear_eqb in H.
  assert (Hz : forall xs, forallb (fun x => Z.eqb (snd x) 0) xs = true -> lin_den ρ xs = 0).
  { induction xs as [|[x k] xs IH]; cbn; [auto|].
    rewrite andb_true_iff. intros [Hk Hxs]. apply Z.eqb_eq in Hk. rewrite Hk (IH Hxs). ring. }
  apply Hz in H. rewrite lin_acc_sound in H.
  cbn [zden lin_den] in H.
  rewrite (zclean_sound ρ fs a Hfs) (zclean_sound ρ fs b Hfs) in H. lia.
Qed.

(** ## Reading symbolic operands

    Each instruction reads its operands at the classes specified by the IR.
    The symbolic evaluator applies the same integer truncations and preserves
    pointer capabilities when it reads or copies a pointer. *)

(** Capability syntax agrees when its object bases describe the same address. *)
Definition csame (fs : facts) (a b : scap) : bool :=
  match a, b with
  | SCNone, SCNone => true
  | SCObj x, SCObj y | SCRo x, SCRo y => zlinear_eqb fs x y
  | SCOf n, SCOf m => Nat.eqb n m
  | _, _ => false
  end.

(** A recorded equation can relate two otherwise opaque capabilities. *)
Definition cequal (fs : facts) (a b : scap) : bool :=
  csame fs a b || existsb (fun ce =>
    (csame fs a (fst ce) && csame fs b (snd ce)) ||
    (csame fs b (fst ce) && csame fs a (snd ce))) (f_caps fs).

(** The equation list can identify an opaque capability as an object capability. *)
Fixpoint object_find (fs : facts) (c : scap) (cs : list (scap * scap)) : option zexp :=
  match cs with
  | [] => None
  | (a, SCObj b) :: cs => if csame fs c a then Some b else object_find fs c cs
  | (SCObj b, a) :: cs => if csame fs c a then Some b else object_find fs c cs
  | _ :: cs => object_find fs c cs
  end.

(** Object access requires an object capability, possibly supplied by an equation. *)
Definition object_base (fs : facts) (c : scap) : option zexp :=
  match c with SCObj b => Some b | _ => object_find fs c (f_caps fs) end.

(** Reading an integer temporary truncates it to the requested register width. *)
Definition sword_at (fs : facts) (k : class) (w : sword) : option sword :=
  match k, w with
  | (W | Single), SWInt x => Some (SWInt (zwrap fs x (2 ^ 32)))
  | (L | Double), SWInt x => Some (SWInt (zwrap fs x (2 ^ 64)))
  | Extended, SWInt x => Some (SWInt (zwrap fs x (2 ^ 80)))
  | (P | A | F), _ => Some w
  | _, _ => None
  end.

(** Global pointers can be described when their capabilities name ordinary objects. *)
Definition quote_ptr (p : ptr) : option sword :=
  match ptr_cap p with
  | CNone => Some (SWPtr (ZK (ptr_addr p)) SCNone)
  | Obj b => Some (SWPtr (ZK (ptr_addr p)) (SCObj (ZK b)))
  | Ro b => Some (SWPtr (ZK (ptr_addr p)) (SCRo (ZK b)))
  | _ => None
  end.

(** An operand is read from the known temporaries or the module's globals. *)
Definition svalue (ge : genv) (fs : facts) (se : senv) (k : class) (v : value) : option sword :=
  match v with
  | Tmp n => match lookup n se with Some w => sword_at fs k w | None => None end
  | Const z =>
      match modulus k with
      | Some m => Some (match k with P => SWPtr (ZK (z mod m)) SCNone | _ => SWInt (ZK (z mod m)) end)
      | None => None
      end
  | Global n => match lookup n (ge_globals ge) with Some p => quote_ptr p | None => None end
  end.

(** Integer operations retain wraps unless their input facts prove them redundant. *)
Definition salu (fs : facts) (o : op) (k : class) (xs : list sword) : option sword :=
  match o, xs with
  | Copy, [x] => Some x
  | Ptoi, [SWPtr a _] => Some (SWInt a)
  | Add, [SWInt x; SWInt y] =>
      match modulus k with Some m => Some (SWInt (zwrap fs (ZAdd x y) m)) | None => None end
  | Sub, [SWInt x; SWInt y] =>
      match modulus k with Some m => Some (SWInt (zwrap fs (ZSub x y) m)) | None => None end
  | And, [SWInt x; SWInt y] => Some (SWInt (ZBits BAnd x y))
  | Or, [SWInt x; SWInt y] => Some (SWInt (ZBits BOr x y))
  | Xor, [SWInt x; SWInt y] => Some (SWInt (ZBits BXor x y))
  | Sar, [SWInt x; SWInt y] =>
      match k with W | L => Some (SWInt (ZShift SArith k x y)) | _ => None end
  | Shr, [SWInt x; SWInt y] =>
      match k with W | L => Some (SWInt (ZShift SRight k x y)) | _ => None end
  | Shl, [SWInt x; SWInt y] =>
      match k with W | L => Some (SWInt (ZShift SLeft k x y)) | _ => None end
  | Ext n, [SWInt x] =>
      match modulus k with Some m => Some (SWInt (zextend fs n x m)) | None => None end
  | Cmp c ck, [SWInt x; SWInt y] =>
      match cond_bit c ck 0 0 with
      | Some _ => Some (SWInt (zclean fs (ZCmp c ck x y)))
      | None => None
      end
  | _, _ => None
  end.

(** General lets also allow pointer addition and subtraction, but not floating arithmetic. *)
Definition sop (fs : facts) (o : op) (k : class) (xs : list sword) : option sword :=
  if float_class k then None else
  match o, k, xs with
  | Add, P, [SWPtr a c; SWInt x] => Some (SWPtr (zwrap fs (ZAdd a x) (2 ^ 64)) c)
  | Sub, P, [SWPtr a c; SWInt x] => Some (SWPtr (zwrap fs (ZSub a x) (2 ^ 64)) c)
  | (Add | Sub | And | Or | Xor | Sar | Shr | Shl | Ext _), (W | L), _ => salu fs o k xs
  | Cmp _ ck, _, _ => if float_class ck then None else salu fs o k xs
  | (Copy | Ptoi), _, _ => salu fs o k xs
  | _, _, _ => None
  end.

(** Flight arguments either read an integer or extract a pointer's address. *)
Definition sflight_arg (ge : genv) (fs : facts) (se : senv) (a : flight_arg) : option sword :=
  match a with
  | FValue v => svalue ge fs se L v
  | FAddress v =>
      match svalue ge fs se P v with
      | Some (SWPtr a _) => Some (SWInt (zwrap fs a (2 ^ 64)))
      | _ => None
      end
  end.

(** A flight inherits the capability of its source pointer, or no capability. *)
Definition sflight_cap (ge : genv) (fs : facts) (se : senv) (lw : flight_lower) : option scap :=
  match lw with
  | LowerNone => Some SCNone
  | LowerOf v => match svalue ge fs se P v with Some (SWPtr _ c) => Some c | _ => None end
  end.

(** Symbolic assignments replace earlier bindings and record their execution order. *)
Definition sbind (d : name) (w : sword) (s : sstate) : sstate :=
  mkSState (put d w (st_env s)) (st_ups s ++ [(d, w)]) (st_heap s) (st_obs s).

(** Each memory step appends its remaining conditions without changing their meaning. *)
Definition sobserve (os : list ob) (s : sstate) : sstate :=
  mkSState (st_env s) (st_ups s) (st_heap s) (st_obs s ++ os).

(** A raw address adds its displacement before wrapping to the machine's address width. *)
Definition sraw (fs : facts) (a : zexp) (off : Z) : zexp := zwrap fs (ZAdd a (ZK off)) (2 ^ 64).

(** A missing temporary is reported before an instruction's other unsupported operands. *)
Definition operand_stop (se : senv) (i : inst) : stop_reason :=
  let fix missing ns :=
    match ns with
    | [] => Unsupported i
    | n :: ns => match lookup n se with None => UnknownTmp n | Some _ => missing ns end
    end in missing (Validate.inst_uses i).

(** A known symbolic binding denotes the same value as the real environment. *)
Lemma env_models_lookup ρ se e n w : env_models ρ se e ->
  lookup n se = Some w -> lookup n e = Some (wden ρ w).
Proof.
  intros H. induction H as [|[n' w'] se Hnw Hse IH]; cbn [lookup]; [discriminate|].
  destruct (name_eqb n n') eqn:E.
  - apply term_eqb_eq in E. subst n'. intros H. inversion H; subst. exact Hnw.
  - exact IH.
Qed.

(** Reading a register class agrees with the model's truncation of a word. *)
Lemma sword_at_sound ρ fs k w w' : facts_hold ρ fs ->
  sword_at fs k w = Some w' -> word_at_class k (wden ρ w) = Some (wden ρ w').
Proof.
  intros Hfs. destruct k, w; cbn [sword_at]; try discriminate;
    intros H; inversion H; subst; cbn [word_at_class wden];
    rewrite ?(zwrap_sound _ _ _ _ Hfs); reflexivity.
Qed.

(** Quoting a global pointer preserves both its address and its capability. *)
Lemma quote_ptr_sound ρ p w : quote_ptr p = Some w -> wden ρ w = WPtr p.
Proof.
  destruct p as [a c]. destruct c; cbn [quote_ptr ptr_cap ptr_addr];
    try discriminate; intros H; inversion H; reflexivity.
Qed.

(** Symbolic operand evaluation agrees with the model under the known environment. *)
Lemma svalue_sound ρ ge fs se e k v w : facts_hold ρ fs -> env_models ρ se e ->
  svalue ge fs se k v = Some w -> value_x ge e k v = Some (wden ρ w).
Proof.
  intros Hfs Henv. destruct v; cbn [svalue value_x].
  - destruct (lookup n se) as [w'|] eqn:E; [|discriminate].
    rewrite (env_models_lookup _ _ _ _ _ Henv E).
    apply sword_at_sound. exact Hfs.
  - destruct k; cbn; intros H; inversion H; reflexivity.
  - destruct (lookup s (ge_globals ge)) as [p|] eqn:E; [|discriminate].
    intros H. rewrite (quote_ptr_sound _ _ _ H). reflexivity.
Qed.

(** A list of symbolic arguments denotes exactly the model's argument list. *)
Lemma svalues_sound ρ ge fs se e ks vs ws : facts_hold ρ fs -> env_models ρ se e ->
  map2_option (svalue ge fs se) ks vs = Some ws ->
  map2_option (value_x ge e) ks vs = Some (map (wden ρ) ws).
Proof.
  intros Hfs Henv. revert vs ws. induction ks as [|k ks IH]; intros vs ws;
    destruct vs as [|v vs]; cbn; try discriminate.
  - intros H. inversion H. reflexivity.
  - destruct (svalue ge fs se k v) as [w|] eqn:E; [|discriminate].
    destruct (map2_option (svalue ge fs se) ks vs) as [ws'|] eqn:Es; [|discriminate].
    intros H. inversion H; subst. rewrite (svalue_sound _ _ _ _ _ _ _ _ Hfs Henv E).
    rewrite (IH _ _ Es). reflexivity.
Qed.

(** Structural capability comparison never identifies distinct runtime capabilities. *)
Lemma csame_sound ρ fs a b : facts_hold ρ fs -> csame fs a b = true -> cden ρ a = cden ρ b.
Proof.
  intros Hfs. destruct a, b; cbn [csame]; try discriminate; intros H; try reflexivity.
  - cbn [cden]. f_equal. eapply zlinear_eqb_sound; eauto.
  - cbn [cden]. f_equal. eapply zlinear_eqb_sound; eauto.
  - apply Nat.eqb_eq in H. subst. reflexivity.
Qed.

(** Capability equations are used in either direction, without changing their interpretation. *)
Lemma cequal_sound ρ fs a b : facts_hold ρ fs -> cequal fs a b = true -> cden ρ a = cden ρ b.
Proof.
  intros Hfs. unfold cequal. rewrite orb_true_iff. intros [H|H].
  - eapply csame_sound; eauto.
  - apply existsb_exists in H as [[x y] [Hin H]].
    pose proof (proj2 Hfs) as Hcs. rewrite Forall_forall in Hcs.
    specialize (Hcs _ Hin). cbn in Hcs, H.
    apply orb_true_iff in H as [H|H]; apply andb_true_iff in H as [H1 H2];
      apply (csame_sound _ _ _ _ Hfs) in H1; apply (csame_sound _ _ _ _ Hfs) in H2; congruence.
Qed.

(** Finding an object equation justifies using its base in a memory rule. *)
Lemma object_find_sound ρ fs c cs b : facts_hold ρ fs ->
  Forall (fun ce => cden ρ (fst ce) = cden ρ (snd ce)) cs ->
  object_find fs c cs = Some b -> cden ρ c = Obj (zden ρ b).
Proof.
  intros Hfs Hcs. induction Hcs as [|[a d] cs Had Hcs IH]; cbn [object_find]; [discriminate|].
  destruct a, d; cbn [fst snd] in Had; cbn [object_find]; try exact IH;
    match goal with |- context [if ?test then _ else _] => destruct test eqn:E end;
    try exact IH; intros H; injection H as <-;
    apply (csame_sound _ _ _ _ Hfs) in E; cbn [cden] in Had, E; congruence.
Qed.

(** A known object base denotes the pointer's actual capability. *)
Lemma object_base_sound ρ fs c b : facts_hold ρ fs ->
  object_base fs c = Some b -> cden ρ c = Obj (zden ρ b).
Proof.
  intros Hfs. destruct c; cbn [object_base];
    try (eapply object_find_sound; [exact Hfs|exact (proj2 Hfs)]).
  intros H. injection H as <-. reflexivity.
Qed.

(** Integer comparison support depends on the condition and class, not on the operands. *)
Lemma cond_bit_total c k v x y : cond_bit c k 0 0 = Some v ->
  exists w, cond_bit c k x y = Some w.
Proof.
  destruct c, k; cbn [cond_bit signed modulus half_modulus];
    try discriminate; intros; eexists; reflexivity.
Qed.

(** Symbolic integer arithmetic agrees with the model's arithmetic evaluator. *)
Lemma salu_sound ρ fs o k xs w : facts_hold ρ fs ->
  salu fs o k xs = Some w -> alu o k (map (wden ρ) xs) = Some (wden ρ w).
Proof.
  intros Hfs. destruct o; cbn [salu]; try discriminate;
    destruct xs as [|x [|y [|z xs]]]; try discriminate;
    destruct x; try discriminate; try destruct y; try discriminate;
    cbn [salu]; try discriminate.
  all: try (intros H; inversion H; subst; reflexivity).
  all: try solve [destruct k; try discriminate; intros H; injection H as <-; reflexivity].
  - destruct (modulus k) eqn:E; [|discriminate].
    intros H. injection H as <-.
    change (alu Add k [WInt (zden ρ x); WInt (zden ρ x0)] =
      Some (WInt (zden ρ (zwrap fs (ZAdd x x0) z)))).
    rewrite (zwrap_sound _ _ _ _ Hfs). cbn [alu zden]. rewrite E. reflexivity.
  - destruct (modulus k) eqn:E; [|discriminate].
    intros H. injection H as <-.
    change (alu Sub k [WInt (zden ρ x); WInt (zden ρ x0)] =
      Some (WInt (zden ρ (zwrap fs (ZSub x x0) z)))).
    rewrite (zwrap_sound _ _ _ _ Hfs). cbn [alu zden]. rewrite E. reflexivity.
  - destruct (cond_bit c k0 0 0) eqn:E; [|discriminate].
    intros H. injection H as <-.
    change (alu (Cmp c k0) k [WInt (zden ρ x); WInt (zden ρ x0)] =
      Some (WInt (zden ρ (zclean fs (ZCmp c k0 x x0))))).
    rewrite (zclean_sound _ _ _ Hfs). cbn [alu zden].
    destruct (cond_bit_total _ _ _ (zden ρ x) (zden ρ x0) E) as [v Ev].
    rewrite Ev. reflexivity.
  - destruct (modulus k) eqn:E; [|discriminate].
    intros H. injection H as <-.
    change (alu (Ext t) k [WInt (zden ρ x)] =
      Some (WInt (zden ρ (zextend fs t x z)))).
    rewrite (zextend_sound _ _ _ _ _ Hfs). cbn [alu zden]. rewrite E. reflexivity.
Qed.

(** Updating a temporary preserves every other known binding. *)
Lemma env_models_put ρ se e d w : env_models ρ se e ->
  env_models ρ (put d w se) (put d (wden ρ w) e).
Proof.
  intros Henv. unfold env_models, put. constructor.
  - cbn [fst snd lookup]. rewrite /name_eqb term_eqb_refl. reflexivity.
  - apply Forall_forall. intros [n v] Hin. apply filter_In in Hin as [Hin Hneq].
    cbn in Hneq. apply negb_true_iff in Hneq.
    assert (Hnd : name_eqb n d = false).
    { destruct (name_eqb n d) eqn:E; [|reflexivity].
      apply term_eqb_eq in E. subst. rewrite /name_eqb term_eqb_refl in Hneq. discriminate. }
    cbn [fst snd]. change (lookup n (put d (wden ρ w) e) = Some (wden ρ v)).
    apply lookup_put_miss; [exact Hnd|].
    unfold env_models in Henv. rewrite Forall_forall in Henv. exact (Henv _ Hin).
Qed.

(** Appending an assignment gives exactly the environment used by the instruction rule. *)
Lemma apply_ups_sbind ρ s d w e :
  apply_ups ρ (st_ups (sbind d w s)) e = put d (wden ρ w) (apply_ups ρ (st_ups s) e).
Proof. unfold apply_ups, sbind. cbn. rewrite fold_left_app. reflexivity. Qed.

(** Flight arguments denote the same integer words as the model's argument evaluator. *)
Lemma sflight_arg_sound ρ ge fs se e a w : facts_hold ρ fs -> env_models ρ se e ->
  sflight_arg ge fs se a = Some w -> flight_arg_x ge e a = Some (wden ρ w).
Proof.
  intros Hfs Henv. destruct a as [v|v]; cbn [sflight_arg flight_arg_x].
  - apply svalue_sound; assumption.
  - destruct (svalue ge fs se P v) as [[x|x c]|] eqn:E; try discriminate.
    intros H. injection H as <-. rewrite (svalue_sound _ _ _ _ _ _ _ _ Hfs Henv E).
    change (Some (WInt (zden ρ x mod 2 ^ 64)) = Some (WInt (zden ρ (zwrap fs x (2 ^ 64))))).
    rewrite (zwrap_sound _ _ _ _ Hfs). reflexivity.
Qed.

(** Flight capability selection preserves the source pointer's runtime capability. *)
Lemma sflight_cap_sound ρ ge fs se e lw c : facts_hold ρ fs -> env_models ρ se e ->
  sflight_cap ge fs se lw = Some c -> flight_cap ge e lw = Some (cden ρ c).
Proof.
  intros Hfs Henv. destruct lw as [|v]; cbn [sflight_cap flight_cap].
  - intros H. injection H as <-. reflexivity.
  - destruct (svalue ge fs se P v) as [[x|x c']|] eqn:E; try discriminate.
    intros H. injection H as <-. rewrite (svalue_sound _ _ _ _ _ _ _ _ Hfs Henv E). reflexivity.
Qed.

(** Mapping symbolic flight arguments preserves every argument in order. *)
Lemma sflight_args_sound ρ ge fs se e args xs : facts_hold ρ fs -> env_models ρ se e ->
  map_option (sflight_arg ge fs se) args = Some xs ->
  map_option (flight_arg_x ge e) args = Some (map (wden ρ) xs).
Proof.
  intros Hfs Henv. revert xs. induction args as [|a args IH]; intros xs; cbn.
  - intros H. injection H as <-. reflexivity.
  - destruct (sflight_arg ge fs se a) as [x|] eqn:E; [|discriminate].
    destruct (map_option (sflight_arg ge fs se) args) as [ys|] eqn:Es; [|discriminate].
    intros H. injection H as <-. rewrite (sflight_arg_sound _ _ _ _ _ _ _ Hfs Henv E).
    rewrite (IH _ eq_refl). reflexivity.
Qed.

(** General symbolic lets are pure operations with the result predicted by the executor. *)
Lemma sop_sound ρ fs o k xs w : facts_hold ρ fs -> sop fs o k xs = Some w ->
  general_op o = true /\ forall m, op_res o k (map (wden ρ) xs) m = Some (OpRes (RVal (wden ρ w)) m).
Proof.
  intros Hfs H. destruct o, k; cbn [sop float_class] in H; try discriminate.
  all: try solve [split; [reflexivity|]; intros m;
    cbn [op_res op_res_int additive_res fmt_of];
    rewrite (salu_sound _ _ _ _ _ _ Hfs H); reflexivity].
  all: try (destruct xs as [|x [|y [|z xs]]]; try discriminate;
    destruct x; try discriminate; try destruct y; try discriminate).
  all: try solve [injection H as <-; split; [reflexivity|]; intros m;
    change (Some (OpRes (RVal (WPtr (mkPtr ((zden ρ a + zden ρ x) mod 2 ^ 64) (cden ρ c)))) m) =
      Some (OpRes (RVal (WPtr (mkPtr (zden ρ (zwrap fs (ZAdd a x) (2 ^ 64))) (cden ρ c)))) m));
    rewrite (zwrap_sound _ _ _ _ Hfs); reflexivity].
  all: try solve [injection H as <-; split; [reflexivity|]; intros m;
    change (Some (OpRes (RVal (WPtr (mkPtr ((zden ρ a - zden ρ x) mod 2 ^ 64) (cden ρ c)))) m) =
      Some (OpRes (RVal (WPtr (mkPtr (zden ρ (zwrap fs (ZSub a x) (2 ^ 64))) (cden ρ c)))) m));
    rewrite (zwrap_sound _ _ _ _ Hfs); reflexivity].
  all: destruct k0; cbn [float_class] in H; try discriminate.
  all: pose proof (salu_sound _ _ _ _ _ _ Hfs H) as E.
  all: destruct xs as [|x [|y [|z xs]]]; cbn [map alu] in E; try discriminate;
    destruct x; cbn [wden] in E; try discriminate;
    destruct y; cbn [wden] in E; try discriminate.
  all: split; try reflexivity; intros m;
    cbn [op_res op_res_int fmt_of map wden];
    match type of E with context [cond_bit ?c ?k ?x ?y] => destruct (cond_bit c k x y) eqn:Ec end;
    try discriminate;
    injection E as E; rewrite <- E; cbn [alu]; rewrite Ec; reflexivity.
Qed.

(** ## Selecting owned memory

    A memory rule needs separate ownership of each resource it consumes.
    Selection removes an atom while searching for the next resource, so
    one lifetime cannot accidentally satisfy two separating premises. *)

(** Selection retains the atoms on either side so that their names keep their order. *)
Fixpoint pick_atom (test : atom -> bool) (h : list atom) : option (list atom * atom * list atom) :=
  match h with
  | [] => None
  | a :: h => if test a then Some ([], a, h) else
      match pick_atom test h with
      | Some (pre, a', post) => Some (a :: pre, a', post)
      | None => None
      end
  end.

(** A live object can be supplied directly or through an equivalent capability lifetime. *)
Definition is_live (fs : facts) (b : zexp) (a : atom) : bool :=
  match a with
  | ALive b' _ => zlinear_eqb fs b b'
  | ALiveCap c _ => cequal fs (SCObj b) c
  | _ => false
  end.

(** Both forms of lifetime ownership carry a region number. *)
Definition atom_region (a : atom) : nat :=
  match a with ALive _ r | ALiveCap _ r => r | _ => O end.

(** Cell selection compares both the object's base and the full access address. *)
Definition is_cell (fs : facts) (pointer : bool) (b addr : zexp) (a : atom) : bool :=
  match pointer, a with
  | false, ACell b' o _ | true, APCell b' o _ _ =>
      zlinear_eqb fs b b' && zlinear_eqb fs addr (ZAdd b' o)
  | _, _ => false
  end.

(** A narrow load selects a cell with the same byte width and address. *)
Definition is_narrow (fs : facts) (n : narrow) (b addr : zexp) (a : atom) : bool :=
  match a with
  | ANarrow t b' o _ =>
      Z.eqb (fst (narrow_type n)) (fst (narrow_type t)) &&
      zlinear_eqb fs b b' && zlinear_eqb fs addr (ZAdd b' o)
  | _ => false
  end.

(** A loaded pointer needs its own target lifetime, apart from the source object's lifetime. *)
Definition is_cap (fs : facts) (c : scap) (a : atom) : bool :=
  match a with
  | ALive b _ => cequal fs c (SCObj b)
  | ALiveCap c' _ => cequal fs c c'
  | _ => false
  end.

(** A check records its range and alignment conditions for the leaf proof. *)
Definition check_obs (fs : facts) (b addr : zexp) (r : nat) (lo hi al : Z) : list ob :=
  let a := sraw fs addr lo in
  [OLe b a; OLe (ZAdd a (ZK (hi - lo))) (ZEnd r); OEq (ZMod a al) (ZK 0)].

(** Checks and loads preserve owned memory and assign their result to a temporary. *)
Definition smemory (fs : facts) (s : sstate) (d : name) (k : class) (o : op)
    (xs : list sword) (fallback : stop_reason) : (stop_reason + sstate)%type :=
  let access p extra :=
    match p with
    | SWInt _ => inl fallback
    | SWPtr addr c =>
        match object_base fs c with
        | None => inl (NotObject c)
        | Some b =>
            match pick_atom (is_live fs b) (st_heap s) with
            | None => inl (NoLive b)
            | Some (pre, live, post) =>
                let r := atom_region live in
                match o with
                | Check lo hi _ al =>
                    inr (sbind d p (sobserve (check_obs fs b addr r lo hi al) s))
                | Renew lo hi _ al =>
                    match extra with
                    | Some (SWPtr _ c1) =>
                        if cequal fs c1 (SCObj b) then
                          inr (sbind d p (sobserve (check_obs fs b addr r lo hi al) s))
                        else inl (NotObject c1)
                    | _ => inl fallback
                    end
                | HalfCheck _ lo hi _ al =>
                    match extra with
                    | Some (SWPtr _ c1) =>
                        if cequal fs c1 (SCObj b) then
                          inr (sbind d p (sobserve
                            (check_obs fs b addr r lo hi al ++ [OLt (ZK lo) (ZK hi); OLe (ZEnd r) (ZK (2 ^ 63))]) s))
                        else inl (NotObject c1)
                    | _ => inl fallback
                    end
                | RawLoad LdL off =>
                    let a := sraw fs addr off in
                    match pick_atom (is_cell fs false b a) (pre ++ post) with
                    | Some (_, ACell _ _ v, _) => inr (sbind d (SWInt (zwrap fs v (2 ^ 64))) s)
                    | _ => inl (NoCell b (ZSub a b))
                    end
                | RawLoad (LdNarrow n) off =>
                    let a := sraw fs addr off in
                    match modulus k, pick_atom (is_narrow fs n b a) (pre ++ post) with
                    | Some m, Some (_, ANarrow t _ _ v, _) =>
                        inr (sbind d (SWInt (zextend fs n
                          (zwrap fs v (2 ^ (8 * fst (narrow_type t)))) m)) s)
                    | _, _ => inl (NoCell b (ZSub a b))
                    end
                | RawLoadPointer off [AuxRead; LowerResolve; AddressRead] =>
                    let a := sraw fs addr off in
                    match pick_atom (is_cell fs true b a) (pre ++ post) with
                    | Some (pre', APCell b' off' v c', post') =>
                        match pick_atom (is_cap fs c') (pre' ++ post') with
                        | Some _ => inr (sbind d (SWPtr v c') (sobserve
                            [OEq (ZMod (ZAdd b' off') 8) (ZK 0); OLe (ZK 0) v; OLt v (ZK (2 ^ 64))] s))
                        | None => inl (NoLiveCap c')
                        end
                    | _ => inl (NoCell b (ZSub a b))
                    end
                | _ => inl fallback
                end
            end
        end
    end in
  match o, k, xs with
  | Check _ _ _ _, A, [p] => access p None
  | Renew _ _ _ _, A, [p1; p] => access p (Some p1)
  | HalfCheck _ _ _ _ _, A, [p1; p] => access p (Some p1)
  | RawLoad LdL _, _, [p] => access p None
  | RawLoad (LdNarrow _) _, _, [p] => access p None
  | RawLoadPointer _ [AuxRead; LowerResolve; AddressRead], P, [p] => access p None
  | _, _, _ => inl fallback
  end.

(** A store replaces only its selected cell and leaves a world-preservation obligation. *)
Definition sstore (fs : facts) (s : sstate) (pointer : bool) (off : Z)
    (v p : sword) (fallback : stop_reason) : (stop_reason + sstate)%type :=
  match p with
  | SWInt _ => inl fallback
  | SWPtr addr c =>
      match object_base fs c with
      | None => inl (NotObject c)
      | Some b =>
          match pick_atom (is_live fs b) (st_heap s) with
          | None => inl (NoLive b)
          | Some (pre, live, post) =>
              let r := atom_region live in let a := sraw fs addr off in
              match pick_atom (is_cell fs pointer b a) (pre ++ post) with
              | Some (pre', cell, post') =>
                  let updated new os :=
                    mkSState (st_env s) (st_ups s)
                      (live :: pre' ++ new :: post') (st_obs s ++ os) in
                  match pointer, cell, v with
                  | false, ACell b' off' old, SWInt new =>
                      inr (updated (ACell b' off' new) [OStoreW b' off' r old new])
                  | true, APCell b' off' old c', SWPtr new nc =>
                      inr (updated (APCell b' off' new nc)
                        [OEq (ZMod (ZAdd b' off') 8) (ZK 0); OStoreP b' off' r (SWPtr old c') v])
                  | _, _, _ => inl fallback
                  end
              | None => inl (NoCell b (ZSub a b))
              end
          end
      end
  end.

(** One instruction either advances the symbolic state or explains why it cannot advance. *)
Definition sym_step (ge : genv) (fs : facts) (s : sstate) (i : inst) : (stop_reason + sstate)%type :=
  let se := st_env s in let fallback := operand_stop se i in
  match i with
  | Let d k o args =>
      match op_arg_classes o k with
      | None => inl fallback
      | Some classes =>
          match map2_option (svalue ge fs se) classes args with
          | None => inl fallback
          | Some xs =>
              match sop fs o k xs with
              | Some w => inr (sbind d w s)
              | None => smemory fs s d k o xs fallback
              end
          end
      end
  | Flight d o args lw =>
      match map_option (sflight_arg ge fs se) args, sflight_cap ge fs se lw with
      | Some xs, Some c =>
          match salu fs o L xs with
          | Some (SWInt a) => inr (sbind d (SWPtr a c) s)
          | _ => inl fallback
          end
      | _, _ => inl fallback
      end
  | RawStore Wl off v p =>
      match svalue ge fs se L v, svalue ge fs se A p with
      | Some v, Some p => sstore fs s false off v p fallback
      | _, _ => inl fallback
      end
  | RawStorePointer off v p [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite] =>
      match svalue ge fs se P v, svalue ge fs se A p with
      | Some v, Some p => sstore fs s true off v p fallback
      | _, _ => inl fallback
      end
  | _ => inl (Unsupported i)
  end.

(** A block stops at its first unsupported instruction, preserving all preceding progress. *)
Fixpoint sym_exec (ge : genv) (fs : facts) (s : sstate) (insts : list inst) (j : jump) : leaf :=
  match insts with
  | i :: rest =>
      match sym_step ge fs s i with
      | inl why => LStop why insts j s
      | inr s' => sym_exec ge fs s' rest j
      end
  | [] =>
      match j with
      | JGoto t => LGoto t s
      | JBranch v t1 t2 =>
          match svalue ge fs (st_env s) W v with
          | Some (SWInt c) => LBranch c t1 t2 s
          | _ => LStop (match v with Tmp n => UnknownTmp n | _ => UnsupportedJump j end) [] j s
          end
      | _ => LStop (UnsupportedJump j) [] j s
      end
  end.

(** ## The executor

    The executor walks the block's instructions with the facts, the
    known environment and the owned atoms. A supported instruction updates
    this description; an unsupported instruction returns control to the
    ordinary step tactics with a reason for stopping. *)

(** [sym_block] ge fs se h l insts j runs the instructions insts and the
    jump j of the block labelled l, starting from the known environment
    se and the atoms h. It handles integer arithmetic, flag operations,
    shifts, extensions, copies, comparisons and flights. Memory operations
    include checks, half checks, renewals, integer and pointer loads,
    narrow loads, and 64-bit integer and pointer stores with writable object capabilities.
    It finds an atom by comparing base expressions
    and offsets after removing wraps that the bounds make redundant,
    settles comparisons between constants itself, and leaves every
    other condition as an [ob]. *)
Definition sym_block (ge : genv) (fs : facts) (se : senv) (h : list atom)
    (l : name) (insts : list inst) (j : jump) : leaf :=
  sym_exec ge fs (mkSState se [] h []) insts j.

(** A checked pointer load reaches its target with its value and ownership intact. *)
Example sym_check_pointer_goto ge :
  let h := [ALive (ZK 4096) 0; APCell (ZK 4096) (ZK 8) (ZK 8200) (SCObj (ZK 8192));
            ALiveCap (SCObj (ZK 8192)) 1] in
  match sym_block ge (mkFacts [] [])
    [(TAtom "p", SWPtr (ZK 4104) (SCObj (ZK 4096)))] h (TAtom "entry")
    [Let (TAtom "checked") A (Check 0 8 Read 8) [Tmp (TAtom "p")];
     Let (TAtom "loaded") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [Tmp (TAtom "checked")]]
    (JGoto (To (TAtom "next"))) with
  | LGoto (To target) s =>
      target = TAtom "next" /\
      lookup (TAtom "loaded") (st_env s) = Some (SWPtr (ZK 8200) (SCObj (ZK 8192))) /\
      st_heap s = h /\ List.length (st_obs s) = 6%nat
  | _ => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Renewal preserves the new address, but rejects an earlier check of a different object's capability. *)
Example sym_renew_run ge :
  let run c := sym_block ge (mkFacts [] [])
    [(TAtom "old", SWPtr (ZK 4100) c);
     (TAtom "new", SWPtr (ZK 4104) (SCObj (ZK 4096)))]
    [ALive (ZK 4096) 0] (TAtom "entry")
    [Let (TAtom "checked") A (Renew 0 8 Read 8) [Tmp (TAtom "old"); Tmp (TAtom "new")]]
    (JGoto (To (TAtom "next"))) in
  (match run (SCObj (ZK 4096)) with
   | LGoto _ s => lookup (TAtom "checked") (st_env s) = Some (SWPtr (ZK 4104) (SCObj (ZK 4096))) /\
       st_heap s = [ALive (ZK 4096) 0] /\ List.length (st_obs s) = 3%nat
   | _ => False
   end) /\
  (match run (SCObj (ZK 8192)) with LStop (NotObject _) _ _ _ => True | _ => False end).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Loads at each sign boundary distinguish sign extension from zero extension and preserve the owned bytes. *)
Example sym_narrow_loads ge :
  Forall (fun test =>
    let '(n, k, v, expected) := test in
    let h := [ALive (ZK 4096) 0; ANarrow n (ZK 4096) (ZK 0) (ZK v)] in
    match sym_block ge (mkFacts [] [])
      [(TAtom "p", SWPtr (ZK 4096) (SCObj (ZK 4096)))] h (TAtom "entry")
      [Let (TAtom "loaded") k (RawLoad (LdNarrow n) 0) [Tmp (TAtom "p")]]
      (JGoto (To (TAtom "next"))) with
    | LGoto _ s =>
        option_map (wden (mkVal [] [] [])) (lookup (TAtom "loaded") (st_env s)) = Some (WInt expected) /\
        st_heap s = h
    | _ => False
    end)
    [(Sb, L, 127, 127); (Sb, L, 128, 2 ^ 64 - 128); (Ub, L, 128, 128);
     (Sh, L, 32767, 32767); (Sh, L, 32768, 2 ^ 64 - 32768); (Uh, L, 32768, 32768);
     (Sw, L, 2 ^ 31 - 1, 2 ^ 31 - 1); (Sw, L, 2 ^ 31, 2 ^ 64 - 2 ^ 31);
     (Uw, L, 2 ^ 31, 2 ^ 31); (Sw, W, 2 ^ 31, 2 ^ 31); (Ub, W, 257, 1)].
Proof.
  repeat (apply Forall_cons; [vm_compute; split; reflexivity|]). apply Forall_nil.
Qed.

(** Flag operations and wrapped shift counts agree with concrete register arithmetic. *)
Example sym_flag_operations :
  map (fun test => let '(o, k, x, y) := test in
    option_map (wden (mkVal [] [] [])) (salu (mkFacts [] []) o k [SWInt (ZK x); SWInt (ZK y)]))
    [(And, W, 165, 15); (Or, W, 160, 15); (Xor, W, 165, 15);
     (Shl, W, 3, 33); (Shr, W, 2147483648, 1); (Sar, W, 2147483648, 1)] =
    map (fun x => Some (WInt x)) [5; 175; 170; 6; 1073741824; 3221225472].
Proof. vm_compute. reflexivity. Qed.

(** ## Soundness

    The meaning of an atom is the logic's assertion it names, and the
    meaning of a leaf is what the proof must still show. The theorem
    [sym_sound] then says that showing the leaf proves the block. *)

Section sound.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
Local Instance sym_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** An atom means the assertion it names. A region variable outside
    the valuation makes the atom false. *)
Definition atom_den (ρ : valuation) (a : atom) : iProp Σ :=
  match a with
  | ALive b r => match nth_error (vr ρ) r with Some reg => live (zden ρ b) reg | None => False end
  | ACell b o v => icell (zden ρ b) (zden ρ o) (zden ρ v)
  | APCell b o a c => pcell (zden ρ b) (zden ρ o) (mkPtr (zden ρ a) (cden ρ c))
  | ALiveCap c r => match nth_error (vr ρ) r with Some reg => live_cap (cden ρ c) reg | None => False end
  | ANarrow n b o v => sym_ML.bytes (zden ρ b) (zden ρ o) (sym_bytes n (zden ρ v))
  end.

(** A list of atoms means their separating conjunction, written so that
    it computes to the nested form that the proof mode combines. *)
Fixpoint heap_den (ρ : valuation) (h : list atom) : iProp Σ :=
  match h with
  | [] => emp
  | a :: h => atom_den ρ a ∗ heap_den ρ h
  end.

(** A store must preserve the external world's interpretation of memory.
    Its premise lists the object lifetime before the cell's owned pieces. *)
Definition cell_pieces (b o : Z) (reg : region) (w : word) : list (piece * pval) :=
  match w with
  | WInt v => [(PLive b, VLive reg)] ++ cell b o v
  | WPtr x => [(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x)
  | WLimit _ _ => []
  end.

(** A condition means the corresponding proposition. The world
    condition of a store is the premise that [wp_raw_store] and
    [wp_raw_store_pointer] take. *)
Definition ob_den (ρ : valuation) (o : ob) : Prop :=
  match o with
  | OLe a b => zden ρ a <= zden ρ b
  | OLt a b => zden ρ a < zden ρ b
  | OEq a b => zden ρ a = zden ρ b
  | OStoreW b o r old new =>
      exists reg, nth_error (vr ρ) r = Some reg /\
      let b' := zden ρ b in let o' := zden ρ o in
      forall m wd h,
        (forall l v, (l, v) ∈ cell_pieces b' o' reg (WInt (zden ρ old)) -> h !! l = Some v) ->
        wi m wd h ->
        wi (store_bytes m (b' + o') 8 (zden ρ new)) wd
           (overwrite (cell_pieces b' o' reg (WInt (zden ρ new))) h)
  | OStoreP b o r old new =>
      exists reg, nth_error (vr ρ) r = Some reg /\
      match wden ρ old, wden ρ new with
      | WPtr x, WPtr xp =>
          let b' := zden ρ b in let o' := zden ρ o in
          forall m wd h,
            (forall l v, (l, v) ∈ cell_pieces b' o' reg (WPtr x) -> h !! l = Some v) ->
            wi m wd h ->
            wi (store_bytes (store_aux m (b' + o') (ptr_cap xp)) (b' + o') 8 (ptr_addr xp)) wd
               (overwrite (cell_pieces b' o' reg (WPtr xp)) h)
      | _, _ => False
      end
  end.

(** All conditions of a list hold. *)
Definition obs_den (ρ : valuation) (os : list ob) : Prop := Forall (ob_den ρ) os.

(** A leaf describes what remains to prove. After a jump or a branch the
    rest of the proof comes after at least one step, so it may use
    hypotheses guarded by a [[later-modality]]. The new atoms and the
    facts about the new environment are handed to it as premises. A
    stopped execution returns the remaining instructions to the
    ordinary step tactics. *)
Definition leaf_den (ρ : valuation) (f : func) (e : env) (ls : list (name * option Z))
    (l : name) (Φ : val (nanofil_lang registry ge) -> iProp Σ) (lf : leaf) : iProp Σ :=
  match lf with
  | LGoto t s =>
      let e' := apply_ups ρ (st_ups s) e in
      ⌜obs_den ρ (st_obs s)⌝ ∗
      ▷ (heap_den ρ (st_heap s) -∗ ⌜env_models ρ (st_env s) e'⌝ -∗
         WP (ERun (mkFrame f e' ls None (Enter (edge_label t) (Some l))) : gexpr) {{ Φ }})
  | LBranch c t1 t2 s =>
      let e' := apply_ups ρ (st_ups s) e in
      ⌜obs_den ρ (st_obs s)⌝ ∗
      ▷ (heap_den ρ (st_heap s) -∗ ⌜env_models ρ (st_env s) e'⌝ -∗
         WP (ERun (mkFrame f e' ls None
              (Enter (edge_label (if zden ρ c =? 0 then t2 else t1)) (Some l))) : gexpr) {{ Φ }})
  | LStop _ rest j s =>
      let e' := apply_ups ρ (st_ups s) e in
      ⌜obs_den ρ (st_obs s)⌝ ∗
      (heap_den ρ (st_heap s) -∗ ⌜env_models ρ (st_env s) e'⌝ -∗
       WP (ERun (mkFrame f e' ls None (Exec l rest j)) : gexpr) {{ Φ }})
  end.

(** Selecting an atom partitions the original list and establishes its selection test. *)
Lemma pick_atom_sound test h pre a post : pick_atom test h = Some (pre, a, post) ->
  h = pre ++ a :: post /\ test a = true.
Proof.
  revert pre a post. induction h as [|x h IH]; intros pre a post; cbn; [discriminate|].
  destruct (test x) eqn:E.
  - intros H. inversion H; subst. auto.
  - destruct (pick_atom test h) as [[[p y] q]|] eqn:Ep; [|discriminate].
    intros H. inversion H; subst. destruct (IH _ _ _ eq_refl) as [-> Hy]. auto.
Qed.

(** Concatenating atom lists corresponds to separating their ownership. *)
Lemma heap_den_app ρ h1 h2 : heap_den ρ (h1 ++ h2) ⊣⊢ heap_den ρ h1 ∗ heap_den ρ h2.
Proof.
  induction h1 as [|a h1 IH]; cbn [heap_den app].
  - rewrite bi.emp_sep. reflexivity.
  - rewrite IH bi.sep_assoc. reflexivity.
Qed.

(** A selected atom can be removed and returned without changing the other resources. *)
Lemma heap_den_pick ρ test h pre a post : pick_atom test h = Some (pre, a, post) ->
  heap_den ρ h ⊣⊢ atom_den ρ a ∗ heap_den ρ (pre ++ post).
Proof.
  intros H. destruct (pick_atom_sound _ _ _ _ _ H) as [-> _].
  rewrite !heap_den_app /=. iSplit; iIntros "(H1 & H2 & H3)"; iFrame.
Qed.

(** A matching lifetime atom owns the live object required by a memory rule. *)
Lemma is_live_den ρ fs b a : facts_hold ρ fs -> is_live fs b a = true ->
  atom_den ρ a ⊣⊢
    match nth_error (vr ρ) (atom_region a) with
    | Some reg => live (zden ρ b) reg | None => False
    end.
Proof.
  intros Hfs. destruct a; cbn [is_live]; try discriminate; intros H.
  - apply (zlinear_eqb_sound _ _ _ _ Hfs) in H. cbn [atom_den atom_region].
    rewrite H. reflexivity.
  - apply (cequal_sound _ _ _ _ Hfs) in H. cbn [cden] in H.
    cbn [atom_den atom_region]. rewrite <- H. destruct (nth_error (vr ρ) r); reflexivity.
Qed.

(** A matching target lifetime prevents collection from changing a loaded capability. *)
Lemma is_cap_den ρ fs c a : facts_hold ρ fs -> is_cap fs c a = true ->
  atom_den ρ a ⊣⊢
    match nth_error (vr ρ) (atom_region a) with
    | Some reg => live_cap (cden ρ c) reg | None => False
    end.
Proof.
  intros Hfs. destruct a; cbn [is_cap]; try discriminate; intros H;
    apply (cequal_sound _ _ _ _ Hfs) in H; cbn [atom_den atom_region];
    rewrite H; destruct (nth_error (vr ρ) r); reflexivity.
Qed.

(** The symbolic access address denotes the same wrapped address as the machine. *)
Lemma sraw_sound ρ fs a off : facts_hold ρ fs ->
  zden ρ (sraw fs a off) = raw_address (zden ρ a) off.
Proof. intros Hfs. unfold sraw. rewrite (zwrap_sound _ _ _ _ Hfs). reflexivity. Qed.

(** Check obligations supply exactly the bounds and alignment premises of the check rule. *)
Lemma check_obs_sound ρ fs b a r reg lo hi al : facts_hold ρ fs ->
  nth_error (vr ρ) r = Some reg -> obs_den ρ (check_obs fs b a r lo hi al) ->
  zden ρ b <= raw_address (zden ρ a) lo /\
  raw_address (zden ρ a) lo + (hi - lo) <= r_end reg /\
  raw_address (zden ρ a) lo mod al = 0.
Proof.
  intros Hfs Hr H. unfold obs_den, check_obs in H.
  inversion H as [|? ? H1 Hs]; subst. inversion Hs as [|? ? H2 Hs']; subst.
  inversion Hs' as [|? ? H3 _]; subst.
  cbn [ob_den zden] in H1, H2, H3.
  rewrite Hr in H2. rewrite (sraw_sound _ _ _ _ Hfs) in H1, H2, H3. auto.
Qed.

(** A check uses the object's lifetime permission without consuming any owned memory. *)
Lemma sym_check_rule ρ fs h pre life post f e ls l d lo hi mode al args rest j classes a c b Φ :
  facts_hold ρ fs ->
  op_arg_classes (Check lo hi mode al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [wden ρ (SWPtr a c)] ->
  object_base fs c = Some b -> pick_atom (is_live fs b) h = Some (pre, life, post) ->
  obs_den ρ (check_obs fs b a (atom_region life) lo hi al) ->
  heap_den ρ h -∗
  ▷ (heap_den ρ h -∗ WP (ERun (mkFrame f (put d (wden ρ (SWPtr a c)) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (Check lo hi mode al) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hfs Hclasses Hargs Hobj Hp Hobs.
  pose proof (object_base_sound _ _ _ _ Hfs Hobj) as Hcap.
  destruct (pick_atom_sound _ _ _ _ _ Hp) as [_ Hlive].
  rewrite (heap_den_pick _ _ _ _ _ _ Hp) (is_live_den _ _ _ _ Hfs Hlive).
  destruct (nth_error (vr ρ) (atom_region life)) as [reg|] eqn:Hr; last first.
  { iIntros "[Hfalse _] _". iDestruct "Hfalse" as %[]. }
  destruct (check_obs_sound _ _ _ _ _ _ _ _ _ Hfs Hr Hobs) as [Hlo [Hhi Hal]].
  iIntros "[Hl Hrest] HK".
  iApply (wp_check with "Hl"); [exact Hclasses|exact Hargs|exact Hcap|exact Hlo|exact Hhi|exact Hal|].
  iNext. iIntros "Hl". iApply "HK". iFrame.
Qed.

(** Renewal reuses a matching capability and checks the new address against the live object's bounds. *)
Lemma sym_renew_rule ρ fs h pre life post f e ls l d lo hi mode al args rest j classes a1 c1 a c b Φ :
  facts_hold ρ fs ->
  op_arg_classes (Renew lo hi mode al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [wden ρ (SWPtr a1 c1); wden ρ (SWPtr a c)] ->
  object_base fs c = Some b -> cequal fs c1 (SCObj b) = true ->
  pick_atom (is_live fs b) h = Some (pre, life, post) ->
  obs_den ρ (check_obs fs b a (atom_region life) lo hi al) ->
  heap_den ρ h -∗
  ▷ (heap_den ρ h -∗ WP (ERun (mkFrame f (put d (wden ρ (SWPtr a c)) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (Renew lo hi mode al) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hfs Hclasses Hargs Hobj Hsame Hp Hobs.
  pose proof (object_base_sound _ _ _ _ Hfs Hobj) as Hcap.
  pose proof (cequal_sound _ _ _ _ Hfs Hsame) as Hcap1.
  cbn [cden] in Hcap1.
  destruct (pick_atom_sound _ _ _ _ _ Hp) as [_ Hlive].
  rewrite (heap_den_pick _ _ _ _ _ _ Hp) (is_live_den _ _ _ _ Hfs Hlive).
  destruct (nth_error (vr ρ) (atom_region life)) as [reg|] eqn:Hr; last first.
  { iIntros "[Hfalse _] _". iDestruct "Hfalse" as %[]. }
  destruct (check_obs_sound _ _ _ _ _ _ _ _ _ Hfs Hr Hobs) as [Hlo [Hhi Hal]].
  iIntros "[Hl Hrest] HK".
  iApply (wp_renew with "Hl");
    [exact Hclasses|exact Hargs|cbn; congruence|exact Hcap|exact Hlo|exact Hhi|exact Hal|].
  iNext. iIntros "Hl". iApply "HK". iFrame.
Qed.

(** A reflected half check also proves that both pointers name the same live object. *)
Lemma sym_half_check_rule ρ fs h pre life post f e ls l d bd lo hi mode al args rest j classes a1 c1 a c b Φ :
  facts_hold ρ fs ->
  op_arg_classes (HalfCheck bd lo hi mode al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [wden ρ (SWPtr a1 c1); wden ρ (SWPtr a c)] ->
  object_base fs c = Some b -> cequal fs c1 (SCObj b) = true ->
  pick_atom (is_live fs b) h = Some (pre, life, post) ->
  obs_den ρ (check_obs fs b a (atom_region life) lo hi al ++
    [OLt (ZK lo) (ZK hi); OLe (ZEnd (atom_region life)) (ZK (2 ^ 63))]) ->
  heap_den ρ h -∗
  ▷ (heap_den ρ h -∗ WP (ERun (mkFrame f (put d (wden ρ (SWPtr a c)) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (HalfCheck bd lo hi mode al) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hfs Hclasses Hargs Hobj Hsame Hp Hobs.
  pose proof (object_base_sound _ _ _ _ Hfs Hobj) as Hcap.
  pose proof (cequal_sound _ _ _ _ Hfs Hsame) as Hcap1.
  destruct (pick_atom_sound _ _ _ _ _ Hp) as [_ Hlive].
  rewrite (heap_den_pick _ _ _ _ _ _ Hp) (is_live_den _ _ _ _ Hfs Hlive).
  destruct (nth_error (vr ρ) (atom_region life)) as [reg|] eqn:Hr; last first.
  { iIntros "[Hfalse _] _". iDestruct "Hfalse" as %[]. }
  apply Forall_app in Hobs as [Hobs Hextra].
  inversion Hextra as [|? ? Hlt Htail]; subst. inversion Htail as [|? ? Hend _]; subst.
  cbn [ob_den zden] in Hlt, Hend. rewrite Hr in Hend.
  destruct (check_obs_sound _ _ _ _ _ _ _ _ _ Hfs Hr Hobs) as [Hlo [Hhi Hal]].
  iIntros "[Hl Hrest] HK".
  iApply (wp_half_check with "Hl");
    [exact Hclasses|exact Hargs|exact Hcap1|exact Hcap|exact Hlo|exact Hhi|exact Hlt|exact Hend|exact Hal|].
  iNext. iIntros "Hl". iApply "HK". iFrame.
Qed.

(** A reflected integer load returns the cell's value at the machine's register width. *)
Lemma sym_load_rule ρ fs h pre life post pre' post' f e ls l d k off args rest j classes a c b b' o v Φ :
  facts_hold ρ fs ->
  op_arg_classes (RawLoad LdL off) k = Some classes ->
  map2_option (value_x ge e) classes args = Some [wden ρ (SWPtr a c)] ->
  object_base fs c = Some b -> pick_atom (is_live fs b) h = Some (pre, life, post) ->
  pick_atom (is_cell fs false b (sraw fs a off)) (pre ++ post) = Some (pre', ACell b' o v, post') ->
  heap_den ρ h -∗
  ▷ (heap_den ρ h -∗ WP (ERun (mkFrame f (put d (wden ρ (SWInt (zwrap fs v (2 ^ 64)))) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k (RawLoad LdL off) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hfs Hclasses Hargs Hobj Hp Hcell.
  pose proof (object_base_sound _ _ _ _ Hfs Hobj) as Hcap.
  destruct (pick_atom_sound _ _ _ _ _ Hp) as [_ Hlive].
  destruct (pick_atom_sound _ _ _ _ _ Hcell) as [_ Haddr].
  cbn [is_cell] in Haddr. apply andb_true_iff in Haddr as [Hb Ha].
  apply (zlinear_eqb_sound _ _ _ _ Hfs) in Hb. apply (zlinear_eqb_sound _ _ _ _ Hfs) in Ha.
  rewrite (sraw_sound _ _ _ _ Hfs) in Ha. cbn [zden] in Ha.
  rewrite (heap_den_pick _ _ _ _ _ _ Hp) (is_live_den _ _ _ _ Hfs Hlive).
  rewrite (heap_den_pick _ _ _ _ _ _ Hcell).
  destruct (nth_error (vr ρ) (atom_region life)) as [reg|] eqn:Hr; last first.
  { iIntros "[Hfalse _] _". iDestruct "Hfalse" as %[]. }
  cbn [atom_den wden]. rewrite (zwrap_sound _ _ _ _ Hfs) Hb.
  rewrite Hb in Hcap. iIntros "(Hl & Hcell & Hrest) HK".
  iApply (wp_raw_load with "Hl Hcell"); [exact Hclasses|exact Hargs|exact Hcap|exact Ha|].
  iNext. iIntros "Hl Hcell". iApply "HK". iFrame.
Qed.

(** A narrow load preserves its byte ownership and applies the instruction's signed or unsigned extension. *)
Lemma sym_load_narrow_rule ρ fs h pre life post pre' post' f e ls l d k n t off args rest j classes a c b b' o v m Φ :
  facts_hold ρ fs -> modulus k = Some m ->
  op_arg_classes (RawLoad (LdNarrow n) off) k = Some classes ->
  map2_option (value_x ge e) classes args = Some [wden ρ (SWPtr a c)] ->
  object_base fs c = Some b -> pick_atom (is_live fs b) h = Some (pre, life, post) ->
  pick_atom (is_narrow fs n b (sraw fs a off)) (pre ++ post) = Some (pre', ANarrow t b' o v, post') ->
  heap_den ρ h -∗
  ▷ (heap_den ρ h -∗ WP (ERun (mkFrame f (put d
       (wden ρ (SWInt (zextend fs n (zwrap fs v (2 ^ (8 * fst (narrow_type t)))) m))) e)
       ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k (RawLoad (LdNarrow n) off) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hfs Hm Hclasses Hargs Hobj Hp Hcell.
  pose proof (object_base_sound _ _ _ _ Hfs Hobj) as Hcap.
  destruct (pick_atom_sound _ _ _ _ _ Hp) as [_ Hlive].
  destruct (pick_atom_sound _ _ _ _ _ Hcell) as [_ Haddr].
  cbn [is_narrow] in Haddr. apply andb_true_iff in Haddr as [Hwidth Ha].
  apply andb_true_iff in Hwidth as [Hwidth Hb]. apply Z.eqb_eq in Hwidth.
  apply (zlinear_eqb_sound _ _ _ _ Hfs) in Hb. apply (zlinear_eqb_sound _ _ _ _ Hfs) in Ha.
  rewrite (sraw_sound _ _ _ _ Hfs) in Ha. cbn [zden] in Ha.
  rewrite (heap_den_pick _ _ _ _ _ _ Hp) (is_live_den _ _ _ _ Hfs Hlive).
  rewrite (heap_den_pick _ _ _ _ _ _ Hcell).
  destruct (nth_error (vr ρ) (atom_region life)) as [reg|] eqn:Hr; last first.
  { iIntros "[Hfalse _] _". iDestruct "Hfalse" as %[]. }
  cbn [atom_den wden]. rewrite (zextend_sound _ _ _ _ _ Hfs). cbn [zden].
  rewrite (zwrap_sound _ _ _ _ Hfs) Hb. rewrite Hb in Hcap.
  iIntros "(Hl & Hcell & Hrest) HK".
  iApply (sym_ML.wp_raw_load_sub_bytes_dq registry wi ge with "Hl Hcell").
  - exact Hclasses.
  - exact Hargs.
  - unfold sym_bytes. rewrite length_le_bytes Hwidth. reflexivity.
  - rewrite sym_bytes_decode. unfold extended. rewrite Hm. reflexivity.
  - left. exact Hcap.
  - exact Ha.
  - iNext. iIntros "Hl Hcell". iApply "HK". iFrame.
Qed.

(** A reflected pointer load returns both source ownership and the loaded pointer's target lifetime. *)
Lemma sym_load_pointer_rule ρ fs h pre life post pre' post' pre'' target post''
    f e ls l d off args rest j classes a c b b' o v vc Φ :
  facts_hold ρ fs ->
  op_arg_classes (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) P = Some classes ->
  map2_option (value_x ge e) classes args = Some [wden ρ (SWPtr a c)] ->
  object_base fs c = Some b -> pick_atom (is_live fs b) h = Some (pre, life, post) ->
  pick_atom (is_cell fs true b (sraw fs a off)) (pre ++ post) = Some (pre', APCell b' o v vc, post') ->
  pick_atom (is_cap fs vc) (pre' ++ post') = Some (pre'', target, post'') ->
  obs_den ρ [OEq (ZMod (ZAdd b' o) 8) (ZK 0); OLe (ZK 0) v; OLt v (ZK (2 ^ 64))] ->
  heap_den ρ h -∗
  ▷ (heap_den ρ h -∗ WP (ERun (mkFrame f (put d (wden ρ (SWPtr v vc)) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Let d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hfs Hclasses Hargs Hobj Hp Hcell Htarget Hobs.
  pose proof (object_base_sound _ _ _ _ Hfs Hobj) as Hcap.
  destruct (pick_atom_sound _ _ _ _ _ Hp) as [_ Hlive].
  destruct (pick_atom_sound _ _ _ _ _ Hcell) as [_ Haddr].
  destruct (pick_atom_sound _ _ _ _ _ Htarget) as [_ Htargetcap].
  cbn [is_cell] in Haddr. apply andb_true_iff in Haddr as [Hb Ha].
  apply (zlinear_eqb_sound _ _ _ _ Hfs) in Hb. apply (zlinear_eqb_sound _ _ _ _ Hfs) in Ha.
  rewrite (sraw_sound _ _ _ _ Hfs) in Ha. cbn [zden] in Ha.
  rewrite (heap_den_pick _ _ _ _ _ _ Hp) (is_live_den _ _ _ _ Hfs Hlive).
  rewrite (heap_den_pick _ _ _ _ _ _ Hcell).
  rewrite (heap_den_pick _ _ _ _ _ _ Htarget) (is_cap_den _ _ _ _ Hfs Htargetcap).
  destruct (nth_error (vr ρ) (atom_region life)) as [reg|] eqn:Hr; last first.
  { iIntros "[Hfalse _] _". iDestruct "Hfalse" as %[]. }
  destruct (nth_error (vr ρ) (atom_region target)) as [reg'|] eqn:Hr'; last first.
  { iIntros "(_ & _ & Hfalse & _) _". iDestruct "Hfalse" as %[]. }
  inversion Hobs as [|? ? Hal Htail]; subst. inversion Htail as [|? ? Hlo Htail']; subst.
  inversion Htail' as [|? ? Hhi _]; subst. cbn [ob_den zden] in Hal, Hlo, Hhi.
  cbn [atom_den wden]. rewrite Hb. rewrite Hb in Hcap.
  iIntros "(Hl & Hcell & Htarget & Hrest) HK".
  iApply (wp_raw_load_pointer with "Hl Hcell Htarget");
    [exact Hclasses|exact Hargs|exact Hcap|exact Ha|exact Hal|cbn; lia|].
  iNext. iIntros "Hl Hcell Htarget". iApply "HK". iFrame.
Qed.

(** A reflected integer store changes its cell while preserving the caller's world interpretation. *)
Lemma sym_store_rule ρ fs h pre life post pre' post' f e ls l off v p rest j a c b b' o old new Φ :
  facts_hold ρ fs -> value_x ge e L v = Some (wden ρ (SWInt new)) ->
  value_x ge e A p = Some (wden ρ (SWPtr a c)) ->
  object_base fs c = Some b -> pick_atom (is_live fs b) h = Some (pre, life, post) ->
  pick_atom (is_cell fs false b (sraw fs a off)) (pre ++ post) = Some (pre', ACell b' o old, post') ->
  ob_den ρ (OStoreW b' o (atom_region life) old new) ->
  heap_den ρ h -∗
  ▷ (heap_den ρ (life :: pre' ++ ACell b' o new :: post') -∗
    WP (ERun (mkFrame f e ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (RawStore Wl off v p :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hfs Hv Hp Hobj Hlivepick Hcell Hobs.
  pose proof (object_base_sound _ _ _ _ Hfs Hobj) as Hcap.
  destruct (pick_atom_sound _ _ _ _ _ Hlivepick) as [_ Hlive].
  destruct (pick_atom_sound _ _ _ _ _ Hcell) as [_ Haddr].
  cbn [is_cell] in Haddr. apply andb_true_iff in Haddr as [Hb Ha].
  apply (zlinear_eqb_sound _ _ _ _ Hfs) in Hb. apply (zlinear_eqb_sound _ _ _ _ Hfs) in Ha.
  rewrite (sraw_sound _ _ _ _ Hfs) in Ha. cbn [zden] in Ha.
  rewrite (heap_den_pick _ _ _ _ _ _ Hlivepick) (heap_den_pick _ _ _ _ _ _ Hcell).
  cbn [heap_den]. rewrite (is_live_den _ _ _ _ Hfs Hlive) !heap_den_app.
  destruct Hobs as (reg & Hr & Hwi). rewrite Hr. cbn [heap_den atom_den].
  rewrite Hb. rewrite Hb in Hcap.
  iIntros "(Hl & Hcell & Hrest) HK".
  iApply (wp_raw_store with "Hl Hcell"); [exact Hv|exact Hp|exact Hcap|exact Ha|exact Hwi|].
  iNext. iIntros "Hl Hcell". iApply "HK". iFrame.
Qed.

(** A reflected pointer store updates both the address bytes and the shadow capability. *)
Lemma sym_store_pointer_rule ρ fs h pre life post pre' post' f e ls l off v p rest j
    a c b b' o old oc new nc Φ :
  facts_hold ρ fs -> value_x ge e P v = Some (wden ρ (SWPtr new nc)) ->
  value_x ge e A p = Some (wden ρ (SWPtr a c)) ->
  object_base fs c = Some b -> pick_atom (is_live fs b) h = Some (pre, life, post) ->
  pick_atom (is_cell fs true b (sraw fs a off)) (pre ++ post) = Some (pre', APCell b' o old oc, post') ->
  ob_den ρ (OEq (ZMod (ZAdd b' o) 8) (ZK 0)) ->
  ob_den ρ (OStoreP b' o (atom_region life) (SWPtr old oc) (SWPtr new nc)) ->
  heap_den ρ h -∗
  ▷ (heap_den ρ (life :: pre' ++ APCell b' o new nc :: post') -∗
    WP (ERun (mkFrame f e ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (RawStorePointer off v p [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite] :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hfs Hv Hp Hobj Hlivepick Hcell Hal Hobs.
  pose proof (object_base_sound _ _ _ _ Hfs Hobj) as Hcap.
  destruct (pick_atom_sound _ _ _ _ _ Hlivepick) as [_ Hlive].
  destruct (pick_atom_sound _ _ _ _ _ Hcell) as [_ Haddr].
  cbn [is_cell] in Haddr. apply andb_true_iff in Haddr as [Hb Ha].
  apply (zlinear_eqb_sound _ _ _ _ Hfs) in Hb. apply (zlinear_eqb_sound _ _ _ _ Hfs) in Ha.
  rewrite (sraw_sound _ _ _ _ Hfs) in Ha. cbn [zden] in Ha.
  rewrite (heap_den_pick _ _ _ _ _ _ Hlivepick) (heap_den_pick _ _ _ _ _ _ Hcell).
  cbn [heap_den]. rewrite (is_live_den _ _ _ _ Hfs Hlive) !heap_den_app.
  destruct Hobs as (reg & Hr & Hwi). rewrite Hr. cbn [heap_den atom_den].
  rewrite Hb. rewrite Hb in Hcap.
  iIntros "(Hl & Hcell & Hrest) HK".
  iApply (wp_raw_store_pointer with "Hl Hcell"); [exact Hv|exact Hp|exact Hcap|exact Ha|exact Hal|exact Hwi|].
  iNext. iIntros "Hl Hcell". iApply "HK". iFrame.
Qed.

(** The continuation receives the new ownership and the values of the updated temporaries. *)
Definition next_den ρ f e ls l rest j Φ s : iProp Σ :=
  heap_den ρ (st_heap s) -∗ ⌜env_models ρ (st_env s) (apply_ups ρ (st_ups s) e)⌝ -∗
  WP (ERun (mkFrame f (apply_ups ρ (st_ups s) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}.

(** This proof helper follows only the finite decisions of an instruction evaluator. *)
Local Ltac sym_cases H :=
  repeat first [progress cbn beta iota zeta in H |
    lazymatch type of H with
    | inl _ = inr _ => discriminate
    | None = Some _ => discriminate
    | context [match ?x with _ => _ end] => let E := fresh "E" in destruct x eqn:E
    end].

(** Successful memory lets preserve the environment and ownership described by their state. *)
Lemma smemory_rule ρ fs s s' f e ls l d k op args rest j classes xs why Φ :
  facts_hold ρ fs -> env_models ρ (st_env s) (apply_ups ρ (st_ups s) e) ->
  op_arg_classes op k = Some classes ->
  map2_option (value_x ge (apply_ups ρ (st_ups s) e)) classes args = Some (map (wden ρ) xs) ->
  smemory fs s d k op xs why = inr s' -> obs_den ρ (st_obs s') ->
  heap_den ρ (st_heap s) -∗ ▷ next_den ρ f e ls l rest j Φ s' -∗
  WP (ERun (mkFrame f (apply_ups ρ (st_ups s) e) ls None (Exec l (Let d k op args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hfs Henv Hclasses Hargs Hstep Hobs.
  unfold smemory in Hstep. sym_cases Hstep.
  all: injection Hstep as <-; unfold next_den; rewrite apply_ups_sbind;
    cbn [sbind sobserve st_env st_heap st_ups st_obs] in Hobs |- *.
  all: try (apply Forall_app in Hobs as [_ Hobs]).
  all: repeat match goal with p : (_ * _)%type |- _ => destruct p end.
  all: iIntros "Hheap HK".
  all: first [iApply (sym_check_rule with "Hheap") |
    iApply (sym_renew_rule with "Hheap") |
    iApply (sym_half_check_rule with "Hheap") |
    iApply (sym_load_rule with "Hheap") |
    iApply (sym_load_narrow_rule with "Hheap") |
    iApply (sym_load_pointer_rule with "Hheap")]; try eassumption.
  all: try (iNext; iIntros "Hheap"; iApply ("HK" with "Hheap"); iPureIntro;
    apply env_models_put; exact Henv).
  all: try eassumption.
  all: try (lazymatch type of Hargs with
    | _ = Some (map _ [SWPtr ?a1 _; _]) =>
        lazymatch goal with |- _ = Some [wden _ (SWPtr ?x _); _] => unify x a1 end;
        exact Hargs
    end).
  all: try eassumption.
Qed.

(** Successful stores preserve every known temporary and return their updated cell ownership. *)
Lemma sstore_rule ρ fs s s' f e ls l off v p rest j (pointer : bool) sv sp why Φ :
  facts_hold ρ fs -> env_models ρ (st_env s) (apply_ups ρ (st_ups s) e) ->
  value_x ge (apply_ups ρ (st_ups s) e) (if pointer then P else L) v = Some (wden ρ sv) ->
  value_x ge (apply_ups ρ (st_ups s) e) A p = Some (wden ρ sp) ->
  sstore fs s pointer off sv sp why = inr s' -> obs_den ρ (st_obs s') ->
  heap_den ρ (st_heap s) -∗ ▷ next_den ρ f e ls l rest j Φ s' -∗
  WP (ERun (mkFrame f (apply_ups ρ (st_ups s) e) ls None
    (Exec l ((if pointer then RawStorePointer off v p [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]
              else RawStore Wl off v p) :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hfs Henv Hv Hp Hstep Hobs. unfold sstore in Hstep. sym_cases Hstep.
  all: injection Hstep as <-; unfold next_den;
    cbn [st_env st_heap st_ups st_obs] in Hobs |- *;
    apply Forall_app in Hobs as [_ Hobs].
  all: repeat match goal with p : (_ * _)%type |- _ => destruct p end.
  all: iIntros "Hheap HK".
  all: first [iApply (sym_store_rule with "Hheap") | iApply (sym_store_pointer_rule with "Hheap")]; try eassumption.
  all: try solve [inversion Hobs; subst; assumption].
  all: try solve [inversion Hobs as [|? ? ? Htail]; subst; inversion Htail; subst; assumption].
  all: iNext; iIntros "Hheap"; iApply ("HK" with "Hheap"); iPureIntro; exact Henv.
Qed.

(** Every successful symbolic instruction is justified by its corresponding machine rule. *)
Lemma sym_step_rule ρ fs s s' f e ls l i rest j Φ :
  facts_hold ρ fs -> env_models ρ (st_env s) (apply_ups ρ (st_ups s) e) ->
  sym_step ge fs s i = inr s' -> obs_den ρ (st_obs s') ->
  heap_den ρ (st_heap s) -∗ ▷ next_den ρ f e ls l rest j Φ s' -∗
  WP (ERun (mkFrame f (apply_ups ρ (st_ups s) e) ls None (Exec l (i :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hfs Henv Hstep Hobs. destruct i; cbn [sym_step] in Hstep; try discriminate.
  - destruct (op_arg_classes o k) as [classes|] eqn:Hclasses; [|discriminate].
    destruct (map2_option (svalue ge fs (st_env s)) classes args) as [xs|] eqn:Hargs; [|discriminate].
    pose proof (svalues_sound _ _ _ _ _ _ _ _ Hfs Henv Hargs) as Hvalues.
    destruct (sop fs o k xs) as [w|] eqn:Hop.
    + injection Hstep as <-. destruct (sop_sound _ _ _ _ _ _ Hfs Hop) as [Hg Ho].
      unfold next_den. rewrite apply_ups_sbind. cbn [sbind st_heap st_env].
      iIntros "Hheap HK". iApply wp_let; [exact Hg|exact Hclasses|exact Hvalues|exact Ho|].
      iNext. iApply ("HK" with "Hheap"). iPureIntro. apply env_models_put. exact Henv.
    + eapply smemory_rule; eassumption.
  - destruct (map_option (sflight_arg ge fs (st_env s)) args) as [xs|] eqn:Hargs; [|discriminate].
    destruct (sflight_cap ge fs (st_env s) lower) as [c|] eqn:Hcap; [|discriminate].
    destruct (salu fs o L xs) as [[a|a c']|] eqn:Hop; try discriminate.
    injection Hstep as <-. unfold next_den. rewrite apply_ups_sbind. cbn [sbind st_heap st_env].
    iIntros "Hheap HK". iApply wp_flight.
    + eapply sflight_args_sound; eassumption.
    + exact (salu_sound _ _ _ _ _ _ Hfs Hop).
    + exact (sflight_cap_sound _ _ _ _ _ _ _ Hfs Henv Hcap).
    + iNext. iApply ("HK" with "Hheap"). iPureIntro. apply env_models_put. exact Henv.
  - destruct w; try discriminate.
    destruct (svalue ge fs (st_env s) L v) as [sv|] eqn:Hv; [|discriminate].
    destruct (svalue ge fs (st_env s) A a) as [sp|] eqn:Hp; [|discriminate].
    eapply (sstore_rule _ _ _ _ _ _ _ _ _ _ _ _ _ false sv sp _ _ Hfs Henv);
      try eassumption; eapply svalue_sound; eassumption.
  - sym_cases Hstep.
    eapply (sstore_rule _ _ _ _ _ _ _ _ _ _ _ _ _ true); try eassumption;
      eapply svalue_sound; eassumption.
Qed.

(** Instructions append conditions rather than forgetting conditions from earlier instructions. *)
Lemma sym_step_obs fs s i s' : sym_step ge fs s i = inr s' ->
  exists os, st_obs s' = st_obs s ++ os.
Proof.
  intros H. unfold sym_step in H. sym_cases H.
  all: try unfold smemory in H; try unfold sstore in H; sym_cases H.
  all: injection H as <-; cbn [sbind sobserve st_obs];
    first [eexists; reflexivity | exists []; rewrite app_nil_r; reflexivity].
Qed.

(** Every kind of leaf carries the state reached by the executor. *)
Definition leaf_state (lf : leaf) : sstate :=
  match lf with LGoto _ s | LBranch _ _ _ s | LStop _ _ _ s => s end.

(** A block's final conditions include every condition already present at its entry. *)
Lemma sym_exec_obs fs insts j s :
  exists os, st_obs (leaf_state (sym_exec ge fs s insts j)) = st_obs s ++ os.
Proof.
  revert s. induction insts as [|i insts IH]; intros s; cbn [sym_exec].
  - destruct j; cbn [leaf_state]; try solve [exists []; rewrite app_nil_r; reflexivity].
    destruct (svalue ge fs (st_env s) W v) as [[x|a c]|];
      exists []; cbn [leaf_state]; rewrite app_nil_r; reflexivity.
  - destruct (sym_step ge fs s i) as [why|s'] eqn:E.
    + exists []. cbn [leaf_state]. rewrite app_nil_r. reflexivity.
    + destruct (IH s') as [os H]. destruct (sym_step_obs _ _ _ _ E) as [os' H'].
      exists (os' ++ os). rewrite H H' app_assoc. reflexivity.
Qed.

(** Arithmetic facts can be used more than once, unlike ownership of a memory cell.
    The proof copies those facts here and keeps the original requirement for later. *)
Lemma leaf_den_obs ρ f e ls l Φ lf :
  leaf_den ρ f e ls l Φ lf ⊢ ⌜obs_den ρ (st_obs (leaf_state lf))⌝ ∗ leaf_den ρ f e ls l Φ lf.
Proof. destruct lf; cbn [leaf_den leaf_state]; iIntros "[%H HK]"; iFrame; auto. Qed.

(** Each successful instruction preserves enough information to justify the next instruction in the block. *)
Lemma sym_exec_rule ρ fs insts j s f e ls l Φ :
  facts_hold ρ fs -> env_models ρ (st_env s) (apply_ups ρ (st_ups s) e) ->
  heap_den ρ (st_heap s) -∗ leaf_den ρ f e ls l Φ (sym_exec ge fs s insts j) -∗
  WP (ERun (mkFrame f (apply_ups ρ (st_ups s) e) ls None (Exec l insts j)) : gexpr) {{ Φ }}.
Proof.
  intros Hfs. revert s. induction insts as [|i insts IH]; intros s Henv; cbn [sym_exec].
  - destruct j; try solve [cbn [leaf_den]; iIntros "Hheap [_ HK]"; iApply ("HK" with "Hheap []"); done].
    + cbn [leaf_den]. iIntros "Hheap [_ HK]". iApply wp_goto.
      iNext. iApply ("HK" with "Hheap []"). done.
    + destruct (svalue ge fs (st_env s) W v) as [[x|a c]|] eqn:Ev;
        try solve [cbn [leaf_den]; iIntros "Hheap [_ HK]"; iApply ("HK" with "Hheap []"); done].
      cbn [leaf_den]. iIntros "Hheap [_ HK]". iApply wp_branch.
      * exact (svalue_sound _ _ _ _ _ _ _ _ Hfs Henv Ev).
      * iNext. iApply ("HK" with "Hheap []"). done.
  - destruct (sym_step ge fs s i) as [why|s'] eqn:E.
    + cbn [leaf_den]. iIntros "Hheap [_ HK]". iApply ("HK" with "Hheap []"). done.
    + iIntros "Hheap HK". iDestruct (leaf_den_obs with "HK") as "[%Hobs HK]".
      destruct (sym_exec_obs fs insts j s') as [os Hos]. rewrite Hos in Hobs.
      apply Forall_app in Hobs as [Hobs _].
      iApply (sym_step_rule _ _ _ _ _ _ _ _ _ _ _ _ Hfs Henv E Hobs with "Hheap").
      iNext. iIntros "Hheap %Henv'". iApply (IH with "Hheap HK"). exact Henv'.
Qed.

(** Running the executor on a block is a valid proof step: when the
    facts hold and the known environment and the atoms describe the
    real state, the leaf's requirement proves the block. *)
Theorem sym_sound fs se h f e ls l insts j ρ Φ :
  facts_hold ρ fs -> env_models ρ se e ->
  heap_den ρ h -∗ leaf_den ρ f e ls l Φ (sym_block ge fs se h l insts j) -∗
  WP (ERun (mkFrame f e ls None (Exec l insts j)) : gexpr) {{ Φ }}.
Proof.
  intros Hfs Henv. apply (sym_exec_rule ρ fs insts j (mkSState se [] h []) f e ls l Φ Hfs Henv).
Qed.

End sound.

(** ## Quoting a proof context

    The caller names only the ownership facts that the block may use.
    The tactic quotes their values and the known temporaries, while leaving
    every other Iris hypothesis in the proof's frame. *)

(** Reconstructing a pointer from its projections preserves the original pointer. *)
Lemma sym_ptr_eta p : mkPtr (ptr_addr p) (ptr_cap p) = p.
Proof. destruct p. reflexivity. Qed.

(** Interning an opaque value gives it a stable index in the valuation. *)
Ltac sym_intern x xs :=
  lazymatch xs with
  | [] => constr:((O, [x]))
  | x :: _ => constr:((O, xs))
  | ?y :: ?ys =>
      let r := sym_intern x ys in
      lazymatch r with (?n, ?ys') => constr:((S n, y :: ys')) end
  end.

(** This recognizer accepts only closed binary integer literals. *)
Ltac sym_literal x :=
  let rec pos p := lazymatch p with xH => idtac | xO ?p => pos p | xI ?p => pos p end in
  lazymatch x with Z0 => idtac | Zpos ?p => pos p | Zneg ?p => pos p end.

(** Arithmetic is quoted structurally, while unknown integer expressions become variables. *)
Ltac sym_quote_z rho t :=
  let t := eval cbn [ptr_addr r_end] in t in
  lazymatch rho with mkVal ?zs ?ps ?rs =>
    lazymatch t with
    | Z.add ?a ?b =>
        let qa := sym_quote_z rho a in
        lazymatch qa with (?a', ?r1) =>
          let qb := sym_quote_z r1 b in
          lazymatch qb with (?b', ?r2) => constr:((ZAdd a' b', r2)) end
        end
    | Z.sub ?a ?b =>
        let qa := sym_quote_z rho a in
        lazymatch qa with (?a', ?r1) =>
          let qb := sym_quote_z r1 b in
          lazymatch qb with (?b', ?r2) => constr:((ZSub a' b', r2)) end
        end
    | ptr_addr ?p =>
        let q := sym_intern p ps in
        lazymatch q with (?n, ?ps') => constr:((ZAddr n, mkVal zs ps' rs)) end
    | r_end ?r =>
        let q := sym_intern r rs in
        lazymatch q with (?n, ?rs') => constr:((ZEnd n, mkVal zs ps rs')) end
    | _ =>
        let v := eval cbv in t in
        let q := match goal with
          | _ => let literal := sym_literal v in constr:((ZK v, rho))
          | _ => let q := sym_intern t zs in
              lazymatch q with (?n, ?zs') => constr:((ZV n, mkVal zs' ps rs)) end
          end in q
    end
  end.

(** Capabilities retain their object bases, or refer to a pointer carrying an opaque capability. *)
Ltac sym_quote_c rho c :=
  let c := eval cbn [ptr_cap] in c in
  lazymatch c with
  | CNone => constr:((SCNone, rho))
  | Obj ?b => let q := sym_quote_z rho b in
      lazymatch q with (?b', ?r) => constr:((SCObj b', r)) end
  | Ro ?b => let q := sym_quote_z rho b in
      lazymatch q with (?b', ?r) => constr:((SCRo b', r)) end
  | _ =>
      let p := lazymatch c with ptr_cap ?p => p | _ => constr:(mkPtr 0 c) end in
      lazymatch rho with mkVal ?zs ?ps ?rs =>
        let q := sym_intern p ps in
        lazymatch q with (?n, ?ps') => constr:((SCOf n, mkVal zs ps' rs)) end
      end
  end.

(** Quoting a word preserves opaque pointer identities through their two projections. *)
Ltac sym_quote_w rho w :=
  lazymatch w with
  | WInt ?x => let q := sym_quote_z rho x in
      lazymatch q with (?x', ?r) => constr:((SWInt x', r)) end
  | WPtr ?p =>
      let qa := sym_quote_z rho constr:(ptr_addr p) in
      lazymatch qa with (?a, ?r1) =>
        let qc := sym_quote_c r1 constr:(ptr_cap p) in
        lazymatch qc with (?c, ?r2) => constr:((SWPtr a c, r2)) end
      end
  | _ => fail "sym_run: unsupported word" w
  end.

(** A region receives its own index, separate from integer and pointer variables. *)
Ltac sym_quote_r rho reg :=
  lazymatch rho with mkVal ?zs ?ps ?rs =>
    let q := sym_intern reg rs in
    lazymatch q with (?n, ?rs') => constr:((n, mkVal zs ps rs')) end
  end.

(** The tactic recognizes cell and lifetime permissions by name, without inspecting their implementation. *)
Ltac sym_quote_atom rho P :=
  lazymatch P with
  | live ?b ?reg =>
      let qb := sym_quote_z rho b in
      lazymatch qb with (?b', ?r1) => let qr := sym_quote_r r1 reg in
        lazymatch qr with (?r, ?r2) => constr:((ALive b' r, r2)) end end
  | live_cap ?c ?reg =>
      let qc := sym_quote_c rho c in
      lazymatch qc with (?c', ?r1) => let qr := sym_quote_r r1 reg in
        lazymatch qr with (?r, ?r2) => constr:((ALiveCap c' r, r2)) end end
  | icell ?b ?o ?v =>
      let qb := sym_quote_z rho b in
      lazymatch qb with (?b', ?r1) => let qo := sym_quote_z r1 o in
        lazymatch qo with (?o', ?r2) => let qv := sym_quote_z r2 v in
          lazymatch qv with (?v', ?r3) => constr:((ACell b' o' v', r3)) end end end
  | pcell ?b ?o ?p =>
      let qb := sym_quote_z rho b in
      lazymatch qb with (?b', ?r1) => let qo := sym_quote_z r1 o in
        lazymatch qo with (?o', ?r2) => let qp := sym_quote_w r2 constr:(WPtr p) in
          lazymatch qp with (SWPtr ?a ?c, ?r3) => constr:((APCell b' o' a c, r3)) end end end
  | ?byte_assertion ?b ?o ?bs =>
      let checked := constr:(eq_refl P : P = sym_ML.bytes b o bs) in
      let bs := eval cbv beta delta [sym_bytes] in bs in
      lazymatch bs with
      | le_bytes ?v ?sz =>
          let n := lazymatch sz with 1%nat => constr:(Ub) | 2%nat => constr:(Uh) | 4%nat => constr:(Uw) end in
          let qb := sym_quote_z rho b in
          lazymatch qb with (?b', ?r1) => let qo := sym_quote_z r1 o in
            lazymatch qo with (?o', ?r2) => let qv := sym_quote_z r2 v in
              lazymatch qv with (?v', ?r3) => constr:((ANarrow n b' o' v', r3)) end end end
      end
  | _ => fail "sym_run: expected live, icell, pcell, narrow bytes, or live_cap; found" P
  end.

(** Named spatial hypotheses become an ordered list of ownership atoms. *)
Ltac sym_quote_heap rho names :=
  lazymatch names with
  | [] => constr:((@nil atom, rho))
  | ?n :: ?names' =>
      let ty := iTypeOf constr:(INamed n) in
      lazymatch ty with
      | Some (false, ?P) =>
          let qa := sym_quote_atom rho P in
          lazymatch qa with (?a, ?r1) => let qh := sym_quote_heap r1 names' in
            lazymatch qh with (?h, ?r2) => constr:((a :: h, r2)) end end
      | _ => fail "sym_run: expected a spatial hypothesis named" n
      end
  end.

(** A list membership check prevents the context collector from visiting a proposition twice. *)
Ltac sym_not_in x xs :=
  lazymatch xs with [] => idtac | x :: _ => fail | _ :: ?xs => sym_not_in x xs end.

(** The collector records pure propositions without changing the caller's hypotheses. *)
Ltac sym_context seen :=
  match goal with
  | H : ?P |- _ =>
      let relevant := lazymatch P with
        | Z.le _ _ => idtac | Z.lt _ _ => idtac
        | @eq cap _ _ => idtac | lookup _ _ = Some _ => idtac
        | _ /\ _ => idtac
        end in
      let unseen := sym_not_in P seen in
      sym_context constr:(P :: seen)
  | _ => seen
  end.

(** When a hypothesis joins two facts, the tactic collects each fact separately. *)
Ltac sym_flatten props :=
  lazymatch props with
  | [] => props
  | (?P /\ ?Q) :: ?ps => sym_flatten constr:(P :: Q :: ps)
  | ?P :: ?ps => let qs := sym_flatten ps in constr:(P :: qs)
  end.

(** Lookup hypotheses describe the unmodified part of the current environment. *)
Ltac sym_quote_lookups rho props e :=
  lazymatch props with
  | [] => constr:((@nil (name * sword), rho))
  | (lookup ?n e = Some ?w) :: ?ps =>
      let qw := sym_quote_w rho w in
      lazymatch qw with (?w', ?r1) => let qs := sym_quote_lookups r1 ps e in
        lazymatch qs with (?se, ?r2) => constr:(((n, w') :: se, r2)) end end
  | _ :: ?ps => sym_quote_lookups rho ps e
  end.

(** Explicit assignments override older lookup hypotheses when a proof enters another block. *)
Ltac sym_quote_env rho props e :=
  lazymatch e with
  | put ?n ?w ?e0 =>
      let qe := sym_quote_env rho props e0 in
      lazymatch qe with (?se, ?r1) => let qw := sym_quote_w r1 w in
        lazymatch qw with (?sw, ?r2) =>
          let se' := eval vm_compute in (put n sw se) in constr:((se', r2))
        end end
  | _ => sym_quote_lookups rho props e
  end.

(** Pure capability equations are quoted after the ownership and environment expressions. *)
Ltac sym_quote_caps rho props :=
  lazymatch props with
  | [] => constr:((@nil (scap * scap), rho))
  | (@eq cap ?a ?b) :: ?ps =>
      let qa := sym_quote_c rho a in
      lazymatch qa with (?a', ?r1) => let qb := sym_quote_c r1 b in
        lazymatch qb with (?b', ?r2) => let qs := sym_quote_caps r2 ps in
          lazymatch qs with (?cs, ?r3) => constr:(((a', b') :: cs, r3)) end end end
  | _ :: ?ps => sym_quote_caps rho ps
  end.

(** Closed endpoints in the context give candidate bounds for an atomic integer. *)
Ltac sym_limits props x lo hi :=
  lazymatch props with
  | [] => constr:((lo, hi))
  | ?P :: ?ps =>
      let bounds := match goal with
        | _ => lazymatch P with
            | Z.le ?a x => let v := eval cbv in a in let literal := sym_literal v in
                let lo' := eval vm_compute in (Z.max lo v) in constr:((lo', hi))
            | Z.lt ?a x => let v := eval cbv in a in let literal := sym_literal v in
                let lo' := eval vm_compute in (Z.max lo (v + 1)) in constr:((lo', hi))
            | Z.le x ?b => let v := eval cbv in b in let literal := sym_literal v in
                let hi' := eval vm_compute in (Z.min hi (v + 1)) in constr:((lo, hi'))
            | Z.lt x ?b => let v := eval cbv in b in let literal := sym_literal v in
                let hi' := eval vm_compute in (Z.min hi v) in constr:((lo, hi'))
            end
        | _ => constr:((lo, hi))
        end in
      lazymatch bounds with (?lo', ?hi') => sym_limits ps x lo' hi' end
  end.

(** Every valuation entry supplies an atomic expression that may have useful bounds. *)
Ltac sym_bound_terms rho :=
  let rec zs xs n := lazymatch xs with
    | [] => constr:(@nil (zexp * Z))
    | ?x :: ?xs => let rest := zs xs constr:(S n) in constr:((ZV n, x) :: rest) end in
  let rec ps xs n := lazymatch xs with
    | [] => constr:(@nil (zexp * Z))
    | ?x :: ?xs => let rest := ps xs constr:(S n) in constr:((ZAddr n, ptr_addr x) :: rest) end in
  let rec rs xs n := lazymatch xs with
    | [] => constr:(@nil (zexp * Z))
    | ?x :: ?xs => let rest := rs xs constr:(S n) in constr:((ZEnd n, r_end x) :: rest) end in
  lazymatch rho with mkVal ?zz ?pp ?rr =>
    let zz' := zs zz constr:(O) in let pp' := ps pp constr:(O) in let rr' := rs rr constr:(O) in
    eval cbn [app] in (zz' ++ pp' ++ rr')
  end.

(** Candidate intervals enter the facts only after arithmetic proves both endpoints. *)
Ltac sym_bounds props terms bs finish :=
  lazymatch terms with
  | [] => finish bs
  | (?sx, ?x) :: ?terms' =>
      let lim := sym_limits props x constr:(-(2 ^ 128)) constr:(2 ^ 128) in
      lazymatch lim with (?lo, ?hi) =>
        let rec attempt candidates := lazymatch candidates with
          | [] => sym_bounds props terms' bs finish
          | (?l, ?h) :: ?cs =>
              let l := eval vm_compute in l in let h := eval vm_compute in h in
              let Hb := fresh "Hsym_bound" in
              tryif (assert (Hb : l <= x < h) by lia)
              then (clear Hb; sym_bounds props terms' constr:(mkBound sx l h :: bs) finish)
              else attempt cs
          end in
        attempt constr:([(Z.max lo 0, Z.min hi (2 ^ 32));
          (Z.max lo 0, Z.min hi (2 ^ 63 + 1)); (Z.max lo 0, Z.min hi (2 ^ 64));
          (lo, hi)])
      end
  end.

(** A store changes a cell's contents, but its base and offset still identify the caller's name. *)
Definition atom_slot (fs : facts) (a b : atom) : bool :=
  match a, b with
  | ALive x r, ALive y s => zlinear_eqb fs x y && Nat.eqb r s
  | ALiveCap c r, ALiveCap d s => csame fs c d && Nat.eqb r s
  | ACell x o _, ACell y p _ | APCell x o _ _, APCell y p _ _ =>
      zlinear_eqb fs x y && zlinear_eqb fs o p
  | ANarrow n x o _, ANarrow m y p _ =>
      Z.eqb (fst (narrow_type n)) (fst (narrow_type m)) &&
      zlinear_eqb fs x y && zlinear_eqb fs o p
  | _, _ => false
  end.

(** Returning an atom consumes its old name from the list, so no name is returned twice. *)
Ltac sym_atom_name fs a old names :=
  lazymatch old with
  | ?b :: ?old' => lazymatch names with ?n :: ?names' =>
      let same := eval vm_compute in (atom_slot fs a b) in
      lazymatch same with
      | true => constr:((n, old', names'))
      | false => let r := sym_atom_name fs a old' names' in
          lazymatch r with (?m, ?remaining, ?rest) => constr:((m, b :: remaining, n :: rest)) end
      end end
  | [] => fail "sym_run: returned an atom without a caller name" a
  end.

(** Denotation reduction leaves the program's environment updates and arithmetic visible. *)
Ltac sym_den_simpl :=
  cbn [facts_hold env_models obs_den ob_den heap_den atom_den wden cden zden
    vz vp vr nth nth_error bd_exp bd_lo bd_hi f_bounds f_caps fst snd
    apply_ups fold_left]; rewrite ?sym_ptr_eta.

(** Each unsolved arithmetic condition remains a separate, ordinary Coq goal. *)
Ltac sym_forall_side solve :=
  cbn [f_bounds f_caps];
  lazymatch goal with
  | |- Forall _ [] => apply Forall_nil
  | |- Forall _ (_ :: _) => apply Forall_cons; [sym_den_simpl; try solve | sym_forall_side solve]
  | _ => sym_den_simpl; try solve
  end.

(** Returned resources recover their original Iris names, including after a store. *)
Ltac sym_restore fs h old names H :=
  lazymatch h with
  | [] => iClear H
  | ?a :: ?h' =>
      let found := sym_atom_name fs a old names in
      lazymatch found with (?n, ?remaining, ?rest) =>
        let tail := iFresh in
        let pat := constr:(intro_patterns.IList [[intro_patterns.IIdent (INamed n); intro_patterns.IIdent tail]]) in
        iDestruct H as pat;
        sym_restore fs h' remaining rest tail
      end
  end.

(** One computation supplies the leaf, and the cast lets the kernel check that computed result. *)
Ltac sym_finish fs se h rho names solve :=
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (_ (mkFrame ?f ?e ?ls None (Exec ?l ?insts ?j))) ?Phi) =>
      let Hheap := iFresh in
      let selected := eval vm_compute in (String.append "[" (String.append (String.concat " " names) "]")) in
      iAssert (heap_den rho h) with selected as Hheap;
      [sym_den_simpl; iFrame |];
      iApply (sym_sound _ _ _ fs se h f e ls l insts j rho Phi with Hheap);
      [unfold facts_hold; split; sym_forall_side solve |
       unfold env_models; sym_forall_side ltac:(lk_prove) |
      lazymatch goal with
      | |- environments.envs_entails _ (leaf_den _ _ _ _ _ _ _ _ _ ?call) =>
          let lf := eval vm_compute in call in
          let Eq := fresh "Hsym_computed" in
          assert (Eq : call = lf) by (vm_cast_no_check (eq_refl lf));
          rewrite Eq; clear Eq;
          cbn [leaf_den st_obs st_heap st_env st_ups];
          iSplit; [iPureIntro; unfold obs_den; sym_forall_side solve |
          lazymatch lf with LStop ?why _ _ _ => idtac "sym_run stopped:" why | _ => iNext end;
          let Hnew := iFresh in let Henv := fresh "Hsym_env" in
          iIntros Hnew; iIntros (Henv);
          iEval (cbn [heap_den atom_den wden cden zden vz vp vr nth nth_error]; rewrite ?sym_ptr_eta) in Hnew;
          let hs := eval cbn [leaf_state st_heap] in (st_heap (leaf_state lf)) in
          sym_restore fs hs h names Hnew;
          clear Henv;
          cbn [apply_ups fold_left fst snd wden cden zden vz vp vr nth nth_error edge_label];
          rewrite ?sym_ptr_eta]
      end]
  | _ => fail "sym_run: expected a block-entry WP with no pending fault"
  end.

(** Once bounds are collected, the other quoted facts complete the executor's input. *)
Ltac sym_finish_bounds cs se h rho names solve bs :=
  sym_finish constr:(mkFacts bs cs) se h rho names solve.

(** The caller supplies resource names; the tactic reads the other facts from the context. *)
Ltac sym_run_with names solve :=
  iStartProof; autounfold with offs in *;
  let names := String.words names in
  let props := sym_context constr:(@nil Prop) in
  let props := sym_flatten props in
  let qh := sym_quote_heap constr:(mkVal [] [] []) names in
  lazymatch qh with (?h, ?r1) =>
    lazymatch goal with
    | |- environments.envs_entails _ (wp _ _ (_ (mkFrame _ ?e _ None (Exec _ _ _))) _) =>
        let qe := sym_quote_env r1 props e in
        lazymatch qe with (?se, ?r2) => let qc := sym_quote_caps r2 props in
          lazymatch qc with (?cs, ?rho) =>
            let terms := sym_bound_terms rho in
            sym_bounds props terms constr:(@nil bound)
              ltac:(sym_finish_bounds cs se h rho names solve)
          end end
    end
  end.

(** The default solver tries integer arithmetic first, then removes remainders whose inputs already fit.
    Only the remaining goals need division and modulo equations. *)
Ltac sym_lia := first [assumption | reflexivity | lia |
  progress (repeat match goal with
    | |- context [?x mod ?m] =>
        let H := fresh "Hmod" in assert (H : 0 <= x < m) by lia;
        rewrite (Z.mod_small x m H); clear H
    end); lia | Z.div_mod_to_equations; lia].

Ltac sym_run names := sym_run_with names ltac:(sym_lia).
