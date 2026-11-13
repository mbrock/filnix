(** The nanofil backend gives every temporary of a function a slot in
    the function's stack frame. An emitted instruction loads its
    operands from their slots into registers, computes in the
    registers, and stores its result into the slot of its
    destination. This module relates that frame to the environment in
    which the IR's semantics keeps the values of the temporaries.

    The relation [represents] says that the slot of each live
    temporary holds the integer that the IR's environment binds to
    it. With it a theorem about emitted code can speak of the IR's
    state before and after an instruction, and no longer only of the
    registers that the instruction computes in.

    The relation speaks about integers only. When the environment
    binds a temporary to an integer, the slot must hold that integer.
    When the environment binds a temporary to a pointer, the relation
    says nothing about its slot. A pointer also has a capability,
    which the backend keeps in a second slot, and a later extension of
    the relation will cover both slots.

    The backend may give two temporaries the same slot when no point
    of the function has both of them live. The relation therefore
    takes the set of live temporaries as a parameter. A store into a
    slot keeps the relation for the stored temporary and for every
    live temporary in a different slot, and it drops a temporary that
    shared the slot. FrameSlots.v assigns the slots, and the proof
    that its assignment never drops a temporary that is still needed
    is separate work.

    The module has three parts. The first states what the theorems
    assume about the layout of a frame and about where the frame lies
    in memory. The second defines the relation and its rules. The
    third shows that the lines which Layout.v emits for the load of an
    operand and for the store of a result are inside the model, never
    fault, and act on the relation as the IR's semantics acts on the
    environment. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Maps.
From Nanofil Require Values Semantics.
From Backend Require Import Asm Plan Layout.
From Backend Require Import Amd64Word Amd64Memory Amd64Machine Amd64Step Amd64Asm
  Amd64Total.
Import ListNotations.
Local Open Scope Z_scope.

(** ## The frame in memory

    The emitted code addresses a slot as a negative displacement from
    the register `%rbp`, and the context of Layout.v records the
    displacement of each slot. The theorems of this module assume
    three facts about a frame, which this section states: the slots
    lie inside the frame and do not overlap in part, every
    displacement fits its instruction field, and the frame's bytes are
    mapped. *)

(** The function [slot_address] returns the address of the slot at the
    offset off, which is that many bytes below the content of
    `%rbp`. *)
Definition slot_address (off : Z) (s : machine) : Z := regs s RBP - off.

(** The function [slot_operand] returns the memory operand through
    which the emitted code reaches the slot at the offset off. *)
Definition slot_operand (off : Z) : address := mkAddress RBP (- off).

(** A context has its [slots_laid_out] when every slot lies within the
    frame's size and starts at a multiple of eight bytes below `%rbp`.
    Two slots at different offsets are then at least eight bytes
    apart, so a 64-bit store into one does not change the other. The
    theorem `plan_slots_laid_out` of Amd64Layout.v shows that the
    contexts which the backend builds have this property. *)
Definition slots_laid_out (cx : ctx) : Prop :=
  forall k off, slot cx k = Some off -> 8 <= off <= cx_size cx /\ off mod 8 = 0.

(** A context is [frame_encodable] when its frame is at most two to
    the 31 bytes long. Every displacement of a slot then fits the
    signed 32-bit field of a memory operand. A frame beyond that size
    has no encodable slot operands, and the model does not read
    them. *)
Definition frame_encodable (cx : ctx) : Prop := cx_size cx <= 2147483648.

(** A frame is [frame_placed] in a state when `%rbp` holds a 64-bit
    address that is at least the frame's size, and every byte from
    that many bytes below `%rbp` up to `%rbp` is mapped. The function
    prologue establishes this after it has moved `%rsp`, and a theorem
    about a function body assumes it. *)
Definition frame_placed (cx : ctx) (s : machine) : Prop :=
  cx_size cx <= regs s RBP < size_modulus S64
  /\ (forall a, regs s RBP - cx_size cx <= a < regs s RBP -> mapped s a = true).

(** The processor computes the address of a slot operand as the
    address of the slot. The sum does not wrap, because the slot lies
    inside a frame that is placed below `%rbp`. *)
Lemma slot_effective_address (cx : ctx) (k : key) (off : Z) (s : machine) :
  slots_laid_out cx -> frame_placed cx s -> slot cx k = Some off ->
  effective_address (slot_operand off) s = slot_address off s.
Proof.
  intros Hlay [Hbase Hmap] Hslot.
  destruct (Hlay _ _ Hslot) as [[Hlo Hhi] Hmod].
  unfold effective_address, slot_operand, slot_address, get_reg.
  change (wrap S64 (wrap S64 (regs s RBP) - off) = regs s RBP - off).
  rewrite (wrap_small S64 (regs s RBP)) by lia.
  apply wrap_small. lia.
Qed.

(** An access to a slot at any operand size touches only mapped
    bytes. *)
Lemma slot_accessible (cx : ctx) (k : key) (off : Z) (z : size) (s : machine) :
  slots_laid_out cx -> frame_placed cx s -> slot cx k = Some off ->
  accessible z (slot_address off s) s = true.
Proof.
  intros Hlay [Hbase Hmap] Hslot.
  destruct (Hlay _ _ Hslot) as [[Hlo Hhi] Hmod].
  unfold accessible. apply all_mapped_spec. intros i Hi.
  apply Hmap. unfold slot_address.
  destruct z; cbn in Hi; lia.
Qed.

(** Two slots at different offsets are at least eight bytes apart. *)
Lemma slots_apart (cx : ctx) (k k' : key) (off off' : Z) :
  slots_laid_out cx -> slot cx k = Some off -> slot cx k' = Some off' ->
  off <> off' -> off + 8 <= off' \/ off' + 8 <= off.
Proof.
  intros Hlay Hslot Hslot' Hne.
  destruct (Hlay _ _ Hslot) as [_ Hmod].
  destruct (Hlay _ _ Hslot') as [_ Hmod'].
  pose proof (Z.div_mod off 8 ltac:(lia)).
  pose proof (Z.div_mod off' 8 ltac:(lia)). lia.
Qed.

(** The emitter writes the operand of a slot as `-off(%rbp)`, and that
    operand reads as the typed slot operand. *)
Lemma slot_operand_decodes (cx : ctx) (k : key) (off : Z) :
  slots_laid_out cx -> frame_encodable cx -> slot cx k = Some off ->
  memory_operand (mem (- off) "rbp") = Some (slot_operand off).
Proof.
  intros Hlay Henc Hslot.
  destruct (Hlay _ _ Hslot) as [[Hlo Hhi] Hmod].
  assert (Hfit : fits_signed S32 (- off) = true).
  { apply fits_signed_iff. change (-2147483648 <= -off < 2147483648).
    unfold frame_encodable in Henc. lia. }
  change ((if fits_signed S32 (-off) then Some (slot_operand off) else None)
    = Some (slot_operand off)).
  rewrite Hfit. reflexivity.
Qed.

(** A frame stays placed when `%rbp` and the set of mapped addresses
    stay the same. *)
Lemma frame_placed_preserved (cx : ctx) (s s' : machine) :
  frame_placed cx s -> regs s' RBP = regs s RBP -> mapped s' = mapped s ->
  frame_placed cx s'.
Proof.
  unfold frame_placed. intros H Hr Hm. rewrite Hr, Hm. exact H.
Qed.

(** ## The relation

    The IR's semantics keeps the value of each temporary in an
    environment, and the emitted code keeps it in a slot. This section
    defines when a machine state represents an environment, and proves
    the rules by which a load reads the relation and a store updates
    it. *)

(** A machine state [represents] an environment for a set of live
    temporaries when the slot of each live temporary holds the integer
    that the environment binds to it. The slot holds the low 64 bits
    of the integer as an unsigned pattern, which is the content that a
    64-bit store of the integer leaves. The relation says nothing
    about a temporary that is not live, that has no slot, or that the
    environment binds to a pointer or a limit. *)
Definition represents (cx : ctx) (live : name -> Prop) (e : Semantics.env)
    (s : machine) : Prop :=
  forall n v off,
    live n ->
    lookup n e = Some (Values.WInt v) ->
    slot cx (KTmp n) = Some off ->
    read_at S64 (bytes s) (slot_address off s) = wrap S64 v.

(** The set [live_after] contains the temporaries for which the
    relation still holds after a store into the slot of d. They are d
    itself and every temporary that was live and whose slot is not the
    slot of d. A temporary that shares the slot of d has lost its
    value, so it leaves the set. *)
Definition live_after (cx : ctx) (live : name -> Prop) (d : name) : name -> Prop :=
  fun n => n = d \/ (live n /\ slot cx (KTmp n) <> slot cx (KTmp d)).

(** A proof may forget that a temporary is live. If a state represents
    an environment for a set of live temporaries, then it represents
    the environment for every subset of that set. *)
Lemma represents_subset (cx : ctx) (live live' : name -> Prop) (e : Semantics.env)
    (s : machine) :
  (forall n, live' n -> live n) ->
  represents cx live e s -> represents cx live' e s.
Proof.
  unfold represents. intros Hsub Hrep n v off Hlive He Hslot.
  eapply Hrep; eauto.
Qed.

(** The relation depends only on `%rbp` and on the bytes of the frame.
    A state with the same `%rbp` and the same frame content represents
    the same environment. *)
Lemma represents_same_frame (cx : ctx) (live : name -> Prop) (e : Semantics.env)
    (s s' : machine) :
  slots_laid_out cx ->
  regs s' RBP = regs s RBP ->
  (forall a, regs s RBP - cx_size cx <= a < regs s RBP -> bytes s' a = bytes s a) ->
  represents cx live e s -> represents cx live e s'.
Proof.
  intros Hlay Hr Hb Hrep n v off Hlive He Hslot.
  unfold slot_address. rewrite Hr.
  rewrite (read_at_agree S64 (bytes s') (bytes s)).
  - exact (Hrep n v off Hlive He Hslot).
  - intros i Hi. apply Hb.
    destruct (Hlay _ _ Hslot) as [[Hlo Hhi] Hmod]. cbn in Hi. lia.
Qed.

(** A read of a live temporary's slot at the size of an integer class
    returns the low part of the integer that the environment binds to
    the temporary. A 32-bit read of a 64-bit slot therefore returns
    the temporary's value at the class `w`. *)
Lemma represents_read (cx : ctx) (live : name -> Prop) (e : Semantics.env)
    (s : machine) (n : name) (v off : Z) (z : size) :
  represents cx live e s ->
  live n ->
  lookup n e = Some (Values.WInt v) ->
  slot cx (KTmp n) = Some off ->
  read_at z (bytes s) (slot_address off s) = wrap z v.
Proof.
  intros Hrep Hlive He Hslot.
  rewrite (read_at_narrower z S64) by (destruct z; cbn; lia).
  rewrite (Hrep n v off Hlive He Hslot).
  apply wrap_narrower. destruct z; cbn; lia.
Qed.

(** A 64-bit store of the integer v into the slot of d makes the state
    represent the environment in which d is bound to v. The relation
    holds afterwards for the set [live_after]. *)
Lemma represents_store (cx : ctx) (live : name -> Prop) (e : Semantics.env)
    (s : machine) (d : name) (off v : Z) :
  slots_laid_out cx ->
  slot cx (KTmp d) = Some off ->
  represents cx live e s ->
  represents cx (live_after cx live d) (put d (Values.WInt v) e)
    (set_bytes (write_at S64 (bytes s) (slot_address off s) v) s).
Proof.
  intros Hlay Hd Hrep n v' off' Hlive He Hslot.
  unfold slot_address. rewrite regs_set_bytes, bytes_set_bytes.
  rewrite lookup_put_name in He.
  destruct (name_eqb n d) eqn:End.
  - apply term_eqb_eq in End. subst n.
    rewrite Hd in Hslot. inversion Hslot; subst off'.
    inversion He; subst v'. apply read_write_at_same.
  - destruct Hlive as [-> | [Hlive Hne]].
    + rewrite term_eqb_refl in End. discriminate.
    + assert (Hoff : off <> off') by (intro E; subst; apply Hne; congruence).
      pose proof (slots_apart cx (KTmp d) (KTmp n) off off' Hlay Hd Hslot Hoff).
      rewrite read_write_at_apart by (cbn; unfold slot_address; lia).
      exact (Hrep n v' off' Hlive He Hslot).
Qed.

(** ## Operands in the IR's semantics

    The IR evaluates an operand with the function `value_x` of
    Semantics.v, which reads a temporary from the environment or
    reduces a constant to its class. This section states what that
    evaluation returns for an integer class, in the terms of
    Amd64Word.v. *)

(** The modulus of an integer class is the modulus of its operand
    size. *)
Lemma class_size_modulus (k : class) (z : size) :
  class_size k = Some z -> modulus k = Some (size_modulus z).
Proof.
  destruct k; cbn [class_size]; intros H; inversion H; reflexivity.
Qed.

(** A temporary that evaluates to an integer at an integer class is
    bound to an integer, and the evaluation returns the low part of
    that integer at the size of the class. *)
Lemma value_x_temporary (ge : Semantics.genv) (e : Semantics.env) (k : class)
    (z : size) (n : name) (w : Z) :
  class_size k = Some z ->
  Semantics.value_x ge e k (Tmp n) = Some (Values.WInt w) ->
  exists v, lookup n e = Some (Values.WInt v) /\ w = wrap z v.
Proof.
  destruct k; cbn [class_size]; intros Hk; inversion Hk; subst z;
    unfold Semantics.value_x;
    destruct (lookup n e) as [x|] eqn:He; try discriminate;
    destruct x; cbn [Values.word_at_class]; try discriminate;
    intros H; inversion H; subst; eexists; split; reflexivity.
Qed.

(** A constant evaluates at an integer class to its low part at the
    size of the class. *)
Lemma value_x_constant (ge : Semantics.genv) (e : Semantics.env) (k : class)
    (z : size) (n w : Z) :
  class_size k = Some z ->
  Semantics.value_x ge e k (Const n) = Some (Values.WInt w) ->
  w = wrap z n.
Proof.
  destruct k; cbn [class_size]; intros Hk; inversion Hk; subst z;
    cbn [Semantics.value_x modulus]; intros H; inversion H; reflexivity.
Qed.

(** An operand that evaluates to an integer at an integer class
    evaluates to a valid pattern of the size of the class. *)
Lemma value_x_range (ge : Semantics.genv) (e : Semantics.env) (k : class)
    (z : size) (v : value) (w : Z) :
  class_size k = Some z ->
  Semantics.value_x ge e k v = Some (Values.WInt w) ->
  0 <= w < size_modulus z.
Proof.
  intros Hk Hv. destruct v as [n|n|n].
  - destruct (value_x_temporary ge e k z n w Hk Hv) as [x [_ ->]].
    apply wrap_range.
  - rewrite (value_x_constant ge e k z n w Hk Hv). apply wrap_range.
  - unfold Semantics.value_x in Hv.
    destruct (lookup n (Semantics.ge_globals ge)); discriminate.
Qed.

(** ## Loads and stores of the emitter

    The emitter's `load` puts an operand in a register, and its
    `slot_store` puts a register in a slot. This section proves one
    fragment specification for each. Both hold from every state in
    which the frame is placed and represents the environment. *)

(** The emitter names a register by a short string such as `a` or
    `c`, from which Layout.v derives the 64-bit and the 32-bit name.
    The relation [names_register] holds of a short string and a
    register when both derived names select that register. *)
Definition names_register (r : string) (g : gpr) : Prop :=
  register (reg64 r) = Some (S64, g) /\ register (reg32 r) = Some (S32, g).

(** An operand is [operand_live] when it is a constant, a global, or a
    temporary in the set of live temporaries. *)
Definition operand_live (live : name -> Prop) (v : value) : Prop :=
  match v with
  | Tmp n => live n
  | Const _ | Global _ => True
  end.

(** An operand is [operand_placed] when it is a constant, a global, or
    a temporary that has a slot in the frame. The emitter writes a
    placeholder for a temporary without a slot, and the placeholder
    has no typed form. *)
Definition operand_placed (cx : ctx) (v : value) : Prop :=
  match v with
  | Tmp n => exists off, slot cx (KTmp n) = Some off
  | Const _ | Global _ => True
  end.

(** The relation [only_register] holds of two states when the second
    differs from the first in at most the register g and the flags.
    Every other register, the memory and the set of mapped addresses
    are the same. *)
Definition only_register (g : gpr) (s s' : machine) : Prop :=
  (forall r, r <> g -> regs s' r = regs s r)
  /\ bytes s' = bytes s
  /\ mapped s' = mapped s.

(** The relation [only_slot] holds of two states when the second
    differs from the first in at most the eight bytes of the slot at
    the offset off. Every register, every byte outside the slot and
    the set of mapped addresses are the same. *)
Definition only_slot (off : Z) (s s' : machine) : Prop :=
  (forall r, regs s' r = regs s r)
  /\ mapped s' = mapped s
  /\ (forall a, a < slot_address off s \/ slot_address off s + 8 <= a ->
        bytes s' a = bytes s a).

(** The short names `a` and `c` name the registers `%rax` and `%rcx`,
    which hold the operands of a division. *)
Example names_rax : names_register "a" RAX.
Proof. split; reflexivity. Qed.

(** The short name `c` names the register `%rcx`. *)
Example names_rcx : names_register "c" RCX.
Proof. split; reflexivity. Qed.

(** A register write preserves the rest of the machine, which the
    operand load specification requires for both kinds of source. *)
Lemma set_reg_only (z : size) (g : gpr) (v : Z) (s : machine) :
  only_register g s (set_reg z g v s).
Proof.
  split; [intros r H; apply regs_set_reg_other; exact H |].
  split; [apply bytes_set_reg | apply mapped_set_reg].
Qed.

(** An immediate move completes with its value in the destination.
    This rule supplies the execution part of the constant load proof. *)
Lemma immediate_move_spec (z : size) (n : Z) (g : gpr) :
  establishes (fun _ => True) [IMov z (SImm n) g]
    (fun s s' => s' = set_reg z g (wrap z n) s).
Proof.
  intros s o _ Hr.
  destruct (runs_cons_inv _ _ _ _ Hr) as [h [[t [Ht Hrest]] | [f [Hf Ho]]]].
  - change (Next (set_reg z g (wrap z n) s) = Next t) in Ht.
    inversion Ht; subst t. apply runs_nil_inv in Hrest.
    eexists; split; [exact Hrest | reflexivity].
  - discriminate Hf.
Qed.

(** The emitted load of an operand is inside the model and never
    faults. It leaves in the whole register the integer to which the
    IR evaluates the operand at the class k, so a 32-bit value is
    zero-extended. It changes no other register and no memory. The
    operand is a live temporary with a slot or a constant; a global
    does not evaluate to an integer, so the hypothesis on `value_x`
    excludes it. *)
Lemma load_operand_spec (cx : ctx) (ge : Semantics.genv) (live : name -> Prop)
    (e : Semantics.env) (k : class) (z : size) (v : value) (w : Z) (r : string)
    (g : gpr) :
  class_size k = Some z ->
  slots_laid_out cx ->
  frame_encodable cx ->
  names_register r g ->
  operand_placed cx v ->
  operand_live live v ->
  Semantics.value_x ge e k v = Some (Values.WInt w) ->
  exists code,
    decode_lines (load cx v k r) = Some code
    /\ establishes (fun s => frame_placed cx s /\ represents cx live e s) code
         (fun s s' => regs s' g = w /\ only_register g s s').
Proof.
  intros Hk Hlay Henc [Hr64 Hr32] Hplaced Hlive Hv.
  destruct v as [n|n|n].
  - destruct Hplaced as [off Hslot].
    destruct (value_x_temporary ge e k z n w Hk Hv) as [x [He ->]].
    exists [ILoad z (slot_operand off) g]. split.
    + assert (Hd : forall r', register r' = Some (z, g) ->
        decode_move z (mem (-off) "rbp") (reg r') = Some (ILoad z (slot_operand off) g)).
      { intros r' Hr. unfold decode_move.
        rewrite (slot_operand_decodes cx (KTmp n) off Hlay Henc Hslot).
        change ((match sized_register z (reg r') with
          | Some d => Some (ILoad z (slot_operand off) d) | None => None end)
          = Some (ILoad z (slot_operand off) g)).
        unfold sized_register, reg. rewrite Hr.
        destruct z; reflexivity. }
      destruct k; cbn [class_size] in Hk; inversion Hk; subst z;
        unfold load, with_slot; rewrite Hslot.
      * change ((match decode_move S32 (mem (-off) "rbp") (reg (reg32 r)) with
          | Some i => Some [i] | None => None end) = Some [ILoad S32 (slot_operand off) g]).
        rewrite Hd by assumption. reflexivity.
      * change ((match decode_move S64 (mem (-off) "rbp") (reg (reg64 r)) with
          | Some i => Some [i] | None => None end) = Some [ILoad S64 (slot_operand off) g]).
        rewrite Hd by assumption. reflexivity.
    + eapply establishes_weaken; [apply load_spec | |].
      * intros s [Hp _]. rewrite (slot_effective_address cx (KTmp n) off s Hlay Hp Hslot).
        exact (slot_accessible cx (KTmp n) off z s Hlay Hp Hslot).
      * intros s s' [Hp Hrep] ->.
        rewrite (slot_effective_address cx (KTmp n) off s Hlay Hp Hslot).
        rewrite (represents_read cx live e s n x off z Hrep Hlive He Hslot).
        split; [|apply set_reg_only].
        destruct k; cbn [class_size] in Hk; inversion Hk; subst z;
          rewrite ?regs_set_reg_32, ?regs_set_reg_64; apply wrap_wrap.
  - pose proof (value_x_constant ge e k z n w Hk Hv) as Hw. subst w.
    destruct k; cbn [class_size] in Hk; inversion Hk; subst z.
    + exists [IMov S32 (SImm (wrap S32 n)) g]. split.
      * assert (Hfit : immediate_fits S32 (wrap S32 n) = true).
        { unfold immediate_fits. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt.
          change (-2147483648 <= wrap S32 n < 4294967296).
          pose proof (wrap_range S32 n) as Hrange.
          change (0 <= wrap S32 n < 4294967296) in Hrange. lia. }
        change ((match decode_move S32 (imm (wrap S32 n)) (reg (reg32 r)) with
          | Some i => Some [i] | None => None end) = Some [IMov S32 (SImm (wrap S32 n)) g]).
        unfold decode_move. cbn [memory_operand].
        unfold sized_source, imm, sized_register, reg. rewrite Hr32, Hfit. reflexivity.
      * eapply establishes_weaken; [apply immediate_move_spec | intros; exact I |].
        intros s s' _ ->. split; [rewrite regs_set_reg_32, !wrap_wrap; reflexivity | apply set_reg_only].
    + exists [IMov S64 (SImm (signed_at S64 n)) g]. split.
      * assert (Hfit : wide_immediate_fits (signed_at S64 n) = true).
        { unfold wide_immediate_fits. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt.
          change (-9223372036854775808 <= signed_at S64 n < 18446744073709551616).
          pose proof (signed_at_range S64 n) as Hrange.
          change (-9223372036854775808 <= signed_at S64 n < 9223372036854775808) in Hrange. lia. }
        assert (Hs : (if n mod two64 >=? two63 then n mod two64 - two64 else n mod two64)
          = signed_at S64 n).
        { unfold signed_at, sign_bit, wrap.
          change ((if n mod two64 >=? two63 then n mod two64 - two64 else n mod two64) =
            (if two63 <=? n mod two64 then n mod two64 - two64 else n mod two64)).
          rewrite Z.geb_leb. reflexivity. }
        unfold load. change ((match decode_wide_move S64
          (imm (if n mod two64 >=? two63 then n mod two64 - two64 else n mod two64))
          (reg (reg64 r)) with | Some i => Some [i] | None => None end) = Some [IMov S64 (SImm (signed_at S64 n)) g]).
        rewrite Hs. unfold decode_wide_move, sized_register, reg, imm.
        rewrite Hr64, Hfit. reflexivity.
      * eapply establishes_weaken; [apply immediate_move_spec | intros; exact I |].
        intros s s' _ ->. split; [|apply set_reg_only].
        rewrite regs_set_reg_64, wrap_wrap, wrap_signed_at. reflexivity.
  - unfold Semantics.value_x in Hv.
    destruct (lookup n (Semantics.ge_globals ge)); discriminate.
Qed.

(** The emitter saves the result of an instruction by storing a 64-bit
    register into the slot of the destination temporary d. This lemma
    says that the store never faults and that the frame afterwards
    agrees with the IR once it has bound d. The final state represents
    the environment in which d is bound to the content of the
    register, for the set [live_after]. The store changes only the
    bytes of that slot. *)
Lemma store_slot_spec (cx : ctx) (live : name -> Prop) (e : Semantics.env)
    (d : name) (off : Z) (r : string) (g : gpr) :
  slots_laid_out cx ->
  frame_encodable cx ->
  register r = Some (S64, g) ->
  slot cx (KTmp d) = Some off ->
  exists code,
    decode_lines (slot_store cx r (KTmp d)) = Some code
    /\ establishes (fun s => frame_placed cx s /\ represents cx live e s) code
         (fun s s' =>
            represents cx (live_after cx live d)
              (put d (Values.WInt (regs s g)) e) s'
            /\ only_slot off s s').
Proof.
  intros Hlay Henc Hr Hslot.
  exists [IStore S64 g (slot_operand off)]. split.
  - unfold slot_store, with_slot. rewrite Hslot.
    assert (Hd : decode_move S64 (reg r) (mem (-off) "rbp") =
      Some (IStore S64 g (slot_operand off))).
    { unfold decode_move. rewrite (slot_operand_decodes cx (KTmp d) off Hlay Henc Hslot).
      change ((match sized_register S64 (reg r) with
        | Some x => Some (IStore S64 x (slot_operand off)) | None => None end)
        = Some (IStore S64 g (slot_operand off))).
      unfold sized_register, reg. rewrite Hr. reflexivity. }
    change ((match decode_move S64 (reg r) (mem (-off) "rbp") with
      | Some i => Some [i] | None => None end) = Some [IStore S64 g (slot_operand off)]).
    rewrite Hd. reflexivity.
  - eapply establishes_weaken; [apply store_spec | |].
    + intros s [Hp _]. rewrite (slot_effective_address cx (KTmp d) off s Hlay Hp Hslot).
      exact (slot_accessible cx (KTmp d) off S64 s Hlay Hp Hslot).
    + intros s s' [Hp Hrep] ->.
      rewrite (slot_effective_address cx (KTmp d) off s Hlay Hp Hslot).
      split.
      * eapply represents_same_frame with
          (s := set_bytes (write_at S64 (bytes s) (slot_address off s) (regs s g)) s);
          [exact Hlay | | |].
        -- repeat rewrite regs_set_bytes. reflexivity.
        -- intros a Ha. repeat rewrite bytes_set_bytes.
           unfold get_reg. apply write_at_wrap.
        -- apply represents_store; assumption.
      * unfold only_slot. split; [intro x; apply regs_set_bytes |].
        split; [apply mapped_set_bytes |]. intros a Ha.
        rewrite bytes_set_bytes. apply write_bytes_outside. exact Ha.
Qed.
