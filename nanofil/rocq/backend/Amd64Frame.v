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
Admitted.

(** An access to a slot at any operand size touches only mapped
    bytes. *)
Lemma slot_accessible (cx : ctx) (k : key) (off : Z) (z : size) (s : machine) :
  slots_laid_out cx -> frame_placed cx s -> slot cx k = Some off ->
  accessible z (slot_address off s) s = true.
Proof.
Admitted.

(** Two slots at different offsets are at least eight bytes apart. *)
Lemma slots_apart (cx : ctx) (k k' : key) (off off' : Z) :
  slots_laid_out cx -> slot cx k = Some off -> slot cx k' = Some off' ->
  off <> off' -> off + 8 <= off' \/ off' + 8 <= off.
Proof.
Admitted.

(** The emitter writes the operand of a slot as `-off(%rbp)`, and that
    operand reads as the typed slot operand. *)
Lemma slot_operand_decodes (cx : ctx) (k : key) (off : Z) :
  slots_laid_out cx -> frame_encodable cx -> slot cx k = Some off ->
  memory_operand (mem (- off) "rbp") = Some (slot_operand off).
Proof.
Admitted.

(** A frame stays placed when `%rbp` and the set of mapped addresses
    stay the same. *)
Lemma frame_placed_preserved (cx : ctx) (s s' : machine) :
  frame_placed cx s -> regs s' RBP = regs s RBP -> mapped s' = mapped s ->
  frame_placed cx s'.
Proof.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

(** A temporary that evaluates to an integer at an integer class is
    bound to an integer, and the evaluation returns the low part of
    that integer at the size of the class. *)
Lemma value_x_temporary (ge : Semantics.genv) (e : Semantics.env) (k : class)
    (z : size) (n : name) (w : Z) :
  class_size k = Some z ->
  Semantics.value_x ge e k (Tmp n) = Some (Values.WInt w) ->
  exists v, lookup n e = Some (Values.WInt v) /\ w = wrap z v.
Proof.
Admitted.

(** A constant evaluates at an integer class to its low part at the
    size of the class. *)
Lemma value_x_constant (ge : Semantics.genv) (e : Semantics.env) (k : class)
    (z : size) (n w : Z) :
  class_size k = Some z ->
  Semantics.value_x ge e k (Const n) = Some (Values.WInt w) ->
  w = wrap z n.
Proof.
Admitted.

(** An operand that evaluates to an integer at an integer class
    evaluates to a valid pattern of the size of the class. *)
Lemma value_x_range (ge : Semantics.genv) (e : Semantics.env) (k : class)
    (z : size) (v : value) (w : Z) :
  class_size k = Some z ->
  Semantics.value_x ge e k v = Some (Values.WInt w) ->
  0 <= w < size_modulus z.
Proof.
Admitted.

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
Admitted.

(** The emitted store of a 64-bit register into the slot of the
    temporary d is inside the model and never faults. Afterwards the
    state represents the environment in which d is bound to the
    content of the register, for the set [live_after]. The store
    changes only the bytes of that slot. *)
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
Admitted.
