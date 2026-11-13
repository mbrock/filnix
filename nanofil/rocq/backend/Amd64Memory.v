(** The code that the nanofil backend emits keeps every temporary in
    the stack frame, so an emitted instruction reads its operands from
    memory and writes its result back to memory. This module defines
    the memory content that those reads and writes act on: one byte at
    each address, with integers stored in little-endian order.

    A read on x86-64 assembles the bytes at consecutive addresses into
    an integer, with the byte at the lowest address as the least
    significant. A write stores the low bytes of an integer in the
    same order. The two functions here state that order once, for
    every operand size.

    The IR model in Memory.v describes the bytes of the program's
    objects in the same way, with the function `byte_of` and the same
    order. This module reuses `byte_of`, and its last section shows
    that its reads and writes agree with the IR's `load_bytes` and
    `store_bytes`. A later theorem about the program's own loads and
    stores can then compare the two memories without a conversion.

    This module does not mention registers or instructions, and it
    does not say which addresses a program may access. The record
    `machine` in Amd64Machine.v adds a byte map to the processor state
    together with the set of mapped addresses. *)

From Stdlib Require Import ZArith List Bool Lia.
From Nanofil Require Import Memory.
From Backend Require Import Amd64Word.
Import ListNotations.
Local Open Scope Z_scope.

(** ## Byte maps

    A byte map gives the content of every address. The functions of
    this section read an integer of a given size from a byte map and
    write one to it. *)

(** A [byte_map] gives one integer for each address. A read uses only
    the low eight bits of each integer, in the same way as a register
    read uses only the low bits of a register content. *)
Definition byte_map : Type := Z -> Z.

(** The function [size_bytes] returns the number of bytes that an
    operand of the given size occupies in memory. *)
Definition size_bytes (z : size) : nat :=
  match z with
  | S8 => 1
  | S16 => 2
  | S32 => 4
  | S64 => 8
  end%nat.

(** The function [read_bytes] assembles the n bytes at the addresses
    from a upward into an unsigned integer. The byte at the address a
    is the least significant, which is the little-endian order of
    x86-64. *)
Fixpoint read_bytes (n : nat) (b : byte_map) (a : Z) : Z :=
  match n with
  | O => 0
  | S n' => b a mod 256 + 256 * read_bytes n' b (a + 1)
  end.

(** The function [write_bytes] stores the n low bytes of the integer v
    at the addresses from a upward, least significant byte first. It
    leaves the content of every other address as it was. *)
Definition write_bytes (n : Z) (b : byte_map) (a v : Z) : byte_map :=
  fun a' => if (a <=? a') && (a' <? a + n) then byte_of v (a' - a) else b a'.

(** The function [read_at] reads an unsigned integer of the size z at
    the address a. *)
Definition read_at (z : size) (b : byte_map) (a : Z) : Z :=
  read_bytes (size_bytes z) b a.

(** The function [write_at] writes the low part of the integer v, at
    the size z, to the address a. *)
Definition write_at (z : size) (b : byte_map) (a v : Z) : byte_map :=
  write_bytes (Z.of_nat (size_bytes z)) b a v.

(** The function [all_mapped] decides whether the predicate p holds of
    each of the n addresses from a upward. The machine uses it to
    check that every byte of an access is mapped. *)
Fixpoint all_mapped (n : nat) (p : Z -> bool) (a : Z) : bool :=
  match n with
  | O => true
  | S n' => p a && all_mapped n' p (a + 1)
  end.

(** ## Facts about reads

    A read returns a valid pattern of its size, and it depends only on
    the bytes that it covers. A narrow read at an address returns the
    low part of a wide read at the same address, which is what makes a
    32-bit load from a 64-bit slot correct. *)

(** The number of bytes of a size, times eight, is its number of
    bits. *)
Lemma size_bytes_bits (z : size) : 8 * Z.of_nat (size_bytes z) = size_bits z.
Proof.
  destruct z; reflexivity.
Qed.

(** A read with one more byte has 256 times as many possible values.
    This factor gives the weight of the remaining bytes after the
    lowest byte is removed. *)
Lemma byte_power_succ (n : nat) :
  2 ^ (8 * Z.of_nat (S n)) = 256 * 2 ^ (8 * Z.of_nat n).
Proof.
  rewrite Nat2Z.inj_succ.
  replace (8 * Z.succ (Z.of_nat n)) with (8 + 8 * Z.of_nat n) by lia.
  rewrite Z.pow_add_r by lia. reflexivity.
Qed.

(** A read of n bytes returns an unsigned integer of n bytes. *)
Lemma read_bytes_range (n : nat) (b : byte_map) (a : Z) :
  0 <= read_bytes n b a < 2 ^ (8 * Z.of_nat n).
Proof.
  revert a. induction n as [|n IH]; intros a.
  - cbn. lia.
  - cbn [read_bytes]. rewrite byte_power_succ.
    pose proof (Z.mod_pos_bound (b a) 256 ltac:(lia)).
    specialize (IH (a + 1)). lia.
Qed.

(** A read at a size returns a valid pattern of that size. *)
Lemma read_at_range (z : size) (b : byte_map) (a : Z) :
  0 <= read_at z b a < size_modulus z.
Proof.
  unfold read_at, size_modulus. rewrite <- size_bytes_bits.
  apply read_bytes_range.
Qed.

(** Two byte maps that agree on the n addresses from a upward give the
    same read there. *)
Lemma read_bytes_agree (n : nat) (b b' : byte_map) (a : Z) :
  (forall i, 0 <= i < Z.of_nat n -> b (a + i) = b' (a + i)) ->
  read_bytes n b a = read_bytes n b' a.
Proof.
  revert a. induction n as [|n IH]; intros a H; cbn [read_bytes].
  - reflexivity.
  - pose proof (H 0 ltac:(rewrite Nat2Z.inj_succ; lia)) as H0.
    rewrite Z.add_0_r in H0. rewrite H0.
    rewrite IH; [reflexivity|]. intros i Hi.
    replace (a + 1 + i) with (a + (i + 1)) by lia.
    apply H. rewrite Nat2Z.inj_succ. lia.
Qed.

(** Two byte maps that agree on the bytes of an access give the same
    read at its size. *)
Lemma read_at_agree (z : size) (b b' : byte_map) (a : Z) :
  (forall i, 0 <= i < Z.of_nat (size_bytes z) -> b (a + i) = b' (a + i)) ->
  read_at z b a = read_at z b' a.
Proof.
  apply read_bytes_agree.
Qed.

(** Splitting a read after its first n bytes separates its low part
    from the remaining bytes. This lets the prefix proof discard the
    high part by reduction modulo the weight of the split. *)
Lemma read_bytes_split (n k : nat) (b : byte_map) (a : Z) :
  read_bytes (n + k) b a = read_bytes n b a
    + 2 ^ (8 * Z.of_nat n) * read_bytes k b (a + Z.of_nat n).
Proof.
  revert a. induction n as [|n IH]; intros a.
  - change (read_bytes k b a = 0 + 1 * read_bytes k b (a + 0)).
    rewrite Z.add_0_r. ring.
  - cbn [Nat.add read_bytes]. rewrite IH, byte_power_succ, Nat2Z.inj_succ.
    replace (a + 1 + Z.of_nat n) with (a + Z.succ (Z.of_nat n)) by lia.
    ring.
Qed.

(** The first n bytes of a longer read are its low part. *)
Lemma read_bytes_prefix (n n' : nat) (b : byte_map) (a : Z) :
  (n <= n')%nat ->
  read_bytes n b a = read_bytes n' b a mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros H. replace n' with (n + (n' - n))%nat by lia.
  rewrite read_bytes_split, Z.mul_comm, Z.mod_add by
    (pose proof (Z.pow_pos_nonneg 2 (8 * Z.of_nat n) ltac:(lia) ltac:(lia)); lia).
  symmetry. apply Z.mod_small, read_bytes_range.
Qed.

(** A read at a narrow size returns the low part of a read at a wider
    size from the same address. *)
Lemma read_at_narrower (z z' : size) (b : byte_map) (a : Z) :
  size_bits z <= size_bits z' ->
  read_at z b a = wrap z (read_at z' b a).
Proof.
  intros H. unfold read_at, wrap, size_modulus.
  rewrite <- size_bytes_bits. apply read_bytes_prefix.
  destruct z, z'; cbn in *; lia.
Qed.

(** ## Facts about writes

    A write changes exactly the bytes that it covers. A read of the
    same size at the same address returns what was written, and a read
    that does not overlap the write returns what it returned before. *)

(** A write leaves the byte at every address outside its range
    unchanged. *)
Lemma write_bytes_outside (n : Z) (b : byte_map) (a v a' : Z) :
  a' < a \/ a + n <= a' -> write_bytes n b a v a' = b a'.
Proof.
  intros H. unfold write_bytes.
  destruct (a <=? a') eqn:L; destruct (a' <? a + n) eqn:U;
    cbn; try reflexivity.
  apply Z.leb_le in L. apply Z.ltb_lt in U. lia.
Qed.

(** A write stores the byte of v that has the index i at the address
    a + i. *)
Lemma write_bytes_inside (n : Z) (b : byte_map) (a v i : Z) :
  0 <= i < n -> write_bytes n b a v (a + i) = byte_of v i.
Proof.
  intros H. unfold write_bytes.
  rewrite (proj2 (Z.leb_le a (a + i)) ltac:(lia)),
    (proj2 (Z.ltb_lt (a + i) (a + n)) ltac:(lia)). cbn [andb].
  replace (a + i - a) with i by lia. reflexivity.
Qed.

(** Reading the bytes extracted from an integer reconstructs its low
    bytes. The write proof uses this fact after identifying each stored
    byte with the corresponding byte of the integer. *)
Lemma read_bytes_byte_of (n : nat) (v a : Z) :
  read_bytes n (fun p => byte_of v (p - a)) a =
  v mod 2 ^ (8 * Z.of_nat n).
Proof.
  induction n as [|n IH].
  - cbn. rewrite Z.mod_1_r. reflexivity.
  - replace (S n) with (n + 1)%nat by lia.
    rewrite read_bytes_split, IH. cbn [read_bytes].
    replace (a + Z.of_nat n - a) with (Z.of_nat n) by lia.
    unfold byte_of. rewrite Z.mod_mod by lia. rewrite Z.mul_0_r, Z.add_0_r.
    replace (n + 1)%nat with (S n) by lia. rewrite byte_power_succ.
    rewrite (Z.mul_comm 256 (2 ^ (8 * Z.of_nat n))), Z.rem_mul_r by
      (lia || (pose proof (Z.pow_pos_nonneg 2 (8 * Z.of_nat n) ltac:(lia) ltac:(lia)); lia)).
    reflexivity.
Qed.

(** A read of the n bytes that a write of n bytes stored returns the
    low n bytes of the written integer. *)
Lemma read_write_bytes_same (n : nat) (b : byte_map) (a v : Z) :
  read_bytes n (write_bytes (Z.of_nat n) b a v) a = v mod 2 ^ (8 * Z.of_nat n).
Proof.
  rewrite <- (read_bytes_byte_of n v a). apply read_bytes_agree.
  intros i Hi. rewrite write_bytes_inside by exact Hi.
  replace (a + i - a) with i by lia. reflexivity.
Qed.

(** A read after a write of the same size at the same address returns
    the pattern of the written integer at that size. *)
Lemma read_write_at_same (z : size) (b : byte_map) (a v : Z) :
  read_at z (write_at z b a v) a = wrap z v.
Proof.
  unfold read_at, write_at. rewrite read_write_bytes_same.
  unfold wrap, size_modulus. rewrite size_bytes_bits. reflexivity.
Qed.

(** A read whose bytes lie entirely below or entirely above the bytes
    of a write returns what it returned before the write. The two
    accesses may have different sizes. *)
Lemma read_write_at_apart (z z' : size) (b : byte_map) (a a' v : Z) :
  a' + Z.of_nat (size_bytes z') <= a \/ a + Z.of_nat (size_bytes z) <= a' ->
  read_at z' (write_at z b a v) a' = read_at z' b a'.
Proof.
  intros H. apply read_at_agree. intros i Hi.
  apply write_bytes_outside. lia.
Qed.

(** A write of an integer and a write of its pattern at the same size
    store the same bytes. *)
Lemma write_at_wrap (z : size) (b : byte_map) (a v a' : Z) :
  write_at z b a (wrap z v) a' = write_at z b a v a'.
Proof.
  unfold write_at, write_bytes. destruct (_ && _) eqn:E; [|reflexivity].
  apply andb_true_iff in E. destruct E as [L U].
  apply Z.leb_le in L. apply Z.ltb_lt in U.
  unfold byte_of, wrap, size_modulus.
  apply Z.bits_inj'. intros k Hk.
  change 256 with (2 ^ 8).
  rewrite !Z.testbit_mod_pow2 by lia.
  rewrite <- !Z.shiftr_div_pow2 by lia.
  rewrite !Z.shiftr_spec by lia.
  rewrite Z.testbit_mod_pow2 by (destruct z; cbn; lia).
  destruct (k <? 8) eqn:K; [|reflexivity].
  apply Z.ltb_lt in K.
  rewrite (proj2 (Z.ltb_lt (k + 8 * (a' - a)) (size_bits z))
    ltac:(rewrite <- size_bytes_bits; lia)).
  reflexivity.
Qed.

(** ## Facts about mapped ranges

    The function [all_mapped] is a computation, and a proof needs it
    as a statement about each address of the range. *)

(** Every one of the n addresses from a upward satisfies p exactly
    when [all_mapped] returns true. *)
Lemma all_mapped_spec (n : nat) (p : Z -> bool) (a : Z) :
  all_mapped n p a = true <-> (forall i, 0 <= i < Z.of_nat n -> p (a + i) = true).
Proof.
  revert a. induction n as [|n IH]; intros a.
  - cbn. split; [intros _ i Hi; lia|reflexivity].
  - cbn [all_mapped]. rewrite andb_true_iff, IH. split.
    + intros [H T] i Hi. destruct (Z.eq_dec i 0) as [->|N].
      * now rewrite Z.add_0_r.
      * replace (a + i) with (a + 1 + (i - 1)) by lia.
        apply T. rewrite Nat2Z.inj_succ in Hi. lia.
    + intros H. split.
      * replace a with (a + 0) by lia. apply H. rewrite Nat2Z.inj_succ. lia.
      * intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia.
        apply H. rewrite Nat2Z.inj_succ. lia.
Qed.

(** A range that is mapped contains only mapped prefixes. *)
Lemma all_mapped_prefix (n n' : nat) (p : Z -> bool) (a : Z) :
  (n <= n')%nat -> all_mapped n' p a = true -> all_mapped n p a = true.
Proof.
  intros H M. apply all_mapped_spec.
  intros i Hi. apply (proj1 (all_mapped_spec n' p a) M). lia.
Qed.

(** ## Agreement with the IR's memory

    The IR model reads and writes the bytes of the program's objects
    with `load_bytes` and `store_bytes` of Memory.v. These lemmas show
    that the machine's reads and writes are the same functions of the
    same bytes, so both models use one byte order. *)

(** A machine read of the IR's bytes returns what the IR's
    `load_bytes` returns, provided that each byte of the range is a
    valid byte. The IR's function does not reduce a byte that it
    reads, which is why the lemma needs the bound. *)
Lemma read_at_load_bytes (z : size) (m : mem) (a : Z) :
  (forall i, 0 <= i < Z.of_nat (size_bytes z) -> 0 <= m_bytes m (a + i) < 256) ->
  read_at z (m_bytes m) a = load_bytes m a (Z.of_nat (size_bytes z)).
Proof.
  intros H. unfold read_at, load_bytes. rewrite Nat2Z.id.
  destruct z; cbn [size_bytes read_bytes].
  all: cbn [Z.to_nat Pos.to_nat Nat.iter] in *.
  all: repeat match goal with
    | |- context [m_bytes ?mm ?p mod 256] =>
      rewrite (Z.mod_small (m_bytes mm p)) by
        (replace p with (a + (p - a)) by lia; apply H; cbn; lia)
    end.
  all: repeat rewrite <- Z.add_assoc.
  all: cbn [Z.of_nat Pos.of_succ_nat Z.add Pos.add PosDef.Pos.succ].
  all: rewrite ?Z.add_0_r.
  all: ring.
Qed.

(** A machine write to the IR's bytes stores what the IR's
    `store_bytes` stores, at every address. *)
Lemma write_at_store_bytes (z : size) (m : mem) (a v a' : Z) :
  write_at z (m_bytes m) a v a'
  = m_bytes (store_bytes m a (Z.of_nat (size_bytes z)) v) a'.
Proof.
  reflexivity.
Qed.

(** ## Tests of the byte order

    These examples evaluate the two functions on concrete integers.
    They test the definitions apart from the proofs. *)

(** The function [zero_bytes] is a byte map whose every byte is 0. *)
Definition zero_bytes : byte_map := fun _ => 0.

(** A 64-bit write stores its least significant byte at the lowest
    address and its most significant byte seven addresses above. *)
Example write_is_little_endian :
  write_at S64 zero_bytes 100 1234605616436508552 100 = 136
  /\ write_at S64 zero_bytes 100 1234605616436508552 107 = 17
  /\ write_at S64 zero_bytes 100 1234605616436508552 108 = 0.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** A 32-bit read of a 64-bit write returns the low half of the
    written integer, and a 32-bit read four addresses above returns
    the high half. *)
Example read_halves :
  read_at S32 (write_at S64 zero_bytes 100 1234605616436508552) 100 = 1432778632
  /\ read_at S32 (write_at S64 zero_bytes 100 1234605616436508552) 104 = 287454020.
Proof. vm_compute. split; reflexivity. Qed.

(** A read uses only the low eight bits of each entry of the byte
    map. *)
Example read_reduces_bytes : read_at S16 (fun _ => 257) 0 = 257.
Proof. vm_compute. reflexivity. Qed.
