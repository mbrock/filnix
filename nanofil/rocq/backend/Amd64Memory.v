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
Admitted.

(** A read of n bytes returns an unsigned integer of n bytes. *)
Lemma read_bytes_range (n : nat) (b : byte_map) (a : Z) :
  0 <= read_bytes n b a < 2 ^ (8 * Z.of_nat n).
Proof.
Admitted.

(** A read at a size returns a valid pattern of that size. *)
Lemma read_at_range (z : size) (b : byte_map) (a : Z) :
  0 <= read_at z b a < size_modulus z.
Proof.
Admitted.

(** Two byte maps that agree on the n addresses from a upward give the
    same read there. *)
Lemma read_bytes_agree (n : nat) (b b' : byte_map) (a : Z) :
  (forall i, 0 <= i < Z.of_nat n -> b (a + i) = b' (a + i)) ->
  read_bytes n b a = read_bytes n b' a.
Proof.
Admitted.

(** Two byte maps that agree on the bytes of an access give the same
    read at its size. *)
Lemma read_at_agree (z : size) (b b' : byte_map) (a : Z) :
  (forall i, 0 <= i < Z.of_nat (size_bytes z) -> b (a + i) = b' (a + i)) ->
  read_at z b a = read_at z b' a.
Proof.
Admitted.

(** The first n bytes of a longer read are its low part. *)
Lemma read_bytes_prefix (n n' : nat) (b : byte_map) (a : Z) :
  (n <= n')%nat ->
  read_bytes n b a = read_bytes n' b a mod 2 ^ (8 * Z.of_nat n).
Proof.
Admitted.

(** A read at a narrow size returns the low part of a read at a wider
    size from the same address. *)
Lemma read_at_narrower (z z' : size) (b : byte_map) (a : Z) :
  size_bits z <= size_bits z' ->
  read_at z b a = wrap z (read_at z' b a).
Proof.
Admitted.

(** ## Facts about writes

    A write changes exactly the bytes that it covers. A read of the
    same size at the same address returns what was written, and a read
    that does not overlap the write returns what it returned before. *)

(** A write leaves the byte at every address outside its range
    unchanged. *)
Lemma write_bytes_outside (n : Z) (b : byte_map) (a v a' : Z) :
  a' < a \/ a + n <= a' -> write_bytes n b a v a' = b a'.
Proof.
Admitted.

(** A write stores the byte of v that has the index i at the address
    a + i. *)
Lemma write_bytes_inside (n : Z) (b : byte_map) (a v i : Z) :
  0 <= i < n -> write_bytes n b a v (a + i) = byte_of v i.
Proof.
Admitted.

(** A read of the n bytes that a write of n bytes stored returns the
    low n bytes of the written integer. *)
Lemma read_write_bytes_same (n : nat) (b : byte_map) (a v : Z) :
  read_bytes n (write_bytes (Z.of_nat n) b a v) a = v mod 2 ^ (8 * Z.of_nat n).
Proof.
Admitted.

(** A read after a write of the same size at the same address returns
    the pattern of the written integer at that size. *)
Lemma read_write_at_same (z : size) (b : byte_map) (a v : Z) :
  read_at z (write_at z b a v) a = wrap z v.
Proof.
Admitted.

(** A read whose bytes lie entirely below or entirely above the bytes
    of a write returns what it returned before the write. The two
    accesses may have different sizes. *)
Lemma read_write_at_apart (z z' : size) (b : byte_map) (a a' v : Z) :
  a' + Z.of_nat (size_bytes z') <= a \/ a + Z.of_nat (size_bytes z) <= a' ->
  read_at z' (write_at z b a v) a' = read_at z' b a'.
Proof.
Admitted.

(** A write of an integer and a write of its pattern at the same size
    store the same bytes. *)
Lemma write_at_wrap (z : size) (b : byte_map) (a v a' : Z) :
  write_at z b a (wrap z v) a' = write_at z b a v a'.
Proof.
Admitted.

(** ## Facts about mapped ranges

    The function [all_mapped] is a computation, and a proof needs it
    as a statement about each address of the range. *)

(** Every one of the n addresses from a upward satisfies p exactly
    when [all_mapped] returns true. *)
Lemma all_mapped_spec (n : nat) (p : Z -> bool) (a : Z) :
  all_mapped n p a = true <-> (forall i, 0 <= i < Z.of_nat n -> p (a + i) = true).
Proof.
Admitted.

(** A range that is mapped contains only mapped prefixes. *)
Lemma all_mapped_prefix (n n' : nat) (p : Z -> bool) (a : Z) :
  (n <= n')%nat -> all_mapped n' p a = true -> all_mapped n p a = true.
Proof.
Admitted.

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
Admitted.

(** A machine write to the IR's bytes stores what the IR's
    `store_bytes` stores, at every address. *)
Lemma write_at_store_bytes (z : size) (m : mem) (a v a' : Z) :
  write_at z (m_bytes m) a v a'
  = m_bytes (store_bytes m a (Z.of_nat (size_bytes z)) v) a'.
Proof.
Admitted.

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
