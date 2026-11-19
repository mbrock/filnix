(** The conversion `%d` of the formatter turns a number into text
    with the function `c: _itoa_word`. The function writes the digits
    of the number backwards, from the end of a buffer towards its
    start, and it returns a pointer to the first digit. The formatter
    passes the end of a work buffer of 1000 bytes, and it then appends
    the digits to its output.

    This module states the contract of `c: _itoa_word` for the base
    ten, which is the base that `%d` uses. The contract says where the
    digits are after the call and which digits they are, so that the
    proof of the formatter's loop can append them. The module does not
    prove the contract. A proof over the compiled function is the work
    of another module. *)

From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv PrintfSpec.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

(** ## The digits of a number *)

(** The C function is a loop. Each round writes the character of the
    last digit of the number in front of the digits that it has
    written, and it divides the number by ten. The loop ends when the
    number is zero, so the number zero gets the one digit `0`. The
    function [dec_digits_from] is this loop: the list acc holds the
    characters written so far, and fuel bounds the rounds. *)
Fixpoint dec_digits_from (fuel : nat) (v : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S fuel' =>
      let acc' := (48 + v mod 10) :: acc in
      if v / 10 =? 0 then acc' else dec_digits_from fuel' (v / 10) acc'
  end.

(** A number below 2^64 has at most 20 decimal digits, so 20 rounds
    are enough for every argument of the C function. *)
Definition dec_digits (v : Z) : list Z := dec_digits_from 20 v [].

(** The numbers zero and 2026 and the largest 64-bit number have the
    digits that a reader expects. *)
Example dec_digits_examples :
  dec_digits 0 = [48] /\ dec_digits 2026 = [50; 48; 50; 54] /\
  dec_digits (2 ^ 64 - 1) = [49; 56; 52; 52; 54; 55; 52; 52; 48; 55; 51; 55; 48; 57; 53; 53; 49; 54; 49; 53].
Proof. vm_compute. split_and!; reflexivity. Qed.

(** The loop writes at least one character, and it writes at most one
    in each round. *)
Lemma dec_digits_from_length fuel v acc :
  (length acc <= length (dec_digits_from fuel v acc) <= fuel + length acc)%nat.
Proof.
  revert v acc. induction fuel as [|fuel IH]; intros v acc; cbn [dec_digits_from]; [lia|].
  destruct (v / 10 =? 0); [cbn [length]; lia|]. specialize (IH (v / 10) ((48 + v mod 10) :: acc)).
  cbn [length] in IH. lia.
Qed.

(** A loop that runs at least one round writes at least one
    character. *)
Lemma dec_digits_from_grows fuel v acc :
  (0 < fuel)%nat -> (S (length acc) <= length (dec_digits_from fuel v acc))%nat.
Proof.
  destruct fuel as [|fuel]; [lia|]. intros _. cbn [dec_digits_from]. destruct (v / 10 =? 0); [cbn [length]; lia|].
  pose proof (dec_digits_from_length fuel (v / 10) ((48 + v mod 10) :: acc)) as H. cbn [length] in H. lia.
Qed.

(** A number has between one and 20 digits. The formatter uses the
    upper bound to show that the digits fit in its work buffer. *)
Lemma dec_digits_length v : (1 <= length (dec_digits v) <= 20)%nat.
Proof.
  unfold dec_digits. pose proof (dec_digits_from_length 20 v []) as Hle.
  pose proof (dec_digits_from_grows 20 v [] ltac:(lia)) as Hge. cbn [length] in *. lia.
Qed.

(** Every character that the loop writes is one of the ten digits. *)
Lemma dec_digits_from_range fuel v acc :
  Forall (fun x => 48 <= x <= 57) acc -> Forall (fun x => 48 <= x <= 57) (dec_digits_from fuel v acc).
Proof.
  revert v acc. induction fuel as [|fuel IH]; intros v acc Hacc; cbn [dec_digits_from]; [exact Hacc|].
  assert (Hd : Forall (fun x => 48 <= x <= 57) ((48 + v mod 10) :: acc)).
  { constructor; [|exact Hacc]. pose proof (Z.mod_pos_bound v 10 ltac:(lia)). lia. }
  destruct (v / 10 =? 0); [exact Hd | exact (IH _ _ Hd)].
Qed.

(** The digits of a number are characters from `0` to `9`. *)
Lemma dec_digits_range v : Forall (fun x => 48 <= x <= 57) (dec_digits v).
Proof. apply dec_digits_from_range. constructor. Qed.

Section spec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** ## The contract *)

(** `c: _itoa_word (value, buflim, 10, 0)` writes the decimal digits
    of the number v below the address buflim, and it returns a pointer
    to the first of them. The last argument 0 asks for lower-case
    letters, which a decimal number does not have.

    The pointer buflim points hi bytes into the object b. The caller
    lends the lifetime of that object and the 20 bytes below buflim,
    which hold the bytes old. The function writes n digits, where n is
    the number of digits of v. After the call the first 20 − n of
    those bytes are as they were, and the last n hold the digits.

    The function reads the character of each digit from the table of
    lower-case digits, so the contract asks that anyone may read that
    table. *)
Definition itoa_word_spec : fspec Σ :=
  FSpec (Z * Z * region * Z * list Z)
    (fun '(v, b, _, hi, _) => [WInt v; WPtr (mkPtr (b + hi) (Obj b)); WInt 10; WInt 0])
    (fun '(v, b, reg, hi, old) =>
       ⌜0 <= v < 2 ^ 64 /\ 0 < b /\ 20 <= hi /\ b + hi <= r_end reg /\ r_end reg <= 2 ^ 48 /\ length old = 20%nat⌝ ∗
       live b reg ∗ bytes b (hi - 20) old ∗ ro_table lower_digits)%I
    (fun '(v, b, reg, hi, old) o =>
       ⌜o = Ret (WPtr (mkPtr (b + hi - Z.of_nat (length (dec_digits v))) (Obj b)))⌝ ∗
       live b reg ∗ bytes b (hi - 20) (take (20 - length (dec_digits v)) old ++ dec_digits v))%I.

End spec.
