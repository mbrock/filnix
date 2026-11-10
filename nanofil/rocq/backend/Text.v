(** Text as the backend builds it: a list of parts, each a string,
    which the driver writes one after another. A printer takes the
    parts that follow it and puts its own in front, as asm.pl's
    grammar rules do with their difference lists, so no text is ever
    copied to be joined: SQLite's assembly is about 100 MB. *)

From Stdlib Require Import String ZArith List Ascii.
Import ListNotations.
Local Open Scope string_scope.

(** The parts of a text, in order. A printer of some X has the type
    [X -> parts -> parts]: the parts of its text, then those given. *)
Definition parts := list string.

(** The newline and tab characters, which Rocq's string notation
    cannot write. *)
Definition nl : string := String "010"%char EmptyString.
Definition tab : string := String "009"%char EmptyString.

(** The digits 0 to 9. A definition of its own, like [ten] below,
    because the extracted code builds a list or a number again each
    time it meets one written inside a function. *)
Definition digit_texts : list string :=
  ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"].

(** The digit [d], for 0 to 9. *)
Definition digit (d : nat) : string := nth d digit_texts "?".

Local Open Scope Z_scope.

Definition ten : Z := 10.

(** The digits of [n], which is not negative, in front of [acc]. The
    fuel is a bound on the number of digits. *)
Fixpoint digits (fuel : nat) (n : Z) (acc : string) : string :=
  match fuel with
  | O => acc
  | S fuel' =>
      let (q, r) := Z.div_eucl n ten in
      let acc' := (digit (Z.to_nat r) ++ acc)%string in
      if q =? 0 then acc' else digits fuel' q acc'
  end.

(** Numbers below this have at most 18 decimal digits. *)
Definition eighteen_digits : Z := 10 ^ 18.

(** A bound on the number of decimal digits of [n]: 18 for the
    numbers below 10^18, which are nearly all a compile prints, and
    the number of binary digits for the others. *)
Definition digits_fuel (n : Z) : nat :=
  if n <? eighteen_digits then 18%nat
  else match n with
       | Zpos p => Pos.size_nat p
       | _ => 1%nat
       end.

(** [n] in decimal, with a minus sign when it is negative, as Prolog
    writes an integer. *)
Definition decimal (n : Z) : string :=
  if n <? 0 then ("-" ++ digits (digits_fuel (- n)) (- n) "")%string
  else digits (digits_fuel n) n "".

Example decimal_0 : decimal 0 = "0"%string.
Proof. reflexivity. Qed.
Example decimal_neg : decimal (-1080) = "-1080"%string.
Proof. reflexivity. Qed.
Example decimal_big : decimal 18446744073709551615 = "18446744073709551615"%string.
Proof. reflexivity. Qed.
