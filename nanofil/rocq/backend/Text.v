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

(** The digit [d], for 0 to 9. *)
Definition digit (d : nat) : string :=
  nth d ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"] "?".

Local Open Scope Z_scope.

(** The digits of [n], which is not negative, in front of [acc]. The
    fuel is a bound on the number of digits. *)
Fixpoint digits (fuel : nat) (n : Z) (acc : string) : string :=
  match fuel with
  | O => acc
  | S fuel' =>
      let acc' := (digit (Z.to_nat (n mod 10)) ++ acc)%string in
      if n <? 10 then acc' else digits fuel' (n / 10) acc'
  end.

(** The number of binary digits of [n] bounds its decimal ones. *)
Definition digits_fuel (n : Z) : nat :=
  match n with
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
