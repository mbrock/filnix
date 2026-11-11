(** The value of each gate program as bytes (`list Byte.byte`), which
    both the arena's driver (driver.c) and the OCaml reference
    (ref_main.ml) write out: the comparison is of those bytes. A byte
    is one of Byte.byte's 256 constructors without arguments, so in
    the arena it is the immediate `(b << 1) | 1`. *)

From Stdlib Require Import List ZArith String Ascii.
From Stdlib Require Import Strings.Byte.
Import ListNotations.

Definition out := list Byte.byte.

(** The bytes of the string s. *)
Fixpoint of_string (s : string) : out :=
  match s with
  | EmptyString => []
  | String c s' => Ascii.byte_of_ascii c :: of_string s'
  end.

(** The digit d, 0 to 9. *)
Definition digit (d : Z) : Byte.byte :=
  nth (Z.to_nat d) [x30; x31; x32; x33; x34; x35; x36; x37; x38; x39] x3f.

(** The digits of n, which is not negative, in front of acc. *)
Fixpoint z_digits (fuel : nat) (n : Z) (acc : out) : out :=
  match fuel with
  | O => acc
  | S f =>
      let (q, r) := Z.div_eucl n 10 in
      if Z.eqb q 0 then digit r :: acc else z_digits f q (digit r :: acc)
  end.

(** z in decimal. *)
Definition show_Z (z : Z) : out :=
  if Z.ltb z 0 then x2d :: z_digits 80 (Z.opp z) [] else z_digits 80 z [].

Definition show_nat (n : nat) : out := show_Z (Z.of_nat n).

Definition show_bool (b : bool) : out :=
  if b then of_string "true"%string else of_string "false"%string.

(** The elements of l, each by f, separated by `;` in brackets. *)
Definition show_list {A : Type} (f : A -> out) (l : list A) : out :=
  x5b :: (fix go (l : list A) (first : bool) : out :=
            match l with
            | [] => [x5d]
            | x :: l' => (if first then [] else [x3b]) ++ f x ++ go l' false
            end) l true.

Definition show_pair {A B : Type} (f : A -> out) (g : B -> out) (p : A * B) : out :=
  x28 :: f (fst p) ++ x2c :: g (snd p) ++ [x29].
