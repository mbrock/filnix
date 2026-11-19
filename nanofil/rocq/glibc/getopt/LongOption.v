(** A long option names the string the parser matches, the argument it
    accepts and the value it returns. Callers use these properties to
    check an option table before reasoning about a call. *)

From stdpp Require Import list.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Values Pieces.
From Glibc Require Import ByteRead.
Import ListNotations.
Open Scope Z_scope.

(** An entry of the table names its option by the pointer lo_name to
    the bytes lo_str. It also records whether the option takes an
    argument, the flag pointer and the value. *)
Record lopt := mkLopt { lo_name : ptr; lo_str : list Z; lo_has : Z; lo_flag : ptr; lo_val : Z }.

(** A leading minus or plus sign selects an ordering and is skipped. *)
Definition opt_skip (os : list Z) : nat :=
  if (sbyte os 0 =? 45) || (sbyte os 0 =? 43) then 1%nat else 0%nat.

(** A leading minus sign is skipped. *)
Lemma opt_skip_minus os : sbyte os 0 = 45 -> opt_skip os = 1%nat.
Proof. unfold opt_skip. intros ->. reflexivity. Qed.

(** A leading plus sign is skipped. *)
Lemma opt_skip_plus os : sbyte os 0 = 43 -> opt_skip os = 1%nat.
Proof. unfold opt_skip. intros ->. reflexivity. Qed.

(** Any other first character remains part of the option list. *)
Lemma opt_skip_other os : sbyte os 0 <> 45 -> sbyte os 0 <> 43 -> opt_skip os = 0%nat.
Proof.
  unfold opt_skip. intros H1 H2. rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2). reflexivity.
Qed.

(** No entry of the table answers -1 through its value. *)
Definition no_neg1_val (os : list lopt) : Prop :=
  Forall (fun y => lo_flag y <> null \/ (lo_val y mod 2 ^ 32 <> 4294967295)%Z) os.

(** ## Codes that carry a string

    Some return values always come with an argument. A value c is such
    a code when three facts hold. No error, fallback or nonoption return
    uses c. Every letter of the option string with code c is followed by
    exactly one colon. Every table entry with value c and no flag has
    the argument kind 1. The definition below states these facts about
    the option string so and the table los. *)

(** The code c of a getopt return always comes with a readable argument. *)
Definition str_code (so : list Z) (los : list lopt) (c : Z) : Prop :=
  c <> 4294967295 /\ c <> 63 /\ c <> 58 /\ c <> 0 /\ c <> 1 /\
  (forall k, (k < List.length so)%nat -> sbyte so k <> 58 -> sbyte so k <> 59 -> chr_w (sbyte so k) = c ->
     sbyte so (S k) = 58 /\ sbyte so (S (S k)) <> 58) /\
  (forall y, y ∈ los -> lo_flag y = null -> lo_val y mod 2 ^ 32 = c -> lo_has y = 1).
