(** Hello records pointers into argv[0] for its program names. These
    offsets describe the base name and the special case for a program
    running from a libtool build directory. *)

From stdpp Require Import list.
From Stdlib Require Import ZArith List Lia.
From Glibc Require Import StrrchrLogic.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** The libtool build directory ends with these bytes. *)
Definition libs_bytes : list Z := [47; 46; 108; 105; 98; 115; 47].

(** Libtool prefixes the executable name with these three bytes. *)
Definition lt_bytes : list Z := [108; 116; 45].

(** The last byte c of bs counted from i, after acc, is acc's or one of
    bs's. *)
Lemma last_from_in c i bs acc t :
  last_from c i bs acc = Some t -> acc = Some t \/ ((i <= t)%nat /\ bs !! (t - i)%nat = Some c).
Proof.
  revert i acc. induction bs as [|x bs IH]; intros i acc H; cbn in H; [left; exact H|].
  destruct (IH _ _ H) as [E | [Hle Ht]].
  - destruct (Z.eqb_spec x c) as [<-|]; [|left; exact E]. injection E as <-. right.
    rewrite Nat.sub_diag. split; [lia | reflexivity].
  - right. split; [lia|]. replace (t - i)%nat with (S (t - S i)) by lia. exact Ht.
Qed.

(** The last `/` of a string and its NUL is one of the string's bytes. *)
Lemma last_slash s t : last_byte 47 (s ++ [0]) = Some t -> (t < length s)%nat.
Proof.
  unfold last_byte. intros H. destruct (last_from_in _ _ _ _ _ H) as [E | [_ Ht]]; [discriminate|].
  rewrite Nat.sub_0_r in Ht. destruct (Nat.lt_ge_cases t (length s)) as [Hlt|Hge]; [exact Hlt|].
  rewrite lookup_app_r in Ht; [|exact Hge]. destruct (t - length s)%nat; cbn in Ht; discriminate.
Qed.

(** The index of argv[0]'s base name: past its last `/`, or 0. *)
Definition base_idx (s : list Z) : nat :=
  match last_byte 47 (s ++ [0]) with Some t => S t | None => O end.

(** The seven bytes before the base name are "/.libs/". *)
Definition in_libs (s : list Z) : bool :=
  (7 <=? base_idx s)%nat && bool_decide (take 7 (drop (base_idx s - 7) s) = libs_bytes).

(** The base name starts with "lt-". *)
Definition lt_prefix (s : list Z) : bool := bool_decide (take 3 (drop (base_idx s) s) = lt_bytes).

(** The index of `program_invocation_short_name`: the base name, past
    "lt-" in a libtool build directory. *)
Definition short_idx (s : list Z) : nat :=
  if in_libs s && lt_prefix s then (base_idx s + 3)%nat else base_idx s.

(** The index of `program_name` and `program_invocation_name`: argv[0]
    itself, or the short name in a libtool build directory. *)
Definition name_idx (s : list Z) : nat := if in_libs s then short_idx s else O.

(** The base name lies within the string. *)
Lemma base_idx_le s : (base_idx s <= length s)%nat.
Proof.
  unfold base_idx. destruct (last_byte 47 (s ++ [0])) as [t|] eqn:E; [|lia].
  pose proof (last_slash s t E). lia.
Qed.

(** So does the short name. *)
Lemma short_idx_le s : (short_idx s <= length s)%nat.
Proof.
  unfold short_idx. destruct (in_libs s && lt_prefix s) eqn:E; [|apply base_idx_le].
  apply andb_true_iff in E as [_ E]. unfold lt_prefix in E. apply bool_decide_eq_true_1 in E.
  pose proof (f_equal length E) as L. rewrite length_take, length_drop in L. unfold lt_bytes in L. cbn [length] in L. lia.
Qed.

(** The name is at or before the short name. *)
Lemma name_idx_le s : (name_idx s <= short_idx s)%nat.
Proof. unfold name_idx. destruct (in_libs s); lia. Qed.
