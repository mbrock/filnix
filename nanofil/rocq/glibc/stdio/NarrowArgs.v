(** Narrow conversions read pointers or promoted integers from the variadic
    snapshot. This module describes those argument types and their scalar
    interpretation without assuming that output succeeds.

    A typed pointer is not evidence that its string can be read. The formatter's
    [[separation logic]] contract must also supply whole-word string ownership,
    snapshot ownership and the mutable cursor's [[capability]]. *)
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Values.
From Glibc Require Import NarrowFormat.
Import ListNotations.
Open Scope Z_scope.

(** Promoted int arguments use the model's canonical unsigned 32-bit representation. *)
Definition promoted_int (n : Z) : Prop := 0 <= n < 2 ^ 32.

(** Signed decimal conversion interprets the high bit as a negative sign. *)
Definition promoted_signed (n : Z) : Z :=
  if n <? 2 ^ 31 then n else n - 2 ^ 32.

(** Character conversion retains the low byte, including a possible output NUL. *)
Definition promoted_char (n : Z) : Z := n mod 256.

(** Each consuming directive requires precisely one pointer or promoted integer. *)
Inductive directive_arg : narrow_directive -> word -> Prop :=
| arg_string p : directive_arg FmtStr (WPtr p)
| arg_char n : promoted_int n -> directive_arg FmtChar (WInt n)
| arg_int n : promoted_int n -> directive_arg FmtInt (WInt n).

(** The relation describes the exact prefix consumed if all directives are processed. *)
Inductive narrow_args : list narrow_directive -> list word -> Prop :=
| args_end : narrow_args [] []
| args_literal c ds xs : literal_byte c = true -> narrow_args ds xs ->
    narrow_args (FmtLit c :: ds) xs
| args_percent ds xs : narrow_args ds xs -> narrow_args (FmtPercent :: ds) xs
| args_conversion d x ds xs : directive_arg d x -> narrow_args ds xs ->
    narrow_args (d :: ds) (x :: xs).

(** The argument relation cannot admit malformed literal bytes or unsupported directives. *)
Lemma narrow_args_valid ds xs : narrow_args ds xs -> Forall directive_valid ds.
Proof.
  intros H. induction H.
  - constructor.
  - constructor; [exact H|exact IHnarrow_args].
  - constructor; [exact I|exact IHnarrow_args].
  - destruct H; constructor; try exact I; exact IHnarrow_args.
Qed.

(** Counting argument slots agrees with the grammar, including non-consuming percent escapes. *)
Lemma narrow_args_length ds xs : narrow_args ds xs -> length xs = format_arity ds.
Proof.
  intros H. induction H.
  - reflexivity.
  - exact IHnarrow_args.
  - exact IHnarrow_args.
  - destruct H; change (S (length xs) = S (format_arity ds)); now rewrite IHnarrow_args.
Qed.

(** Concatenated format fragments consume their argument lists in the same order. *)
Lemma narrow_args_app ds xs es ys :
  narrow_args ds xs -> narrow_args es ys -> narrow_args (ds ++ es) (xs ++ ys).
Proof.
  intros H K. induction H; cbn; [exact K| | |].
  - constructor; [assumption|exact IHnarrow_args].
  - constructor. exact IHnarrow_args.
  - econstructor; [exact H|exact IHnarrow_args].
Qed.

(** Early output failure may leave a suffix of the arguments unconsumed. The
    consumed prefix must still correspond to a prefix of complete directives. *)
Definition narrow_progress (ds : list narrow_directive) (xs rest : list word) : Prop :=
  exists done pending used,
    ds = done ++ pending /\ xs = used ++ rest /\ narrow_args done used.

(** A formatter may fail before reading any variadic argument. *)
Lemma narrow_progress_start ds xs : narrow_progress ds xs xs.
Proof.
  exists [], ds, []. split; [reflexivity|]. split; [reflexivity|constructor].
Qed.

(** Processing a supported format leaves any extra caller arguments untouched. *)
Lemma narrow_progress_done ds xs rest : narrow_args ds xs ->
  narrow_progress ds (xs ++ rest) rest.
Proof.
  intros H. exists ds, [], xs. rewrite app_nil_r. auto.
Qed.

(** The signed interpretation stays within the C int range for canonical words. *)
Lemma promoted_signed_range n : promoted_int n ->
  - (2 ^ 31) <= promoted_signed n < 2 ^ 31.
Proof.
  unfold promoted_int, promoted_signed. destruct (n <? 2 ^ 31) eqn:Hn;
    [apply Z.ltb_lt in Hn|apply Z.ltb_ge in Hn]; cbn in *; lia.
Qed.

(** A promoted character always produces one byte, even for a negative signed int. *)
Lemma promoted_char_range n : 0 <= promoted_char n < 256.
Proof. apply Z.mod_pos_bound. lia. Qed.

(** The boundary computations distinguish sign interpretation from low-byte conversion. *)
Example promoted_boundaries :
  promoted_signed 2147483647 = 2147483647 /\
  promoted_signed 2147483648 = -2147483648 /\
  promoted_signed 4294967295 = -1 /\
  promoted_char 4294967295 = 255 /\ promoted_char 256 = 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
