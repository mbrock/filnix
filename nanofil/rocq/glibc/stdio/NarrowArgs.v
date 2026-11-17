(** The narrow formatter of glibc takes its arguments from a variadic
    call. A `%s` conversion reads a pointer, and a `%c` or `%d`
    conversion reads an int that C has promoted to a full word. This
    module says which argument each conversion needs and how the
    formatter reads an integer argument. It makes no claim that the
    output succeeds.

    A pointer of the right type does not make a `%s` safe by itself,
    because the formatter also reads the string that the pointer points
    to. The formatter's [[separation logic]] contract therefore asks
    for more than this module states. It asks for ownership of the
    string, of the copied arguments and of the cursor that walks
    them. *)
From Glibc Require Import GlibcTactics.
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

(** A call is safe only when it passes what its format asks for. The
    formatter reads one argument for each conversion, so a missing
    argument or an integer in the place of a string makes it read
    memory that the caller never lent. The relation [narrow_fits] says
    that the arguments xs start with the arguments that the directives
    consume, and that rest holds the arguments left over. A contract
    for the formatter asks this of its caller. The relation
    [narrow_progress] above is too weak for that purpose, because it
    holds for every list of arguments when rest is the whole list. *)
Definition narrow_fits (ds : list narrow_directive) (xs rest : list word) : Prop :=
  exists used, xs = used ++ rest /\ narrow_args ds used.

(** A caller often passes exactly the arguments that the directives
    consume. Those arguments fit the format, and no argument is left
    over. *)
Lemma narrow_fits_all ds xs : narrow_args ds xs -> narrow_fits ds xs [].
Proof. intros H. exists xs. rewrite app_nil_r. auto. Qed.

(** Arguments that fit a format are one of the cases that
    [narrow_progress] allows. *)
Lemma narrow_fits_progress ds xs rest : narrow_fits ds xs rest -> narrow_progress ds xs rest.
Proof. intros (used & Hxs & Hargs). exists ds, [], used. rewrite app_nil_r. auto. Qed.

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
