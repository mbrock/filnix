(** Narrow formatting needs an explicit description of the directives it may
    execute. This grammar admits literal bytes, strings, characters, signed
    integers and escaped percent signs. It excludes every other conversion.

    The parser consumes the bytes before the terminating NUL. Its result
    describes syntax, not successful output or a proof of glibc's formatter.
    Callers must separately own the format string and its terminator. *)
From Glibc Require Import GlibcTactics.
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Open Scope Z_scope.

(** Each directive describes one literal byte or one supported conversion. *)
Inductive narrow_directive : Type :=
| FmtLit (c : Z)
| FmtStr
| FmtChar
| FmtInt
| FmtPercent.

(** Literal bytes exclude NUL and percent, which have separate parsing roles. *)
Definition literal_byte (c : Z) : bool :=
  (0 <? c) && (c <? 256) && negb (c =? 37).

(** Only literal constructors need a byte-range condition. *)
Definition directive_valid (d : narrow_directive) : Prop :=
  match d with FmtLit c => literal_byte c = true | _ => True end.

(** A conversion letter determines its directive without consulting arguments. *)
Definition conversion (c : Z) : option narrow_directive :=
  if c =? 115 then Some FmtStr else
  if c =? 99 then Some FmtChar else
  if c =? 100 then Some FmtInt else
  if c =? 37 then Some FmtPercent else None.

(** The spelling records the exact format bytes represented by each directive. *)
Definition directive_bytes (d : narrow_directive) : list Z :=
  match d with
  | FmtLit c => [c]
  | FmtStr => [37; 115]
  | FmtChar => [37; 99]
  | FmtInt => [37; 100]
  | FmtPercent => [37; 37]
  end.

(** Concatenating directive spellings recovers the format without its terminator. *)
Definition format_bytes (ds : list narrow_directive) : list Z :=
  flat_map directive_bytes ds.

(** Parsing rejects unsupported conversions, embedded NULs and incomplete percent escapes. *)
Fixpoint parse_narrow (bs : list Z) : option (list narrow_directive) :=
  match bs with
  | [] => Some []
  | c :: rest =>
      if c =? 37 then
        match rest with
        | [] => None
        | letter :: tail =>
            match conversion letter, parse_narrow tail with
            | Some d, Some ds => Some (d :: ds)
            | _, _ => None
            end
        end
      else if literal_byte c then
        option_map (cons (FmtLit c)) (parse_narrow rest)
      else None
  end.

(** Every accepted conversion has its stated spelling and satisfies the grammar. *)
Lemma conversion_sound c d : conversion c = Some d ->
  directive_bytes d = [37; c] /\ directive_valid d.
Proof.
  unfold conversion.
  destruct (c =? 115) eqn:H1; [apply Z.eqb_eq in H1; subst c|];
    [intros H; inversion H; subst; split; reflexivity|].
  destruct (c =? 99) eqn:H2; [apply Z.eqb_eq in H2; subst c|];
    [intros H; inversion H; subst; split; reflexivity|].
  destruct (c =? 100) eqn:H3; [apply Z.eqb_eq in H3; subst c|];
    [intros H; inversion H; subst; split; reflexivity|].
  destruct (c =? 37) eqn:H4; [apply Z.eqb_eq in H4; subst c|].
  - intros H; inversion H; subst; split; reflexivity.
  - discriminate.
Qed.

(** A successful parse accounts for every input byte and admits only valid directives. *)
Lemma parse_narrow_sound : forall bs ds, parse_narrow bs = Some ds ->
  format_bytes ds = bs /\ Forall directive_valid ds.
Proof.
  fix IH 1. intros bs ds. destruct bs as [|c rest].
  - cbn. intros H; inversion H; subst. split; [reflexivity|constructor].
  - cbn [parse_narrow]. destruct (c =? 37) eqn:Hc.
    + apply Z.eqb_eq in Hc; subst c. destruct rest as [|letter tail]; [discriminate|].
      destruct (conversion letter) as [d|] eqn:Hd; [|discriminate].
      destruct (parse_narrow tail) as [ts|] eqn:Ht; [|discriminate].
      intros H; inversion H; subst ds.
      destruct (IH tail ts Ht) as [Hb Hv].
      destruct (conversion_sound letter d Hd) as [Hdb Hdv].
      split.
      * change (directive_bytes d ++ format_bytes ts = 37 :: letter :: tail).
        rewrite Hdb, Hb. reflexivity.
      * constructor; assumption.
    + destruct (literal_byte c) eqn:Hl; [|discriminate].
      destruct (parse_narrow rest) as [ts|] eqn:Ht; [|discriminate].
      intros H; inversion H; subst ds.
      destruct (IH rest ts Ht) as [Hb Hv]. split.
      * change (c :: format_bytes ts = c :: rest). now rewrite Hb.
      * constructor; assumption.
Qed.

(** Every valid directive sequence parses back from its spelling. *)
Lemma parse_narrow_complete ds : Forall directive_valid ds ->
  parse_narrow (format_bytes ds) = Some ds.
Proof.
  intros H. induction H as [|d ds Hd Hds IH]; [reflexivity|].
  change (parse_narrow (flat_map directive_bytes ds) = Some ds) in IH.
  destruct d; cbn [format_bytes flat_map directive_bytes] in *.
  - unfold directive_valid in Hd.
    assert (Hne : (c =? 37) = false).
    { unfold literal_byte in Hd. apply andb_true_iff in Hd as [_ Hne].
      now apply negb_true_iff in Hne. }
    change ((if c =? 37 then
      match flat_map directive_bytes ds with
      | [] => None
      | letter :: tail => match conversion letter, parse_narrow tail with
        | Some d, Some ts => Some (d :: ts) | _, _ => None end
      end else if literal_byte c then
        option_map (cons (FmtLit c)) (parse_narrow (flat_map directive_bytes ds))
      else None) = Some (FmtLit c :: ds)).
    rewrite Hne, Hd, IH. reflexivity.
  - change (option_map (cons FmtStr) (parse_narrow (flat_map directive_bytes ds)) = Some (FmtStr :: ds)).
    now rewrite IH.
  - change (option_map (cons FmtChar) (parse_narrow (flat_map directive_bytes ds)) = Some (FmtChar :: ds)).
    now rewrite IH.
  - change (option_map (cons FmtInt) (parse_narrow (flat_map directive_bytes ds)) = Some (FmtInt :: ds)).
    now rewrite IH.
  - change (option_map (cons FmtPercent) (parse_narrow (flat_map directive_bytes ds)) = Some (FmtPercent :: ds)).
    now rewrite IH.
Qed.

(** Literal characters and escaped percent signs consume no variadic argument. *)
Definition directive_arity (d : narrow_directive) : nat :=
  match d with FmtLit _ | FmtPercent => 0%nat | _ => 1%nat end.

(** The syntax fixes the argument count independently of stream success. *)
Definition format_arity (ds : list narrow_directive) : nat :=
  fold_right (fun d n => (directive_arity d + n)%nat) 0%nat ds.

(** These computations exercise all directives in an asymmetric sequence. *)
Example parse_narrow_mixed :
  parse_narrow [65; 37; 115; 58; 37; 100; 37; 99; 37; 37] =
  Some [FmtLit 65; FmtStr; FmtLit 58; FmtInt; FmtChar; FmtPercent].
Proof. vm_compute. reflexivity. Qed.

(** The grammar rejects width, precision, length, positional and unsupported conversions. *)
Example parse_narrow_rejections :
  map parse_narrow [[37]; [37; 110]; [37; 102]; [37; 117];
    [37; 50; 115]; [37; 46; 115]; [37; 108; 115]; [37; 49; 36; 115];
    [0]; [256]; [-1]; [65; 0; 66]] = repeat None 12.
Proof. vm_compute. reflexivity. Qed.
