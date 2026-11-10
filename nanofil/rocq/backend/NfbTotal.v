(** NFB's Gallina reader is total and its fuel never runs out
    (docs/nfb.md, Relation to the term form and the Rocq model).

    Every function of NfbTerm.v is a Gallina function, so [decode]
    returns on every list of words, a module or none. Where a reader
    recurses on more than the structure of its input it takes fuel,
    and each call site gives it the length of the words it reads.
    This file proves that length is enough: with any more fuel each
    reader gives the same answer, so no input is refused for want of
    fuel ([sections_fuel], [group_fuel], [blocks_fuel], [rest_fuel],
    [side_term_fuel], [name_recs_fuel]). Each holds because every
    round of the reader takes at least one word. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Cfg.
From Backend Require Import NfbTerm Nfb.
Import ListNotations.

(** Whether fuel f and every larger fuel give the reader the same
    answer. *)
Definition enough {X : Type} (run : nat -> option X) (f : nat) : Prop :=
  forall f', (f <= f')%nat -> run f' = run f.

(** A reader whose answer is the same for the next fuel, from fuel f
    on, has enough fuel f. *)
Lemma enough_step : forall {X : Type} (run : nat -> option X) f,
  (forall g, (f <= g)%nat -> run (S g) = run g) -> enough run f.
Proof.
  intros X run f H f' Hf. induction Hf as [|g Hg IH]; [reflexivity|].
  rewrite H by lia. exact IH.
Qed.

(** ## Taking words *)

(** [take] n leaves n fewer words. *)
Lemma take_length : forall n xs a b, take n xs = Some (a, b) -> (length b + n = length xs)%nat.
Proof.
  induction n as [|n IH]; intros xs a b H; simpl in H.
  - injection H as <- <-. lia.
  - destruct xs as [|x xs]; [discriminate|].
    destruct (take n xs) as [[a' b']|] eqn:E; [|discriminate].
    injection H as <- <-. apply IH in E. simpl. lia.
Qed.

(** Reading n of what a reader reads, where the reader never leaves
    more words than it was given, leaves no more. *)
Lemma read_n_length : forall {X : Type} (r : reader X) n ws v rest,
  (forall ws v rest, r ws = Some (v, rest) -> (length rest <= length ws)%nat) ->
  read_n n r ws = Some (v, rest) -> (length rest <= length ws)%nat.
Proof.
  intros X r n. induction n as [|n IH]; intros ws v rest Hr H; simpl in H.
  - injection H as _ <-. lia.
  - destruct (r ws) as [[a ws1]|] eqn:E1; [|discriminate]. simpl in H.
    destruct (read_n n r ws1) as [[b ws2]|] eqn:E2; [|discriminate]. simpl in H.
    injection H as _ <-. apply Hr in E1. apply IH in E2; [lia | exact Hr].
Qed.

(** As [read_n_length], for a counted list, which also takes its count. *)
Lemma read_counted_length : forall {X : Type} (r : reader X) ws v rest,
  (forall ws v rest, r ws = Some (v, rest) -> (length rest <= length ws)%nat) ->
  read_counted r ws = Some (v, rest) -> (length rest < length ws)%nat.
Proof.
  intros X r ws v rest Hr H. unfold read_counted in H.
  destruct ws as [|n ws']; [discriminate|].
  destruct (Z.of_nat (length ws') <? n); [discriminate|].
  apply read_n_length in H; [simpl; lia | exact Hr].
Qed.

(** Two readers that agree on every list of at most L words, the
    first never leaving more words than it was given, read the same n
    of them from at most L words. *)
Lemma read_n_ext : forall {X : Type} (r1 r2 : reader X) L n ws,
  (forall ws, (length ws <= L)%nat -> r1 ws = r2 ws) ->
  (forall ws v rest, r1 ws = Some (v, rest) -> (length rest <= length ws)%nat) ->
  (length ws <= L)%nat -> read_n n r1 ws = read_n n r2 ws.
Proof.
  intros X r1 r2 L n. induction n as [|n IH]; intros ws Hext Hr Hws; simpl; [reflexivity|].
  rewrite <- (Hext ws Hws).
  destruct (r1 ws) as [[a ws1]|] eqn:E1; simpl; [|reflexivity].
  rewrite IH; [reflexivity | exact Hext | exact Hr |].
  apply Hr in E1. lia.
Qed.

(** As [read_n_ext], for a counted list. *)
Lemma read_counted_ext : forall {X : Type} (r1 r2 : reader X) L ws,
  (forall ws, (length ws <= L)%nat -> r1 ws = r2 ws) ->
  (forall ws v rest, r1 ws = Some (v, rest) -> (length rest <= length ws)%nat) ->
  (length ws <= L)%nat -> read_counted r1 ws = read_counted r2 ws.
Proof.
  intros X r1 r2 L ws Hext Hr Hws. unfold read_counted.
  destruct ws as [|n ws']; [reflexivity|].
  destruct (Z.of_nat (length ws') <? n); [reflexivity|].
  apply (read_n_ext r1 r2 L); auto. simpl in Hws. lia.
Qed.

(** ## Sections *)

(** Splitting the words into sections, with fuel their length. *)
Lemma sections_fuel : forall ws, enough (fun f => read_sections f ws) (length ws).
Proof.
  intros ws. apply enough_step. intros g Hg. revert ws Hg.
  induction g as [|g IH]; intros ws Hg.
  - destruct ws as [|a [|b ws]]; simpl in *; try reflexivity; lia.
  - destruct ws as [|a [|b ws]]; try reflexivity.
    change (read_sections (S (S g)) (a :: b :: ws))
      with (let* p := take (Z.to_nat b) ws in
            let* rest := read_sections (S g) (snd p) in Some ((a, fst p) :: rest)).
    change (read_sections (S g) (a :: b :: ws))
      with (let* p := take (Z.to_nat b) ws in
            let* rest := read_sections g (snd p) in Some ((a, fst p) :: rest)).
    destruct (take (Z.to_nat b) ws) as [[c rest]|] eqn:E; [|reflexivity]. cbn [fst snd].
    apply take_length in E. simpl in Hg. rewrite IH by lia. reflexivity.
Qed.

(** ## Side sections *)

(** Case on every match in the hypotheses, dropping the cases where
    one says none is some, then on every pair, and take apart each
    hypothesis that says some is some. *)
Ltac cases :=
  repeat match goal with
         | H : context [match ?x with _ => _ end] |- _ => destruct x eqn:?; try discriminate
         end;
  repeat match goal with q : (_ * _)%type |- _ => destruct q end; cbn [fst snd] in *;
  repeat match goal with H : Some _ = Some _ |- _ => injection H as; subst end.

(** A side section's term leaves fewer words than it was given. *)
Lemma side_term_length : forall pool f ws t rest,
  read_side_term pool f ws = Some (t, rest) -> (length rest < length ws)%nat.
Proof.
  intros pool f. induction f as [|f IH]; intros ws t rest H; simpl in H; [discriminate|].
  assert (Hr : forall ws v rest, read_side_term pool f ws = Some (v, rest) ->
                                 (length rest <= length ws)%nat).
  { intros ws' v rest' H'. apply IH in H'. lia. }
  unfold read_wide in H. cases; simpl; try lia;
    match goal with
    | E : read_counted _ _ = Some (_, _) |- _ => apply read_counted_length in E; [simpl; lia | exact Hr]
    end.
Qed.

(** A side section's term, with fuel the length of its words: each
    level of the term takes a word. *)
Lemma side_term_fuel : forall pool ws, enough (fun f => read_side_term pool f ws) (length ws).
Proof.
  intros pool ws. apply enough_step. intros g Hg. revert ws Hg.
  induction g as [|g IH]; intros ws Hg.
  - destruct ws; simpl in *; [reflexivity | lia].
  - assert (Hext : forall ws', (length ws' <= g)%nat ->
                   read_side_term pool (S g) ws' = read_side_term pool g ws') by auto.
    assert (Hr : forall ws v rest, read_side_term pool (S g) ws = Some (v, rest) ->
                                   (length rest <= length ws)%nat).
    { intros ws' v rest H. apply side_term_length in H. lia. }
    destruct ws as [|tag ws]; [reflexivity|]. simpl in Hg.
    change (read_side_term pool (S (S g)) (tag :: ws)) with
      (match tag :: ws with
       | 0 :: ws' => let* p := read_wide ws' in Some (TInt (fst p), snd p)
       | 1 :: i :: ws' => let* a := ZMap.find i pool in Some (a, ws')
       | 2 :: i :: ws' =>
           let* fa := ZMap.find i pool in
           let* fn := atom_string fa in
           let* p := read_counted (read_side_term pool (S g)) ws' in
           match fst p with [] => None | _ => Some (TApp fn (fst p), snd p) end
       | 3 :: ws' => let* p := read_counted (read_side_term pool (S g)) ws' in
                     Some (TList (fst p), snd p)
       | _ => None
       end).
    change (read_side_term pool (S g) (tag :: ws)) with
      (match tag :: ws with
       | 0 :: ws' => let* p := read_wide ws' in Some (TInt (fst p), snd p)
       | 1 :: i :: ws' => let* a := ZMap.find i pool in Some (a, ws')
       | 2 :: i :: ws' =>
           let* fa := ZMap.find i pool in
           let* fn := atom_string fa in
           let* p := read_counted (read_side_term pool g) ws' in
           match fst p with [] => None | _ => Some (TApp fn (fst p), snd p) end
       | 3 :: ws' => let* p := read_counted (read_side_term pool g) ws' in
                     Some (TList (fst p), snd p)
       | _ => None
       end).
    cbv beta iota.
    repeat first
      [ reflexivity
      | rewrite (read_counted_ext (read_side_term pool (S g)) (read_side_term pool g) g _ Hext Hr)
          by (simpl in *; lia)
      | match goal with |- context [match ?x with _ => _ end] => destruct x eqn:? end ].
Qed.

(** One round of reading NAMES, with fuel S f. *)
Lemma name_recs_S : forall pool f w ws,
  read_name_recs pool (S f) (w :: ws) =
  (let rt := read_side_term pool (length (w :: ws)) in
   let* a := read_counted rt (w :: ws) in let* b := read_counted rt (snd a) in
   let* c := read_counted rt (snd b) in
   let* rest := read_name_recs pool f (snd c) in
   Some (mkFnames (fst a) (fst b) (fst c) :: rest)).
Proof. reflexivity. Qed.

(** NAMES, with fuel the length of its words: each function's names
    take a word at least. *)
Lemma name_recs_fuel : forall pool ws, enough (fun f => read_name_recs pool f ws) (length ws).
Proof.
  intros pool ws. apply enough_step. intros g Hg. revert ws Hg.
  induction g as [|g IH]; intros ws Hg.
  - destruct ws; simpl in *; [reflexivity | lia].
  - destruct ws as [|w ws]; [reflexivity|]. rewrite !name_recs_S. cbv zeta.
    set (rt := read_side_term pool (length (w :: ws))).
    assert (Hr : forall ws v rest, rt ws = Some (v, rest) -> (length rest <= length ws)%nat).
    { intros ws' v rest H. apply side_term_length in H. lia. }
    destruct (read_counted rt (w :: ws)) as [[a wa]|] eqn:Ea; [|reflexivity]. cbn [fst snd].
    destruct (read_counted rt wa) as [[b wb]|] eqn:Eb; [|reflexivity]. cbn [fst snd].
    destruct (read_counted rt wb) as [[c wc]|] eqn:Ec; [|reflexivity]. cbn [fst snd].
    apply read_counted_length in Ea, Eb, Ec; try exact Hr.
    rewrite IH by (simpl in *; lia). reflexivity.
Qed.

(** ## Instructions and blocks *)

(** An instruction leaves fewer words than it was given: at least its
    header is read. *)
Lemma inst_length : forall r g n x ws t n' x' rest,
  read_inst r g n x ws = Some (t, n', x', rest) -> (length rest < length ws)%nat.
Proof.
  intros r g n x ws t n' x' rest H. unfold read_inst in H. cases;
    repeat match goal with E : take _ _ = Some _ |- _ => apply take_length in E end;
    simpl in *; lia.
Qed.

(** One round of reading a group, with fuel S f. *)
Lemma group_S : forall r g f n x ws,
  read_group r g (S f) n x ws =
  match next_opcode ws with
  | Some c =>
      if Z.eqb (group c) g then
        let* p := read_inst r g n x ws in
        let '(t, n1, x1, ws1) := p in
        let* q := read_group r g f n1 x1 ws1 in
        let '(ts, n2, x2, ws2) := q in
        Some (t :: ts, n2, x2, ws2)
      else Some ([], n, x, ws)
  | None => Some ([], n, x, ws)
  end.
Proof. reflexivity. Qed.

(** A group leaves no more words than it was given. *)
Lemma group_length : forall r g f n x ws ts n' x' rest,
  read_group r g f n x ws = Some (ts, n', x', rest) -> (length rest <= length ws)%nat.
Proof.
  intros r g f. induction f as [|f IH]; intros n x ws ts n' x' rest H.
  - simpl in H. destruct (next_opcode ws); [destruct (Z.eqb (group z) g)|]; try discriminate;
      injection H as; subst; lia.
  - rewrite group_S in H.
    destruct (next_opcode ws) as [c|]; [|injection H as; subst; lia].
    destruct (Z.eqb (group c) g); [|injection H as; subst; lia].
    destruct (read_inst r g n x ws) as [[[[t n1] x1] ws1]|] eqn:E1; [|discriminate].
    destruct (read_group r g f n1 x1 ws1) as [[[[ts' n2] x2] ws2]|] eqn:E2; [|discriminate].
    injection H as; subst. apply inst_length in E1. apply IH in E2. lia.
Qed.

(** A group of instructions, with fuel the length of its words: each
    instruction takes a word. *)
Lemma group_fuel : forall r g n x ws, enough (fun f => read_group r g f n x ws) (length ws).
Proof.
  intros r g n x ws. apply enough_step. intros f Hf. revert n x ws Hf.
  induction f as [|f IH]; intros n x ws Hf.
  - destruct ws; simpl in Hf; [|lia]. reflexivity.
  - rewrite (group_S r g (S f)), (group_S r g f).
    destruct (next_opcode ws) as [c|]; [|reflexivity].
    destruct (Z.eqb (group c) g); [|reflexivity].
    destruct (read_inst r g n x ws) as [[[[t n1] x1] ws1]|] eqn:E1; [|reflexivity].
    apply inst_length in E1. rewrite IH by lia. reflexivity.
Qed.

(** Blocks, with fuel the length of their words. *)
Lemma blocks_fuel : forall r k i n x ws, enough (fun f => read_blocks r f i k n x ws) (length ws).
Proof.
  intros r k i n x ws f' Hf. revert i n x ws f' Hf.
  induction k as [|k IH]; intros i n x ws f' Hf; [reflexivity|]. simpl.
  destruct (ZMap.find i (r_labels r)) as [l|]; [|reflexivity].
  rewrite (group_fuel r 0 n x ws f') by lia.
  destruct (read_group r 0 (length ws) n x ws) as [[[[phis n1] x1] ws1]|] eqn:E1; [|reflexivity].
  pose proof E1 as L1. apply group_length in L1.
  destruct (Z.eqb i 0 && negb (Nat.eqb (length phis) 0)); [reflexivity|].
  rewrite (group_fuel r 1 n1 x1 ws1 f') by lia.
  rewrite <- (group_fuel r 1 n1 x1 ws1 (length ws)) by lia.
  destruct (read_group r 1 (length ws) n1 x1 ws1) as [[[[insts n2] x2] ws2]|] eqn:E2; [|reflexivity].
  pose proof E2 as L2. apply group_length in L2.
  destruct (read_inst r 2 n2 x2 ws2) as [[[[j n3] x3] ws3]|] eqn:E3; [|reflexivity].
  pose proof E3 as L3. apply inst_length in L3.
  rewrite (IH (i + 1)%Z n3 x3 ws3 f') by lia.
  rewrite (IH (i + 1)%Z n3 x3 ws3 (length ws)) by lia.
  reflexivity.
Qed.

(** ## Elements of a list *)

(** Whether reading the field f takes a word: all fields but a
    definition's. *)
Definition takes_word (f : field) : bool :=
  match f with FDef _ | FLocalDef _ => false | _ => true end.

(** Naming a definition reads no word. *)
Lemma def_name_words : forall r s t s', def_name r s = Some (t, s') -> s_words s' = s_words s.
Proof. intros r s t s' H. unfold def_name in H. cases; reflexivity. Qed.

(** The next word is one word. *)
Lemma next_word_words : forall s z s',
  next_word s = Some (z, s') -> (S (length (s_words s')) = length (s_words s))%nat.
Proof. intros [ws rb n x] z s' H. unfold next_word in H. simpl in *. cases; reflexivity. Qed.

(** A field leaves no more words than it was given, and fewer if it
    takes a word. *)
Lemma field_words : forall r f e s e' s',
  read_field r f e s = Some (e', s') ->
  (length (s_words s') + (if takes_word f then 1 else 0) <= length (s_words s))%nat.
Proof.
  intros r f e s e' s' H.
  destruct f; simpl in H |- *; cases;
    repeat match goal with
           | E : next_word _ = Some _ |- _ => apply next_word_words in E
           | E : def_name _ _ = Some _ |- _ => apply def_name_words in E
           | E : read_result _ _ _ = Some _ |- _ => unfold read_result in E
           end;
    cases;
    repeat match goal with
           | E : next_word _ = Some _ |- _ => apply next_word_words in E
           | E : def_name _ _ = Some _ |- _ => apply def_name_words in E
           end;
    simpl in *;
    repeat match goal with E : s_words ?a = s_words _ |- _ => rewrite E in *; clear E end; lia.
Qed.

(** Fields leave no more words than they were given, and fewer if one
    of them takes a word. *)
Lemma fields_words : forall r fs e s e' s',
  read_fields r fs e s = Some (e', s') ->
  (length (s_words s') + (if existsb takes_word fs then 1 else 0) <= length (s_words s))%nat.
Proof.
  intros r fs. induction fs as [|f fs IH]; intros e s e' s' H; simpl in H |- *.
  - injection H as <- <-. lia.
  - destruct (read_field r f e s) as [[e1 s1]|] eqn:E; [|discriminate].
    apply field_words in E. apply IH in H.
    destruct (takes_word f), (existsb takes_word fs); simpl in *; lia.
Qed.

(** One round of reading the rest, with fuel S f. *)
Lemma rest_S : forall r el fs f s,
  read_rest r el fs (S f) s =
  match s_words s with
  | [] => Some ([], s)
  | _ => let* p := read_fields r fs [] s in let* t := fill_pat el (fst p) in
         let* q := read_rest r el fs f (snd p) in Some (t :: fst q, snd q)
  end.
Proof. reflexivity. Qed.

(** The elements to the end of an instruction, with fuel the number of
    its words left, when each element takes a word. *)
Lemma rest_fuel : forall r el fs s, existsb takes_word fs = true ->
  enough (fun f => read_rest r el fs f s) (length (s_words s)).
Proof.
  intros r el fs s Hfs. apply enough_step. intros g Hg. revert s Hg.
  induction g as [|g IH]; intros s Hg.
  - destruct (s_words s) eqn:E; simpl in Hg; [|lia].
    rewrite rest_S. simpl. rewrite E. reflexivity.
  - rewrite (rest_S r el fs (S g)), (rest_S r el fs g).
    destruct (s_words s) as [|w ws] eqn:Ew; [reflexivity|].
    destruct (read_fields r fs [] s) as [[e s1]|] eqn:E; [|reflexivity]. cbn [fst snd].
    destruct (fill_pat el e); [|reflexivity].
    apply fields_words in E. rewrite Hfs, Ew in E. simpl in E, Hg.
    rewrite IH by lia. reflexivity.
Qed.

(** Every list of a form read to the end has elements that take a
    word, so [rest_fuel] covers each one the reader reads. *)
Lemma forms_rest_take_words :
  forallb (fun f => forallb (fun lf => match lf with
                                       | FRest _ _ fs => existsb takes_word fs
                                       | _ => true
                                       end) (f_fields f)) forms = true.
Proof. vm_compute. reflexivity. Qed.

(** ## The reader as a whole *)

(** [decode] gives every list of words a module or refuses it: it is
    a function, and by the lemmas above no refusal is for want of
    fuel. *)
Theorem decode_total : forall ws, decode ws = None \/ exists m, decode ws = Some m.
Proof. intros ws. destruct (decode ws) as [m|]; [right; exists m |left]; reflexivity. Qed.
