(** The backend inserts a [[poll|poll edge]] on each jump to an earlier
    block or to the block itself. This file proves that the validator
    accepts the resulting cycle coverage, including in unreachable blocks. *)

From Stdlib Require Import String ZArith List Bool Ascii Lia.
From Nanofil Require Import Term Maps Syntax Cfg Validate Transport.
From Backend Require Import Text Pizlonate.
Import ListNotations.
Local Notation map_option := Semantics.map_option.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Unset Lia Cache.

(** ## Fresh check names *)

(** The pass names each [[check]] with a decimal counter. Reading the
    printed digits recovers the counter, so a rejected name cannot
    collide with a later candidate. *)

(** The reader adds each digit to ten times the value of the preceding digits. *)
Local Fixpoint read_digits (s : string) (a : Z) : Z :=
  match s with
  | EmptyString => a
  | String c rest => read_digits rest (10 * a + (Z.of_nat (nat_of_ascii c) - 48))
  end.

(** Each entry in the printer's table contributes its digit value. *)
Local Lemma read_digit : forall d a s, 0 <= d < 10 ->
  read_digits (String.append (digit (Z.to_nat d)) s) a = read_digits s (10 * a + d).
Proof.
  intros d a s Hd.
  assert (H : (Z.to_nat d < 10)%nat) by lia.
  rewrite <- (Z2Nat.id d) at 2 by lia.
  destruct (Z.to_nat d) as [|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]; try reflexivity; lia.
Qed.

(** The printer prepends digits to a suffix. Reading the result from
    zero has the same effect as reading that suffix from the printed number. *)
Local Lemma read_printed_digits : forall fuel n s, 0 <= n < 10 ^ Z.of_nat fuel ->
  read_digits (digits fuel n s) 0 = read_digits s n.
Proof.
  induction fuel as [|fuel IH]; intros n s Hbound.
  - change (0 <= n < 1) in Hbound. replace n with 0 by lia. reflexivity.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hbound by lia.
    cbn [digits]. unfold ten.
    pose proof (Z.div_mod n 10 ltac:(lia)) as Hdiv.
    pose proof (Z.mod_pos_bound n 10 ltac:(lia)) as Hrem.
    unfold Z.div, Z.modulo in Hdiv, Hrem.
    destruct (Z.div_eucl n 10) as [q r]. cbn [fst snd] in Hdiv, Hrem.
    destruct (Z.eqb_spec q 0) as [->|Hq].
    + rewrite read_digit by lia. replace (10 * 0 + r) with n by lia. reflexivity.
    + rewrite IH by lia. rewrite read_digit by lia. now rewrite <- Hdiv.
Qed.

(** Small counters fit in eighteen digits. For larger counters, the number
    of binary digits also bounds the number of decimal digits. *)
Local Lemma decimal_fuel_bound : forall n, 0 <= n -> n < 10 ^ Z.of_nat (digits_fuel n).
Proof.
  intros n Hn. unfold digits_fuel. destruct (Z.ltb_spec n eighteen_digits) as [H|H].
  - exact H.
  - destruct n as [|p|p]; try (unfold eighteen_digits in H; lia).
    clear H Hn. induction p as [p IH|p IH|]; cbn [Pos.size_nat].
    + rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
    + rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
    + reflexivity.
Qed.

(** Equal decimal strings identify equal nonnegative counters. *)
Lemma decimal_injective : forall n1 n2 : Z, 0 <= n1 -> 0 <= n2 ->
  Text.decimal n1 = Text.decimal n2 -> n1 = n2.
Proof.
  intros n1 n2 H1 H2 E. apply (f_equal (fun s => read_digits s 0)) in E.
  unfold decimal in E. destruct (Z.ltb_spec n1 0); [lia|].
  destruct (Z.ltb_spec n2 0); [lia|]. cbv beta in E.
  rewrite !read_printed_digits in E by (split; auto using decimal_fuel_bound). exact E.
Qed.

(** Every candidate begins with the prefix reserved for checks. *)
Lemma chk_decimal_prefix : forall n : Z,
  String.prefix "chk" (String.append "chk" (Text.decimal n)) = true.
Proof. intro n. destruct (Text.decimal n); reflexivity. Qed.

(** The common prefix preserves the distinction between counters. *)
Lemma chk_decimal_inj : forall n1 n2 : Z, 0 <= n1 -> 0 <= n2 ->
  String.append "chk" (Text.decimal n1) = String.append "chk" (Text.decimal n2) ->
  n1 = n2.
Proof. intros n1 n2 H1 H2 E. apply decimal_injective; auto. injection E. auto. Qed.

(** The remaining list covers every reserved name the search can still
    encounter. Removing a rejected candidate preserves this property. *)
Local Lemma fresh_remaining : forall fuel names n q n' rem,
  0 <= n -> (length rem <= fuel)%nat ->
  (forall k, n <= k -> In (String.append "chk" (decimal k)) names ->
                       In (String.append "chk" (decimal k)) rem) ->
  fresh fuel names n = (q, n') ->
  ~ In q names /\ n < n' /\ q = String.append "chk" (decimal (n' - 1)) /\
  String.prefix "chk" q = true.
Proof.
  induction fuel as [|fuel IH]; intros names n q n' rem Hn Hlen Hrem Run.
  - injection Run as <- <-. replace (n + 1 - 1) with n by lia.
    repeat split; try lia; try apply chk_decimal_prefix; try reflexivity.
    intro Hin. specialize (Hrem n ltac:(lia) Hin). destruct rem; cbn in *; tauto || lia.
  - cbn [fresh] in Run. set (key := String.append "chk" (decimal n)) in *.
    destruct (existsb (String.eqb key) names) eqn:Hit.
    + apply existsb_exists in Hit. destruct Hit as (s & Hin & E).
      apply String.eqb_eq in E. subst s.
      assert (Here : In key rem) by (apply Hrem; auto; lia).
      specialize (IH names (n + 1) q n' (remove string_dec key rem)).
      assert (Bound := remove_length_lt string_dec rem key Here).
      assert (Next : forall k, n + 1 <= k -> In (String.append "chk" (decimal k)) names ->
                     In (String.append "chk" (decimal k)) (remove string_dec key rem)).
      { intros k Hk Hmem. apply in_in_remove.
        - unfold key. intro E. apply chk_decimal_inj in E; lia.
        - apply Hrem; auto; lia. }
      destruct (IH ltac:(lia) ltac:(lia) Next Run) as (A & B & C).
      repeat split; tauto || lia.
    + injection Run as <- <-. replace (n + 1 - 1) with n by lia.
      repeat split; try apply chk_decimal_prefix; try reflexivity; try lia. intro Hin.
      assert (H : existsb (String.eqb key) names = true).
      { apply existsb_exists. exists key. auto using String.eqb_refl. }
      congruence.
Qed.

(** Each collision consumes a distinct reserved name. The number of
    names therefore bounds the fuel needed to find a free one. *)
Lemma fresh_spec : forall fuel names n q n',
  0 <= n -> (length names <= fuel)%nat -> Pizlonate.fresh fuel names n = (q, n') ->
  ~ In q names /\ n < n' /\ q = String.append "chk" (Text.decimal (n' - 1)) /\
  String.prefix "chk" q = true.
Proof. intros. eapply fresh_remaining with (rem := names); eauto. Qed.

(** ## Instruction order *)

(** The pass collects instructions in reverse order. A recursive expansion
    in source order describes both the emitted code and the final counter. *)

(** The expansion emits each instruction's replacement before processing
    the rest of the list with the updated counter. *)
Fixpoint expand_insts (names : list string) (fuel : nat) (n : Z) (insts : list term)
  : Z * list term :=
  match insts with
  | [] => (n, [])
  | i :: rest =>
      match Pizlonate.checked_access i with
      | Some access =>
          let '(q, n1) := Pizlonate.fresh fuel names n in
          let '(n2, out) := expand_insts names fuel n1 rest in
          (n2, access (TAtom q) ++ out)
      | None =>
          let j := match Pizlonate.flight_inst i with Some j => j | None => i end in
          let '(n2, out) := expand_insts names fuel n rest in
          (n2, j :: out)
      end
  end.

(** Reversing the fold's result puts the previous output before the expansion. *)
Lemma fold_left_inst_step_expand : forall names fuel insts n acc,
  let '(n1, out1) := fold_left (Pizlonate.inst_step names fuel) insts (n, acc) in
  let '(n2, out2) := expand_insts names fuel n insts in
  n1 = n2 /\ rev' out1 = rev acc ++ out2.
Proof.
  intros names fuel insts. induction insts as [|i rest IH]; intros n acc.
  - cbn. rewrite app_nil_r. split; auto using rev_alt.
  - cbn [fold_left expand_insts inst_step]. destruct (checked_access i) as [access|].
    + destruct (fresh fuel names n) as [q k].
      specialize (IH k (rev_append (access (TAtom q)) acc)).
      destruct (fold_left _ _ _) as [k1 out1]. destruct (expand_insts _ _ _ _) as [k2 out2].
      destruct IH as [E R]. split; auto.
      rewrite R, rev_append_rev, rev_app_distr, rev_involutive, app_assoc. reflexivity.
    + specialize (IH n ((match flight_inst i with Some j => j | None => i end) :: acc)).
      destruct (fold_left _ _ _) as [k1 out1]. destruct (expand_insts _ _ _ _) as [k2 out2].
      destruct IH as [E R]. split; auto. rewrite R. cbn [rev]. now rewrite <- app_assoc.
Qed.

(** An empty accumulator yields exactly the source-order expansion. *)
Lemma fold_left_inst_step_nil : forall names fuel insts n,
  let '(n1, out1) := fold_left (Pizlonate.inst_step names fuel) insts (n, []) in
  let '(n2, out2) := expand_insts names fuel n insts in
  n1 = n2 /\ rev' out1 = out2.
Proof. intros. exact (fold_left_inst_step_expand names fuel insts n []). Qed.

(** ## Block positions *)

(** The label index assigns successive positions to the input blocks.
    Inserting a label requires that it be absent, so later blocks preserve
    every earlier binding. *)

(** Indexing a nonempty list first inserts the head block's label. *)
Local Lemma index_cons : forall k b bs m idx, label_index k (b :: bs) m = Some idx ->
  exists l phis insts j, b = TApp "block" [l; phis; insts; j] /\
    nm_mem l m = false /\ label_index (k + 1) bs (nm_add l k m) = Some idx.
Proof.
  intros k b bs m idx H. destruct b as [| |f xs|]; try discriminate.
  destruct xs as [|l [|phis [|insts [|j [|extra rest]]]]]; try discriminate.
  cbn [label_index] in H. destruct (String.eqb f "block") eqn:E; [|discriminate].
  apply String.eqb_eq in E. subst f. destruct (nm_mem l m) eqn:M; [discriminate|].
  eauto 8.
Qed.

(** A successful indexing pass preserves the bindings it starts with. *)
Local Lemma index_preserves : forall bs k m idx l v, label_index k bs m = Some idx ->
  nm_find l m = Some v -> nm_find l idx = Some v.
Proof.
  induction bs as [|b bs IH]; intros k m idx l v H Found.
  - injection H as <-. exact Found.
  - destruct (index_cons _ _ _ _ _ H) as (a & ph & ins & j & E & Absent & Tail).
    eapply IH; [exact Tail|]. rewrite nm_find_add.
    destruct (name_eqb l a) eqn:Same; auto. apply term_eqb_eq in Same. subst a.
    unfold nm_mem in Absent. rewrite Found in Absent. discriminate.
Qed.

(** Each input block has a fresh label whose final binding gives its position. *)
Lemma label_index_blocks : forall k bs m idx, Pizlonate.label_index k bs m = Some idx ->
  forall pos b, nth_error bs pos = Some b -> exists l phis insts j,
  b = TApp "block" [l; phis; insts; j] /\ nm_mem l m = false /\
  nm_find l idx = Some (k + Z.of_nat pos).
Proof.
  intros k bs. revert k. induction bs as [|b bs IH]; intros k m idx H pos x At.
  - destruct pos; discriminate.
  - destruct (index_cons _ _ _ _ _ H) as (a & ph & ins & j & E & Absent & Tail).
    destruct pos as [|p].
    + injection At as <-. exists a, ph, ins, j. repeat split; auto.
      rewrite Z.add_0_r. eapply index_preserves; [exact Tail|].
      rewrite nm_find_add. unfold name_eqb. now rewrite term_eqb_refl.
    + destruct (IH _ _ _ Tail _ _ At) as (l & ph' & ins' & j' & Shape & Free & Find).
      rewrite nm_mem_add in Free. apply orb_false_iff in Free.
      exists l, ph', ins', j'. rewrite Nat2Z.inj_succ.
      replace (k + Z.succ (Z.of_nat p)) with (k + 1 + Z.of_nat p) by lia. tauto.
Qed.

(** Every binding comes from the initial map or a block at the indicated position. *)
Lemma label_index_find_inv : forall k bs m idx l v, Pizlonate.label_index k bs m = Some idx ->
  nm_find l idx = Some v -> nm_find l m = Some v \/ exists pos phis insts j,
  nth_error bs pos = Some (TApp "block" [l; phis; insts; j]) /\ v = k + Z.of_nat pos.
Proof.
  intros k bs. revert k. induction bs as [|b bs IH]; intros k m idx l v H Found.
  - injection H as <-. now left.
  - destruct (index_cons _ _ _ _ _ H) as (a & ph & ins & j & -> & Free & Tail).
    destruct (IH _ _ _ _ _ Tail Found) as [Before|(p & ph' & ins' & j' & At & E)].
    + rewrite nm_find_add in Before. destruct (name_eqb l a) eqn:Same; [|now left].
      apply term_eqb_eq in Same. subst a. right. exists O, ph, ins, j. split; [reflexivity|]. injection Before as <-. lia.
    + right. exists (S p), ph', ins', j'. split; [exact At|]. rewrite Nat2Z.inj_succ. lia.
Qed.

(** The validator's membership test recognizes exactly the names in the list. *)
Local Lemma mem_names : forall l ns, Validate.mem l ns = true <-> In l ns.
Proof.
  intros l ns. unfold Validate.mem. rewrite existsb_exists. split.
  - intros (s & Hin & E). apply term_eqb_eq in E. now subst.
  - intro Hin. exists l. split; auto. apply term_eqb_refl.
Qed.

(** Each label in an aligned list identifies an input block at some position. *)
Local Lemma listed_label : forall bs ls,
  Forall2 (fun b l => exists phis insts j, b = TApp "block" [l; phis; insts; j]) bs ls ->
  forall l, In l ls -> exists pos phis insts j,
    nth_error bs pos = Some (TApp "block" [l; phis; insts; j]).
Proof.
  intros bs ls P. induction P as [|b a bs ls Shape P IH]; intros l Hin.
  - contradiction.
  - destruct Hin as [<-|Hin].
    + destruct Shape as (ph & ins & j & ->). exists O, ph, ins, j. reflexivity.
    + destruct (IH _ Hin) as (p & ph & ins & j & At). exists (S p), ph, ins, j. exact At.
Qed.

(** The validator's duplicate check succeeds on the indexed labels. *)
Lemma label_index_no_dups : forall k bs m idx ls, Pizlonate.label_index k bs m = Some idx ->
  Forall2 (fun b l => exists phis insts j, b = TApp "block" [l; phis; insts; j]) bs ls ->
  Validate.no_dups ls = true.
Proof.
  intros k bs m idx ls H P. revert k m H.
  induction P as [|b l bs ls Shape P IH]; intros k m H; [reflexivity|].
  destruct (index_cons _ _ _ _ _ H) as (a & ph & ins & j & Eb & Free & Tail).
  destruct Shape as (ph' & ins' & j' & Es). assert (a = l) by congruence. subst a.
  cbn [no_dups]. rewrite (IH _ _ Tail), andb_true_r.
  destruct (Validate.mem l ls) eqn:M; [|reflexivity]. apply mem_names in M.
  destruct (listed_label _ _ P _ M) as (pos & p & i & t & At).
  destruct (label_index_blocks _ _ _ _ Tail _ _ At) as (x & px & ix & jx & E & A & F).
  assert (x = l) by congruence. subst x. rewrite nm_mem_add in A.
  unfold name_eqb in A. rewrite term_eqb_refl in A. discriminate.
Qed.

(** ## Jump decoding *)

(** A [[poll|poll edge]] keeps its destination label. The pass also
    keeps the branch condition and return values, which determine the
    operands that the validator checks. *)

(** The decoder treats every term outside the unary poll form as a plain label. *)
Local Lemma plain_dtarget : forall l, (forall a, l <> TApp "poll" [a]) ->
  dtarget l = Some (To l).
Proof.
  intros l Plain. unfold dtarget.
  repeat match goal with
  | |- context [match ?x with _ => _ end] => destruct x; try reflexivity
  end.
  exfalso. eapply Plain. reflexivity.
Qed.

(** A plain target must resolve to an index greater than its source index. *)
Local Definition forward_edge (idx : nmap Z) (from : Z) (t : target) : Prop :=
  is_poll t = false -> exists to, nm_find (edge_label t) idx = Some to /\ from < to.

(** An existing poll keeps its label. For a plain input, the position
    comparison determines whether the pass wraps the label in a poll. *)
Local Lemma target_pair : forall idx from l t, polled_target idx from l = Some t ->
  exists dl dt, dtarget l = Some dl /\ dtarget t = Some dt /\
                edge_label dt = edge_label dl /\ forward_edge idx from dt.
Proof.
  intros idx from l t Run.
  assert (Plain : (exists a, l = TApp "poll" [a]) \/
    ((forall a, l <> TApp "poll" [a]) /\
     polled_target idx from l =
       match nm_find l idx with
       | Some to => Some (if to <=? from then TApp "poll" [l] else l)
       | None => None
       end)).
  { destruct l as [z|atom|f xs|terms]; try (right; split; [intros a E; discriminate|reflexivity]).
    destruct xs as [|a [|b xs]]; try (right; split; [intros x E; discriminate|reflexivity]).
    destruct (String.eqb f "poll") eqn:E.
    - apply String.eqb_eq in E. subst. left. eauto.
    - right. split.
      + intros x H. injection H as H _. subst. discriminate.
      + cbn [polled_target]. now rewrite E. }
  destruct Plain as [(a & ->)|[Other Step]].
  - injection Run as <-. exists (Poll a), (Poll a). repeat split; discriminate.
  - rewrite Step in Run. destruct (nm_find l idx) as [to|] eqn:Find; [|discriminate].
    destruct (Z.leb_spec to from); injection Run as <-.
    + exists (To l), (Poll l). repeat split; auto using plain_dtarget. discriminate.
    + exists (To l), (To l). repeat split; auto using plain_dtarget.
      intro Unpolled. exists to. auto.
Qed.

(** Decoding a rewritten target recovers its original label and certifies
    a strict increase in block position for a plain edge. *)
Lemma polled_target_dtarget : forall idx from l t dt,
  Pizlonate.polled_target idx from l = Some t -> Transport.dtarget t = Some dt ->
  exists dl, Transport.dtarget l = Some dl /\ edge_label dt = edge_label dl /\
    (is_poll dt = false -> exists to, nm_find (edge_label dt) idx = Some to /\ from < to).
Proof.
  intros idx from l t dt Run Decode.
  destruct (target_pair _ _ _ _ Run) as (dl & out & L & T & Label & Forward).
  rewrite Decode in T. injection T as <-. exists dl. auto.
Qed.

Module JumpFacts.
(** A rewritten goto or branch can change how its targets poll. A jump
    without targets stays the same. *)
Inductive jump_change (idx : nmap Z) (from : Z) : jump -> jump -> Prop :=
| change_goto : forall a a', edge_label a' = edge_label a -> forward_edge idx from a' ->
    jump_change idx from (JGoto a) (JGoto a')
| change_branch : forall v a b a' b',
    edge_label a' = edge_label a -> edge_label b' = edge_label b ->
    forward_edge idx from a' -> forward_edge idx from b' ->
    jump_change idx from (JBranch v a b) (JBranch v a' b')
| change_exit : forall j, jump_targets j = [] -> jump_change idx from j j.

End JumpFacts.
Import JumpFacts.

(** The two decodings succeed together. Their jump constructors record
    which labels and operands the rewrite preserves. *)
Local Lemma jump_decodings : forall idx from j j', polled_jump idx from j = Some j' ->
  (djump j = None /\ djump j' = None) \/
  exists d d', djump j = Some d /\ djump j' = Some d' /\ jump_change idx from d d'.
Proof.
  intros idx from j j' Run. destruct j as [z|atom|f xs|ts]; try discriminate.
  - cbn [polled_jump] in Run.
    destruct (String.eqb atom "ret" || String.eqb atom "unreachable") eqn:E; [|discriminate].
    injection Run as <-. apply orb_true_iff in E. destruct E as [E|E];
      apply String.eqb_eq in E; subst atom; right; do 2 eexists; repeat split;
      apply change_exit; reflexivity.
  - cbn [polled_jump] in Run. destruct (String.eqb f "goto") eqn:G.
    + apply String.eqb_eq in G. subst f. destruct xs as [|l [|extra rest]]; try discriminate.
      destruct (polled_target idx from l) as [t|] eqn:T; [|discriminate].
      injection Run as <-. destruct (target_pair _ _ _ _ T) as (a & a' & A & A' & E & F).
      cbn [djump]. rewrite A, A'. right. do 2 eexists. repeat split. now constructor.
    + destruct (String.eqb f "branch") eqn:B.
      * apply String.eqb_eq in B. subst f.
        destruct xs as [|v [|l [|r [|extra rest]]]]; try discriminate.
        destruct (polled_target idx from l) as [s|] eqn:L; [|discriminate].
        destruct (polled_target idx from r) as [t|] eqn:R; [|discriminate].
        injection Run as <-.
        destruct (target_pair _ _ _ _ L) as (a & a' & A & A' & Ea & Fa).
        destruct (target_pair _ _ _ _ R) as (b & b' & D & D' & Eb & Fb).
        cbn [djump]. rewrite A, A', D, D'. destruct (dvalue v); [|now left].
        right. do 2 eexists. repeat split. now constructor.
      * destruct (String.eqb f "ret" || String.eqb f "rets") eqn:E; [|discriminate].
        destruct xs as [|v [|extra rest]]; try discriminate. injection Run as <-.
        apply orb_true_iff in E. destruct E as [E|E]; apply String.eqb_eq in E; subst f.
        -- cbn [djump]. destruct (dvalue v); [|now left].
           right. do 2 eexists. repeat split. apply change_exit. reflexivity.
        -- destruct v as [z|s|h args|vs]; try (left; split; reflexivity).
           cbn [djump]. destruct (map_option dvalue vs); [|now left].
           right. do 2 eexists. repeat split. apply change_exit. reflexivity.
Qed.

(** Every plain target of a related output jump carries the forward-edge guarantee. *)
Local Lemma change_forward : forall idx from d d', jump_change idx from d d' ->
  forall t, In t (jump_targets d') -> forward_edge idx from t.
Proof.
  intros idx from d d' H t Hin. destruct H; cbn in Hin.
  - destruct Hin as [<-|[]]. assumption.
  - destruct Hin as [<-|[<-|[]]]; assumption.
  - rewrite H in Hin. contradiction.
Qed.

(** A decoded jump keeps its successors and uses. Each remaining plain
    target lies strictly after the source. *)
Lemma polled_jump_djump : forall idx from j j' dj,
  Pizlonate.polled_jump idx from j = Some j' -> Transport.djump j = Some dj ->
  exists dj', Transport.djump j' = Some dj' /\ succ_labels dj' = succ_labels dj /\
    jump_uses dj' = jump_uses dj /\ (forall t, In t (jump_targets dj') -> is_poll t = false ->
    exists to, nm_find (edge_label t) idx = Some to /\ from < to).
Proof.
  intros idx from j j' dj Run Decode.
  destruct (jump_decodings _ _ _ _ Run) as [[E _]|(d & d' & E & D & Change)]; [congruence|].
  rewrite Decode in E. injection E as <-. exists d'. split; auto.
  split; [destruct Change; cbn; congruence|].
  split; [destruct Change; reflexivity|]. eapply change_forward; eauto.
Qed.

(** The output decoder alone suffices to certify every unpolled edge. *)
Lemma polled_jump_djump_rev : forall idx from j j' dj',
  Pizlonate.polled_jump idx from j = Some j' -> Transport.djump j' = Some dj' ->
  forall t, In t (jump_targets dj') -> is_poll t = false ->
    exists to, nm_find (edge_label t) idx = Some to /\ from < to.
Proof.
  intros idx from j j' dj' Run Decode.
  destruct (jump_decodings _ _ _ _ Run) as [[_ E]|(d & d' & D & E & Change)]; [congruence|].
  rewrite Decode in E. injection E as <-. eapply change_forward; eauto.
Qed.

(** The jump validator sees the same return type, labels and operands. *)
Lemma polled_jump_preserves_valid_jump : forall f1 f2 classes idx from j j' dj dj',
  fn_ret f1 = fn_ret f2 -> Validate.labels f1 = Validate.labels f2 ->
  Pizlonate.polled_jump idx from j = Some j' ->
  Transport.djump j = Some dj -> Transport.djump j' = Some dj' ->
  Validate.valid_jump f1 classes dj = true -> Validate.valid_jump f2 classes dj' = true.
Proof.
  intros f1 f2 classes idx from j j' dj dj' Ret Labels Run Decode Decode'.
  destruct (jump_decodings _ _ _ _ Run) as [[E _]|(d & d' & E & E' & Change)]; [congruence|].
  rewrite Decode in E. rewrite Decode' in E'. injection E as <-. injection E' as <-.
  destruct Change as [a a' Ea Fa|v a b a' b' Ea Eb Fa Fb|d Exit].
  - cbn [valid_jump]. now rewrite Ea, Labels.
  - cbn [valid_jump]. now rewrite Ea, Eb, Labels.
  - destruct d; cbn [valid_jump]; now rewrite ?Labels, ?Ret.
Qed.

(** ## Control flow and dominance *)

(** The graph builder uses each block's label and the ordered labels of
    its successors. These lists also determine the predecessor lists
    that the validator uses for [[phi]] nodes. *)

(** The graph builder and the validator enumerate successors in the same order. *)
Local Lemma cfg_successors : forall j, jump_succs j = succ_labels j.
Proof. destruct j; reflexivity. Qed.

(** Block labels and successor lists determine all three lists used to build the graph. *)
Local Lemma cfg_inputs : forall bs1 bs2 : list block,
  map b_label bs1 = map b_label bs2 ->
  map (fun b => succ_labels (b_jump b)) bs1 = map (fun b => succ_labels (b_jump b)) bs2 ->
  map (fun b => (b_label b, jump_succs (b_jump b))) bs1 =
  map (fun b => (b_label b, jump_succs (b_jump b))) bs2 /\
  flat_map (fun b => map (fun s => (s, b_label b)) (jump_succs (b_jump b))) bs1 =
  flat_map (fun b => map (fun s => (s, b_label b)) (jump_succs (b_jump b))) bs2 /\
  map (fun b => (b_label b, @nil name)) bs1 = map (fun b => (b_label b, @nil name)) bs2.
Proof.
  induction bs1 as [|a bs IH]; intros [|b cs] Labels Edges; try discriminate.
  - repeat split.
  - injection Labels as L Ls. injection Edges as E Es.
    destruct (IH _ Ls Es) as (Pairs & Flat & Empty).
    cbn [map flat_map]. rewrite !cfg_successors, L, E, Pairs, Flat, Empty. repeat split.
Qed.

(** Equal labels and successors give the same graph and dominance intervals. *)
Lemma same_cfg_block_intervals : forall bs1 bs2 : list block,
  map b_label bs1 = map b_label bs2 ->
  map (fun b => succ_labels (b_jump b)) bs1 = map (fun b => succ_labels (b_jump b)) bs2 ->
  Cfg.func_cfg bs1 = Cfg.func_cfg bs2 /\ Cfg.block_intervals bs1 = Cfg.block_intervals bs2.
Proof.
  intros bs1 bs2 L E. enough (G : func_cfg bs1 = func_cfg bs2).
  { split; auto. unfold block_intervals. now rewrite G. }
  destruct (cfg_inputs _ _ L E) as (Pairs & Flat & Empty).
  destruct bs1 as [|a bs], bs2 as [|b cs]; try discriminate; [reflexivity|].
  assert (Entry : b_label a = b_label b) by now injection L.
  unfold func_cfg. now rewrite Pairs, Flat, Empty, Entry.
Qed.

(** Equal labels and successors preserve the order of every predecessor list. *)
Lemma same_cfg_preds_of : forall bs1 bs2 l,
  map b_label bs1 = map b_label bs2 ->
  map (fun b => succ_labels (b_jump b)) bs1 = map (fun b => succ_labels (b_jump b)) bs2 ->
  Validate.preds_of bs1 l = Validate.preds_of bs2 l.
Proof.
  induction bs1 as [|a bs IH]; intros [|b cs] l Labels Edges; try discriminate; [reflexivity|].
  injection Labels as L Ls. injection Edges as E Es.
  specialize (IH _ l Ls Es). unfold preds_of in *. cbn [filter]. rewrite E.
  destruct (Validate.mem l (succ_labels (b_jump b))); cbn [map]; congruence.
Qed.

(** ## Peeling the graph of unpolled edges *)

(** Every unpolled edge leads to a block with a larger index. A block
    of maximal index in any remaining subgraph is therefore a sink,
    and each peeling step removes at least that block. *)

(** A nonempty finite list contains an element of maximal rank. *)
Local Lemma maximum_member : forall (A : Type) (rank : A -> Z) a xs,
  exists m, In m (a :: xs) /\ forall x, In x (a :: xs) -> rank x <= rank m.
Proof.
  intros A rank a xs. revert a. induction xs as [|b xs IH]; intro a.
  - exists a. split; [now left|]. intros x [<-|[]]. lia.
  - destruct (IH b) as (m & Member & Max).
    destruct (Z_le_gt_dec (rank a) (rank m)).
    + exists m. split; [now right|]. intros x [<-|Hin]; auto.
    + exists a. split; [now left|]. intros x [<-|Hin]; [lia|]. specialize (Max _ Hin). lia.
Qed.

(** A filter that rejects a member strictly shortens the list. *)
Local Lemma filter_drops_member : forall (A : Type) (keep : A -> bool) xs x,
  In x xs -> keep x = false -> (length (filter keep xs) < length xs)%nat.
Proof.
  intros A keep xs. induction xs as [|a xs IH]; intros x Hin Drop; [contradiction|].
  cbn [filter]. destruct (keep a) eqn:K.
  - destruct Hin as [<-|Hin]; [congruence|]. specialize (IH _ Hin Drop). cbn. lia.
  - pose proof (filter_length_le keep xs). cbn. lia.
Qed.

(** The index assigns a rank to each source and a greater rank to each destination. *)
Local Definition ranked_edges (idx : nmap Z) (g : list (name * list name)) : Prop :=
  forall u sucs, In (u, sucs) g -> exists iu, nm_find u idx = Some iu /\
    forall v, In v sucs -> exists iv, nm_find v idx = Some iv /\ iu < iv.

(** A row is a sink when none of its destinations remains in the graph. *)
Local Definition sink_in (g : list (name * list name)) (e : name * list name) : bool :=
  negb (existsb (fun s => Validate.mem s (map fst g)) (snd e)).

(** An internal edge from a maximal source would lead to a still larger source. *)
Local Lemma ranked_sink : forall idx e es, ranked_edges idx (e :: es) ->
  exists s, In s (e :: es) /\ sink_in (e :: es) s = true.
Proof.
  intros idx e es Edges. set (g := e :: es) in *.
  set (rank := fun p : name * list name =>
    match nm_find (fst p) idx with Some i => i | None => 0 end).
  destruct (maximum_member _ rank e es) as ([u sucs] & Member & Max).
  fold g in Member, Max. exists (u, sucs). split; auto.
  destruct (Edges _ _ Member) as (iu & U & Next). unfold sink_in. cbn [snd].
  destruct (existsb (fun s => Validate.mem s (map fst g)) sucs) eqn:E; [|reflexivity].
  apply existsb_exists in E. destruct E as (v & V & Internal). apply mem_names in Internal.
  apply in_map_iff in Internal. destruct Internal as ([w ws] & Eq & W). cbn in Eq. subst w.
  destruct (Next _ V) as (iv & Find & Lt). specialize (Max _ W).
  unfold rank in Max. cbn [fst] in Max. rewrite U, Find in Max. lia.
Qed.

(** A finite graph with strictly increasing edge ranks peels within its length. *)
Lemma peel_dag : forall (idx : nmap Z) (g : list (name * list name)) (fuel : nat),
  (length g <= fuel)%nat ->
  (forall u sucs, In (u, sucs) g -> exists iu, nm_find u idx = Some iu /\
    forall v, In v sucs -> exists iv, nm_find v idx = Some iv /\ iu < iv) ->
  Validate.peel fuel g = true.
Proof.
  intros idx g fuel. revert g. induction fuel as [|fuel IH]; intros [|e es] Bound Edges;
    try reflexivity; [cbn in Bound; lia|].
  set (g := e :: es) in *. destruct (ranked_sink idx e es Edges) as (s & Member & Sink).
  fold g in Member, Sink.
  set (sinks := filter (sink_in g) g).
  assert (InSinks : In s sinks) by (apply filter_In; auto).
  set (keep := fun p : name * list name => negb (Validate.mem (fst p) (map fst sinks))).
  change (match sinks with [] => false | _ :: _ => peel fuel (filter keep g) end = true).
  assert (Drop : keep s = false).
  { unfold keep. apply negb_false_iff. apply mem_names. now apply in_map. }
  destruct sinks; [contradiction|]. apply IH.
  - pose proof (filter_drops_member _ _ _ _ Member Drop). lia.
  - intros u sucs Hin. apply filter_In in Hin. apply Edges. tauto.
Qed.

(** ## From rewritten blocks to cycle coverage *)

(** The decoder preserves the label at each position in the block list.
    This correspondence proves that every indexed destination occurs in
    the output, while the jump proof supplies the rank of each plain edge. *)

(** A decoded block retains the input label and satisfies the forward-edge
    guarantee at that label's index. *)
Local Definition block_facts (idx : nmap Z) (b : term) (db : block) : Prop :=
  (exists phis insts j, b = TApp "block" [b_label db; phis; insts; j]) /\
  exists i, nm_find (b_label db) idx = Some i /\
    forall t, In t (jump_targets (b_jump db)) -> forward_edge idx i t.

(** Indexing, rewriting and decoding visit the blocks in the same order. *)
Local Lemma rewritten_block_facts : forall bs filc drop names fuel idx k m n bs' dbs,
  label_index k bs m = Some idx ->
  pizlonated_blocks filc drop names fuel idx k n bs = Some bs' ->
  map_option dblock bs' = Some dbs -> Forall2 (block_facts idx) bs dbs.
Proof.
  induction bs as [|b bs IH]; intros filc drop names fuel idx k m n bs' dbs Index Run Decode.
  - injection Run as <-. injection Decode as <-. constructor.
  - destruct (index_cons _ _ _ _ _ Index) as (l & phis & insts & j & -> & Free & Tail).
    destruct insts as [z|s|f args|ins]; try discriminate.
    cbn [pizlonated_blocks String.eqb Ascii.eqb Bool.eqb andb] in Run.
    match type of Run with
    | context [let '(_, _) := ?p in _] => destruct p as [next out]
    end.
    destruct (polled_jump idx k j) as [j'|] eqn:Jump; [|discriminate].
    destruct (pizlonated_blocks filc drop names fuel idx (k + 1) next bs) as [rest|] eqn:Rest;
      [|discriminate]. injection Run as <-.
    destruct phis as [z|s|f args|ps]; try discriminate.
    cbn [map_option dblock] in Decode.
    destruct (map_option dphi ps) as [ds|]; [|discriminate].
    destruct (map_option dinst out) as [di|]; [|discriminate].
    destruct (djump j') as [dj|] eqn:J; [|discriminate].
    destruct (map_option dblock rest) as [dbrest|] eqn:D; [|discriminate].
    injection Decode as <-. constructor.
    + unfold block_facts. cbn [b_label b_jump]. split; [eauto|].
      exists k. split.
      * eapply index_preserves; [exact Tail|]. rewrite nm_find_add.
        unfold name_eqb. now rewrite term_eqb_refl.
      * intros t Hin. exact (polled_jump_djump_rev _ _ _ _ _ Jump J t Hin).
    + eapply IH; eauto.
Qed.

(** Every input block position contributes its label to the decoded list. *)
Local Lemma block_label_present : forall idx bs dbs, Forall2 (block_facts idx) bs dbs ->
  forall pos l phis insts j, nth_error bs pos = Some (TApp "block" [l; phis; insts; j]) ->
  In l (map b_label dbs).
Proof.
  intros idx bs dbs P. induction P as [|b db bs dbs Facts P IH];
    intros [|pos] l phis insts j At; try discriminate.
  - destruct Facts as [(p & i & t & ->) _]. left. now injection At.
  - right. eapply IH; eauto.
Qed.

(** The validator keeps just the plain successors of each block when testing cycles. *)
Local Definition unpolled_row (b : block) : name * list name :=
  (b_label b, map edge_label (filter (fun t => negb (is_poll t)) (jump_targets (b_jump b)))).

(** The per-block guarantees supply increasing ranks for every edge the validator keeps. *)
Local Lemma decoded_ranks : forall idx bs dbs, Forall2 (block_facts idx) bs dbs ->
  ranked_edges idx (map unpolled_row dbs).
Proof.
  intros idx bs dbs P. induction P as [|b db bs dbs Facts P IH]; intros u sucs Member.
  - contradiction.
  - destruct Member as [E|Member]; [|now apply IH].
    unfold unpolled_row in E. injection E as <- <-.
    destruct Facts as [_ (i & Find & Next)]. exists i. split; auto.
    intros v Hin. apply in_map_iff in Hin. destruct Hin as (t & <- & Ht).
    apply filter_In in Ht. destruct Ht as [Target Poll]. apply negb_true_iff in Poll.
    exact (Next t Target Poll).
Qed.

(** Every successfully rewritten and decoded block list passes the
    validator's cycle check, regardless of the input instructions. *)
Theorem pizlonated_blocks_polls_every_cycle : forall filc drop names fuel idx n0 bs bs' dbs' f',
  Pizlonate.label_index 0 bs nm_empty = Some idx ->
  Pizlonate.pizlonated_blocks filc drop names fuel idx 0 n0 bs = Some bs' ->
  map_option Transport.dblock bs' = Some dbs' -> fn_blocks f' = dbs' ->
  Validate.polls_every_cycle f' = true.
Proof.
  intros filc drop names fuel idx n0 bs bs' dbs' f' Index Run Decode Blocks.
  pose proof (rewritten_block_facts _ _ _ _ _ _ _ _ _ _ _ Index Run Decode) as Facts.
  pose proof (decoded_ranks _ _ _ Facts) as Ranks.
  unfold polls_every_cycle. rewrite Blocks. fold unpolled_row.
  apply andb_true_iff. split.
  - apply forallb_forall. intros [u sucs] Member. apply forallb_forall. intros v Edge.
    destruct (Ranks _ _ Member) as (iu & U & Next). destruct (Next _ Edge) as (iv & Find & Lt).
    destruct (label_index_find_inv _ _ _ _ _ _ Index Find) as [Empty|(pos & p & i & j & At)].
    + rewrite nm_find_empty in Empty. discriminate.
    + apply mem_names. rewrite map_map. exact (block_label_present _ _ _ Facts _ _ _ _ _ (proj1 At)).
  - eapply peel_dag; [lia|exact Ranks].
Qed.
