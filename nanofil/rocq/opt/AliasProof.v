(** The address analysis describes a [[temporary]] by a base word and a
    signed byte offset. This module proves that the description recovers the
    temporary's address modulo the word size. For pointers it also recovers
    the entire [[capability]] from the base. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Values Ops Semantics Cfg.
From Backend Require Import Order Pizlonate TermCfg Escape.
From Opt Require Import Provenance OptIr Alias.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ## Signed offsets

    The analysis stores the signed representative of a residue. The machine
    uses its unsigned representative when it computes an address. *)

(** The signed representative fits in the interval for a 64-bit displacement. *)
Theorem wrap_signed64_bounds : forall off delta,
  -9223372036854775808 <= wrap_signed64 off delta < 9223372036854775808.
Proof.
  intros off delta. unfold wrap_signed64.
  pose proof (Z.mod_pos_bound (off + delta) 18446744073709551616 ltac:(lia)).
  destruct (9223372036854775808 <=? _)%Z eqn:Hsign.
  - apply Z.leb_le in Hsign. lia.
  - apply Z.leb_gt in Hsign. lia.
Qed.

(** Selecting the signed representative preserves all 64 address bits. *)
Theorem wrap_signed64_mod : forall off delta,
  wrap_signed64 off delta mod 18446744073709551616 =
  (off + delta) mod 18446744073709551616.
Proof.
  intros off delta. unfold wrap_signed64.
  destruct (9223372036854775808 <=? _)%Z.
  - rewrite Zminus_mod, Z.mod_same, Z.sub_0_r by lia.
    repeat rewrite Z.mod_mod by lia. reflexivity.
  - apply Z.mod_mod. lia.
Qed.

(** Successive wraps and a single wrap of the sum give the same signed offset. *)
Theorem wrap_signed64_add : forall a b c,
  wrap_signed64 (wrap_signed64 a b) c = wrap_signed64 a (b + c).
Proof.
  intros a b c.
  assert (H : (wrap_signed64 a b + c) mod 18446744073709551616 =
              (a + (b + c)) mod 18446744073709551616).
  { rewrite <- Z.add_mod_idemp_l by lia. rewrite wrap_signed64_mod.
    rewrite Z.add_mod_idemp_l, Z.add_assoc by lia. reflexivity. }
  unfold wrap_signed64 at 1 3. rewrite H. reflexivity.
Qed.

(** ## Addresses of run-time words

    An integer base contributes its low 64 bits to the result. A pointer
    base supplies both its address bits and the capability of the result. *)

(** A displacement relates two integer words or two pointers of the given
    class. A pointer displacement preserves the capability exactly. *)
Inductive addr_word_rel : term -> word -> word -> Z -> Prop :=
| addr_int : forall a b off,
    b = (a + off) mod 2 ^ 64 ->
    addr_word_rel (TAtom "l") (WInt a) (WInt b) off
| addr_ptr : forall p q off,
    ptr_cap q = ptr_cap p ->
    ptr_addr q = (ptr_addr p + off) mod 2 ^ 64 ->
    addr_word_rel (TAtom "p") (WPtr p) (WPtr q) off.

(** At integer class the relation describes exactly the two word payloads
    and their modular sum. *)
Lemma addr_word_rel_l : forall bw w off,
  addr_word_rel (TAtom "l") bw w off <->
  exists a b, bw = WInt a /\ w = WInt b /\ b = (a + off) mod 2 ^ 64.
Proof.
  intros bw w off. split.
  - intros H. inversion H; subst. eauto.
  - intros (a & b & -> & -> & H). constructor. exact H.
Qed.

(** At pointer class the relation identifies both pointers, equates their
    capabilities and determines the destination address. *)
Lemma addr_word_rel_p : forall bw w off,
  addr_word_rel (TAtom "p") bw w off <->
  exists p q, bw = WPtr p /\ w = WPtr q /\ ptr_cap q = ptr_cap p /\
              ptr_addr q = (ptr_addr p + off) mod 2 ^ 64.
Proof.
  intros bw w off. split.
  - intros H. inversion H; subst. eauto 7.
  - intros (p & q & -> & -> & Hcap & Haddr). constructor; assumption.
Qed.

(** Adding two displacements in address bits agrees with wrapping their sum. *)
Lemma address_add_wrap : forall a off delta,
  ((a + off) mod 2 ^ 64 + delta) mod 2 ^ 64 =
  (a + wrap_signed64 off delta) mod 2 ^ 64.
Proof.
  intros. change (2 ^ 64) with 18446744073709551616.
  rewrite Z.add_mod_idemp_l, <- (Z.add_mod_idemp_r a (wrap_signed64 off delta)) by lia.
  rewrite wrap_signed64_mod, Z.add_mod_idemp_r, Z.add_assoc by lia. reflexivity.
Qed.

(** Two successive address displacements compose at either address class. *)
Theorem addr_word_rel_trans : forall k bw ws wd off delta,
  addr_word_rel k bw ws off -> addr_word_rel k ws wd delta ->
  addr_word_rel k bw wd (wrap_signed64 off delta).
Proof.
  intros k bw ws wd off delta Hfirst Hnext.
  destruct Hfirst; inversion Hnext; subst; constructor;
    try congruence; rewrite <- address_add_wrap; congruence.
Qed.

(** ## Instructions that produce an offset

    The analysis accepts copies and arithmetic with one literal. An integer
    addition can put the literal first, while pointer arithmetic takes the
    pointer as its first operand. *)

(** A successful temporary lookup identifies the original operand. *)
Lemma tmp_name_single : forall v s, tmp_name v = [s] -> v = tmp s.
Proof.
  intros [n|a|f xs|ts] s H; try discriminate.
  destruct xs as [|x [|y xs]]; try discriminate.
  unfold tmp_name in H. destruct (String.eqb f "tmp") eqn:E; try discriminate.
  apply String.eqb_eq in E. inversion H. subst. reflexivity.
Qed.

(** A successful literal lookup identifies the original integer constant. *)
Lemma const_int_some : forall v n,
  const_int v = Some n -> v = TApp "const" [TInt n].
Proof.
  intros [z|a|f xs|ts] n H; try discriminate.
  destruct xs as [|[z|a|g ys|ts] [|y xs]]; try discriminate.
  unfold const_int in H. destruct (String.eqb f "const") eqn:E; try discriminate.
  apply String.eqb_eq in E. inversion H. subst. reflexivity.
Qed.

(** An atom test identifies the entire class term. *)
Lemma address_atom_true : forall a k, is_atom a k = true -> k = TAtom a.
Proof.
  intros a [n|b|f xs|ts] H; try discriminate.
  apply String.eqb_eq in H. congruence.
Qed.

(** Each constructor records the actual operand order and the signed
    contribution of the literal to the displacement. *)
Inductive offset_instruction (s : term) : term -> term -> list term -> Z -> Prop :=
| offset_copy : forall k, offset_instruction s k (TAtom "copy") [tmp s] 0
| offset_add : forall k n, offset_instruction s k (TAtom "add")
    [tmp s; TApp "const" [TInt n]] n
| offset_add_left : forall n, offset_instruction s (TAtom "l") (TAtom "add")
    [TApp "const" [TInt n]; tmp s] n
| offset_sub : forall k n, offset_instruction s k (TAtom "sub")
    [tmp s; TApp "const" [TInt n]] (- n).

(** An offset returned by the recognizer has a source of the same class
    and comes from one of the four instruction forms. *)
Lemma address_offset_instruction : forall op args k by_temp s delta,
  address_offset (SrcLet op args) k by_temp = Some (s, delta) ->
  (exists src, nm_find s by_temp = Some (k, src)) /\
  offset_instruction s k op args delta.
Proof.
  intros op args k by_temp s delta H.
  destruct op as [z|a|f xs|ts]; try discriminate.
  unfold address_offset in H.
  repeat match type of H with
  | context [match ?v with _ => _ end] => destruct v eqn:? in H
  end; try discriminate; inversion H; subst;
  repeat match goal with
  | E : context [match nm_find ?x ?m with _ => _ end] |- _ =>
      destruct (nm_find x m) as [[? ?]|] eqn:? in E; try discriminate
  end;
  repeat match goal with
  | E : String.eqb _ _ = true |- _ => apply String.eqb_eq in E
  | E : term_eqb _ _ = true |- _ => apply term_eqb_eq in E
  | E : is_atom _ _ = true |- _ => apply address_atom_true in E
  | E : tmp_name _ = [_] |- _ => apply tmp_name_single in E
  | E : const_int _ = Some _ |- _ => apply const_int_some in E
  end; subst.
  all: split.
  all: try solve [eexists; eassumption].
  all: try first [apply offset_copy | apply offset_add | apply offset_add_left | apply offset_sub].
  discriminate.
Qed.

(** The evaluator reads the source temporary from the execution and truncates
    integer literals to their 64-bit operand class. *)
Definition address_operand (eval : term -> option word) (v : term) : option word :=
  match tmp_name v with
  | [s] => eval s
  | _ => match const_int v with
         | Some n => Some (WInt (n mod 2 ^ 64))
         | None => None
         end
  end.

(** The evaluator passes the operands in program order to Nanofil's copy,
    addition, or subtraction operation. *)
Definition eval_address_let (eval : term -> option word) (k op : term)
    (args : list term) : option word :=
  let c := if is_atom "l" k then L else P in
  match map_option (address_operand eval) args with
  | Some ws =>
      if is_atom "copy" op then alu Copy c ws
      else if is_atom "add" op then additive_res c Add ws
      else if is_atom "sub" op then additive_res c Sub ws
      else None
  | None => None
  end.

(** Integer sources hold unsigned word values. Pointer arithmetic accepts
    any pointer address, while copying requires the address to be reduced. *)
Inductive address_source_word : term -> term -> word -> Prop :=
| source_int : forall op n, 0 <= n < 2 ^ 64 ->
    address_source_word (TAtom "l") op (WInt n)
| source_ptr : forall op p,
    (op = TAtom "copy" -> ptr_addr p mod 2 ^ 64 = ptr_addr p) ->
    address_source_word (TAtom "p") op (WPtr p).

(** Every recognized instruction computes the stated displacement and keeps
    the source pointer's capability, including when the address wraps. *)
Theorem address_offset_step_sound : forall op args k by_temp s delta eval ws,
  address_offset (SrcLet op args) k by_temp = Some (s, delta) ->
  is_address_class k = true ->
  eval s = Some ws -> address_source_word k op ws ->
  exists wd, eval_address_let eval k op args = Some wd /\
             addr_word_rel k ws wd delta.
Proof.
  intros op args k by_temp s delta eval ws Hstep _ Hread Hword.
  destruct (address_offset_instruction _ _ _ _ _ _ Hstep) as [_ Hinst].
  destruct Hinst; inversion Hword; subst;
    cbv beta iota zeta delta [eval_address_let map_option address_operand tmp_name
      tmp const_int is_atom String.eqb Ascii.eqb Bool.eqb]; rewrite Hread.
  all: eexists; split; [reflexivity | constructor].
  all: cbn [ptr_addr ptr_cap]; try reflexivity.
  - rewrite Z.add_0_r, Z.mod_small by assumption. reflexivity.
  - rewrite Z.add_0_r. symmetry. auto.
  - apply Z.add_mod_idemp_r. lia.
  - apply Z.add_mod_idemp_r. lia.
  - rewrite Z.add_comm. apply Z.add_mod_idemp_r. lia.
  - rewrite <- Z.add_opp_r. apply Zminus_mod_idemp_r.
  - rewrite <- Z.add_opp_r. apply Zminus_mod_idemp_r.
Qed.

(** ## Propagation from a base

    The worklist carries the same descriptions as the fact table. Each
    update extends one description along an instruction edge and writes it
    to both places. *)

(** A sound entry names its class, its base word and a signed displacement
    that recovers the word observed at the destination. *)
Definition fact_sound (eval base_word : term -> option word) (d addr : term) : Prop :=
  exists k base off,
    addr = TApp "addr" [k; base; TInt off] /\ is_address_class k = true /\
    -9223372036854775808 <= off < 9223372036854775808 /\
    exists bw wd, base_word base = Some bw /\ eval d = Some wd /\
                  addr_word_rel k bw wd off.

(** Every successful lookup in a sound table returns a sound entry. *)
Definition facts_sound (eval base_word : term -> option word) (facts : nmap term) : Prop :=
  forall d addr, nm_find d facts = Some addr -> fact_sound eval base_word d addr.

(** A list traversal preserves an invariant if each input element preserves
    it at every intermediate accumulator. *)
Lemma fold_preserves : forall (A B : Type) (step : B -> A -> B) (I : B -> Prop)
    xs st, I st -> (forall x acc, In x xs -> I acc -> I (step acc x)) ->
    I (fold_left step xs st).
Proof.
  intros A B step I xs. induction xs as [|x xs IH]; intros st Hinit Hstep.
  - exact Hinit.
  - apply IH. apply Hstep; simpl; auto.
    intros y acc Hin. apply Hstep. right. exact Hin.
Qed.

(** Writing a sound entry preserves the meaning of every lookup, including
    a lookup that previously returned another value for the same name. *)
Lemma facts_sound_add : forall eval base_word facts d addr,
  fact_sound eval base_word d addr -> facts_sound eval base_word facts ->
  facts_sound eval base_word (nm_add d addr facts).
Proof.
  intros eval base_word facts d addr Hentry Htable x v Hfind.
  rewrite nm_find_add in Hfind. destruct (name_eqb x d) eqn:E.
  - apply term_eqb_eq in E. inversion Hfind. subst. assumption.
  - eapply Htable. exact Hfind.
Qed.

(** A sound edge extends every known displacement from its source and
    preserves the interpretation of the original base. *)
Definition edge_sound (eval : term -> option word) (s d : term) (delta : Z) : Prop :=
  forall k bw ws off, eval s = Some ws -> addr_word_rel k bw ws off ->
    exists wd, eval d = Some wd /\ addr_word_rel k bw wd (wrap_signed64 off delta).

(** Propagation preserves soundness for every fuel bound, even when the
    worklist still holds entries at the end of the traversal. *)
Theorem pending_facts_sound : forall fuel pending users facts eval base_word,
  (forall s addr, In (s, addr) pending -> fact_sound eval base_word s addr) ->
  facts_sound eval base_word facts ->
  (forall s es d delta, nm_find s users = Some es -> In (d, delta) es ->
                        edge_sound eval s d delta) ->
  facts_sound eval base_word (pending_facts fuel pending users facts).
Proof.
  induction fuel as [|fuel IH]; intros pending users facts eval base_word Hp Hf He;
    [exact Hf | destruct pending as [|[s addr] rest]; [exact Hf |]].
  destruct (Hp s addr (or_introl eq_refl)) as
    (k & base & off & -> & Hk & Hbounds & bw & ws & Hb & Hs & Hrel).
  cbn [pending_facts].
  set (edges := match nm_find s users with Some es => es | None => [] end).
  assert (Hedges : forall d delta, In (d, delta) edges -> edge_sound eval s d delta).
  { unfold edges. destruct (nm_find s users) as [es|] eqn:E.
    - intros. eapply He; eassumption.
    - intros d delta H. contradiction. }
  set (I := fun st : nmap term * list (term * term) =>
    facts_sound eval base_word (fst st) /\
    forall d v, In (d, v) (snd st) -> fact_sound eval base_word d v).
  match goal with
  | |- context [fold_left ?step edges ?st] =>
      assert (Hfold : I (fold_left step edges st))
  end.
  { apply fold_preserves.
    - split; [exact Hf |]. intros d v Hin. apply Hp. right. exact Hin.
    - intros [d delta] [fs pend] Hin [Hfs Hpend]. cbn [fst snd] in *.
      destruct (Hedges d delta Hin k bw ws off Hs Hrel) as (wd & Hd & Hnext).
      assert (Hentry : fact_sound eval base_word d
        (TApp "addr" [k; base; TInt (wrap_signed64 off delta)])).
      { exists k, base, (wrap_signed64 off delta). split; [reflexivity |].
        split; [exact Hk |]. split; [apply wrap_signed64_bounds |].
        exists bw, wd. auto. }
      split; [apply facts_sound_add; assumption |].
      intros x v [E | Htail]; [inversion E; subst; assumption | auto]. }
  unfold I in Hfold. destruct (fold_left _ edges _) as [fs pend].
  destruct Hfold as [Hfs Hpend]. apply IH; assumption.
Qed.

(** ## Building the table of users

    The analysis sorts edges by source and collects each source's users into
    a list. To recover the instruction behind an edge, we trace a lookup
    through the name map, the groups and the merge sort. *)

(** A value found in a map built from pairs occurs with its key in the input. *)
Lemma nm_of_list_member : forall (A : Type) (ps : list (term * A)) k v,
  nm_find k (nm_of_list ps) = Some v -> In (k, v) ps.
Proof.
  intros A ps. unfold nm_of_list.
  apply (fold_preserves _ _ _ (fun m => forall k v, nm_find k m = Some v ->
                                                    In (k, v) ps)).
  - intros k v H. rewrite nm_find_empty in H. discriminate.
  - intros [x w] m Hin IH k v H. rewrite nm_find_add in H. cbn [fst snd] in H.
    destruct (name_eqb k x) eqn:E.
    + apply term_eqb_eq in E. inversion H. subst. assumption.
    + now apply IH.
Qed.

Section Sorting.
  Context {A : Type} (cmp : A -> A -> comparison) (R : A -> Prop).

  (** Merging two runs preserves any property shared by all their elements,
      even for a merge that stops early. *)
  Lemma merge_steps_forall : forall n xs ys, Forall R xs -> Forall R ys ->
    Forall R (merge_steps cmp n xs ys).
  Proof.
    induction n as [|n IH]; intros [|x xs] [|y ys] Hx Hy;
      cbn [merge_steps]; try assumption.
    inversion Hx; inversion Hy; subst.
    destruct (cmp x y); constructor; auto.
  Qed.

  (** An occupied stack slot carries the element property through its run.
      An empty slot places no condition on the stack. *)
  Definition run_valid (r : option (list A)) : Prop :=
    match r with Some xs => Forall R xs | None => True end.

  (** Pushing a run preserves the property throughout the stack of runs. *)
  Lemma push_run_forall : forall stack run,
    Forall run_valid stack ->
    Forall R run ->
    Forall run_valid (push_run cmp stack run).
  Proof.
    induction stack as [|[r|] rs IH]; intros run Hstack Hrun;
      inversion Hstack; subst; cbn [push_run]; constructor;
      cbn [run_valid] in *; auto.
    apply IH; auto. apply merge_steps_forall; assumption.
  Qed.

  (** Sorting a list preserves every property shared by its elements. *)
  Lemma msort_forall : forall xs, Forall R xs -> Forall R (msort cmp xs).
  Proof.
    intros xs Hxs. unfold msort.
    assert (Hstack : Forall run_valid (fold_left
      (fun stack x => push_run cmp stack [x]) xs [])).
    { apply fold_preserves; [constructor |].
      intros x stack Hin Hvalid. apply push_run_forall; auto.
      constructor; [now apply (proj1 (Forall_forall _ _) Hxs) | constructor]. }
    induction Hstack as [|[r|] rs Hr Hrs IH]; cbn [merge_runs]; auto.
    apply merge_steps_forall; assumption.
  Qed.
End Sorting.

(** Grouping adjacent equal keys preserves each value's relation to its key. *)
Lemma group_sorted_forall : forall (A : Type) (R : term -> A -> Prop) ps,
  Forall (fun p => R (fst p) (snd p)) ps ->
  Forall (fun p => Forall (R (fst p)) (snd p)) (group_sorted_pairs ps).
Proof.
  intros A R ps H. induction H as [|[k v] ps Hv Hps IH]; [constructor |].
  cbn [group_sorted_pairs]. destruct (group_sorted_pairs ps) as [|[j vs] gs].
  - repeat constructor; assumption.
  - inversion IH; subst. destruct (term_eqb k j) eqn:E.
    + apply term_eqb_eq in E. subst. repeat constructor; assumption.
    + constructor; [repeat constructor; assumption | exact IH].
Qed.

(** Looking up a user in the grouped map recovers the original source and
    destination pair, even when several users share a source. *)
Lemma grouped_user_member : forall (A : Type) (ps : list (term * A)) s es e,
  nm_find s (nm_of_list (group_pairs_by_key ps)) = Some es ->
  In e es -> In (s, e) ps.
Proof.
  intros A ps s es e Hfind Hin. apply nm_of_list_member in Hfind.
  assert (H : Forall (fun p => Forall (fun x => In (fst p, x) ps) (snd p))
                     (group_pairs_by_key ps)).
  { apply (group_sorted_forall _ (fun k v => In (k, v) ps)).
    apply msort_forall. apply Forall_forall. intros [k v] H. exact H. }
  apply (proj1 (Forall_forall _ _) H) in Hfind. cbn [fst snd] in Hfind.
  now apply (proj1 (Forall_forall _ _) Hfind).
Qed.

(** ## Interpreting a function

    An execution supplies words for the bases that start propagation and
    respects the defining instructions of the temporaries it evaluates.
    These conditions refer to the function's definitions before the analysis
    sorts any edges or propagates any facts. *)

(** The word constructor distinguishes the two address classes, including
    when a pointer and an integer have the same address bits. *)
Definition address_word_class (w : word) : option term :=
  match w with
  | WInt _ => Some (TAtom "l")
  | WPtr _ => Some (TAtom "p")
  | WLimit _ _ => None
  end.

(** A word reached from a base has the recorded class and a reduced address.
    It can therefore serve as the source of any supported instruction. *)
Lemma related_source_word : forall k bw ws off op,
  addr_word_rel k bw ws off ->
  address_word_class ws = Some k /\ address_source_word k op ws.
Proof.
  intros k bw ws off op H. destruct H as [a b off Hb|p q off Hcap Haddr];
    split; try reflexivity.
  - subst. constructor. apply Z.mod_pos_bound. lia.
  - constructor. intros _. rewrite Haddr. apply Z.mod_mod. lia.
Qed.

(** A base observed at its own definition has zero displacement when its
    address already fits in a word. *)
Lemma base_word_zero : forall k w, address_source_word k (TAtom "copy") w ->
  is_address_class k = true /\ addr_word_rel k w w 0.
Proof.
  intros k w H. inversion H; subst; split; try reflexivity;
    constructor; try reflexivity; rewrite Z.add_0_r.
  - symmetry. apply Z.mod_small. assumption.
  - symmetry. auto.
Qed.

(** An interpretation assigns each observed definition a word of its class.
    At a base it supplies the same reduced word for the base and its temporary.
    At a recognized use it agrees with evaluation of the defining instruction. *)
Definition defs_consistent (eval base_word : term -> option word)
    (defs : list (term * (term * addr_source))) : Prop :=
  (forall d k src w, In (d, (k, src)) defs -> eval d = Some w ->
                     address_word_class w = Some k) /\
  (forall d k src base, In (d, (k, src)) defs ->
     address_base src d k (nm_of_list defs) = Some base ->
     exists w, base_word base = Some w /\ eval d = Some w /\
               address_source_word k (TAtom "copy") w) /\
  (forall d k op args s delta wd, In (d, (k, SrcLet op args)) defs ->
     address_offset (SrcLet op args) k (nm_of_list defs) = Some (s, delta) ->
     eval_address_let eval k op args = Some wd -> eval d = Some wd).

(** The base constructor contributes precisely the sound zero-offset seeds
    required by the worklist. *)
Lemma definition_seed_sound : forall eval base_word defs d v,
  defs_consistent eval base_word defs ->
  In (d, v) (flat_map (fun p =>
    let '(x, (k, src)) := p in
    match address_base src x k (nm_of_list defs) with
    | Some base => [(x, TApp "addr" [k; base; TInt 0])]
    | None => []
    end) defs) ->
  fact_sound eval base_word d v.
Proof.
  intros eval base_word defs d v [_ [Hbase _]] Hin.
  apply in_flat_map in Hin. destruct Hin as ([x [k src]] & Hdef & Hin).
  destruct (address_base src x k (nm_of_list defs)) as [base|] eqn:E;
    cbn in Hin; [|contradiction].
  destruct Hin as [Heq|[]]. inversion Heq; subst.
  destruct (Hbase _ _ _ _ Hdef E) as (w & Hb & Hd & Hw).
  destruct (base_word_zero _ _ Hw) as [Hk Hr].
  exists k, base, 0. split; [reflexivity |]. split; [exact Hk |].
  split; [lia |]. exists w, w. auto.
Qed.

(** Each entry in the table of users traces back to a recognized instruction.
    Its source lookup and the source word select the same address class. *)
Lemma definition_user_sound : forall eval base_word defs s es d delta,
  defs_consistent eval base_word defs ->
  nm_find s (nm_of_list (group_pairs_by_key (flat_map (fun p =>
    let '(x, (k, src)) := p in
    match address_offset src k (nm_of_list defs) with
    | Some (y, n) => [(y, (x, n))]
    | None => []
    end) defs))) = Some es ->
  In (d, delta) es -> edge_sound eval s d delta.
Proof.
  intros eval base_word defs s es d delta [Htyped [_ Heval]] Hfind Hin.
  pose proof (grouped_user_member _ _ _ _ _ Hfind Hin) as Hpair.
  apply in_flat_map in Hpair. destruct Hpair as ([x [k src]] & Hdef & Hpair).
  destruct src as [| |op args]; try contradiction.
  destruct (address_offset (SrcLet op args) k (nm_of_list defs)) as [[y n]|] eqn:E;
    cbn in Hpair; [|contradiction].
  destruct Hpair as [Heq|[]]. inversion Heq; subst.
  destruct (address_offset_instruction _ _ _ _ _ _ E) as [[src Hsrc] _].
  apply nm_of_list_member in Hsrc.
  intros kc bw ws off Hs Hr.
  destruct (related_source_word _ _ _ _ op Hr) as [Hclass Hw].
  pose proof (Htyped _ _ _ _ Hsrc Hs) as Hk. rewrite Hclass in Hk.
  inversion Hk; subst kc.
  assert (Haddr : is_address_class k = true) by (destruct Hr; reflexivity).
  destruct (address_offset_step_sound _ _ _ _ _ _ _ _ E Haddr Hs Hw)
    as (wd & Hstep & Hdelta).
  exists wd. split; [eapply Heval; eassumption |].
  eapply addr_word_rel_trans; eassumption.
Qed.

(** An interpretation of a function respects the address definitions in its
    decoded blocks and parameter list. *)
Definition function_consistent (fn : term) (eval base_word : term -> option word) : Prop :=
  forall name linkage ret params blocks bs,
    fn = TApp "func" [name; linkage; ret; TList params; TList blocks] ->
    map_option term_block blocks = Some bs ->
    defs_consistent eval base_word (address_defs params bs).

(** Every entry returned for a function gives the exact modular displacement
    and, at pointer class, the exact capability of its base. *)
Theorem alias_facts_sound : forall fn facts eval base_word,
  alias_facts fn = Some facts -> function_consistent fn eval base_word ->
  forall d addr, nm_find d facts = Some addr ->
    exists k base off,
      addr = TApp "addr" [k; base; TInt off] /\ is_address_class k = true /\
      - (2 ^ 63) <= off < 2 ^ 63 /\
      exists bw wd, base_word base = Some bw /\ eval d = Some wd /\
                    addr_word_rel k bw wd off.
Proof.
  intros fn facts eval base_word Hfn Hconsistent.
  change (facts_sound eval base_word facts).
  destruct fn as [z|a|f xs|ts]; try discriminate.
  destruct xs as [|name [|linkage [|ret [|ps xs]]]]; try discriminate.
  destruct ps as [z|a|g ys|params]; try discriminate.
  destruct xs as [|b xs]; try discriminate.
  destruct b as [z|a|g ys|blocks]; try discriminate.
  destruct xs as [|extra rest]; try discriminate.
  unfold alias_facts in Hfn.
  destruct (String.eqb f "func") eqn:Ef; [|discriminate].
  apply String.eqb_eq in Ef. subst f.
  destruct (map_option term_block blocks) as [bs|] eqn:Eb; try discriminate.
  specialize (Hconsistent _ _ _ _ _ _ eq_refl Eb).
  destruct (term_cfg bs) as [g|]; try discriminate.
  destruct (cfg_idoms g) as [idom|]; try discriminate.
  destruct (negb (strict_ssa (def_counts params bs) params bs g idom)).
  - inversion Hfn; subst. intros d v H. rewrite nm_find_empty in H. discriminate.
  - cbv beta iota zeta delta [negb] in Hfn.
    match type of Hfn with Some ?table = Some facts =>
      replace facts with table by congruence
    end. apply pending_facts_sound.
    + intros. eapply definition_seed_sound; eassumption.
    + intros d v H. apply nm_of_list_member in H.
      eapply definition_seed_sound; eassumption.
    + intros. eapply definition_user_sound; eassumption.
Qed.
