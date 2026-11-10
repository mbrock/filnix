(** The term half of NFB's round trip (docs/nfb.md): a module that
    Transport.v's [decode_module] reads from any term is read back
    from the term Nfb.v's [enc_module] writes for it
    ([decode_enc_module]), and no item of that term is a context item
    ([enc_module_no_context]).

    Most of the syntax is canonical: for every decoder of Transport.v
    but the data item's, what it reads from a term t is written back
    by its encoder as t itself ([dinst_enc], [dblock_enc], [dfunc_enc]
    and the others below). So [enc_module m] would be t with its
    context items dropped, except for one construct: a string item
    whose character is an overlong two-byte UTF-8 atom, such as the
    atom of the bytes 0xC0 0x80. [char_code] reads it as the code 0,
    which [code_char] writes back as the one-byte atom. Then
    [enc_module m] is not the term m was read from
    ([strong_form_fails]). The term is still read back as the same
    module, because [char_code] reads every code [code_char] writes
    ([char_code_code_char]), and that is all [decode_enc_module]
    needs. *)

From Stdlib Require Import String ZArith List Bool Ascii Lia.
From Nanofil Require Import Term Syntax Semantics Validate Transport Cfg.
From Backend Require Import IrTerm NfbTerm Nfb.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** ## Taking a decoder apart *)

(** Turn a fact E, that a decoder read a term, into the term itself,
    using one of the earlier lemmas in the context. *)
Ltac use_inv E :=
  match goal with I : _ |- _ => apply I in E; match type of E with _ = _ => idtac end end; subst.

(** Split the hypothesis H on what blocks its match x: a variable, a
    string comparison, a list length, or a decoder's result. *)
Ltac split_on H x :=
  lazymatch x with
  | match ?y with _ => _ end => split_on H y
  | _ =>
      first [ is_var x; destruct x; simpl in H
            | match x with context [String.eqb ?a ?s] =>
                is_var a; let E := fresh "E" in
                destruct (String.eqb a s) eqn:E; [apply String.eqb_eq in E; subst a | clear E]; simpl in H end
            | match x with context [length ?xs] => is_var xs; destruct xs; simpl in H end
            | let E := fresh "E" in destruct x eqn:E; try use_inv E; simpl in H ]
  end.

(** One step of reading back a hypothesis H that a decoder gave
    [Some]: refute it, take apart what blocks it, or take its value. *)
Ltac dstep H :=
  lazymatch type of H with
  | None = Some _ => discriminate H
  | Some ?v = Some _ =>
      first [ match v with context [match ?y with _ => _ end] => split_on H y end
            | injection H as H; subst ]
  | (match ?y with _ => _ end) = Some _ => split_on H y
  | _ = Some _ => use_inv H
  end.

(** Close a goal that the encoding is the term, rewriting with what
    the encoders of the parts gave back. *)
Ltac close :=
  repeat match goal with E : @eq term _ ?b |- context [?b] => progress rewrite <- E end;
  reflexivity.

(** The head normal form of e. *)
Ltac hnf_of e := eval hnf in e.

(** Destruct the variable that blocks the match r, looking through the
    head of each scrutinee in turn. *)
Ltac blocker r :=
  match r with
  | match ?x with _ => _ end => first [is_var x; destruct x | let y := hnf_of x in blocker y]
  end.

(** One step of proving a goal [match d t with Some x => P x | None =>
    True end] for a decoder d without lists: close it once d t has a
    head, or destruct what blocks it. *)
Ltac spec_step :=
  match goal with |- match ?e with _ => _ end =>
    let r := hnf_of e in
    lazymatch r with
    | Some _ => exact eq_refl
    | None => exact I
    | _ => blocker r
    end
  end.

(** ## Values and the small tables *)

(** An integer is read from the term [TInt n] only. *)
Lemma dz_enc : forall t n, dz t = Some n -> TInt n = t.
Proof. intros t n H. unfold dz in H. repeat dstep H. all: close. Qed.

(** A class is read from its own atom only. *)
Lemma dclass_enc : forall t k, dclass t = Some k -> eclass k = t.
Proof. intros t k H. unfold dclass, datom in H. repeat dstep H. all: close. Qed.

(** A temporary n is read from `tmp(N)` only. *)
Lemma dtmp_enc : forall t n, dtmp t = Some n -> enc_tmp n = t.
Proof. intros t n H. unfold dtmp, dapp in H. repeat dstep H. all: close. Qed.

(** A value is read from the term [enc_value] writes for it only. *)
Lemma dvalue_enc : forall t v, dvalue t = Some v -> enc_value v = t.
Proof. intros t v H. unfold dvalue in H. repeat dstep H. all: close. Qed.

(** Rights are read from their own atom only. *)
Lemma drights_enc : forall t r, drights t = Some r -> enc_rights r = t.
Proof. intros t r H. unfold drights, datom in H. repeat dstep H. all: close. Qed.

(** A bound is read from its own atom only. *)
Lemma dbound_enc : forall t b, dbound t = Some b -> enc_bound b = t.
Proof. intros t b H. unfold dbound, datom in H. repeat dstep H. all: close. Qed.

(** A narrow type is read from its own atom only. *)
Lemma dnarrow_enc : forall t n, dnarrow t = Some n -> enc_narrow n = t.
Proof. intros t n H. unfold dnarrow, datom in H. repeat dstep H. all: close. Qed.

(** A load type is read from its own atom only. *)
Lemma dload_type_enc : forall t l, dload_type t = Some l -> enc_load_type l = t.
Proof.
  intros t l H. pose proof dnarrow_enc. unfold dload_type, datom in H. repeat dstep H. all: close.
Qed.

(** A condition is read from its own atom only. *)
Lemma dcond_enc : forall t c, dcond t = Some c -> enc_cond c = t.
Proof. intros t c H. unfold dcond, datom in H. repeat dstep H. all: close. Qed.

(** An effect is read from its own atom only. *)
Lemma deffect_enc : forall t e, deffect t = Some e -> enc_effect e = t.
Proof. intros t e H. unfold deffect, datom in H. repeat dstep H. all: close. Qed.

(** A width is read from its own atom only. *)
Lemma dwidth_enc : forall t w, dwidth t = Some w -> enc_width w = t.
Proof. intros t w H. unfold dwidth, datom in H. repeat dstep H. all: close. Qed.

(** If e writes back every term d reads, it writes back every list of
    terms that [map_option] d reads. *)
Lemma map_option_enc : forall (X : Type) (d : term -> option X) (e : X -> term),
  (forall t x, d t = Some x -> e x = t) ->
  forall ts xs, map_option d ts = Some xs -> map e xs = ts.
Proof.
  intros X d e He ts. induction ts as [|t ts IH]; intros xs H; simpl in H.
  - injection H as <-. reflexivity.
  - destruct (d t) eqn:E1; [|discriminate]. destruct (map_option d ts) eqn:E2; [|discriminate].
    injection H as <-. simpl. f_equal; auto.
Qed.

(** A list of effects is read from the list of their atoms only. *)
Lemma deffects_enc : forall t es, deffects t = Some es -> enc_effects es = t.
Proof.
  intros t es H. pose proof (map_option_enc _ _ _ deffect_enc).
  unfold deffects, dlist in H. repeat dstep H. all: close.
Qed.

(** An op is read from the term [enc_op] writes for it only. *)
Lemma dop_enc : forall t o, dop t = Some o -> enc_op o = t.
Proof.
  intros t o H. pose proof dz_enc. pose proof dclass_enc. pose proof drights_enc.
  pose proof dbound_enc. pose proof dnarrow_enc. pose proof dload_type_enc.
  pose proof dcond_enc. pose proof deffects_enc.
  unfold dop, dcheck4 in H. repeat dstep H. all: close.
Qed.

(** ## Instructions *)

(** A flight's argument is read from its own term only. *)
Lemma dflight_arg_enc : forall t a, dflight_arg t = Some a -> enc_flight_arg a = t.
Proof.
  intros t a H.
  assert (S : match dflight_arg t with Some a' => enc_flight_arg a' = t | None => True end)
    by (clear H; repeat spec_step).
  rewrite H in S. exact S.
Qed.

(** A flight's Lower is read from its own term only. *)
Lemma dflight_lower_enc : forall t l, dflight_lower t = Some l -> enc_flight_lower l = t.
Proof. intros t l H. pose proof dvalue_enc. unfold dflight_lower in H. repeat dstep H. all: close. Qed.

(** One result of a call is read from `result(tmp(D), K)` only. *)
Lemma dresult_enc : forall t r, dresult t = Some r -> enc_result r = t.
Proof.
  intros t r H. pose proof dtmp_enc. pose proof dclass_enc.
  unfold dresult, dapp in H. repeat dstep H. all: close.
Qed.

(** A call's Res is read from its own term only. *)
Lemma dcall_result_enc : forall t r, dcall_result t = Some r -> enc_call_result r = t.
Proof.
  intros t r H. pose proof dresult_enc. pose proof (map_option_enc _ _ _ dresult_enc).
  unfold dcall_result in H. repeat dstep H. all: close.
Qed.

(** A call's argument is read from `arg(K, V)` only. *)
Lemma darg_enc : forall t a, darg t = Some a -> enc_arg a = t.
Proof.
  intros t a H. pose proof dvalue_enc. pose proof dclass_enc.
  unfold darg, dapp in H. repeat dstep H. all: close.
Qed.

(** A call's arguments are read from the list of their terms only. *)
Lemma dargs_enc : forall t args, dargs t = Some args -> enc_args args = t.
Proof.
  intros t args H. pose proof (map_option_enc _ _ _ darg_enc).
  unfold dargs, dlist in H. repeat dstep H. all: close.
Qed.

(** An instruction is read from the term [enc_inst] writes for it only. *)
Lemma dinst_enc : forall t i, dinst t = Some i -> enc_inst i = t.
Proof.
  intros t i H. pose proof dtmp_enc. pose proof dclass_enc. pose proof dop_enc.
  pose proof dvalue_enc. pose proof (map_option_enc _ _ _ dvalue_enc).
  pose proof (map_option_enc _ _ _ dflight_arg_enc). pose proof dflight_lower_enc.
  pose proof dwidth_enc. pose proof dz_enc. pose proof deffects_enc.
  pose proof dcall_result_enc. pose proof dargs_enc.
  unfold dinst in H. repeat dstep H. all: close.
Qed.

(** ## Jumps, phis, blocks and functions *)

(** A jump's target is read from its own term only. *)
Lemma dtarget_enc : forall t l, dtarget t = Some l -> enc_target l = t.
Proof. intros t l H. unfold dtarget in H. repeat dstep H. all: close. Qed.

(** A jump is read from the term [enc_jump] writes for it only. *)
Lemma djump_enc : forall t j, djump t = Some j -> enc_jump j = t.
Proof.
  intros t j H. pose proof dtarget_enc. pose proof dvalue_enc.
  pose proof (map_option_enc _ _ _ dvalue_enc). unfold djump in H. repeat dstep H. all: close.
Qed.

(** One pair of a phi is read from `Pred-Value` only. *)
Lemma dpair_enc : forall t p, dpair t = Some p -> enc_pair p = t.
Proof. intros t p H. pose proof dvalue_enc. unfold dpair, dapp in H. repeat dstep H. all: close. Qed.

(** A phi is read from the term [enc_phi] writes for it only. *)
Lemma dphi_enc : forall t p, dphi t = Some p -> enc_phi p = t.
Proof.
  intros t p H. pose proof dtmp_enc. pose proof dclass_enc.
  pose proof (map_option_enc _ _ _ dpair_enc). unfold dphi in H. repeat dstep H. all: close.
Qed.

(** A block is read from the term [enc_block] writes for it only. *)
Lemma dblock_enc : forall t b, dblock t = Some b -> enc_block b = t.
Proof.
  intros t b H. pose proof djump_enc. pose proof (map_option_enc _ _ _ dphi_enc).
  pose proof (map_option_enc _ _ _ dinst_enc). unfold dblock in H. repeat dstep H. all: close.
Qed.

(** A function's Ret is read from its own term only. *)
Lemma dret_enc : forall t r, dret t = Some r -> enc_ret r = t.
Proof.
  intros t r H. pose proof dclass_enc. pose proof (map_option_enc _ _ _ dclass_enc).
  unfold dret in H. repeat dstep H. all: close.
Qed.

(** A function's parameter is read from `param(K, tmp(D))` only. *)
Lemma dparam_enc : forall t p, dparam t = Some p ->
  TApp "param" [eclass (fst p); TApp "tmp" [snd p]] = t.
Proof.
  intros t p H. pose proof dtmp_enc. pose proof dclass_enc.
  unfold dparam, dapp in H. repeat dstep H. all: close.
Qed.

(** A function read from the arguments of a `func` term is written
    back as that term. *)
Lemma dfunc_enc : forall n lk r ps bs f, dfunc n lk r ps bs = Some f ->
  enc_func f = TApp "func" [n; lk; r; ps; bs].
Proof.
  intros n lk r ps bs f H. pose proof dret_enc. pose proof (map_option_enc _ _ _ dparam_enc).
  pose proof (map_option_enc _ _ _ dblock_enc). unfold dfunc, dlist in H. repeat dstep H. all: close.
Qed.

(** A data object's Linkage is read from its own term only. *)
Lemma dlinkage_enc : forall t l, dlinkage t = Some l -> enc_linkage l = t.
Proof.
  intros t l H.
  assert (S : match dlinkage t with Some l' => enc_linkage l' = t | None => True end)
    by (clear H; repeat spec_step).
  rewrite H in S. exact S.
Qed.

(** ## Data *)

(** [char_code] reads only the codes 0 to 2047. *)
Lemma char_code_range : forall t c, char_code t = Some c -> 0 <= c < 2048.
Proof.
  intros t c H. unfold char_code in H.
  destruct t as [| a | |]; try discriminate H.
  destruct a as [|c1 [|c2 [|c3 s]]]; try discriminate H.
  - destruct (Z.of_nat (nat_of_ascii c1) <? 128) eqn:E; [|discriminate H].
    injection H as <-. apply Z.ltb_lt in E. lia.
  - destruct ((192 <=? Z.of_nat (nat_of_ascii c1)) && (Z.of_nat (nat_of_ascii c1) <? 224)
      && (128 <=? Z.of_nat (nat_of_ascii c2)) && (Z.of_nat (nat_of_ascii c2) <? 192)) eqn:E;
      [|discriminate H].
    injection H as <-. repeat rewrite andb_true_iff in E. rewrite !Z.leb_le, !Z.ltb_lt in E. lia.
Qed.

(** [char_code] reads back every code from 0 to 2047 from the atom
    [code_char] writes for it. *)
Lemma char_code_code_char : forall c, 0 <= c < 2048 -> char_code (code_char c) = Some c.
Proof.
  intros c Hc. unfold code_char. destruct (c <? 128) eqn:E.
  - apply Z.ltb_lt in E. unfold char_code; cbv beta iota zeta.
    rewrite nat_ascii_embedding by lia. rewrite Z2Nat.id by lia.
    replace (c <? 128) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - apply Z.ltb_ge in E. unfold char_code; cbv beta iota zeta.
    assert (Hd : 2 <= c / 64 < 32)
      by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
    assert (Hm : 0 <= c mod 64 < 64) by (apply Z.mod_pos_bound; lia).
    rewrite !nat_ascii_embedding by lia. rewrite !Z2Nat.id by lia.
    replace ((192 <=? 192 + c / 64) && (192 + c / 64 <? 224) && (128 <=? 128 + c mod 64)
             && (128 + c mod 64 <? 192)) with true.
    + f_equal. pose proof (Z.div_mod c 64). lia.
    + symmetry. repeat rewrite andb_true_iff. rewrite !Z.leb_le, !Z.ltb_lt. lia.
Qed.

(** The codes of a string item are all from 0 to 2047. *)
Lemma char_codes_range : forall cs codes, map_option char_code cs = Some codes ->
  Forall (fun c => 0 <= c < 2048) codes.
Proof.
  induction cs as [|t cs IH]; intros codes H; simpl in H.
  - injection H as <-. constructor.
  - destruct (char_code t) eqn:E1; [|discriminate]. destruct (map_option char_code cs) eqn:E2;
      [|discriminate].
    injection H as <-. constructor; [eapply char_code_range; eassumption | auto].
Qed.

(** Codes from 0 to 2047 are read back from the atoms [code_char]
    writes for them. *)
Lemma char_codes_round : forall codes, Forall (fun c => 0 <= c < 2048) codes ->
  map_option char_code (map code_char codes) = Some codes.
Proof.
  induction codes as [|c codes IH]; intros H; simpl.
  - reflexivity.
  - inversion H as [|? ? Hc Hr]; subst. rewrite char_code_code_char by exact Hc.
    rewrite IH by exact Hr. reflexivity.
Qed.

(** What is known of a data item x read from the term t: it is written
    back as t, or it is a string of codes from 0 to 2047. *)
Definition data_ok (t : term) (x : data_item) : Prop :=
  enc_data_item x = t \/ exists codes, x = Str codes /\ Forall (fun c => 0 <= c < 2048) codes.

(** Close a goal [data_ok t x]. *)
Ltac data_close :=
  unfold data_ok;
  first [ left; close
        | right; eexists; split; [reflexivity | eapply char_codes_range; eassumption] ].

(** A data item read from t is written back as t, or is a string of
    codes from 0 to 2047. The item's subterms on its second argument
    are taken apart once each, then stand for themselves, so that its
    first argument and its second are not taken apart together. *)
Lemma ddata_item_enc : forall t x, ddata_item t = Some x -> data_ok t x.
Proof.
  intros t x H. pose proof dwidth_enc.
  destruct t as [n|a|f args|ts]; [ | | destruct args as [|a1 [|a2 tl]] | ];
    unfold ddata_item in H; cbv beta iota zeta in H.
  5: { repeat match type of H with context [?w] =>
         match w with match a2 with _ => _ end =>
           let F := fresh "F" in
           lazymatch w with
           | context [Sym _ _] =>
               assert (F : forall y, w = Some y -> f = "item" -> a1 = TAtom "p" ->
                             data_ok (TApp f (a1 :: a2 :: tl)) y)
                 by (clear H; intros y Hy Hf Ha; subst f a1; repeat dstep Hy; data_close)
           | _ =>
               assert (F : forall y, w = Some y -> f = "item" ->
                             data_ok (TApp f (a1 :: a2 :: tl)) y)
                 by (clear H; intros y Hy Hf; subst f; repeat dstep Hy; data_close)
           end;
           let wv := fresh "wv" in set (wv := w) in *; clearbody wv
         end end.
       repeat dstep H.
       all: first [ match goal with F : forall y, _ = Some y -> _ |- _ => exact (F _ H eq_refl) end
                  | match goal with F : forall y, _ = Some y -> _ |- _ =>
                      exact (F _ H eq_refl eq_refl) end
                  | data_close ]. }
  all: repeat dstep H. all: data_close.
Qed.

(** A data item read from any term is read back from the term
    [enc_data_item] writes for it. *)
Lemma ddata_item_round : forall t x, ddata_item t = Some x ->
  ddata_item (enc_data_item x) = Some x.
Proof.
  intros t x H. destruct (ddata_item_enc t x H) as [He | [codes [-> Hr]]].
  - rewrite He. exact H.
  - simpl. rewrite char_codes_round by exact Hr. reflexivity.
Qed.

(** If d reads back from e's term whatever it read from some term, the
    same holds of lists by [map_option]. *)
Lemma map_option_round : forall (X : Type) (d : term -> option X) (e : X -> term),
  (forall t x, d t = Some x -> d (e x) = Some x) ->
  forall ts xs, map_option d ts = Some xs -> map_option d (map e xs) = Some xs.
Proof.
  intros X d e He ts. induction ts as [|t ts IH]; intros xs H; simpl in H.
  - injection H as <-. reflexivity.
  - destruct (d t) eqn:E1; [|discriminate]. destruct (map_option d ts) eqn:E2; [|discriminate].
    injection H as <-. simpl. rewrite (He _ _ E1). rewrite (IH _ eq_refl). reflexivity.
Qed.

(** ## Items and the module *)

(** An item read from t is written back as t, unless it is a data
    object: then t is its `data` term, with its Linkage and items as
    read. *)
Lemma ditem_enc : forall t i, ditem t = Some (Some i) ->
  enc_item i = t \/
  exists n lk al its lk' its', t = TApp "data" [n; lk; TInt al; TList its] /\
    i = IData n lk' al its' /\ dlinkage lk = Some lk' /\ map_option ddata_item its = Some its'.
Proof.
  intros t i H. pose proof dfunc_enc. unfold ditem in H. repeat dstep H.
  all: first [ left; close
             | right; do 6 eexists; split; [reflexivity | split; [reflexivity | split; eassumption]] ].
Qed.

(** An item read from any term is read back from the term
    [enc_item] writes for it. *)
Lemma ditem_round : forall t i, ditem t = Some (Some i) -> ditem (enc_item i) = Some (Some i).
Proof.
  intros t i H.
  destruct (ditem_enc t i H) as [He | [n [lk [al [its [lk' [its' [-> [-> [Hl Hi]]]]]]]]]].
  - rewrite He. exact H.
  - simpl. rewrite (dlinkage_enc _ _ Hl). rewrite Hl.
    rewrite (map_option_round _ _ _ ddata_item_round _ _ Hi). reflexivity.
Qed.

(** The items a module keeps of what [ditem] read: none for a context
    item. *)
Definition keep (o : option item) : list item := match o with Some i => [i] | None => [] end.

(** The items kept of a list that [ditem] read are each read back from
    the term [enc_item] writes for it. *)
Lemma items_round : forall items os, map_option ditem items = Some os ->
  map_option ditem (map enc_item (flat_map keep os)) = Some (map Some (flat_map keep os)).
Proof.
  induction items as [|t items IH]; intros os H; simpl in H.
  - injection H as <-. reflexivity.
  - destruct (ditem t) as [o|] eqn:E1; [|discriminate].
    destruct (map_option ditem items) as [os'|] eqn:E2; [|discriminate].
    injection H as <-. destruct o as [i|]; simpl.
    + rewrite (ditem_round _ _ E1). rewrite (IH _ eq_refl). reflexivity.
    + exact (IH _ eq_refl).
Qed.

(** Keeping every item of a list of items read as items gives the
    list. *)
Lemma keep_some : forall m : module, flat_map keep (map Some m) = m.
Proof. induction m as [|i m IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(** Every item of a module read from any term is read back, as that
    item, from the term [enc_item] writes for it. *)
Lemma decode_items : forall t m, decode_module t = Some m ->
  map_option ditem (map enc_item m) = Some (map Some m).
Proof.
  intros t m H. unfold decode_module in H. repeat dstep H.
  pose proof (items_round _ _ E) as R. unfold keep in R. exact R.
Qed.

(** The term half of NFB's round trip: a module read from any term is
    read back from the term [enc_module] writes for it. *)
Theorem decode_enc_module : forall t m, decode_module t = Some m ->
  decode_module (enc_module m) = Some m.
Proof.
  intros t m H. pose proof (keep_some m) as K. unfold keep in K.
  unfold decode_module, enc_module. rewrite (decode_items t m H). simpl. rewrite K. reflexivity.
Qed.

(** ## Context items *)

(** Whether the term is not a `context(_, _)` item. *)
Definition not_context (t : term) : bool :=
  match t with TApp "context" [_; _] => false | _ => true end.

(** A term that [ditem] reads as an item is not a context item. *)
Lemma ditem_not_context : forall u i, ditem u = Some (Some i) -> not_context u = true.
Proof.
  intros u i H. destruct (not_context u) eqn:Hc; [reflexivity | exfalso].
  unfold not_context in Hc.
  repeat lazymatch type of Hc with (match ?y with _ => _ end) = _ => split_on Hc y end.
  all: try discriminate Hc. simpl in H. discriminate H.
Qed.

(** No item of the term [enc_module] writes for a module read from any
    term is a context item. *)
Corollary enc_module_no_context : forall t m, decode_module t = Some m ->
  forall u, In u (map enc_item m) -> not_context u = true.
Proof.
  intros t m H. pose proof (decode_items t m H) as R. clear H. revert R.
  induction m as [|i m IH]; intros R u Hu; simpl in Hu; [contradiction|].
  simpl in R. destruct (ditem (enc_item i)) as [o|] eqn:E1; [|discriminate].
  destruct (map_option ditem (map enc_item m)) as [os|] eqn:E2; [|discriminate].
  injection R as Ho Hos. subst o. destruct Hu as [<- | Hu].
  - exact (ditem_not_context _ _ E1).
  - exact (IH (f_equal Some Hos) u Hu).
Qed.

(** ## The strong form fails *)

(** The term t with its context items dropped, if it is a module. *)
Definition strip_context (t : term) : term :=
  match t with
  | TApp "module" [TList items] => TApp "module" [TList (filter not_context items)]
  | _ => t
  end.

(** A module of one data object whose string is the overlong UTF-8
    sequence 0xC0 0x80, an atom of two characters. *)
Definition overlong : term :=
  TApp "module" [TList [TApp "data" [TAtom "s"; TAtom "local"; TInt 1;
    TList [TApp "item" [TAtom "b"; TApp "str"
      [TList [TAtom (String (ascii_of_nat 192) (String (ascii_of_nat 128) EmptyString))]]]]]]].

(** [overlong] is read as the string of the one code 0, which is
    written back as a one-byte atom. *)
Lemma overlong_normalized :
  decode_module overlong = Some [IData (TAtom "s") LLocal 1 [Str [0]]] /\
  enc_module [IData (TAtom "s") LLocal 1 [Str [0]]] <> strip_context overlong.
Proof. split; [reflexivity | cbv; discriminate]. Qed.

(** So [enc_module m] is not always the term m was read from with its
    context items dropped. *)
Lemma strong_form_fails :
  ~ (forall t m, decode_module t = Some m -> enc_module m = strip_context t).
Proof.
  intros Hs. destruct overlong_normalized as [Hd Hn]. exact (Hn (Hs _ _ Hd)).
Qed.
