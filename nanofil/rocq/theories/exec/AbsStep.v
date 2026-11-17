(** The checker of [AbsRun](AbsRun.v) runs a function one instruction at
    a time on abstract states. This module shows that each of those
    steps follows a step of the machine. When the checker accepts an
    instruction in a state that is true of a real environment, the
    machine executes the instruction without a panic, and the
    checker's next state is true of the machine's next environment.

    The instructions fall into three groups. Most instructions leave
    memory alone, and [ainst_read_sound] covers them. A store changes
    the bytes of one owned object, and [ainst_write_sound] says which
    object and what its contents become. An allocation adds an object,
    and [ainst_alloc_sound] covers it. The module ends with the lemmas
    for a branch and for the phis of a block. Calls are left to
    [AbsSound](AbsSound.v), because a call needs the program logic. *)

From Stdlib Require Import String ZArith List Bool Lia PeanoNat.
From Nanofil Require Import Term Maps Syntax Values Memory Runtime Ops Semantics Symbolic Pieces StepRules
  AbsRun AbsDen AbsMem.
Import ListNotations.
Open Scope Z_scope.

Section step.
Variable guard : Prop.
Variable ge : genv.
Variable builtin : hook.
Variable gobjs : list name.
Variable fnames : list (name * (list class * ret_type)).
Variable specs : name -> list fspec.
Hypothesis Hfn : fnames_ok ge fnames.

Local Notation M := (M guard ge gobjs).
Local Notation R := (R guard ge gobjs).
Local Notation ainst := (ainst builtin gobjs fnames specs).
Local Notation avalue := (avalue gobjs fnames).
Local Notation avalues := (avalues gobjs fnames).

(** * Instructions that leave memory alone *)

(** The machine steps from one instruction to the next and changes
    only the environment, in every memory that agrees with the
    contents of the state. *)
Definition steps_to (B : list place) (X : cont) (e : env) (i : inst) (e' : env) : Prop :=
  forall f ls l rest j cs m fuel, mholds B X m ->
    Semantics.step ge (mkConfig (mkFrame f e ls None (Exec l (i :: rest) j)) cs m fuel) =
    Next (mkConfig (mkFrame f e' ls None (Exec l rest j)) cs m fuel).

Lemma let_steps B X e d k o args classes ws w :
  general_op o = true -> op_arg_classes o k = Some classes ->
  map2_option (value_x ge e) classes args = Some ws ->
  (forall m, mholds B X m -> op_res o k ws m = Some (OpRes (RVal w) m)) ->
  steps_to B X e (Let d k o args) (put d w e).
Proof using Type.
  intros Hg Hc Hx Ho f ls l rest j cs m fuel Hm. apply rule_let with (classes := classes) (xs := ws); auto.
Qed.

(** Reading the operands of an instruction returns a list of values
    and a list of words. These two lemmas take one or two operands out
    of those lists. *)
Lemma Rs_one ρ B e X st st1 p ws :
  Rs guard ge gobjs ρ B e X st st1 [p] ws ->
  exists ρ1 w, ws = [w] /\ M ρ1 B st1 e X /\ wf_val (length (st_bnd st1)) p /\ dval ge ρ1 B p w.
Proof using Type.
  intros (ρ1 & HM1 & _ & W1 & D1). inversion D1 as [|? w ? ws' Dp D']; subst. inversion D'; subst.
  exists ρ1, w. split; [reflexivity|]. split; [exact HM1|]. split; [exact (Forall_inv W1) | exact Dp].
Qed.

Lemma Rs_two ρ B e X st st1 q p ws :
  Rs guard ge gobjs ρ B e X st st1 [q; p] ws ->
  exists ρ1 wq w, ws = [wq; w] /\ M ρ1 B st1 e X /\ wf_val (length (st_bnd st1)) q /\ dval ge ρ1 B q wq /\
                  wf_val (length (st_bnd st1)) p /\ dval ge ρ1 B p w.
Proof using Type.
  intros (ρ1 & HM1 & _ & W1 & D1). inversion D1 as [|? wq ? ws' Dq D']; subst.
  inversion D' as [|? w ? ws'' Dp D'']; subst. inversion D''; subst.
  exists ρ1, wq, w. split; [reflexivity|]. split; [exact HM1|].
  split; [exact (Forall_inv W1)|]. split; [exact Dq|]. split; [exact (Forall_inv (Forall_inv_tail W1)) | exact Dp].
Qed.

(** The checker accepts a check of one pointer when the checked span
    lies inside an owned object. The machine's check then passes. *)
Lemma check_sound ρ B st e X d k lo hi r al args st' :
  M ρ B st e X -> ainst (Let d k (Check lo hi r al) args) st = Some st' ->
  exists e', steps_to B X e (Let d k (Check lo hi r al) args) e' /\ exists ρ', M ρ' B st' e' X.
Proof using Hfn.
  intros HM. cbn [AbsRun.ainst].
  destruct (avalues [P] args st) as [[xs st1]|] eqn:Ea; [|discriminate].
  destruct k; try discriminate. destruct xs as [|p [|]]; try discriminate.
  destruct (acheck lo hi r al p st1) eqn:Ec; [|discriminate]. intros [= <-].
  destruct (avalues_sound guard ge gobjs fnames Hfn ρ B st e X _ _ _ _ HM Ea) as (ws & Ews & HR).
  destruct (Rs_one _ _ _ _ _ _ _ _ HR) as (ρ1 & w & -> & HM1 & Wp & Dp).
  destruct (acheck_sound guard ge gobjs ρ1 B st1 e X lo hi r al p w HM1 Wp Dp Ec)
    as (Hlt & o & a & ob & alo & ahi & pl & xs & cs & -> & [Hpl Hx Hok Ew Ra Hb0 Hloc]).
  subst w. eexists. split.
  - eapply (let_steps B X e d A (Check lo hi r al) args [P] _ _ eq_refl eq_refl Ews).
    intros m Hm. apply (check_op m pl). apply Hloc. exact (proj1 (Hm o pl xs cs Hpl Hx)).
  - exists ρ1. apply M_bind; [exact HM1 | exact Wp | exact Dp].
Qed.

(** A renewed check and a half check have a second operand, the
    pointer that an earlier check proved. The checker asks that both
    point into the same object. *)
Lemma check2_sound ρ B st e X d k o0 lo hi r al args st' :
  M ρ B st e X -> general_op o0 = true -> op_arg_classes o0 A = Some [A; P] ->
  (forall m pl q1 q, located m pl q lo (hi - lo) al r -> lo < hi -> ptr_cap q1 = ptr_cap q ->
     op_res o0 A [WPtr q1; WPtr q] m = Some (OpRes (RVal (WPtr q)) m)) ->
  (let? (xs, st1) := avalues [A; P] args st in
   match k, xs with
   | A, [q; p] => if same_obj q p && acheck lo hi r al p st1 then Some (bind st1 d p) else None
   | _, _ => None
   end) = Some st' ->
  exists e', steps_to B X e (Let d k o0 args) e' /\ exists ρ', M ρ' B st' e' X.
Proof using Hfn.
  intros HM Hg Hcl Hop.
  destruct (avalues [A; P] args st) as [[xs st1]|] eqn:Ea; [|discriminate].
  destruct k; try discriminate. destruct xs as [|q [|p [|]]]; try discriminate.
  destruct (same_obj q p && acheck lo hi r al p st1) eqn:Ec; [|discriminate]. intros [= <-].
  apply andb_true_iff in Ec as [Eso Ec].
  destruct (avalues_sound guard ge gobjs fnames Hfn ρ B st e X _ _ _ _ HM Ea) as (ws & Ews & HR).
  destruct (Rs_two _ _ _ _ _ _ _ _ _ HR) as (ρ1 & wq & w & -> & HM1 & Wq & Dq & Wp & Dp).
  destruct (acheck_sound guard ge gobjs ρ1 B st1 e X lo hi r al p w HM1 Wp Dp Ec)
    as (Hlt & o & a & ob & alo & ahi & pl & xs & cs & -> & [Hpl Hx Hok Ew Ra Hb0 Hloc]).
  subst w. destruct q as [| | |o' a'| | |]; try discriminate Eso. cbn [same_obj] in Eso.
  apply Nat.eqb_eq in Eso. subst o'. destruct Dq as (pl' & Hpl' & ->). rewrite Hpl in Hpl'. injection Hpl' as <-.
  eexists. split.
  - eapply (let_steps B X e d A o0 args [A; P] _ _ Hg Hcl Ews).
    intros m Hm. apply (Hop m pl); [|exact Hlt | reflexivity]. apply Hloc. exact (proj1 (Hm o pl xs cs Hpl Hx)).
  - exists ρ1. apply M_bind; [exact HM1 | exact Wp | exact Dp].
Qed.

(** The machine loads an integer that the checker's value describes. *)
Lemma load_sound ρ B st e X d k t off args st' :
  M ρ B st e X -> ainst (Let d k (RawLoad t off) args) st = Some st' ->
  exists e', steps_to B X e (Let d k (RawLoad t off) args) e' /\ exists ρ', M ρ' B st' e' X.
Proof using Hfn.
  intros HM. cbn [AbsRun.ainst].
  destruct (avalues [A] args st) as [[xs st1]|] eqn:Ea; [|discriminate].
  destruct xs as [|p [|]]; try discriminate.
  destruct (aload t k off p st1) as [[v st2]|] eqn:El; [|discriminate]. intros [= <-].
  destruct (avalues_sound guard ge gobjs fnames Hfn ρ B st e X _ _ _ _ HM Ea) as (ws & Ews & HR).
  destruct (Rs_one _ _ _ _ _ _ _ _ HR) as (ρ1 & w & -> & HM1 & Wp & Dp).
  destruct (aload_sound guard ge gobjs ρ1 B st1 e X t k off p w v st2 HM1 Wp Dp El)
    as (o & pl & xs & cs & q & x & Hpl & Hx & -> & Hop & HR2).
  exists (put d x e). split.
  - apply (let_steps B X e d k (RawLoad t off) args [A] _ _ eq_refl eq_refl Ews).
    intros m Hm. apply Hop. exact (Hm o pl xs cs Hpl Hx).
  - destruct (R_bind guard ge gobjs _ _ _ _ _ _ _ _ d HR2) as (ρ2 & H2 & _). exists ρ2. exact H2.
Qed.

(** The machine loads a pointer, and the checker binds a value that
    describes any pointer. *)
Lemma load_ptr_sound ρ B st e X d k off args st' :
  M ρ B st e X ->
  ainst (Let d k (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) args) st = Some st' ->
  exists e', steps_to B X e (Let d k (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) args) e' /\
             exists ρ', M ρ' B st' e' X.
Proof using Hfn.
  intros HM. cbn [AbsRun.ainst].
  destruct (avalues [A] args st) as [[xs st1]|] eqn:Ea; [|discriminate].
  destruct k; try discriminate. destruct xs as [|p [|]]; try discriminate.
  destruct (aload_ptr off p st1) as [[v st2]|] eqn:El; [|discriminate]. intros [= <-].
  destruct (avalues_sound guard ge gobjs fnames Hfn ρ B st e X _ _ _ _ HM Ea) as (ws & Ews & HR).
  destruct (Rs_one _ _ _ _ _ _ _ _ HR) as (ρ1 & w & -> & HM1 & Wp & Dp).
  destruct (aload_ptr_sound guard ge gobjs ρ1 B st1 e X off p w v st2 HM1 Wp Dp El)
    as (-> & -> & q & x & -> & Hop).
  exists (put d (WPtr x) e). split.
  - exact (let_steps B X e d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) args [A] _ _ eq_refl eq_refl Ews Hop).
  - exists ρ1. apply M_bind; [exact HM1 | exact I | eexists; reflexivity].
Qed.

(** The checker accepts a function check on the address of a named
    function, and the machine's check passes on that address. *)
Lemma check_function_sound ρ B st e X d k args st' :
  M ρ B st e X -> ainst (Let d k CheckFunction args) st = Some st' ->
  exists e', steps_to B X e (Let d k CheckFunction args) e' /\ exists ρ', M ρ' B st' e' X.
Proof using Hfn.
  intros HM. cbn [AbsRun.ainst]. destruct k; try discriminate. destruct args as [|v [|]]; try discriminate.
  destruct (avalue P v st) as [[x st1]|] eqn:Ea; [|discriminate].
  destruct x as [| | | | | |g]; try discriminate. intros [= <-].
  destruct (avalue_sound guard ge gobjs fnames Hfn ρ B st e X _ _ _ _ HM Ea) as (w & Ev & ρ1 & HM1 & _ & W1 & D1).
  pose proof D1 as (p & -> & Hl & Hc).
  exists (put d (WPtr p) e). split.
  - intros f ls l rest j cs m fuel _. apply rule_check_function; [exact Ev|].
    unfold function_check_res. rewrite Hc, Hl, Z.eqb_refl. reflexivity.
  - exists ρ1. apply M_bind; [exact HM1 | exact W1 | exact D1].
Qed.

(** The machine computes an arithmetic operation, a comparison or an
    extension to a word that the checker's value describes. *)
Lemma arith_sound ρ B st e X d k o args st' :
  M ρ B st e X -> general_op o = true ->
  (let* classes := op_arg_classes o k in
   let? (xs, st1) := avalues classes args st in
   let? (v, st2) := aop o k xs st1 in
   Some (bind st2 d v)) = Some st' ->
  exists e', steps_to B X e (Let d k o args) e' /\ exists ρ', M ρ' B st' e' X.
Proof using Hfn.
  intros HM Hg. destruct (op_arg_classes o k) as [classes|] eqn:Ecl; [|discriminate].
  destruct (avalues classes args st) as [[xs st1]|] eqn:Ea; [|discriminate].
  destruct (aop o k xs st1) as [[v st2]|] eqn:Eo; [|discriminate]. intros [= <-].
  destruct (avalues_sound guard ge gobjs fnames Hfn ρ B st e X _ _ _ _ HM Ea) as (ws & Ews & ρ1 & HM1 & _ & W1 & D1).
  destruct (aop_sound guard ge gobjs ρ1 B st1 e X o k xs ws v st2 HM1 W1 D1 Eo) as (w & Hop & HR).
  exists (put d w e). split.
  - apply (let_steps B X e d k o args classes ws w Hg Ecl Ews). intros m _. apply Hop.
  - destruct (R_bind guard ge gobjs _ _ _ _ _ _ _ _ d HR) as (ρ2 & H2 & _). exists ρ2. exact H2.
Qed.

(** The machine moves a pointer by a flight to an address that the
    checker's value describes. *)
Lemma flight_sound ρ B st e X d p x q st' :
  M ρ B st e X -> ainst (Flight d Add [FAddress p; FValue x] (LowerOf q)) st = Some st' ->
  exists e', steps_to B X e (Flight d Add [FAddress p; FValue x] (LowerOf q)) e' /\ exists ρ', M ρ' B st' e' X.
Proof using Hfn.
  intros HM. cbn [AbsRun.ainst].
  destruct (avalue P p st) as [[pv st1]|] eqn:E1; [|discriminate].
  destruct (avalue L x st1) as [[xv st2]|] eqn:E2; [|discriminate].
  destruct (avalue P q st2) as [[qv st3]|] eqn:E3; [|discriminate].
  destruct (aflight pv xv qv st3) as [[v st4]|] eqn:E4; [|discriminate]. intros [= <-].
  destruct (avalue_sound guard ge gobjs fnames Hfn ρ B st e X _ _ _ _ HM E1) as (wp & Ep & ρ1 & HM1 & _ & Wp1 & Dp1).
  destruct (avalue_sound guard ge gobjs fnames Hfn ρ1 B st1 e X _ _ _ _ HM1 E2) as (wx & Ex & ρ2 & HM2 & S2 & Wx2 & Dx2).
  destruct (avalue_sound guard ge gobjs fnames Hfn ρ2 B st2 e X _ _ _ _ HM2 E3) as (wq & Eq & ρ3 & HM3 & S3 & Wq3 & Dq3).
  destruct (step_val ge _ _ _ _ B pv wp S2 Wp1 Dp1) as [Wp2 Dp2].
  destruct (step_val ge _ _ _ _ B pv wp S3 Wp2 Dp2) as [Wp3 Dp3].
  destruct (step_val ge _ _ _ _ B xv wx S3 Wx2 Dx2) as [Wx3 Dx3].
  destruct xv as [xi| | | | | |]; try discriminate E4.
  destruct (aflight_sound guard ge gobjs ρ3 B st3 e X pv xi qv wp wx wq v st4 HM3 Wp3 Wx3 Dp3 Dx3 Dq3 E4)
    as (pp & qq & -> & -> & -> & HR).
  eexists. split.
  - intros f ls l rest j cs m fuel _.
    apply rule_flight with (xs := [WInt (ptr_addr pp mod 2 ^ 64); WInt (dint ρ3 xi)]).
    + cbn [map_option flight_arg_x]. rewrite Ep, Ex. reflexivity.
    + reflexivity.
    + cbn [flight_cap]. rewrite Eq. reflexivity.
  - destruct (R_bind guard ge gobjs _ _ _ _ _ _ _ _ d HR) as (ρ4 & H4 & _). exists ρ4. exact H4.
Qed.

(** The function [reads] recognises the instructions of this section.
    An allocation is a [Let] that changes memory, so it is not one of
    them. *)
Definition reads (i : inst) : bool :=
  match i with
  | Let _ _ (Alloc _) _ => false
  | Let _ _ _ _ | Flight _ _ _ _ => true
  | _ => false
  end.

Ltac eff es :=
  let x := fresh "x" in
  destruct es as [|x es]; [discriminate|]; destruct x; try discriminate.

(** The lemmas above combine into one statement. If the checker
    accepts an instruction that leaves memory alone, then the machine
    steps over it, and the checker's next state is true of the
    machine's next environment. *)
Lemma ainst_read_sound ρ B st e X i st' :
  M ρ B st e X -> reads i = true -> ainst i st = Some st' ->
  exists e', steps_to B X e i e' /\ exists ρ', M ρ' B st' e' X.
Proof using Hfn.
  intros HM Hr. destruct i as [d k o args|d o args lw| | | | | | |]; try discriminate Hr.
  - destruct o; try discriminate Hr;
      try (match goal with |- AbsRun.ainst _ _ _ _ (Let ?d ?k ?o ?args) ?st = _ -> _ =>
             exact (arith_sound ρ B st e X d k o args st' HM eq_refl) end);
      try (cbn [AbsRun.ainst]; discriminate).
    + apply (check_sound ρ). exact HM.
    + apply (check2_sound ρ); [exact HM | reflexivity | reflexivity|].
      intros m pl q1 q Hl _ Hc. exact (renew_op m pl q1 q _ _ _ _ Hl Hc).
    + apply (check2_sound ρ); [exact HM | reflexivity | reflexivity|].
      intros m pl q1 q Hl Hlt Hc. exact (half_check_op m pl q1 q _ _ _ _ _ Hl Hlt Hc).
    + apply (check_function_sound ρ). exact HM.
    + apply (load_sound ρ). exact HM.
    + cbn [AbsRun.ainst]. eff es. eff es. eff es. destruct es; [|discriminate].
      apply (load_ptr_sound ρ). exact HM.
  - cbn [AbsRun.ainst]. destruct o; try discriminate.
    destruct args as [|[p|p] [|[x|x] [|]]]; try discriminate. destruct lw as [|q]; try discriminate.
    apply (flight_sound ρ). exact HM.
Qed.

(** * Stores *)

(** A store changes memory inside one object. The regions stay the
    same, the object holds its new contents, and every byte and every
    shadow slot outside the object's contents keeps its value. *)
Definition writes (m m' : mem) (pl : place) (xs : list Z) (cs : list cap) (xs' : list Z) (cs' : list cap) : Prop :=
  m_regions m' = m_regions m /\ holds m' pl xs' cs' /\
  (forall a, ~ (pl_base pl <= a < pl_base pl + Z.of_nat (length xs)) -> m_bytes m' a = m_bytes m a) /\
  (forall a, ~ (pl_base pl <= a < pl_base pl + Z.of_nat (length cs)) -> m_aux m' a = m_aux m a).

(** The machine steps over a store instruction, in every memory where
    the object holds its old contents, and the step writes the new
    contents. The environment does not change. *)
Definition stores_to (pl : place) (xs : list Z) (cs : list cap) (xs' : list Z) (cs' : list cap)
    (e : env) (i : inst) : Prop :=
  exists upd : mem -> mem, forall f ls l rest j cs0 m fuel, holds m pl xs cs ->
    Semantics.step ge (mkConfig (mkFrame f e ls None (Exec l (i :: rest) j)) cs0 m fuel) =
    Next (mkConfig (mkFrame f e ls None (Exec l rest j)) cs0 (upd m) fuel) /\
    writes m (upd m) pl xs cs xs' cs'.

(** The proposition [store_post] says what follows when the checker
    accepts a store. The store goes to the object numbered [o], and the
    checker's next state is true of the contents with that object
    replaced. *)
Definition store_post (ρ : nat -> Z) (B : list place) (st' : astate) (e : env) (X : cont) (i : inst) : Prop :=
  exists o pl xs cs xs' cs', nth_error B o = Some pl /\ nth_error X o = Some (Some (xs, cs)) /\
    length xs' = length xs /\ length cs' = length cs /\ stores_to pl xs cs xs' cs' e i /\
    exists ρ', M ρ' B st' e (list_set o (Some (xs', cs')) X).

Lemma store_sound ρ B st e X w off v a st' :
  M ρ B st e X -> ainst (RawStore w off v a) st = Some st' -> store_post ρ B st' e X (RawStore w off v a).
Proof using Hfn.
  intros HM. cbn [AbsRun.ainst]. destruct (width_value_class w) as [vk|] eqn:Ek; [|discriminate].
  destruct (avalue vk v st) as [[x st1]|] eqn:E1; [|discriminate].
  destruct (avalue A a st1) as [[p st2]|] eqn:E2; [|discriminate]. intros Es.
  destruct (avalue_sound guard ge gobjs fnames Hfn ρ B st e X _ _ _ _ HM E1) as (wv & Ev & ρ1 & HM1 & _ & Wx1 & Dx1).
  destruct (avalue_sound guard ge gobjs fnames Hfn ρ1 B st1 e X _ _ _ _ HM1 E2) as (wa & Ea & ρ2 & HM2 & S2 & Wp2 & Dp2).
  destruct (step_val ge _ _ _ _ B x wv S2 Wx1 Dx1) as [Wx2 Dx2].
  destruct (astore_sound guard ge gobjs ρ2 B st2 e X w off x p wv wa st' HM2 Wx2 Wp2 Dx2 Dp2 Es)
    as (o & pl & xs & cs & q & z & k & n & Ew & [Hpl Hx Ep Ez Hk Hn Haddr Hloc (ρ3 & HM3 & _)]).
  subst wa wv.
  exists o, pl, xs, cs, (splice k (bytes_of z n) xs), cs. split; [exact Hpl|]. split; [exact Hx|].
  split; [apply length_splice; rewrite ?length_bytes_of; lia|]. split; [reflexivity|].
  split; [|exists ρ3; exact HM3].
  exists (fun m => store_bytes m (pl_base pl + k) (Z.of_nat n) z). intros f ls l rest j cs0 m fuel Hm. split.
  - apply rule_raw_store with (vk := vk) (x := WInt z) (p := q); [exact Ek | exact Ev | exact Ea|].
    rewrite (raw_store_op m pl q w off (Z.of_nat n) z Ew (Hloc m (proj1 Hm))), Haddr. reflexivity.
  - split; [reflexivity|]. split; [apply holds_store_bytes; assumption|]. split.
    + intros a0 Ha0. apply store_bytes_other. lia.
    + intros a0 _. reflexivity.
Qed.

Lemma store_ptr_sound ρ B st e X off v a st' :
  M ρ B st e X ->
  ainst (RawStorePointer off v a [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]) st = Some st' ->
  store_post ρ B st' e X (RawStorePointer off v a [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]).
Proof using Hfn.
  intros HM. cbn [AbsRun.ainst].
  destruct (avalue P v st) as [[x st1]|] eqn:E1; [|discriminate].
  destruct (avalue A a st1) as [[p st2]|] eqn:E2; [|discriminate]. intros Es.
  destruct (avalue_sound guard ge gobjs fnames Hfn ρ B st e X _ _ _ _ HM E1) as (wv & Ev & ρ1 & HM1 & _ & Wx1 & Dx1).
  destruct (avalue_sound guard ge gobjs fnames Hfn ρ1 B st1 e X _ _ _ _ HM1 E2) as (wa & Ea & ρ2 & HM2 & S2 & Wp2 & Dp2).
  destruct (step_val ge _ _ _ _ B x wv S2 Wx1 Dx1) as [Wx2 Dx2].
  destruct (astore_ptr_sound guard ge gobjs ρ2 B st2 e X off x p wv wa st' HM2 Wp2 Dx2 Dp2 Es)
    as (o & pl & xs & cs & q & xp & k & [Hpl Hx Ep Ez Hk Hn Hc Haddr Hloc HM3]).
  subst wa wv.
  exists o, pl, xs, cs, (splice k (bytes_of (ptr_addr xp) 8) xs), (splice k [ptr_cap xp] cs).
  split; [exact Hpl|]. split; [exact Hx|].
  split; [apply length_splice; rewrite ?length_bytes_of; cbn [Z.of_nat]; lia|].
  split; [apply length_splice; cbn [length]; lia|]. split; [|exists ρ2; exact HM3].
  exists (fun m => store_bytes (store_aux m (pl_base pl + k) (ptr_cap xp)) (pl_base pl + k) 8 (ptr_addr xp)).
  intros f ls l rest j cs0 m fuel Hm. pose proof (Hloc m (proj1 Hm)) as Hl. split.
  - apply rule_raw_store_pointer with (xp := xp) (p := q); [exact Ev | exact Ea | exact (located_access _ _ _ _ _ _ _ Hl)|].
    rewrite (loc_addr _ _ _ _ _ _ _ Hl), Haddr. apply pointer_store_plain.
  - split; [reflexivity|]. split; [apply holds_store_ptr; assumption|]. split.
    + intros a0 Ha0. rewrite store_bytes_other by lia. reflexivity.
    + intros a0 Ha0. cbn [store_bytes store_aux m_aux]. destruct (Z.eqb_spec a0 (pl_base pl + k)); [lia | reflexivity].
Qed.

Definition is_store (i : inst) : bool :=
  match i with RawStore _ _ _ _ | RawStorePointer _ _ _ _ => true | _ => false end.

(** A store that the checker accepts steps on the machine and writes
    the contents that the checker's next state describes. *)
Lemma ainst_write_sound ρ B st e X i st' :
  M ρ B st e X -> is_store i = true -> ainst i st = Some st' -> store_post ρ B st' e X i.
Proof using Hfn.
  intros HM Hs. destruct i as [| |w off v a|off v a es| | | | |]; try discriminate Hs.
  - apply (store_sound ρ). exact HM.
  - cbn [AbsRun.ainst]. eff es. eff es. eff es. eff es. eff es. destruct es; [|discriminate].
    apply (store_ptr_sound ρ). exact HM.
Qed.

(** * Allocation *)

(** An allocation that the checker accepts asks for a size within the
    limit. Whatever base the allocator returns, the checker's next
    state is true of the places and contents with the new object added. *)
Lemma ainst_alloc_sound ρ B st e X d k al args st' :
  M ρ B st e X -> ainst (Let d k (Alloc al) args) st = Some st' ->
  exists n, map2_option (value_x ge e) [L] args = Some [WInt n] /\ 0 <= n <= max_allocation_size /\
    forall base, 0 < base -> base mod Z.max al 16 = 0 -> base + (n + 15) / 16 * 16 <= 2 ^ 48 ->
      let N := Z.to_nat ((n + 15) / 16 * 16) in
      let pl := mkPlace base (mkRegion base (base + (n + 15) / 16 * 16) Heap Live) false in
      exists ρ', M ρ' (B ++ [pl]) st' (put d (WPtr (mkPtr base (Obj base))) e)
                   (X ++ [Some (repeat 0 N, repeat CNone N)]).
Proof using Hfn.
  intros HM. cbn [AbsRun.ainst].
  destruct (avalues [L] args st) as [[xs st1]|] eqn:Ea; [|discriminate].
  destruct xs as [|[[n|]| | | | | |] [|]]; try discriminate.
  destruct ((0 <=? n) && (n <? 2 ^ 32)) eqn:En; [|discriminate]. intros [= <-].
  apply andb_true_iff in En as [N1 N2]. apply Z.leb_le in N1. apply Z.ltb_lt in N2.
  destruct (avalues_sound guard ge gobjs fnames Hfn ρ B st e X _ _ _ _ HM Ea) as (ws & Ews & HR).
  destruct (Rs_one _ _ _ _ _ _ _ _ HR) as (ρ1 & w & -> & HM1 & _ & Dn). cbn [dval dint] in Dn. subst w.
  exists n. split; [exact Ews|]. split; [unfold max_allocation_size; lia|].
  intros base Hb Hmod Hend.
  destruct (M_alloc guard ge gobjs ρ1 B st1 e X al n base HM1 N1 Hb Hmod Hend) as [HM2 Dv].
  exists ρ1. apply M_bind; [exact HM2 | exact I | exact Dv].
Qed.

(** * Branches *)

(** A branch reads a number. The checker continues on the side that
    the machine takes, in a state that is true of the same environment. *)
Lemma abranch_sound ρ B st e X v x st2 yes no :
  M ρ B st e X -> avalue W v st = Some (x, st2) -> abranch x st2 = Some (yes, no) ->
  exists n, value_x ge e W v = Some (WInt n) /\
    (n <> 0 -> exists s ρ', yes = Some s /\ M ρ' B s e X) /\
    (n = 0 -> exists s ρ', no = Some s /\ M ρ' B s e X).
Proof using Hfn.
  intros HM Ea Eb.
  destruct (avalue_sound guard ge gobjs fnames Hfn ρ B st e X _ _ _ _ HM Ea) as (w & Ev & ρ1 & HM1 & _ & W1 & D1).
  destruct x as [a|c k a b| | | | |]; try discriminate Eb; cbn [abranch] in Eb; injection Eb as <- <-;
    cbn [dval wf_val] in D1, W1.
  - subst w. exists (dint ρ1 a). split; [exact Ev|]. split; intros Hn.
    + destruct (ref_ne_sound guard ge gobjs ρ1 B st2 e X a (K 0) HM1 W1 I Hn) as (s1 & E1 & H1 & L1).
      rewrite E1. rewrite <- L1 in W1.
      destruct (note_nonzero_sound guard ge gobjs ρ1 B s1 e X a H1 W1 Hn) as (s2 & E2 & H2 & _).
      exists s2, ρ1. split; [exact E2 | exact H2].
    + destruct (ref_eq_sound guard ge gobjs ρ1 B st2 e X a (K 0) HM1 W1 I Hn) as (s1 & E1 & H1 & _).
      exists s1, ρ1. split; [exact E1 | exact H1].
  - destruct D1 as (r & Hc & ->). destruct W1 as [Wa Wb]. exists r. split; [exact Ev|].
    destruct (refine_sound guard ge gobjs ρ1 B st2 e X c k a b r HM1 Wa Wb Hc) as (s1 & E1 & H1 & _).
    split; intros Hn.
    + replace (negb (r =? 0)) with true in E1 by (symmetry; apply negb_true_iff, Z.eqb_neq; exact Hn).
      exists s1, ρ1. split; [exact E1 | exact H1].
    + subst r. exists s1, ρ1. split; [exact E1 | exact H1].
Qed.

(** * Phis *)

(** A state stays true when its environment is replaced by one whose
    values describe the words of a new real environment. *)
Lemma M_set_env ρ B st e X env' e' :
  M ρ B st e X -> Forall (fun nv => wf_val (length (st_bnd st)) (snd nv)) env' ->
  (forall n v, lookup n env' = Some v -> exists w, lookup n e' = Some w /\ dval ge ρ B v w) ->
  M ρ B (set_env st env') e' X.
Proof using Type.
  intros (HB & HG & Hs & (We & Wf & Wl & Wo) & He & Ho) W' H'.
  split; [exact HB|]. split; [exact HG|]. split; [exact Hs|]. split; [|split; [exact H' | exact Ho]].
  split; [exact W'|]. split; [exact Wf | split; [exact Wl | exact Wo]].
Qed.

(** When control enters a block, each phi of the block picks the
    value that belongs to the edge taken and binds it to a name. Every
    phi reads the environment that the previous block left. The checker
    binds abstract values in the same way. The proof handles one phi
    at a time and keeps an invariant between two phis. The checker's
    state is true of the old environment, and each value bound so far
    describes the word that the machine bound to the same name. *)
Definition phi_inv (ρ0 : nat -> Z) (st : astate) (e0 : env) (B : list place) (X : cont)
    (ρ : nat -> Z) (stT : astate) (ea : list (name * aval)) (em : env) : Prop :=
  M ρ B stT e0 X /\ step ρ0 st ρ stT /\
  Forall (fun nv => wf_val (length (st_bnd stT)) (snd nv)) ea /\
  (forall n v, lookup n ea = Some v -> exists w, lookup n em = Some w /\ dval ge ρ B v w).

Lemma aphis_fold ρ0 B st e0 X pred : M ρ0 B st e0 X -> forall phis ρ stT ea em res,
  phi_inv ρ0 st e0 B X ρ stT ea em ->
  fold_left (fun acc ph =>
               let? (e, st') := acc in
               match ph with
               | Phi d k pairs =>
                   let* v := lookup pred pairs in
                   let? (x, st2) := avalue k v (set_env st' (st_env st)) in
                   Some ((d, x) :: e, st2)
               end) phis (Some (ea, stT)) = Some res ->
  exists em' ρ',
    fold_left (fun acc ph =>
                 let* e := acc in
                 match ph with
                 | Phi d k pairs =>
                     let* v := lookup pred pairs in
                     let* x := value_x ge e0 k v in
                     Some (put d x e)
                 end) phis (Some em) = Some em' /\
    phi_inv ρ0 st e0 B X ρ' (snd res) (fst res) em'.
Proof using Hfn.
  intros HM0.
  assert (Hnone : forall phis : list phi,
            fold_left (fun (acc : option (list (name * aval) * astate)) ph =>
               let? (e, st') := acc in
               match ph with
               | Phi d k pairs =>
                   let* v := lookup pred pairs in
                   let? (x, st2) := avalue k v (set_env st' (st_env st)) in
                   Some ((d, x) :: e, st2)
               end) phis None = None).
  { induction phis as [|ph phis IH]; [reflexivity | exact IH]. }
  induction phis as [|[d k pairs] phis IH]; intros ρ stT ea em res Hinv; cbn [fold_left].
  - intros [= <-]. exists em, ρ. split; [reflexivity | exact Hinv].
  - destruct (lookup pred pairs) as [v|] eqn:Ev; [|rewrite Hnone; discriminate].
    destruct (avalue k v (set_env stT (st_env st))) as [[x st2]|] eqn:Ea; [|rewrite Hnone; discriminate].
    destruct Hinv as (HMT & ST & Wea & Hea).
    assert (HMr : M ρ B (set_env stT (st_env st)) e0 X).
    { apply (M_set_env ρ B stT e0 X _ e0 HMT).
      - destruct HM0 as (_ & _ & _ & (We & _) & _). eapply Forall_impl; [|exact We].
        intros nv. apply wf_val_mono. exact (proj2 ST).
      - intros n v0 Hl. destruct (M_env guard ge gobjs _ _ _ _ _ _ _ HM0 Hl) as (W0 & w0 & H1 & H2).
        exists w0. split; [exact H1|]. exact (dval_agree ge _ _ _ B v0 w0 (proj1 ST) W0 H2). }
    destruct (avalue_sound guard ge gobjs fnames Hfn ρ B _ e0 X _ _ _ _ HMr Ea) as (w & Evx & ρ' & HM' & S' & Wx & Dx).
    rewrite Evx. apply (IH ρ' st2 ((d, x) :: ea) (put d w em) res).
    split; [exact HM'|]. split; [exact (step_trans _ _ _ _ _ _ ST S')|]. split.
    + constructor; [exact Wx|]. eapply Forall_impl; [|exact Wea]. intros nv. apply wf_val_mono. exact (proj2 S').
    + intros n v0. cbn [lookup]. rewrite lookup_put_name.
      destruct (name_eqb n d); [intros [= <-]; exists w; split; [reflexivity | exact Dx]|].
      intros Hl. destruct (Hea n v0 Hl) as (w0 & H1 & H2). exists w0. split; [exact H1|].
      destruct (lookup_In _ _ _ Hl) as [k0 Hin]. rewrite Forall_forall in Wea.
      exact (dval_agree ge _ _ _ B v0 w0 (proj1 S') (Wea _ Hin) H2).
Qed.

(** Entering a block is safe when the checker accepts it. If the
    checker can bind the names at the start of a block, then the
    machine can bind them too, and the checker's new state is true of
    the machine's new environment. *)
Lemma aphis_sound ρ B st e X phis from st' :
  M ρ B st e X -> aphis gobjs fnames phis from st = Some st' ->
  exists e' ρ', phis_env ge phis from e = Some e' /\ M ρ' B st' e' X.
Proof using Hfn.
  intros HM. unfold aphis, phis_env. destruct from as [pred|].
  - match goal with |- match ?t with Some _ => _ | None => _ end = _ -> _ => destruct t as [[ea stT]|] eqn:Ef end;
      [|discriminate].
    intros [= <-].
    destruct (aphis_fold ρ B st e X pred HM phis ρ st (st_env st) e (ea, stT)) as (em' & ρ' & Em & (HMT & ST & Wea & Hea)).
    + split; [exact HM|]. split; [apply step_refl|]. destruct HM as (_ & _ & _ & (We & _) & He & _). split; assumption.
    + exact Ef.
    + exists em', ρ'. split; [exact Em|]. exact (M_set_env ρ' B stT e X ea em' HMT Wea Hea).
  - destruct phis; [|discriminate]. intros [= <-]. exists e, ρ. split; [reflexivity | exact HM].
Qed.

End step.
