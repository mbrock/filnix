(** Constant-time cryptographic kernels often allocate temporary buffers on
    the heap, call helper routines, loop over variable-length inputs, and
    free scratch storage before returning. This module brings byte and
    capability [[poison]] tracking into Iris separation logic so one Hoare
    triple proves both memory safety and two-run constant-time trace
    equivalence for heap-using programs.

    A program proof owns both memory contents and the restrictions on using
    them. The logic records those restrictions in a separate [[ghost-state|ghost heap]],
    including the taint of capabilities stored in [[aux]]. Existing proofs
    over Logic.v keep their exact statements. *)

From Stdlib Require Import String ZArith List Bool Lia Relations.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language ectx_language ectxi_language weakestpre lifting
  ectx_lifting adequacy.
From iris.base_logic.lib Require Import gen_heap.
From iris.bi.lib Require Import fractional.
From Nanofil Require Import Term Maps Syntax Values Memory Runtime Ops Semantics
  Run Machine Panics StepRules Pieces Heap Language Logic PoisonModel.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Poison pieces and ghost-heap agreement

    A local proof must know which restrictions apply to the bytes it owns.
    The [[ghost-state|ghost heap]] records those restrictions and checks
    that each entry agrees with the instrumented machine's state. *)

(** Each poison location identifies an object's byte or an [[aux]] slot. *)
Inductive ppiece : Type :=
| PPByte (b o : Z)
| PPAux (b o : Z).

(** A poison entry stores byte restrictions or capability taint. *)
Inductive ppval : Type :=
| VPByte (pb : poison_byte)
| VPAux (tc : taint).

(** Each poison location belongs to one object. *)
Definition ppiece_id (l : ppiece) : Z :=
  match l with
  | PPByte b _ | PPAux b _ => b
  end.

Instance taint_eq_dec : EqDecision taint.
Proof. solve_decision. Qed.

Instance poison_byte_eq_dec : EqDecision poison_byte.
Proof. solve_decision. Qed.

Instance ppiece_eq_dec : EqDecision ppiece.
Proof. solve_decision. Qed.

Instance ppiece_countable : Countable ppiece.
Proof.
  refine (inj_countable'
    (fun l => match l with
              | PPByte b o => inl (b, o)
              | PPAux b o => inr (b, o)
              end)
    (fun t => match t with
              | inl (b, o) => PPByte b o
              | inr (b, o) => PPAux b o
              end) _).
  by intros [].
Qed.

(** An owned entry must match the machine's poison state while its object
    is live. The entry remains valid after free, but cannot justify an
    access without a separate live token. *)
Definition agree_ppiece (m : mem) (pm : Z -> poison_byte) (paux : Z -> taint)
    (l : ppiece) (v : ppval) : Prop :=
  match l, v with
  | PPByte b o, VPByte pb => registered m b /\ in_live m b o (pm (b + o) = pb)
  | PPAux b o, VPAux tc => registered m b /\ in_live m b o (paux (b + o) = tc)
  | _, _ => False
  end.

(** Every entry in the shared poison map must agree with the machine. *)
Definition agrees_p (m : mem) (pm : Z -> poison_byte) (paux : Z -> taint)
    (ph : gmap ppiece ppval) : Prop :=
  forall l v, ph !! l = Some v -> agree_ppiece m pm paux l v.

(** A local proof records restrictions for each byte it owns. This check
    ensures that the recorded restrictions match the executing program. *)
Fixpoint all_p_agree (m : mem) (pm : Z -> poison_byte) (paux : Z -> taint)
    (pps : list (ppiece * ppval)) : Prop :=
  match pps with
  | [] => True
  | lv :: pps' => agree_ppiece m pm paux (fst lv) (snd lv) /\ all_p_agree m pm paux pps'
  end.

(** A local update must preserve agreement for entries it does not own. *)
Definition pframe_ok (ks : list ppiece) (m m' : mem)
    (pm pm' : Z -> poison_byte) (paux paux' : Z -> taint) : Prop :=
  forall l v, l ∉ ks -> agree_ppiece m pm paux l v -> agree_ppiece m' pm' paux' l v.

(** Updating the shared map gives the first listed entry precedence. *)
Fixpoint poverwrite (pps : list (ppiece * ppval)) (ph : gmap ppiece ppval)
  : gmap ppiece ppval :=
  match pps with
  | [] => ph
  | lv :: pps' => <[fst lv := snd lv]> (poverwrite pps' ph)
  end.

(** An eight-byte cell can own the same poison restriction at every byte. *)
Definition pcell_ps (b o : Z) (pb : poison_byte) : list (ppiece * ppval) :=
  map (fun i => (PPByte b (o + i), VPByte pb)) [0; 1; 2; 3; 4; 5; 6; 7].

(** A byte list owns consecutive poison entries within an object. *)
Fixpoint pbytes_ps (b o : Z) (pbs : list poison_byte) : list (ppiece * ppval) :=
  match pbs with
  | [] => []
  | pb :: rest => (PPByte b o, VPByte pb) :: pbytes_ps b (o + 1) rest
  end.

(** A fresh object owns clean bytes and unrestricted capability slots
    throughout its allocated extent. *)
Definition pobj_ps (base : Z) (q : alloc_req) : list (ppiece * ppval) :=
  ((fun i => (PPByte base i, VPByte pb_clean)) <$> seqZ 0 (req_extent q)) ++
  ((fun i => (PPAux base i, VPAux taint_bot)) <$> seqZ 0 (req_extent q)).

Lemma all_p_agree_app m pm paux pps qps :
  all_p_agree m pm paux (pps ++ qps) <-> all_p_agree m pm paux pps /\ all_p_agree m pm paux qps.
Proof. induction pps as [|lv pps IH]; cbn; [tauto | rewrite IH; tauto]. Qed.

Lemma all_p_agree_elem m pm paux pps l v :
  all_p_agree m pm paux pps -> (l, v) ∈ pps -> agree_ppiece m pm paux l v.
Proof.
  induction pps as [|[l' v'] pps IH]; cbn; intros H Hin.
  - by apply not_elem_of_nil in Hin.
  - apply elem_of_cons in Hin as [[= -> ->] | Hin]; [exact (proj1 H) | exact (IH (proj2 H) Hin)].
Qed.

Lemma all_p_agree_intro m pm paux pps :
  (forall l v, (l, v) ∈ pps -> agree_ppiece m pm paux l v) -> all_p_agree m pm paux pps.
Proof.
  induction pps as [|[l v] pps IH]; cbn; intros H; [exact I|].
  split; [apply H; left | apply IH; intros l' v' Hin; apply H; by right].
Qed.

Lemma lookup_poverwrite pps ph l v :
  poverwrite pps ph !! l = Some v ->
  (l, v) ∈ pps \/ (l ∉ pps.*1 /\ ph !! l = Some v).
Proof.
  induction pps as [|[l' v'] pps IH]; cbn.
  - intros H. right. split; [apply not_elem_of_nil | exact H].
  - rewrite lookup_insert. destruct (decide (l' = l)) as [-> | Hne].
    + intros [= ->]. left. by left.
    + intros H. destruct (IH H) as [Hin | [Hn Hph]].
      * left. by right.
      * right. split; [apply not_elem_of_cons; auto | exact Hph].
Qed.

Lemma agree_ppiece_registered m pm paux l v :
  agree_ppiece m pm paux l v -> registered m (ppiece_id l).
Proof. destruct l, v; cbn; tauto. Qed.

(** A collector safepoint preserves poison restrictions. It may sanitize
    stored capabilities but does not change the analysis state. *)
Lemma agree_ppiece_safepoint m m' pm paux l v :
  same_regions m m' ->
  agree_ppiece m pm paux l v ->
  agree_ppiece m' pm paux l v.
Proof.
  intros Hsr.
  destruct l as [b o | b o], v as [pb | tc]; cbn [agree_ppiece]; try tauto;
    unfold registered, in_live; intros [Hr Hin];
    (split; [rewrite (Hsr b); exact Hr | intros reg E L; rewrite (Hsr b) in E; exact (Hin reg E L)]).
Qed.

(** Free keeps the object's identity registered but ends its lifetime.
    Existing poison entries remain valid without permitting further accesses. *)
Lemma agree_ppiece_free m base rs pm paux l v :
  replace_region base (mkRegion base base Heap Freed) (m_regions m) = Some rs ->
  agree_ppiece m pm paux l v ->
  agree_ppiece (mkMem (m_bytes m) rs (m_aux m)) pm paux l v.
Proof.
  intros Hrs.
  destruct l as [b o | b o], v as [pb | tc]; cbn [agree_ppiece]; try tauto;
    unfold registered, in_live; cbn [m_regions]; intros [Hr Hin].
  - destruct (Z.eq_dec b base) as [-> | Hne].
    + rewrite (object_region_replace _ _ _ _ base Hrs eq_refl) Z.eqb_refl.
      split; [discriminate | intros reg [= <-] Hlf; discriminate Hlf].
    + rewrite (object_region_replace _ _ _ _ b Hrs eq_refl) (proj2 (Z.eqb_neq _ _) Hne); auto.
  - destruct (Z.eq_dec b base) as [-> | Hne].
    + rewrite (object_region_replace _ _ _ _ base Hrs eq_refl) Z.eqb_refl.
      split; [discriminate | intros reg [= <-] Hlf; discriminate Hlf].
    + rewrite (object_region_replace _ _ _ _ b Hrs eq_refl) (proj2 (Z.eqb_neq _ _) Hne); auto.
Qed.

(** A write to owned entries preserves every other object's restrictions. *)
Lemma pframe_within ks m m' b reg pm pm' paux paux' :
  m_regions m' = m_regions m ->
  live_disjoint m ->
  live_at m b reg ->
  (forall a, pm' a <> pm a -> b <= a < r_end reg /\ PPByte b (a - b) ∈ ks) ->
  (forall a, paux' a <> paux a -> b <= a < r_end reg /\ PPAux b (a - b) ∈ ks) ->
  pframe_ok ks m m' pm pm' paux paux'.
Proof.
  intros Hreg Hd Hlv Hpm Hpaux l v Hnot Hag.
  destruct l as [b' o | b' o], v as [pb | tc]; cbn [agree_ppiece] in *; try contradiction.
  - destruct Hag as [Hr Hin]. unfold registered, in_live in *. rewrite Hreg.
    split; [exact Hr | intros reg' E' L'].
    destruct (Hin reg' E' L') as (Ho & He & Hval).
    split; [exact Ho | split; [exact He |]].
    destruct (decide (pm' (b' + o) = pm (b' + o))) as [-> | Hne]; [exact Hval|].
    exfalso. destruct (Hpm (b' + o) Hne) as [Hbounds Hin_ks].
    destruct (Z.eq_dec b' b) as [-> | Hbne].
    + replace (b + o - b) with o in Hin_ks by lia. exact (Hnot Hin_ks).
    + destruct (Hd b reg b' reg' Hlv (conj E' L') (not_eq_sym Hbne)); lia.
  - destruct Hag as [Hr Hin]. unfold registered, in_live in *. rewrite Hreg.
    split; [exact Hr | intros reg' E' L'].
    destruct (Hin reg' E' L') as (Ho & He & Hval).
    split; [exact Ho | split; [exact He |]].
    destruct (decide (paux' (b' + o) = paux (b' + o))) as [-> | Hne]; [exact Hval|].
    exfalso. destruct (Hpaux (b' + o) Hne) as [Hbounds Hin_ks].
    destruct (Z.eq_dec b' b) as [-> | Hbne].
    + replace (b + o - b) with o in Hin_ks by lia. exact (Hnot Hin_ks).
    + destruct (Hd b reg b' reg' Hlv (conj E' L') (not_eq_sym Hbne)); lia.
Qed.

Lemma pobj_ps_id base q l v : (l, v) ∈ pobj_ps base q -> ppiece_id l = base.
Proof.
  unfold pobj_ps. intros Hin.
  apply elem_of_app in Hin as [Hin | Hin];
    apply list_elem_of_fmap in Hin as (i & [= -> ->] & _); reflexivity.
Qed.

Lemma pobj_ps_nodup base q : NoDup (pobj_ps base q).*1.
Proof.
  unfold pobj_ps. pose proof (NoDup_seqZ 0 (req_extent q)) as Hl. revert Hl.
  generalize (seqZ 0 (req_extent q)) as ns. intros ns Hl.
  rewrite fmap_app -!list_fmap_compose.
  apply NoDup_app. split; [|split].
  - apply NoDup_fmap_2_strong; [|exact Hl]. intros i j _ _ Hij. by injection Hij.
  - intros l. rewrite !list_elem_of_fmap. intros (i & -> & _) (j & Hj & _). discriminate Hj.
  - apply NoDup_fmap_2_strong; [|exact Hl]. intros i j _ _ Hij. by injection Hij.
Qed.

Lemma pobj_ps_agree m pm paux q base l v :
  Memory.fresh m q base ->
  0 <= req_extent q ->
  (l, v) ∈ pobj_ps base q ->
  agree_ppiece (allocated m q base)
    (unpoison_range pm base (req_extent q))
    (unpoison_aux paux base (req_extent q)) l v.
Proof.
  intros _ Hq Hin. unfold pobj_ps in Hin.
  apply elem_of_app in Hin as [Hin | Hin];
    apply list_elem_of_fmap in Hin as (i & [= -> ->] & Hi);
    apply elem_of_seqZ in Hi; cbn [agree_ppiece]; unfold registered, in_live;
    rewrite object_region_allocated Z.eqb_refl;
    (split; [discriminate|]);
    intros reg [= <-] _; cbn [r_end]; (split; [lia | split; [lia|]]).
  - unfold unpoison_range.
    replace ((base <=? base + i) && (base + i <? base + req_extent q)) with true; [reflexivity|].
    symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  - unfold unpoison_aux.
    replace ((base <=? base + i) && (base + i <? base + req_extent q)) with true; [reflexivity|].
    symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma agree_ppiece_allocated m pm paux q base l v :
  Memory.fresh m q base ->
  agree_ppiece m pm paux l v ->
  agree_ppiece (allocated m q base)
    (unpoison_range pm base (req_extent q))
    (unpoison_aux paux base (req_extent q)) l v.
Proof.
  intros (_ & _ & _ & Hnone & Hdisj & _) Hag.
  assert (Ho : forall b, object_region b (m_regions m) <> None ->
            object_region b (m_regions (allocated m q base)) = object_region b (m_regions m)).
  { intros b Hb. rewrite object_region_allocated.
    destruct (Z.eqb_spec base b) as [<-|]; [contradiction | reflexivity]. }
  destruct l as [b o | b o], v as [pb | tc]; cbn [agree_ppiece] in *; try contradiction;
    destruct Hag as [Hr Hin]; unfold registered, in_live in *; rewrite Ho; [|exact Hr| |exact Hr].
  - split; [exact Hr | intros reg E L].
    destruct (Hin reg E L) as (Ho0 & He & Hval).
    split; [exact Ho0 | split; [exact He |]].
    unfold unpoison_range.
    destruct ((base <=? b + o) && (b + o <? base + req_extent q)) eqn:Ein; [|exact Hval].
    exfalso. apply andb_true_iff in Ein as [E1 E2]; apply Z.leb_le in E1; apply Z.ltb_lt in E2.
    apply (Hdisj b reg E); split; lia.
  - split; [exact Hr | intros reg E L].
    destruct (Hin reg E L) as (Ho0 & He & Hval).
    split; [exact Ho0 | split; [exact He |]].
    unfold unpoison_aux.
    destruct ((base <=? b + o) && (b + o <? base + req_extent q)) eqn:Ein; [|exact Hval].
    exfalso. apply andb_true_iff in Ein as [E1 E2]; apply Z.leb_le in E1; apply Z.ltb_lt in E2.
    apply (Hdisj b reg E); split; lia.
Qed.

(** ## Owning poison pieces

    A proof of one operation should not need to inspect unrelated memory.
    Ownership assertions in [[separation-logic]] let it read and update
    its own entries while preserving the rest. *)

Section ppts.
Context `{!gen_heapGS ppiece ppval Σ}.

Definition ppts (pps : list (ppiece * ppval)) : iProp Σ :=
  [∗ list] lv ∈ pps, pointsto (fst lv) (DfracOwn 1) (snd lv).

Definition pptsq (dq : dfrac) (pps : list (ppiece * ppval)) : iProp Σ :=
  [∗ list] lv ∈ pps, pointsto (fst lv) dq (snd lv).

Lemma ppts_pptsq pps : ppts pps ⊣⊢ pptsq (DfracOwn 1) pps.
Proof. reflexivity. Qed.

Lemma ppts_app pps qps : ppts (pps ++ qps) ⊣⊢ ppts pps ∗ ppts qps.
Proof. by rewrite /ppts big_sepL_app. Qed.

Lemma pptsq_app dq pps qps : pptsq dq (pps ++ qps) ⊣⊢ pptsq dq pps ∗ pptsq dq qps.
Proof. by rewrite /pptsq big_sepL_app. Qed.

Lemma pptsq_split q1 q2 pps :
  pptsq (DfracOwn (q1 + q2)) pps ⊣⊢ pptsq (DfracOwn q1) pps ∗ pptsq (DfracOwn q2) pps.
Proof.
  rewrite /pptsq -big_sepL_sep. apply big_sepL_proper. intros _ lv _.
  exact (fractional (Φ := fun q => pointsto (fst lv) (DfracOwn q) (snd lv)) q1 q2).
Qed.

Lemma pptsq_persist dq pps : pptsq dq pps ==∗ □ pptsq DfracDiscarded pps.
Proof.
  induction pps as [|lv pps IH]; rewrite /pptsq /=; iIntros "H"; [by iModIntro|].
  iDestruct "H" as "[Hl H]". iMod (pointsto_persist with "Hl") as "#Hl".
  iMod (IH with "H") as "#H". iModIntro. iModIntro. iFrame "#".
Qed.

Instance pptsq_persistent pps : Persistent (pptsq DfracDiscarded pps).
Proof. rewrite /pptsq. apply _. Qed.

Lemma ppts_lookup ph pps :
  gen_heap_interp ph -∗ ppts pps -∗ ⌜forall l v, (l, v) ∈ pps -> ph !! l = Some v⌝.
Proof.
  induction pps as [|[l v] pps IH]; iIntros "Hph Hpps".
  - iPureIntro. intros l v Hin. by apply not_elem_of_nil in Hin.
  - rewrite /ppts /=. iDestruct "Hpps" as "[Hl Hpps]".
    iDestruct (gen_heap_valid with "Hph Hl") as %Hl.
    iDestruct (IH with "Hph Hpps") as %Hpps. iPureIntro.
    intros l' v' Hin. apply elem_of_cons in Hin as [[= -> ->] | Hin]; auto.
Qed.

Lemma pptsq_lookup ph dq pps :
  gen_heap_interp ph -∗ pptsq dq pps -∗ ⌜forall l v, (l, v) ∈ pps -> ph !! l = Some v⌝.
Proof.
  induction pps as [|[l v] pps IH]; iIntros "Hph Hpps".
  - iPureIntro. intros l v Hin. by apply not_elem_of_nil in Hin.
  - rewrite /pptsq /=. iDestruct "Hpps" as "[Hl Hpps]".
    iDestruct (gen_heap_valid with "Hph Hl") as %Hl.
    iDestruct (IH with "Hph Hpps") as %Hpps. iPureIntro.
    intros l' v' Hin. apply elem_of_cons in Hin as [[= -> ->] | Hin]; auto.
Qed.

Lemma ppts_update ph pps pps' :
  pps'.*1 = pps.*1 ->
  gen_heap_interp ph -∗ ppts pps ==∗ gen_heap_interp (poverwrite pps' ph) ∗ ppts pps'.
Proof.
  revert pps'. induction pps as [|[l v] pps IH]; intros [|[l' v'] pps'] Hk; try discriminate Hk.
  - iIntros "Hph _". iModIntro. iFrame. by rewrite /ppts.
  - cbn in Hk. injection Hk as -> Hk. iIntros "Hph Hpps". rewrite /ppts /=.
    iDestruct "Hpps" as "[Hl Hpps]".
    iMod (IH pps' Hk with "Hph Hpps") as "[Hph Hpps]".
    iMod (gen_heap_update with "Hph Hl") as "[Hph Hl]". iModIntro. iFrame.
Qed.

Lemma ppts_alloc ph pps :
  NoDup pps.*1 ->
  (forall l v, (l, v) ∈ pps -> ph !! l = None) ->
  gen_heap_interp ph ==∗ gen_heap_interp (poverwrite pps ph) ∗ ppts pps.
Proof.
  induction pps as [|[l v] pps IH]; intros Hnd Hfr.
  - iIntros "Hph". iModIntro. iFrame. by rewrite /ppts.
  - cbn in Hnd. apply NoDup_cons in Hnd as [Hn Hnd]. iIntros "Hph".
    iMod (IH Hnd with "Hph") as "[Hph Hpps]".
    { intros l' v' Hin. apply (Hfr l' v'). by right. }
    iMod (gen_heap_alloc _ l v with "Hph") as "(Hph & Hl & _)".
    { destruct (poverwrite pps ph !! l) as [v'|] eqn:E; [|reflexivity].
      destruct (lookup_poverwrite _ _ _ _ E) as [Hin | [_ Hph]].
      - exfalso. apply Hn. exact (list_elem_of_fmap_2 fst _ (l, v') Hin).
      - rewrite (Hfr l v) in Hph; [discriminate | by left]. }
    iModIntro. rewrite /ppts /=. iFrame.
Qed.

End ppts.

(** A single owned poison byte determines the load and store guards and
    the taint returned by a byte load. *)
Lemma mem_1_facts pm a pb :
  pm a = pb ->
  mem_no_load pm a 1 = pb_no_load pb /\
  mem_no_store pm a 1 = pb_no_store pb /\ mem_load_taint pm a 1 = pb_taint pb.
Proof.
  intros H. unfold mem_no_load, mem_no_store, mem_load_taint.
  change (Z.to_nat 1) with 1%nat; cbn [range_no_load_nat range_no_store_nat range_taint_nat].
  rewrite H !orb_false_r taint_join_bot_r. auto.
Qed.

(** Under the unpatched store rule, a third secret spill to the same stack
    slot still leaves its branch taint cleared. *)
Lemma buggy_third_store_stays_clean :
  t_branch (pb_taint
    (note_store_byte_buggy taint_branch
      (note_store_byte_buggy taint_branch
        (note_store_byte_buggy taint_branch pb_clean)))) = false.
Proof. reflexivity. Qed.

(** Eight bytes with the same poison state stay in bounds and determine
    both access guards and the taint of an 8-byte load. *)
Lemma pcell_ps_facts m pm paux b reg o pb :
  live_at m b reg ->
  all_p_agree m pm paux (pcell_ps b o pb) ->
  0 <= o /\ b + o + 8 <= r_end reg /\
  mem_no_load pm (b + o) 8 = pb_no_load pb /\
  mem_no_store pm (b + o) 8 = pb_no_store pb /\
  mem_load_taint pm (b + o) 8 = pb_taint pb.
Proof.
  intros [E L] Hag.
  cbn [pcell_ps map all_p_agree agree_ppiece fst snd] in Hag.
  destruct Hag as ([_ H0] & [_ H1] & [_ H2] & [_ H3] & [_ H4] & [_ H5] & [_ H6] & [_ H7] & _).
  destruct (H0 reg E L) as (Ho0 & _ & E0).
  destruct (H1 reg E L) as (_ & _ & E1).
  destruct (H2 reg E L) as (_ & _ & E2).
  destruct (H3 reg E L) as (_ & _ & E3).
  destruct (H4 reg E L) as (_ & _ & E4).
  destruct (H5 reg E L) as (_ & _ & E5).
  destruct (H6 reg E L) as (_ & _ & E6).
  destruct (H7 reg E L) as (_ & He7 & E7).
  replace (b + (o + 0)) with (b + o) in E0 by lia.
  replace (b + (o + 1)) with (b + o + 1) in E1 by lia.
  replace (b + (o + 2)) with (b + o + 2) in E2 by lia.
  replace (b + (o + 3)) with (b + o + 3) in E3 by lia.
  replace (b + (o + 4)) with (b + o + 4) in E4 by lia.
  replace (b + (o + 5)) with (b + o + 5) in E5 by lia.
  replace (b + (o + 6)) with (b + o + 6) in E6 by lia.
  replace (b + (o + 7)) with (b + o + 7) in E7 by lia.
  split; [lia | split; [lia |]].
  unfold mem_no_load, mem_no_store, mem_load_taint.
  change (Z.to_nat 8) with 8%nat.
  cbn [range_no_load_nat range_no_store_nat range_taint_nat].
  replace (b + o + 1 + 1) with (b + o + 2) by lia.
  replace (b + o + 2 + 1) with (b + o + 3) by lia.
  replace (b + o + 3 + 1) with (b + o + 4) by lia.
  replace (b + o + 4 + 1) with (b + o + 5) by lia.
  replace (b + o + 5 + 1) with (b + o + 6) by lia.
  replace (b + o + 6 + 1) with (b + o + 7) by lia.
  rewrite E0 E1 E2 E3 E4 E5 E6 E7 !orb_false_r taint_join_bot_r !taint_join_idem.
  destruct (pb_no_load pb), (pb_no_store pb); auto.
Qed.

(** Every byte address inside an 8-byte cell belongs to that cell's key list,
    so framing an 8-byte poison write needs no manual offset enumeration. *)
Lemma elem_pcell_ps_keys b o pb a :
  b + o <= a < b + o + 8 ->
  PPByte b (a - b) ∈ (pcell_ps b o pb).*1.
Proof.
  intros Ha. apply list_elem_of_In; unfold pcell_ps; cbn.
  assert (a - b = o + 0 \/ a - b = o + 1 \/ a - b = o + 2 \/ a - b = o + 3 \/
          a - b = o + 4 \/ a - b = o + 5 \/ a - b = o + 6 \/ a - b = o + 7) as Hc by lia.
  destruct Hc as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E;
    repeat (first [left; reflexivity | right]).
Qed.

(** Storing an 8-byte scalar into a uniform poison cell updates all eight
    poison entries in lockstep while preserving every unowned poison piece. *)
Lemma pcell_ps_store_ok m m' pm paux b reg o pb tv :
  m_regions m' = m_regions m ->
  live_disjoint m ->
  live_at m b reg ->
  all_p_agree m pm paux (pcell_ps b o pb) ->
  all_p_agree m' (mem_store_taint pm (b + o) 8 tv) paux (pcell_ps b o (note_store_byte tv pb)) /\
  pframe_ok (pcell_ps b o (note_store_byte tv pb)).*1 m m'
    pm (mem_store_taint pm (b + o) 8 tv) paux paux.
Proof.
  intros Hreg Hd Hlv Hag.
  destruct (pcell_ps_facts m pm paux b reg o pb Hlv Hag) as (Ho & He & _).
  split.
  - apply all_p_agree_intro. intros l v Hin.
    unfold pcell_ps in Hin; apply list_elem_of_In, in_map_iff in Hin as (i & [= <- <-] & Hi).
    assert (Hi_bound : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7)
      by (cbn in Hi; intuition lia).
    cbn [agree_ppiece]; unfold registered, in_live; rewrite Hreg.
    destruct Hlv as [Eb Lb].
    split; [rewrite Eb; discriminate | intros reg' E' _].
    rewrite Eb in E'; injection E' as <-.
    split; [lia | split; [lia |]].
    cbn [pcell_ps map all_p_agree agree_ppiece fst snd] in Hag.
    assert (Hpm_i : pm (b + (o + i)) = pb).
    { destruct Hag as ([_ H0] & [_ H1] & [_ H2] & [_ H3] & [_ H4] & [_ H5] & [_ H6] & [_ H7] & _).
      destruct Hi_bound as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
        [exact (proj2 (proj2 (H0 reg Eb Lb))) | exact (proj2 (proj2 (H1 reg Eb Lb)))
        |exact (proj2 (proj2 (H2 reg Eb Lb))) | exact (proj2 (proj2 (H3 reg Eb Lb)))
        |exact (proj2 (proj2 (H4 reg Eb Lb))) | exact (proj2 (proj2 (H5 reg Eb Lb)))
        |exact (proj2 (proj2 (H6 reg Eb Lb))) | exact (proj2 (proj2 (H7 reg Eb Lb)))]. }
    unfold mem_store_taint.
    replace ((b + o <=? b + (o + i)) && (b + (o + i) <? b + o + 8)) with true
      by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite Hpm_i; reflexivity.
  - apply (pframe_within _ m m' b reg pm _ paux paux Hreg Hd Hlv).
    + intros a Hne; unfold mem_store_taint in Hne.
      destruct ((b + o <=? a) && (a <? b + o + 8)) eqn:Ein; [|contradiction].
      apply andb_true_iff in Ein as [E1 E2]; apply Z.leb_le in E1; apply Z.ltb_lt in E2.
      split; [lia | exact (elem_pcell_ps_keys b o _ a (conj E1 E2))].
    + intros a Hne; contradiction.
Qed.

(** Storing a pointer into an 8-byte slot updates both the eight address-byte
    poison entries and the shadow capability taint slot while preserving all
    other poison pieces. *)
Lemma ppcell_ps_store_ok m m' pm paux b reg o pb tva tvc :
  m_regions m' = m_regions m ->
  live_disjoint m ->
  live_at m b reg ->
  all_p_agree m pm paux (pcell_ps b o pb) ->
  let paux' := fun a => if a =? b + o then tvc else paux a in
  all_p_agree m' (mem_store_taint pm (b + o) 8 tva) paux'
    ((PPAux b o, VPAux tvc) :: pcell_ps b o (note_store_byte tva pb)) /\
  pframe_ok (((PPAux b o, VPAux tvc) :: pcell_ps b o (note_store_byte tva pb)).*1) m m'
    pm (mem_store_taint pm (b + o) 8 tva) paux paux'.
Proof.
  intros Hreg Hd Hlv Hag paux'.
  destruct (pcell_ps_facts m pm paux b reg o pb Hlv Hag) as (Ho & He & _).
  destruct (pcell_ps_store_ok m m' pm paux b reg o pb tva Hreg Hd Hlv Hag) as [Hbytes _].
  split.
  - cbn [all_p_agree fst snd]. split.
    + cbn [agree_ppiece]; unfold registered, in_live; rewrite Hreg.
      destruct Hlv as [Eb Lb].
      split; [rewrite Eb; discriminate | intros reg' E' _].
      rewrite Eb in E'; injection E' as <-.
      split; [lia | split; [lia | unfold paux'; rewrite Z.eqb_refl; reflexivity]].
    + apply all_p_agree_intro; intros l v Hin.
      pose proof (all_p_agree_elem _ _ _ _ _ _ Hbytes Hin) as H0.
      unfold pcell_ps in Hin; apply list_elem_of_In, in_map_iff in Hin as (i & [= <- <-] & _).
      exact H0.
  - apply (pframe_within _ m m' b reg pm _ paux paux' Hreg Hd Hlv).
    + intros a Hne; unfold mem_store_taint in Hne.
      destruct ((b + o <=? a) && (a <? b + o + 8)) eqn:Ein; [|contradiction].
      apply andb_true_iff in Ein as [E1 E2]; apply Z.leb_le in E1; apply Z.ltb_lt in E2.
      split; [lia | cbn; right; exact (elem_pcell_ps_keys b o (note_store_byte tva pb) a (conj E1 E2))].
    + intros a Hne; unfold paux' in Hne.
      destruct (Z.eqb_spec a (b + o)) as [Ha_eq | _]; [|contradiction]; subst a.
      split; [lia | replace (b + o - b) with o by lia; left].
Qed.

(** When a pointer stored in memory names a heap or global object, a collector
    may clear its [[aux]] slot if that object has been freed. Borrowing a share
    of [cap_live_ps] proves the target object is still live when loaded. *)
Definition cap_live_ps (c : cap) (reg : region) : list (piece * pval) :=
  match c with
  | Obj b | Ro b => [(PLive b, VLive reg)]
  | _ => []
  end.

(** Agreement of [cap_live_ps] rules out collector clearing of the capability. *)
Lemma cap_live_ps_not_freed m c reg :
  all_agree m (cap_live_ps c reg) -> ~ freed_in (m_regions m) c.
Proof.
  intros Hag (b & reg' & Hc & E & L).
  destruct Hc as [-> | ->]; cbn [cap_live_ps all_agree agree_piece fst snd] in Hag;
    destruct Hag as [[E' L'] _]; rewrite E' in E; injection E as <-; congruence.
Qed.

(** ## Poison program logic over a runtime

    Programs execute alongside an allocator and collector that satisfy the
    [[runtime]] contract. The logic follows both ordinary values and poison
    restrictions through each instruction and helper call. *)

Module PoisonLogic (R : Runtime).

Module L := Language R.
Module SS := SafepointShape R.
Module P := L.P.
Module RM := L.RM.
Module PD := PoisonDriver R.
Import L.

(** ### Expressions, callers and head steps

    A helper call suspends the caller until its result is available.
    The [[iris|Iris]] language records both sides of that call so value
    and taint environments resume together. *)

(** An expression runs a frame, returns a value with its taint, or suspends
    a caller while a helper runs. Suspended callers retain their register taints. *)
Inductive pexpr : Type :=
| PRun (fr : frame) (te : tenv)
| PEnd (o : outcome) (ots : list word_taint)
| PWait (e : pexpr) (cf : frame) (cte : tenv) (r : call_result).

Inductive pectx_item : Type :=
| KPWait (cf : frame) (cte : tenv) (r : call_result).

Definition pfill_item (Ki : pectx_item) (e : pexpr) : pexpr :=
  match Ki with
  | KPWait cf cte r => PWait e cf cte r
  end.

Definition pof_val (vo : outcome * list word_taint) : pexpr :=
  PEnd (fst vo) (snd vo).

Definition pto_val (e : pexpr) : option (outcome * list word_taint) :=
  match e with
  | PEnd o ots => Some (o, ots)
  | _ => None
  end.

(** The machine state includes physical memory, poison restrictions,
    runtime state, and the remaining block fuel. *)
Record plstate : Type := mkPLstate {
  pl_mem : mem;
  pl_pm : Z -> poison_byte;
  pl_paux : Z -> taint;
  pl_rt : R.state;
  pl_fuel : Z
}.

(** Wrap `e` under a stack of caller triples `(cf, cte, r)`, innermost first. *)
Fixpoint pstack_expr (e : pexpr) (pcs : list (frame * tenv * call_result)) : pexpr :=
  match pcs with
  | [] => e
  | ((cf, cte), r) :: pcs' => pstack_expr (PWait e cf cte r) pcs'
  end.

Definition pctx_of (pcs : list (frame * tenv * call_result)) : list pectx_item :=
  map (fun '((cf, cte), r) => KPWait cf cte r) pcs.

Definition pcs_callers (pcs : list (frame * tenv * call_result)) : list (frame * pending) :=
  map (fun '((cf, _), r) => (cf, mkPending r None)) pcs.

Definition pcs_tcallers (pcs : list (frame * tenv * call_result)) : list (tenv * call_result) :=
  map (fun '((_, cte), r) => (cte, r)) pcs.

(** The ordinary and taint caller stacks determine the combined stack.
    This lets a lifting rule identify the continuation produced by a call. *)
Lemma pcs_sync_inj pcs1 pcs2 :
  pcs_callers pcs1 = pcs_callers pcs2 ->
  pcs_tcallers pcs1 = pcs_tcallers pcs2 -> pcs1 = pcs2.
Proof.
  revert pcs2. induction pcs1 as [|[[cf cte] r] pcs1 IH];
    intros [|[[cf' cte'] r'] pcs2] Hcs Htcs;
    cbn [pcs_callers pcs_tcallers] in *; try discriminate; [reflexivity|].
  injection Hcs as -> -> Hcs. injection Htcs as -> Htcs.
  f_equal. exact (IH _ Hcs Htcs).
Qed.

Lemma pcs_callers_app pcs1 pcs2 :
  pcs_callers (pcs1 ++ pcs2) = pcs_callers pcs1 ++ pcs_callers pcs2.
Proof. unfold pcs_callers. apply map_app. Qed.

Lemma pcs_tcallers_app pcs1 pcs2 :
  pcs_tcallers (pcs1 ++ pcs2) = pcs_tcallers pcs1 ++ pcs_tcallers pcs2.
Proof. unfold pcs_tcallers. apply map_app. Qed.

Lemma pstack_expr_app e pcs1 pcs2 :
  pstack_expr e (pcs1 ++ pcs2) = pstack_expr (pstack_expr e pcs1) pcs2.
Proof.
  revert e. induction pcs1 as [|[[cf cte] r] pcs1 IH]; intros e; [reflexivity | apply IH].
Qed.

Lemma pto_val_stack e pcs : pto_val e = None -> pto_val (pstack_expr e pcs) = None.
Proof.
  revert e. induction pcs as [|[[cf cte] r] pcs IH]; intros e H; [exact H | apply IH; reflexivity].
Qed.

(** Returning from a helper resumes both the caller's values and its taints. *)
Definition presume (cf : frame) (cte : tenv) (r : call_result)
    (o : outcome) (ots : list word_taint) : option (frame * tenv) :=
  let* cf' := resume cf (mkPending r None) o in
  let* cte' := returned_tenv r ots cte in
  Some (cf', cte').

(** A poisoned configuration fails when [pstep] hits a poison fault, gets
    stuck, ends with a [failure] outcome, or asks for a negative extent. *)
Definition pfails (pol : poison_policy) (ge : genv) (c : config) (ps : pstate) : Prop :=
  match pstep pol ge c ps with
  | PNext _ _ => False
  | PDone o _ => failure o
  | PFresh q _ => req_extent q < 0
  | PTrap _ | PStuck _ => True
  end.

(** A run without poison faults also avoids ordinary memory-safety failures. *)
Lemma not_pfails_not_fails pol ge c ps :
  ~ pfails pol ge c ps -> ~ fails ge c.
Proof.
  intros Hnp. pose proof (pstep_erases pol ge c ps) as Es.
  unfold pfails in Hnp; unfold fails.
  destruct (pstep pol ge c ps) as [c' ps' | o ots | q k | why | why]; try contradiction.
  - rewrite Es. exact Hnp.
  - rewrite Es. exact Hnp.
  - destruct Es as (k0 & -> & _). exact Hnp.
Qed.

(** The language follows the instrumented machine's individual steps. *)
Inductive phead_step (pol : poison_policy) (ge : genv)
  : pexpr -> plstate -> list Empty_set -> pexpr -> plstate -> list pexpr -> Prop :=
| phs_next fr te m pm paux s fuel c' ps' pcs' :
    pstep pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux) = PNext c' ps' ->
    pcs_callers pcs' = c_callers c' ->
    pcs_tcallers pcs' = ps_callers ps' ->
    phead_step pol ge (PRun fr te) (mkPLstate m pm paux s fuel) []
      (pstack_expr (PRun (c_frame c') (ps_tenv ps')) pcs')
      (mkPLstate (c_mem c') (ps_mem ps') (ps_aux ps') s (c_fuel c')) []
| phs_alloc fr te m pm paux s fuel q k base s' :
    pstep pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux) = PFresh q k ->
    0 <= req_extent q ->
    R.alloc s q = Some (base, s') ->
    phead_step pol ge (PRun fr te) (mkPLstate m pm paux s fuel) []
      (PRun (c_frame (fst (k base))) (ps_tenv (snd (k base))))
      (mkPLstate (c_mem (fst (k base))) (ps_mem (snd (k base))) (ps_aux (snd (k base)))
                 s' (c_fuel (fst (k base)))) []
| phs_refused fr te m pm paux s fuel q k :
    pstep pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux) = PFresh q k ->
    0 <= req_extent q ->
    R.alloc s q = None ->
    phead_step pol ge (PRun fr te) (mkPLstate m pm paux s fuel) []
      (PRun fr te) (mkPLstate m pm paux s fuel) []
| phs_return fr te m pm paux s fuel o ots m' :
    pstep pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux) = PDone o ots ->
    returning o ->
    invalidate_locals (fr_locals fr) m = Some m' ->
    phead_step pol ge (PRun fr te) (mkPLstate m pm paux s fuel) []
      (PEnd o ots) (mkPLstate m' pm paux s fuel) []
| phs_stop fr te m pm paux s fuel o ots :
    pstep pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux) = PDone o ots ->
    ~ failure o ->
    ~ returning o ->
    phead_step pol ge (PRun fr te) (mkPLstate m pm paux s fuel) []
      (PRun fr te) (mkPLstate m pm paux s fuel) []
| phs_safepoint fr te m pm paux s fuel s' m' :
    ~ pfails pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux) ->
    RM.safepoint_due ge (mkConfig fr [] m fuel) = true ->
    R.safepoint s m s' m' ->
    phead_step pol ge (PRun fr te) (mkPLstate m pm paux s fuel) []
      (PRun fr te) (mkPLstate m' pm paux s' fuel) []
| phs_resume o ots cf cte r cf' cte' σ :
    presume cf cte r o ots = Some (cf', cte') ->
    phead_step pol ge (PWait (PEnd o ots) cf cte r) σ []
      (PRun cf' cte') σ [].

Lemma poison_mixin pol ge :
  EctxiLanguageMixin pof_val pto_val pfill_item (phead_step pol ge).
Proof.
  split.
  - intros [o ots]. reflexivity.
  - intros e [o ots] H. destruct e; inversion H; reflexivity.
  - intros e1 σ1 κ e2 σ2 efs H. destruct H; reflexivity.
  - intros [cf cte r] e [v H]. discriminate H.
  - intros [cf cte r] e1 e2 H. injection H as H. exact H.
  - intros [cf1 cte1 r1] [cf2 cte2 r2] e1 e2 _ _ H. injection H as _ -> -> ->. reflexivity.
  - intros [cf cte r] e σ1 κ e2 σ2 efs H. inversion H; subst. exists (o, ots). reflexivity.
Qed.

Local Set Warnings "-redundant-canonical-projection".
Canonical Structure poison_ectxi_lang (pol : poison_policy) (ge : genv) : ectxiLanguage :=
  EctxiLanguage (poison_mixin pol ge).
Canonical Structure poison_ectx_lang (pol : poison_policy) (ge : genv) : ectxLanguage :=
  EctxLanguageOfEctxi (poison_ectxi_lang pol ge).
Canonical Structure poison_lang (pol : poison_policy) (ge : genv) : language :=
  LanguageOfEctx (poison_ectx_lang pol ge).
Local Set Warnings "redundant-canonical-projection".

Lemma pstack_expr_fill pol ge e pcs :
  pstack_expr e pcs = @ectx_language.fill (poison_ectx_lang pol ge) (pctx_of pcs) e.
Proof.
  revert e. induction pcs as [|[[cf cte] r] pcs IH]; intros e; [reflexivity | apply IH].
Qed.

Lemma phead_erased pol ge pcs e1 σ1 e2 σ2 :
  phead_step pol ge e1 σ1 [] e2 σ2 [] ->
  @erased_step (poison_lang pol ge) ([pstack_expr e1 pcs], σ1) ([pstack_expr e2 pcs], σ2).
Proof.
  intros H. exists [].
  apply (step_atomic (pstack_expr e1 pcs) σ1 (pstack_expr e2 pcs) σ2 [] [] []);
    [reflexivity | reflexivity |].
  rewrite !(pstack_expr_fill pol ge).
  exact (Ectx_step' (Λ := poison_ectx_lang pol ge) _ _ _ _ _ _ _ H).
Qed.

(** ### Call-stack decomposition

    A local proof reasons about the current frame without inspecting its
    callers. These lemmas show that the [[stage|checked IR]] machine keeps
    the suspended value and taint environments synchronized. *)

Ltac pcases H :=
  repeat (cbv zeta in H;
    match type of H with
    | context [match ?x with _ => _ end] =>
        lazymatch x with
        | context [match _ with _ => _ end] => fail
        | _ => destruct x; try discriminate H
        end
    end).

(** A step from empty caller stacks keeps value and taint callers synchronized. *)
Lemma pstep_nil_callers pol ge fr te m pm paux fuel c' ps' :
  pstep pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux) = PNext c' ps' ->
  exists pcs', pcs_callers pcs' = c_callers c' /\ pcs_tcallers pcs' = ps_callers ps'.
Proof.
  intros Hp. pose proof (pstep_erases pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux)) as Es.
  rewrite Hp in Es. pose proof Es as Es_step.
  unfold pstep in Hp; rewrite Es_step in Hp.
  destruct (tstep pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux)) as [ps0 | | | | ] eqn:Et;
    try discriminate Hp; injection Hp as <-.
  unfold tstep in Et; cbn [c_frame c_fuel ps_tenv ps_callers ps_mem ps_aux] in Et.
  destruct (fr_doomed fr) eqn:Ed; [discriminate Et|].
  destruct (fr_at fr) as [xs l | l from | l [|i rest] j] eqn:Eat; try discriminate Et.
  - destruct (fuel =? 0) eqn:Ef0; [discriminate Et|].
    destruct (find_block _ _); [|discriminate Et].
    destruct (phis_tenv _ _ _) as [te'|]; [|discriminate Et].
    injection Et as <-.
    unfold Semantics.step in Es; cbn [c_frame c_mem c_fuel] in Es; rewrite Eat Ef0 in Es; unfold or_stuck in Es.
    destruct (find_block _ _); [|discriminate Es]; destruct (phis_env _ _ _ _); [|discriminate Es].
    cbn in Es; injection Es as <-. exists []; split; reflexivity.
  - destruct j as [t | v t1 t2 | v | vs | | ]; cbn [jump_tstep return_tstep] in Et; try discriminate Et.
    + injection Et as <-.
      unfold Semantics.step, jump_step, edge_step in Es; cbn in Es; rewrite Eat Ed in Es.
      destruct t; injection Es as <-; exists []; split; reflexivity.
    + destruct (value_t _ W v) as [[tv| |]|]; try discriminate Et.
      destruct (t_branch tv); [discriminate Et|].
      injection Et as <-.
      unfold Semantics.step, jump_step, or_stuck, edge_step in Es; cbn in Es; rewrite Eat Ed in Es.
      destruct (value_x ge (fr_env fr) W v) as [[n| |]|]; try discriminate Es.
      destruct (if n =? 0 then t2 else t1); injection Es as <-; exists []; split; reflexivity.
    + destruct (fn_ret _); try discriminate Et; destruct (value_t _ _ v); discriminate Et.
    + destruct (fn_ret _); discriminate Et.
  - unfold Semantics.step, or_stuck in Es; cbn [c_frame c_mem] in Es; rewrite Eat Ed in Es.
    destruct (inst_step ge fr m i) as [out0|] eqn:Eis; cbn in Es; [|discriminate Es].
    destruct (doomed_result ge fr m i out0) as [[out d']|] eqn:Edr; cbn in Es; [|discriminate Es].
    destruct i as [d k o args | d o args lw | w off v av | off v av es | r cl args | r cl args | x sz | file line | tq];
      cbn [inst_tstep ps_tenv ps_callers ps_mem ps_aux fr_env] in Et; cbv zeta in Et; try discriminate Et.
    + (* Let *)
      assert (Hps_nil : ps_callers ps0 = []).
      { unfold let_tstep, check_ptr_bounds_taint in Et;
          destruct (is_zero_idiom o k args); [injection Et as <-; reflexivity|];
          destruct o; try discriminate Et;
          repeat (cbv zeta in Et;
            match type of Et with
            | context [match ?x with _ => _ end] =>
                lazymatch x with
                | context [match _ with _ => _ end] => fail
                | _ => destruct x; try discriminate Et
                end
            end);
          injection Et as <-; reflexivity. }
      destruct out as [| |g xs pd| |]; cbn in Es; try discriminate Es.
      * injection Es as <-; exists []; split; [reflexivity | symmetry; exact Hps_nil].
      * exfalso.
        destruct (special_let o) eqn:Esl;
          [destruct o; try discriminate Esl; cbn [inst_step] in Eis; pcases Eis;
             unfold bind_res in Eis; pcases Eis; inversion Eis; subst;
             unfold doomed_result in Edr; rewrite ?Ed in Edr; pcases Edr; inversion Edr
          |rewrite (inst_step_let _ _ _ _ _ _ _ Esl) in Eis; cbv zeta in Eis;
           destruct (op_arg_classes o k); [|discriminate Eis]; cbn [map2_option] in Eis;
           destruct (map2_option _ _ _); [|discriminate Eis]; cbn beta iota zeta in Eis;
           destruct (op_res _ _ _ _) as [[[| | ] ?| |]|]; try discriminate Eis;
           cbn in Eis; inversion Eis; subst;
           unfold doomed_result in Edr; rewrite ?Ed in Edr;
           pcases Edr; inversion Edr].
    + (* Flight *)
      destruct (map_option _ _); [|discriminate Et].
      destruct (flight_cap_t _ _); [|discriminate Et].
      destruct (op_checks_vartime _ _ _ && _); [discriminate Et|].
      injection Et as <-.
      cbn [inst_step] in Eis; pcases Eis;
        inversion Eis; subst; cbn in Edr; inversion Edr; subst; cbn in Es; injection Es as <-.
      exists []; split; reflexivity.
    + (* RawStore *)
      pcases Et; injection Et as <-;
        cbn [inst_step] in Eis; pcases Eis; unfold store_out in Eis; pcases Eis; inversion Eis; subst;
        cbn in Edr; rewrite ?Ed in Edr; pcases Edr; inversion Edr; subst; cbn in Es;
        try discriminate Es; injection Es as <-;
        exists []; split; reflexivity.
    + (* RawStorePointer *)
      pcases Et; injection Et as <-;
        cbn [inst_step] in Eis; pcases Eis;
        inversion Eis; subst; cbn in Edr; rewrite ?Ed in Edr; pcases Edr; inversion Edr; subst; cbn in Es;
        try discriminate Es; injection Es as <-;
        exists []; split; reflexivity.
    + (* Call *)
      destruct cl as [| |fn]; try discriminate Et.
      destruct (map_option (arg_t te) args) as [wts|]; [|discriminate Et].
      cbn [inst_step] in Eis; cbv zeta in Eis;
      destruct (map_option (arg_x ge (fr_env fr)) args) as [xs|]; cbn in Eis; [|discriminate Eis].
      destruct (find_fn ge fn) as [[gf|outfn]|]; try discriminate Et.
      * destruct (variadic_func gf); [discriminate Et|].
        destruct (call_tenv gf wts) as [cte|]; [|discriminate Et].
        injection Et as <-.
        inversion Eis; subst. cbn in Edr; inversion Edr; subst.
        cbn in Es. destruct (call_frame gf xs) as [callee|]; [|discriminate Es].
        injection Es as <-.
        exists [(mkFrame (fr_fn fr) (fr_env fr) (fr_locals fr) None (Exec l rest j), te, r)].
        cbn; rewrite Ed; split; reflexivity.
      * unfold external_call in Eis.
        destruct (lookup fn (ge_globals ge)); [discriminate Et|].
        destruct (is_free_name fn) eqn:Efn; [|discriminate Et].
        cbn [negb] in Eis.
        pcases Et; injection Et as <-;
          pcases Eis; inversion Eis; subst; cbn in Edr; rewrite ?Ed in Edr; pcases Edr; inversion Edr; subst;
          cbn in Es; try discriminate Es; injection Es as <-; exists []; split; reflexivity.
    + (* Loc *)
      injection Et as <-.
      cbn in Eis; inversion Eis; subst; cbn in Edr; inversion Edr; subst; cbn in Es; injection Es as <-.
      exists []; split; reflexivity.
    + (* Touch *)
      injection Et as <-.
      cbn in Eis; inversion Eis; subst; cbn in Edr; inversion Edr; subst; cbn in Es; injection Es as <-.
      exists []; split; reflexivity.
Qed.

(** Allocation preserves empty caller stacks at every possible fresh base. *)
Lemma pstep_nil_fresh_callers pol ge fr te m pm paux fuel q k base :
  pstep pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux) = PFresh q k ->
  c_callers (fst (k base)) = [] /\ ps_callers (snd (k base)) = [].
Proof.
  intros Hp.
  pose proof (pstep_erases pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux)) as Es.
  rewrite Hp in Es; destruct Es as (k0 & Es & Hk0).
  pose proof Es as Es_step.
  unfold pstep in Hp; rewrite Es_step in Hp.
  destruct (tstep pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux)) as [| |tps0| |] eqn:Et;
    try discriminate Hp.
  injection Hp as Hk; rewrite <- Hk; cbn [fst snd].
  destruct (fr_doomed fr) eqn:Ed;
    [unfold tstep in Et; cbn [c_frame] in Et; rewrite Ed in Et; discriminate Et|].
  assert (Hc : c_callers (k0 base) = []).
  { unfold Semantics.step, or_stuck in Es; cbn [c_frame c_mem c_fuel c_callers] in Es; cbv zeta in Es.
    destruct (fr_at fr) as [xs l | |l [|i rest] j]; try discriminate Es.
    - destruct xs; [discriminate Es | destruct (negb _); [discriminate Es | injection Es as _ <-; reflexivity]].
    - destruct (fuel =? 0); [discriminate Es|]; destruct (find_block _ _); [|discriminate Es];
        destruct (phis_env _ _ _ _); discriminate Es.
    - unfold jump_step, edge_step in Es; pcases Es; rewrite ?return_nil in Es; pcases Es.
    - rewrite Ed in Es; cbn [ahead_transparent] in Es; cbv zeta in Es.
      destruct (inst_step ge fr m i) as [out0|]; cbn in Es; [|discriminate Es].
      destruct (doomed_result ge fr m i out0) as [[out d']|]; cbn in Es; [|discriminate Es].
      destruct out as [| |g xs pd|qq kk|]; cbn in Es;
        try (destruct (call_frame g xs); discriminate Es); try discriminate Es.
      injection Es as _ <-. destruct (kk base) as [[? ?] ?]; reflexivity. }
  split; [exact Hc|].
  unfold tstep in Et; cbn [c_frame c_fuel ps_tenv ps_callers ps_mem ps_aux] in Et; rewrite Ed in Et.
  destruct (fr_at fr) as [| |l [|i rest] j]; try discriminate Et.
  - destruct (fuel =? 0); [discriminate Et|]; destruct (find_block _ _); [|discriminate Et];
      destruct (phis_tenv _ _ _); discriminate Et.
  - destruct j; cbn [jump_tstep return_tstep ps_callers] in Et; pcases Et; discriminate Et.
  - destruct i as [d kk o args | | | | | | x sz | | ];
      cbn [inst_tstep ps_tenv ps_callers ps_mem ps_aux fr_env] in Et; cbv zeta in Et;
      try solve [pcases Et; discriminate Et].
    + unfold let_tstep, check_ptr_bounds_taint in Et.
      destruct (is_zero_idiom o kk args); [discriminate Et|].
      destruct o; try discriminate Et; try solve [pcases Et; discriminate Et].
      pcases Et; injection Et as <-; reflexivity.
    + injection Et as <-; reflexivity.
Qed.

(** Adding suspended callers preserves a step's behavior within the current frame. *)
Lemma pstep_callers pol ge fr te m pm paux fuel pcs :
  let c0 := mkConfig fr [] m fuel in
  let ps0 := mkPState te [] pm paux in
  let c := mkConfig fr (pcs_callers pcs) m fuel in
  let ps := mkPState te (pcs_tcallers pcs) pm paux in
  match pstep pol ge c0 ps0 with
  | PNext c0' ps0' =>
      pstep pol ge c ps =
        PNext (mkConfig (c_frame c0') (c_callers c0' ++ pcs_callers pcs) (c_mem c0') (c_fuel c0'))
              (mkPState (ps_tenv ps0') (ps_callers ps0' ++ pcs_tcallers pcs) (ps_mem ps0') (ps_aux ps0'))
  | PFresh q k0 =>
      exists k',
        pstep pol ge c ps = PFresh q k' /\
        forall base,
          k' base =
            (mkConfig (c_frame (fst (k0 base))) (c_callers (fst (k0 base)) ++ pcs_callers pcs)
                      (c_mem (fst (k0 base))) (c_fuel (fst (k0 base))),
             mkPState (ps_tenv (snd (k0 base))) (ps_callers (snd (k0 base)) ++ pcs_tcallers pcs)
                      (ps_mem (snd (k0 base))) (ps_aux (snd (k0 base))))
  | PDone o ots =>
      (~ returning o /\ pstep pol ge c ps = PDone o ots) \/
      (returning o /\ exists m', invalidate_locals (fr_locals fr) m = Some m' /\
         match pcs with
         | [] => pstep pol ge c ps = PDone o ots
         | (cf, cte, r) :: pcs' =>
             match presume cf cte r o ots with
             | Some (cf', cte') =>
                 pstep pol ge c ps =
                   PNext (mkConfig cf' (pcs_callers pcs') m' fuel)
                         (mkPState cte' (pcs_tcallers pcs') pm paux)
             | None => exists why, pstep pol ge c ps = PStuck why
             end
         end)
  | PTrap why => pstep pol ge c ps = PTrap why
  | PStuck _ => exists why', pstep pol ge c ps = PStuck why'
  end.
Proof.
  intros c0 ps0 c ps.
  pose proof (step_callers ge fr (pcs_callers pcs) m fuel) as Hsc.
  change (mkConfig fr [] m fuel) with c0 in Hsc.
  change (mkConfig fr (pcs_callers pcs) m fuel) with c in Hsc.
  assert (Htstep_nonret :
    match fr_doomed fr with
    | Some _ => tstep pol ge c ps = TStuck "doomed" /\ tstep pol ge c0 ps0 = TStuck "doomed"
    | None =>
        match fr_at fr with
        | Exec _ [] (JRet v) => True
        | Exec _ [] JRetVoid => True
        | _ =>
            match tstep pol ge c0 ps0 with
            | TNext ps0' =>
                tstep pol ge c ps =
                  TNext (mkPState (ps_tenv ps0') (ps_callers ps0' ++ pcs_tcallers pcs)
                                  (ps_mem ps0') (ps_aux ps0'))
            | TDone ots => tstep pol ge c ps = TDone ots
            | TFresh tps0 =>
                tstep pol ge c ps =
                  TFresh (fun base =>
                    mkPState (ps_tenv (tps0 base)) (ps_callers (tps0 base) ++ pcs_tcallers pcs)
                             (ps_mem (tps0 base)) (ps_aux (tps0 base)))
            | TFault why => tstep pol ge c ps = TFault why
            | TStuck why => tstep pol ge c ps = TStuck why
            end
        end
    end).
  { unfold tstep, c0, ps0, c, ps; cbn [c_frame c_fuel ps_tenv ps_callers ps_mem ps_aux].
    destruct (fr_doomed fr); [split; reflexivity|].
    destruct (fr_at fr) as [xs l | l from | l [|i rest] j]; auto.
    - destruct (fuel =? 0); [reflexivity|].
      destruct (find_block _ _); [|reflexivity].
      destruct (phis_tenv _ _ _); reflexivity.
    - destruct j as [t | v t1 t2 | v | vs | | ]; auto;
        cbn [jump_tstep ps_tenv ps_callers ps_mem ps_aux]; cbv zeta; try reflexivity.
      destruct (value_t te W v) as [[tv| |]|]; try reflexivity.
      destruct (t_branch tv); reflexivity.
    - destruct i as [d k o args | d o args lw | w off v av | off v av es | r cl args | r cl args | x sz | file line | tq];
        cbn [inst_tstep ps_tenv ps_callers ps_mem ps_aux fr_env]; cbv zeta; try reflexivity.
      + unfold let_tstep, check_ptr_bounds_taint; cbn [ps_tenv ps_callers ps_mem ps_aux app]; cbv zeta.
        destruct (is_zero_idiom o k args); [reflexivity|].
        destruct o; try reflexivity;
          repeat (cbv zeta; cbn [ps_tenv ps_callers ps_mem ps_aux app];
            match goal with |- context [match ?x with _ => _ end] =>
              lazymatch x with context [match _ with _ => _ end] => fail | _ => destruct x; try reflexivity end end).
      + destruct (map_option _ _); [|reflexivity]; destruct (flight_cap_t _ _); [|reflexivity];
          destruct (op_checks_vartime _ _ _ && _); reflexivity.
      + repeat (cbv zeta; match goal with |- context [match ?x with _ => _ end] =>
          lazymatch x with context [match _ with _ => _ end] => fail | _ => destruct x; try reflexivity end end).
      + repeat (cbv zeta; match goal with |- context [match ?x with _ => _ end] =>
          lazymatch x with context [match _ with _ => _ end] => fail | _ => destruct x; try reflexivity end end).
      + destruct cl as [| |fn]; try reflexivity.
        destruct (map_option (arg_t te) args) as [wts|]; [|reflexivity].
        destruct (find_fn ge fn) as [[gf|outfn]|]; try reflexivity.
        * destruct (variadic_func gf); [reflexivity|].
          destruct (call_tenv gf wts); reflexivity.
        * destruct (lookup fn (ge_globals ge)); [reflexivity|].
          destruct (is_free_name fn); [|reflexivity].
          repeat (cbv zeta; match goal with |- context [match ?x with _ => _ end] =>
            lazymatch x with context [match _ with _ => _ end] => fail | _ => destruct x; try reflexivity end end). }
  (* Handle the two returning jumps explicitly, then use Htstep_nonret everywhere else. *)
  destruct (fr_doomed fr) eqn:Ed.
  { unfold pstep, tstep, c0, ps0, c, ps; cbn [c_frame]; rewrite Ed. eexists; reflexivity. }
  assert (Hret_cases :
    (exists l v, fr_at fr = Exec l [] (JRet v)) \/
    (exists l vs, fr_at fr = Exec l [] (JRets vs)) \/
    (exists l, fr_at fr = Exec l [] JRetVoid) \/
    ((forall l v, fr_at fr <> Exec l [] (JRet v)) /\
     (forall l vs, fr_at fr <> Exec l [] (JRets vs)) /\
     (forall l, fr_at fr <> Exec l [] JRetVoid))).
  { destruct (fr_at fr) as [| |l [|] []]; eauto;
      (right; right; right; split; [|split]; intros; discriminate). }
  destruct Hret_cases as [(l & v & Eat) | [(l & vs & Eat) | [(l & Eat) | (Hnr1 & Hnr2 & Hnr3)]]].
  - (* JRet v *)
    unfold pstep, tstep, c0, ps0, c, ps; cbn [c_frame ps_tenv ps_callers ps_mem ps_aux]; rewrite Ed Eat;
      cbn [jump_tstep ps_tenv ps_callers ps_mem ps_aux]; cbv zeta.
    destruct (fn_ret (fr_fn fr)) as [rk| |] eqn:Efnr; try (eexists; reflexivity).
    destruct (value_t te rk v) as [wt|] eqn:Evt; [|eexists; reflexivity].
    unfold Semantics.step, jump_step, return_step, return_tstep, or_stuck; cbn [c_frame c_mem c_fuel c_callers ps_callers ps_mem ps_aux]; rewrite Eat Ed Efnr.
    destruct (value_x ge (fr_env fr) rk v) as [w|] eqn:Evx; cbn -[returned_env returned_tenv];
      [|destruct pcs as [|[[cf cte] r] pcs']; unfold pcs_tcallers; cbn -[returned_tenv]; [|destruct (returned_tenv r [wt] cte)]; eexists; reflexivity].
    destruct (invalidate_locals (fr_locals fr) m) as [m'|] eqn:Einv; cbn -[returned_env returned_tenv];
      [|destruct pcs as [|[[cf cte] r] pcs']; unfold pcs_tcallers; cbn -[returned_tenv]; [|destruct (returned_tenv r [wt] cte)]; eexists; reflexivity].
    right. split; [exact I|]. exists m'. split; [reflexivity|].
    destruct pcs as [|[[cf cte] r] pcs']; unfold pcs_callers, pcs_tcallers; cbn -[returned_env returned_tenv].
    + reflexivity.
    + unfold presume, resume; cbn [pd_conv pd_res].
      destruct (returned_tenv r [wt] cte) as [cte'|] eqn:Erte;
        destruct (returned_env r (Ret w) (fr_env cf)) as [e'|] eqn:Ere; cbn;
        try reflexivity; eexists; reflexivity.
  - (* JRets vs: TStuck on both *)
    unfold pstep, tstep, c0, ps0, c, ps; cbn [c_frame]; rewrite Ed Eat; cbn [jump_tstep].
    eexists; reflexivity.
  - (* JRetVoid *)
    unfold pstep, tstep, c0, ps0, c, ps; cbn [c_frame ps_tenv ps_callers ps_mem ps_aux]; rewrite Ed Eat;
      cbn [jump_tstep ps_tenv ps_callers ps_mem ps_aux]; cbv zeta.
    destruct (fn_ret (fr_fn fr)) eqn:Efnr; try (eexists; reflexivity).
    unfold Semantics.step, jump_step, return_step, return_tstep, or_stuck; cbn [c_frame c_mem c_fuel c_callers ps_callers ps_mem ps_aux]; rewrite Eat Ed.
    destruct (invalidate_locals (fr_locals fr) m) as [m'|] eqn:Einv; cbn -[returned_env returned_tenv];
      [|destruct pcs as [|[[cf cte] r] pcs']; unfold pcs_tcallers; cbn -[returned_tenv]; [|destruct (returned_tenv r [] cte)]; eexists; reflexivity].
    right. split; [exact I|]. exists m'. split; [reflexivity|].
    destruct pcs as [|[[cf cte] r] pcs']; unfold pcs_callers, pcs_tcallers; cbn -[returned_env returned_tenv].
    + reflexivity.
    + unfold presume, resume; cbn [pd_conv pd_res].
      destruct (returned_tenv r [] cte) as [cte'|] eqn:Erte;
        destruct (returned_env r RetVoid (fr_env cf)) as [e'|] eqn:Ere; cbn;
        try reflexivity; eexists; reflexivity.
  - (* Non-return point *)
    assert (Ht : match tstep pol ge c0 ps0 with
                 | TNext ps0' =>
                     tstep pol ge c ps =
                       TNext (mkPState (ps_tenv ps0') (ps_callers ps0' ++ pcs_tcallers pcs)
                                       (ps_mem ps0') (ps_aux ps0'))
                 | TDone ots => tstep pol ge c ps = TDone ots
                 | TFresh tps0 =>
                     tstep pol ge c ps =
                       TFresh (fun base =>
                         mkPState (ps_tenv (tps0 base)) (ps_callers (tps0 base) ++ pcs_tcallers pcs)
                                  (ps_mem (tps0 base)) (ps_aux (tps0 base)))
                 | TFault why => tstep pol ge c ps = TFault why
                 | TStuck why => tstep pol ge c ps = TStuck why
                 end).
    { destruct (fr_at fr) as [| |l [|] []] eqn:Eat; try exact Htstep_nonret;
        [exfalso; exact (Hnr1 l v eq_refl) | exfalso; exact (Hnr3 l eq_refl)]. }
    assert (Hnot_ret_step : forall o, Semantics.step ge c0 = Done o -> ~ returning o).
    { intros o Es0 Hro.
      unfold Semantics.step, c0 in Es0; cbn [c_frame c_mem c_fuel] in Es0; cbv zeta in Es0.
      destruct (fr_at fr) as [xs l | l from | l [|i rest] j] eqn:Eat.
      - destruct xs; [discriminate Es0 | destruct (negb _); discriminate Es0].
      - destruct (fuel =? 0); [injection Es0 as <-; exact Hro|].
        unfold or_stuck in Es0; destruct (find_block _ _); [|discriminate Es0];
          destruct (phis_env _ _ _ _); discriminate Es0.
      - unfold jump_step in Es0; rewrite Ed in Es0.
        destruct j as [t | v t1 t2 | v | vs | | ].
        + unfold edge_step in Es0; rewrite Ed in Es0; destruct t; discriminate Es0.
        + unfold or_stuck, edge_step in Es0; rewrite Ed in Es0.
          destruct (value_x _ _ W v) as [[n| |]|]; try discriminate Es0.
          destruct (if n =? 0 then t2 else t1); discriminate Es0.
        + exact (Hnr1 l v eq_refl).
        + exact (Hnr2 l vs eq_refl).
        + exact (Hnr3 l eq_refl).
        + injection Es0 as <-; exact Hro.
      - unfold or_stuck in Es0; rewrite Ed in Es0; cbv zeta in Es0.
        destruct (inst_step ge fr m i) as [out0|] eqn:Eis; cbn in Es0; [|discriminate Es0].
        destruct (doomed_result ge fr m i out0) as [[out d']|] eqn:Edr; cbn in Es0; [|discriminate Es0].
        destruct out as [|o_s|g xs pd| |]; cbn in Es0;
          try (destruct (call_frame g xs); discriminate Es0); try discriminate Es0.
        injection Es0 as <-.
        exact (stop_not_returning ge fr m i out0 (IStop o_s, d') o_s Eis Edr eq_refl Hro). }
    unfold pstep.
    destruct (tstep pol ge c0 ps0) as [ps0' | ots | tps0 | why | why]; rewrite Ht.
    + destruct (Semantics.step ge c0) as [c0' | o | q k0 | swhy] eqn:Es0; cbn [lifted] in Hsc.
      * rewrite Hsc; destruct ps0'; reflexivity.
      * pose proof (Hnot_ret_step o eq_refl) as Hnro.
        destruct Hsc as [[_ ->] | [Hro _]]; [left; auto | contradiction].
      * destruct Hsc as (k' & -> & _); eexists; reflexivity.
      * destruct Hsc as (swhy' & ->); eexists; reflexivity.
    + destruct (Semantics.step ge c0) as [c0' | o | q k0 | swhy] eqn:Es0; cbn [lifted] in Hsc.
      * rewrite Hsc; eexists; reflexivity.
      * pose proof (Hnot_ret_step o eq_refl) as Hnro.
        destruct Hsc as [[_ ->] | [Hro _]]; [left; auto | contradiction].
      * destruct Hsc as (k' & -> & _); eexists; reflexivity.
      * destruct Hsc as (swhy' & ->); eexists; reflexivity.
    + destruct (Semantics.step ge c0) as [c0' | o | q k0 | swhy] eqn:Es0; cbn [lifted] in Hsc.
      * rewrite Hsc; eexists; reflexivity.
      * pose proof (Hnot_ret_step o eq_refl) as Hnro.
        destruct Hsc as [[_ ->] | [Hro _]]; [left; auto | contradiction].
      * destruct Hsc as (k' & -> & Hk').
        exists (fun base =>
          (k' base,
           mkPState (ps_tenv (tps0 base)) (ps_callers (tps0 base) ++ pcs_tcallers pcs)
                    (ps_mem (tps0 base)) (ps_aux (tps0 base)))).
        split; [reflexivity|]. intros base; rewrite Hk'; reflexivity.
      * destruct Hsc as (swhy' & ->); eexists; reflexivity.
    + reflexivity.
    + eexists; reflexivity.
Qed.

(** ### Reducibility and poisoned machine adequacy

    Proving one instruction safe is not enough if the collector can run
    between instructions. This argument connects [[iris|Iris]] proofs to
    whole executions, including collector steps and allocation refusal. *)

Lemma pctx_base_reducible pol ge pcs e σ :
  pto_val e = None ->
  (forall Ki e', e = pfill_item Ki e' -> is_Some (pto_val e')) ->
  @reducible (poison_lang pol ge) (pstack_expr e pcs) σ ->
  @base_reducible (poison_ectx_lang pol ge) e σ.
Proof.
  intros Hv Hsub (κ & e2 & σ2 & efs & Hs).
  rewrite (pstack_expr_fill pol ge) in Hs.
  destruct Hs as [K e1' e2' HK _ Hb].
  destruct (step_by_val (Λ := poison_ectx_lang pol ge) (pctx_of pcs) K e e1' _ _ _ _ _ HK Hv Hb)
    as [K'' ->].
  rewrite <- fill_comp in HK. apply (inj _) in HK.
  assert (Hsr : @sub_redexes_are_values (poison_ectx_lang pol ge) e).
  { exact (ectxi_language_sub_redexes_are_values (Λ := poison_ectxi_lang pol ge) e Hsub). }
  pose proof (Hsr K'' e1' HK (val_base_stuck _ _ _ _ _ _ Hb)) as ->.
  rewrite fill_empty in HK. subst e1'. do 4 eexists. exact Hb.
Qed.

Lemma phead_step_run_inv pol ge fr te σ κ e' σ' efs :
  phead_step pol ge (PRun fr te) σ κ e' σ' efs ->
  let c0 := mkConfig fr [] (pl_mem σ) (pl_fuel σ) in
  let ps0 := mkPState te [] (pl_pm σ) (pl_paux σ) in
  κ = [] /\ efs = [] /\
  ((exists c' ps' pcs',
      pstep pol ge c0 ps0 = PNext c' ps' /\
      pcs_callers pcs' = c_callers c' /\
      pcs_tcallers pcs' = ps_callers ps' /\
      e' = pstack_expr (PRun (c_frame c') (ps_tenv ps')) pcs' /\
      σ' = mkPLstate (c_mem c') (ps_mem ps') (ps_aux ps') (pl_rt σ) (c_fuel c')) \/
   (exists q k base s',
      pstep pol ge c0 ps0 = PFresh q k /\ 0 <= req_extent q /\
      R.alloc (pl_rt σ) q = Some (base, s') /\
      e' = PRun (c_frame (fst (k base))) (ps_tenv (snd (k base))) /\
      σ' = mkPLstate (c_mem (fst (k base))) (ps_mem (snd (k base))) (ps_aux (snd (k base)))
                     s' (c_fuel (fst (k base)))) \/
   (exists q k,
      pstep pol ge c0 ps0 = PFresh q k /\ 0 <= req_extent q /\
      R.alloc (pl_rt σ) q = None /\ e' = PRun fr te /\ σ' = σ) \/
   (exists o ots m',
      pstep pol ge c0 ps0 = PDone o ots /\ returning o /\
      invalidate_locals (fr_locals fr) (pl_mem σ) = Some m' /\
      e' = PEnd o ots /\
      σ' = mkPLstate m' (pl_pm σ) (pl_paux σ) (pl_rt σ) (pl_fuel σ)) \/
   (exists o ots,
      pstep pol ge c0 ps0 = PDone o ots /\ ~ failure o /\ ~ returning o /\
      e' = PRun fr te /\ σ' = σ) \/
   (exists s' m',
      ~ pfails pol ge c0 ps0 /\ RM.safepoint_due ge c0 = true /\
      R.safepoint (pl_rt σ) (pl_mem σ) s' m' /\
      e' = PRun fr te /\
      σ' = mkPLstate m' (pl_pm σ) (pl_paux σ) s' (pl_fuel σ))).
Proof.
  intros H. inversion H; subst; cbn [pl_mem pl_pm pl_paux pl_rt pl_fuel];
    (split; [reflexivity | split; [reflexivity |]]).
  - left; eauto 10.
  - right; left; eauto 10.
  - do 2 right; left; eauto 10.
  - do 3 right; left; eauto 10.
  - do 4 right; left; eauto 10.
  - do 5 right; eauto 10.
Qed.

Lemma prun_not_pfails pol ge fr te σ κ e' σ' efs :
  phead_step pol ge (PRun fr te) σ κ e' σ' efs ->
  ~ pfails pol ge (mkConfig fr [] (pl_mem σ) (pl_fuel σ))
                  (mkPState te [] (pl_pm σ) (pl_paux σ)).
Proof.
  intros H.
  destruct (phead_step_run_inv pol ge fr te σ κ e' σ' efs H)
    as (_ & _ & [(c' & ps' & pcs' & E & _) | [(q & k & base & s' & E & He & _) |
        [(q & k & E & He & _) | [(o & ots & m' & E & Hr & _) |
        [(o & ots & E & Hf & _) | (s' & m' & Hnf & _)]]]]]).
  - unfold pfails; rewrite E; auto.
  - unfold pfails; rewrite E; lia.
  - unfold pfails; rewrite E; lia.
  - unfold pfails; rewrite E; destruct o; cbn in *; tauto.
  - unfold pfails; rewrite E; exact Hf.
  - exact Hnf.
Qed.

Lemma prun_reducible pol ge fr te σ :
  ~ pfails pol ge (mkConfig fr [] (pl_mem σ) (pl_fuel σ))
                  (mkPState te [] (pl_pm σ) (pl_paux σ)) ->
  @base_reducible (poison_ectx_lang pol ge) (PRun fr te) σ.
Proof.
  destruct σ as [m pm paux s fuel]; cbn [pl_mem pl_pm pl_paux pl_fuel].
  intros Hnp. unfold pfails in Hnp.
  destruct (pstep pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux))
    as [c' ps' | o ots | q k | why | why] eqn:Ep; try contradiction.
  - destruct (pstep_nil_callers pol ge fr te m pm paux fuel c' ps' Ep) as (pcs' & Hc & Htc).
    do 4 eexists. exact (phs_next pol ge fr te m pm paux s fuel c' ps' pcs' Ep Hc Htc).
  - destruct (returning_dec o) as [Hr | Hr].
    + pose proof (pstep_callers pol ge fr te m pm paux fuel []) as Hsc; cbn [pcs_callers pcs_tcallers] in Hsc.
      rewrite Ep in Hsc.
      destruct Hsc as [[Hnr _] | (_ & m' & Hi & _)]; [contradiction|].
      do 4 eexists. exact (phs_return pol ge fr te m pm paux s fuel o ots m' Ep Hr Hi).
    + do 4 eexists. exact (phs_stop pol ge fr te m pm paux s fuel o ots Ep Hnp Hr).
  - assert (Hex : 0 <= req_extent q) by lia.
    destruct (R.alloc s q) as [[base s']|] eqn:Ea.
    + do 4 eexists. exact (phs_alloc pol ge fr te m pm paux s fuel q k base s' Ep Hex Ea).
    + do 4 eexists. exact (phs_refused pol ge fr te m pm paux s fuel q k Ep Hex Ea).
Qed.

Lemma pwait_resumes pol ge pcs o ots cf cte r σ :
  @reducible (poison_lang pol ge) (pstack_expr (PWait (PEnd o ots) cf cte r) pcs) σ ->
  exists cf' cte', presume cf cte r o ots = Some (cf', cte').
Proof.
  intros H. apply pctx_base_reducible in H as (κ & e' & σ' & efs & Hs).
  - inversion Hs; subst. eauto.
  - reflexivity.
  - intros [cf' cte' r'] e' Heq. cbn in Heq. injection Heq as <- _ _ _. eexists; reflexivity.
Qed.

Lemma pconf_not_pfails pol ge fr te pcs m pm paux s fuel :
  @not_stuck (poison_lang pol ge) (pstack_expr (PRun fr te) pcs) (mkPLstate m pm paux s fuel) ->
  ~ pfails pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux).
Proof.
  intros [[v Hv] | Hred].
  - change (pto_val (pstack_expr (PRun fr te) pcs) = Some v) in Hv.
    rewrite pto_val_stack in Hv; [discriminate Hv | reflexivity].
  - apply pctx_base_reducible in Hred as (κ & e' & σ' & efs & Hs).
    + exact (prun_not_pfails pol ge fr te (mkPLstate m pm paux s fuel) κ e' σ' efs Hs).
    + reflexivity.
    + intros [cf cte r] e' Heq. discriminate Heq.
Qed.

(** The instrumented machine can execute instructions, allocate, or run a safepoint. *)
Inductive pmstep (pol : poison_policy) (ge : genv)
  : (config * pstate * R.state) -> (config * pstate * R.state) -> Prop :=
| pmstep_next c ps s c' ps' :
    pstep pol ge c ps = PNext c' ps' ->
    pmstep pol ge (c, ps, s) (c', ps', s)
| pmstep_alloc c ps s q k base s' :
    pstep pol ge c ps = PFresh q k ->
    0 <= req_extent q ->
    R.alloc s q = Some (base, s') ->
    pmstep pol ge (c, ps, s) (fst (k base), snd (k base), s')
| pmstep_safepoint c ps s s' m' :
    RM.safepoint_due ge c = true ->
    R.safepoint s (c_mem c) s' m' ->
    pmstep pol ge (c, ps, s) (mkConfig (c_frame c) (c_callers c) m' (c_fuel c), ps, s').

Definition pmreachable (pol : poison_policy) (ge : genv) :=
  clos_refl_trans (config * pstate * R.state) (pmstep pol ge).

Section padequacy.
Context (pol : poison_policy) (ge : genv)
  (fr0 : frame) (te0 : tenv) (m0 : mem) (pm0 : Z -> poison_byte) (paux0 : Z -> taint)
  (s0 : R.state) (fuel0 : Z).

Definition piris_reach (c : config) (ps : pstate) (s : R.state) : Prop :=
  exists pcs,
    c_callers c = pcs_callers pcs /\
    ps_callers ps = pcs_tcallers pcs /\
    rtc (@erased_step (poison_lang pol ge))
      ([PRun fr0 te0], mkPLstate m0 pm0 paux0 s0 fuel0)
      ([pstack_expr (PRun (c_frame c) (ps_tenv ps)) pcs],
       mkPLstate (c_mem c) (ps_mem ps) (ps_aux ps) s (c_fuel c)).

Lemma preach_frame_ok φ c ps s :
  @adequate (poison_lang pol ge) NotStuck (PRun fr0 te0) (mkPLstate m0 pm0 paux0 s0 fuel0) φ ->
  piris_reach c ps s ->
  ~ pfails pol ge (mkConfig (c_frame c) [] (c_mem c) (c_fuel c))
                  (mkPState (ps_tenv ps) [] (ps_mem ps) (ps_aux ps)).
Proof.
  intros Had (pcs & _ & _ & Hr).
  apply (pconf_not_pfails pol ge (c_frame c) (ps_tenv ps) pcs (c_mem c) (ps_mem ps) (ps_aux ps) s (c_fuel c)).
  apply (adequate_not_stuck _ _ _ _ Had _ _ _ eq_refl Hr). left.
Qed.

Lemma preach_step φ c ps s c' ps' s' :
  @adequate (poison_lang pol ge) NotStuck (PRun fr0 te0) (mkPLstate m0 pm0 paux0 s0 fuel0) φ ->
  piris_reach c ps s ->
  pmstep pol ge (c, ps, s) (c', ps', s') ->
  piris_reach c' ps' s'.
Proof.
  intros Had Hreach Hst.
  pose proof (preach_frame_ok φ c ps s Had Hreach) as Hnf.
  destruct Hreach as (pcs & Hcc & Htc & Hr).
  destruct c as [fr cs m fuel], ps as [te tcs pm paux].
  cbn [c_frame c_callers c_mem c_fuel ps_tenv ps_callers ps_mem ps_aux] in *.
  subst cs tcs.
  pose proof (pstep_callers pol ge fr te m pm paux fuel pcs) as Hl; cbv zeta in Hl.
  inversion Hst as [c1 ps1 s1 c2 ps2 Ep | c1 ps1 s1 q k base s1' Ep He Ea | c1 ps1 s1 s1' m' Hdue Hsp];
    subst.
  - destruct (pstep pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux))
      as [c0' ps0' | o ots | q k0 | why | why] eqn:Ep0.
    + rewrite Hl in Ep; injection Ep as <- <-.
      destruct (pstep_nil_callers pol ge fr te m pm paux fuel c0' ps0' Ep0) as (pcs0 & Hcc0 & Htc0).
      exists (pcs0 ++ pcs).
      rewrite pcs_callers_app pcs_tcallers_app Hcc0 Htc0 pstack_expr_app.
      split; [reflexivity | split; [reflexivity |]].
      eapply rtc_r; [exact Hr|].
      exact (phead_erased pol ge pcs _ _ _ _
               (phs_next pol ge fr te m pm paux s' fuel c0' ps0' pcs0 Ep0 Hcc0 Htc0)).
    + destruct Hl as [[_ Hl] | (Hro & m' & Hi & Hl)]; [rewrite Hl in Ep; discriminate Ep|].
      destruct pcs as [|[[cf cte] r] pcs']; [rewrite Hl in Ep; discriminate Ep|].
      destruct (presume cf cte r o ots) as [[cf' cte']|] eqn:Epr;
        [|destruct Hl as [? Hl]; rewrite Hl in Ep; discriminate Ep].
      rewrite Hl in Ep; injection Ep as <- <-.
      exists pcs'; split; [reflexivity | split; [reflexivity |]].
      eapply rtc_r; [eapply rtc_r; [exact Hr|]|].
      * exact (phead_erased pol ge ((cf, cte, r) :: pcs') _ _ _ _
                 (phs_return pol ge fr te m pm paux s' fuel o ots m' Ep0 Hro Hi)).
      * exact (phead_erased pol ge pcs' _ _ _ _
                 (phs_resume pol ge o ots cf cte r cf' cte' _ Epr)).
    + destruct Hl as (k' & Hl & _); rewrite Hl in Ep; discriminate Ep.
    + rewrite Hl in Ep; discriminate Ep.
    + destruct Hl as (why' & Hl); rewrite Hl in Ep; discriminate Ep.
  - destruct (pstep pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux))
      as [c0' ps0' | o ots | q0 k0 | why | why] eqn:Ep0;
      cbn beta zeta in Hl.
    + rewrite Hl in Ep; discriminate Ep.
    + destruct Hl as [[_ Hl] | (_ & m' & _ & Hl)];
        [rewrite Hl in Ep; discriminate Ep
        |destruct pcs as [|[[cf cte] r] pcs'];
           [rewrite Hl in Ep; discriminate Ep
           |destruct (presume cf cte r o ots) as [[? ?]|];
              [rewrite Hl in Ep; discriminate Ep | destruct Hl as [? Hl]; rewrite Hl in Ep; discriminate Ep]]].
    + destruct Hl as (k' & Hl & Hk').
      rewrite Hl in Ep; injection Ep as <- <-.
      rewrite (Hk' base).
      destruct (pstep_nil_fresh_callers pol ge fr te m pm paux fuel q0 k0 base Ep0) as [Hkc Hktc].
      rewrite Hkc Hktc; cbn [app c_frame c_callers c_mem c_fuel ps_tenv ps_callers ps_mem ps_aux].
      exists pcs; split; [reflexivity | split; [reflexivity |]].
      eapply rtc_r; [exact Hr|].
      exact (phead_erased pol ge pcs _ _ _ _
               (phs_alloc pol ge fr te m pm paux s fuel q0 k0 base s' Ep0 He Ea)).
    + rewrite Hl in Ep; discriminate Ep.
    + destruct Hl as (why' & Hl); rewrite Hl in Ep; discriminate Ep.
  - exists pcs; split; [reflexivity | split; [reflexivity |]].
    eapply rtc_r; [exact Hr|].
    exact (phead_erased pol ge pcs _ _ _ _
             (phs_safepoint pol ge fr te m pm paux s fuel s' m' Hnf Hdue Hsp)).
Qed.

Lemma preach_not_pfails φ c ps s :
  @adequate (poison_lang pol ge) NotStuck (PRun fr0 te0) (mkPLstate m0 pm0 paux0 s0 fuel0) φ ->
  piris_reach c ps s ->
  ~ pfails pol ge c ps.
Proof.
  intros Had Hreach.
  pose proof (preach_frame_ok φ c ps s Had Hreach) as Hnf.
  destruct Hreach as (pcs & Hcc & Htc & Hr).
  destruct c as [fr cs m fuel], ps as [te tcs pm paux];
    cbn [c_frame c_callers c_mem c_fuel ps_tenv ps_callers ps_mem ps_aux] in *;
    subst cs tcs.
  pose proof (pstep_callers pol ge fr te m pm paux fuel pcs) as Hl; cbv zeta in Hl.
  unfold pfails in Hnf |- *.
  destruct (pstep pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux))
    as [c0' ps0' | o ots | q k0 | why | why] eqn:Ep0; try contradiction.
  - rewrite Hl; auto.
  - destruct Hl as [[_ Hl] | (Hro & m' & Hi & Hl)].
    + rewrite Hl; exact Hnf.
    + destruct pcs as [|[[cf cte] r] pcs']; [rewrite Hl; exact Hnf|].
      destruct (presume cf cte r o ots) as [[cf' cte']|] eqn:Epr; [rewrite Hl; auto|].
      destruct Hl as [why Hl]; rewrite Hl; intros _.
      assert (Hr' : rtc (@erased_step (poison_lang pol ge))
                      ([PRun fr0 te0], mkPLstate m0 pm0 paux0 s0 fuel0)
                      ([pstack_expr (PWait (PEnd o ots) cf cte r) pcs'],
                       mkPLstate m' pm paux s fuel)).
      { eapply rtc_r; [exact Hr|].
        exact (phead_erased pol ge ((cf, cte, r) :: pcs') _ _ _ _
                 (phs_return pol ge fr te m pm paux s fuel o ots m' Ep0 Hro Hi)). }
      destruct (adequate_not_stuck _ _ _ _ Had _ _ _ eq_refl Hr' ltac:(left)) as [[v Hv] | Hred].
      * change (pto_val (pstack_expr (PWait (PEnd o ots) cf cte r) pcs') = Some v) in Hv.
        rewrite pto_val_stack in Hv; [discriminate Hv | reflexivity].
      * destruct (pwait_resumes pol ge pcs' o ots cf cte r _ Hred) as (cf' & cte' & Hpr).
        congruence.
  - destruct Hl as (k' & -> & _); exact Hnf.
Qed.

End padequacy.

(** An ordinary machine step also has an instrumented step when poison checks pass. *)
Lemma mstep_lifts_pmstep pol ge c ps s c' s' :
  ~ pfails pol ge c ps ->
  RM.mstep ge (c, s) (c', s') ->
  exists ps', pmstep pol ge (c, ps, s) (c', ps', s').
Proof.
  intros Hnp Hs.
  pose proof (pstep_erases pol ge c ps) as Es.
  unfold pfails in Hnp.
  inversion Hs as [c1 c2 s1 E | c1 q k0 s1 base s1' E He Ea | c1 s1 s1' m' Hdue Hsp]; subst.
  - destruct (pstep pol ge c ps) as [c2 ps2 | o ots | q k | why | why] eqn:Ep; try contradiction.
    + rewrite Es in E; injection E as <-. exists ps2; exact (pmstep_next pol ge c ps s' c2 ps2 Ep).
    + rewrite Es in E; discriminate E.
    + destruct Es as (k1 & Es & _); rewrite Es in E; discriminate E.
  - destruct (pstep pol ge c ps) as [c2 ps2 | o ots | q1 k | why | why] eqn:Ep; try contradiction.
    + rewrite Es in E; discriminate E.
    + rewrite Es in E; discriminate E.
    + destruct Es as (k1 & Es & Hk1); rewrite Es in E; injection E as <- <-.
      rewrite <- (Hk1 base).
      exists (snd (k base)); exact (pmstep_alloc pol ge c ps s q1 k base s' Ep He Ea).
  - exists ps; exact (pmstep_safepoint pol ge c ps s s' m' Hdue Hsp).
Qed.

(** An adequate Iris proof rules out failures in every reachable state.
    This covers both machine executions and finite deterministic-driver runs. *)
Lemma adequate_poison_all pol ge fr0 te0 m0 pm0 paux0 s0 fuel0 φ :
  @adequate (poison_lang pol ge) NotStuck (PRun fr0 te0) (mkPLstate m0 pm0 paux0 s0 fuel0) φ ->
  (forall c ps s,
     pmreachable pol ge (mkConfig fr0 [] m0 fuel0, mkPState te0 [] pm0 paux0, s0) (c, ps, s) ->
     ~ pfails pol ge c ps) /\
  (forall st,
     RM.mreachable ge (mkConfig fr0 [] m0 fuel0, s0) st ->
     ~ fails ge (fst st)) /\
  (forall steps,
     match PD.pdriver_run pol ge steps (mkConfig fr0 [] m0 fuel0) (mkPState te0 [] pm0 paux0) s0 with
     | PD.PDriverNext _ _ _ => True
     | PD.PDriverDone o _ => ~ failure o
     | PD.PDriverTrap _ | PD.PDriverBad _ => False
     end).
Proof.
  intros Had.
  assert (Hir0 : piris_reach pol ge fr0 te0 m0 pm0 paux0 s0 fuel0
                   (mkConfig fr0 [] m0 fuel0) (mkPState te0 [] pm0 paux0) s0).
  { exists []; split; [reflexivity | split; [reflexivity | apply rtc_refl]]. }
  assert (Hpm_ir : forall st1 st2,
            pmreachable pol ge st1 st2 ->
            (let '(c1, ps1, s1) := st1 in piris_reach pol ge fr0 te0 m0 pm0 paux0 s0 fuel0 c1 ps1 s1) ->
            (let '(c2, ps2, s2) := st2 in piris_reach pol ge fr0 te0 m0 pm0 paux0 s0 fuel0 c2 ps2 s2)).
  { intros st1 st2 H.
    induction H as [[[c1 ps1] s1] [[c2 ps2] s2] Hs | [[c1 ps1] s1] | [[c1 ps1] s1] [[c2 ps2] s2] [[c3 ps3] s3] _ IH1 _ IH2].
    - intros Hr1; exact (preach_step pol ge fr0 te0 m0 pm0 paux0 s0 fuel0 φ c1 ps1 s1 c2 ps2 s2 Had Hr1 Hs).
    - auto.
    - intros Hr1; exact (IH2 (IH1 Hr1)). }
  assert (Hpm_ok : forall c ps s,
            pmreachable pol ge (mkConfig fr0 [] m0 fuel0, mkPState te0 [] pm0 paux0, s0) (c, ps, s) ->
            ~ pfails pol ge c ps).
  { intros c ps s Hmr.
    exact (preach_not_pfails pol ge fr0 te0 m0 pm0 paux0 s0 fuel0 φ c ps s Had (Hpm_ir _ _ Hmr Hir0)). }
  split; [exact Hpm_ok | split].
  - assert (Hlift : forall st1 st2,
              RM.mreachable ge st1 st2 ->
              (exists ps1, pmreachable pol ge (mkConfig fr0 [] m0 fuel0, mkPState te0 [] pm0 paux0, s0) (fst st1, ps1, snd st1)) ->
              (exists ps2, pmreachable pol ge (mkConfig fr0 [] m0 fuel0, mkPState te0 [] pm0 paux0, s0) (fst st2, ps2, snd st2))).
    { intros st1 st2 H.
      induction H as [[c1 s1] [c2 s2] Hs | st1 | st1 st2 st3 _ IH1 _ IH2].
      - intros [ps1 Hmr1]; cbn [fst snd] in *.
        destruct (mstep_lifts_pmstep pol ge c1 ps1 s1 c2 s2 (Hpm_ok c1 ps1 s1 Hmr1) Hs) as [ps2 Hps2].
        exists ps2; eapply rt_trans; [exact Hmr1 | apply rt_step; exact Hps2].
      - auto.
      - intros H1; exact (IH2 (IH1 H1)). }
    intros [c s] Hmr.
    destruct (Hlift _ _ Hmr (ex_intro _ (mkPState te0 [] pm0 paux0) (rt_refl _ _ _))) as [ps Hpmr].
    cbn [fst snd] in *.
    exact (not_pfails_not_fails pol ge c ps (Hpm_ok c ps s Hpmr)).
  - assert (Hdrv : forall steps c ps s,
              pmreachable pol ge (mkConfig fr0 [] m0 fuel0, mkPState te0 [] pm0 paux0, s0) (c, ps, s) ->
              match PD.pdriver_run pol ge steps c ps s with
              | PD.PDriverNext _ _ _ => True
              | PD.PDriverDone o _ => ~ failure o
              | PD.PDriverTrap _ | PD.PDriverBad _ => False
              end).
    { intros steps; induction steps as [|n IH]; intros c ps s Hmr; cbn [PD.pdriver_run].
      - exact I.
      - pose proof (Hpm_ok c ps s Hmr) as Hnp; unfold pfails in Hnp.
        destruct (pstep pol ge c ps) as [c' ps' | o ots | q k | why | why] eqn:Ep; try contradiction.
        + apply (IH c' ps' s).
          eapply rt_trans; [exact Hmr | apply rt_step; exact (pmstep_next pol ge c ps s c' ps' Ep)].
        + exact Hnp.
        + assert (Hex : 0 <= req_extent q) by lia.
          rewrite (proj2 (Z.ltb_ge _ _) Hex).
          destruct (R.alloc s q) as [[base s']|] eqn:Ea.
          * pose proof (pmstep_alloc pol ge c ps s q k base s' Ep Hex Ea) as Hal.
            destruct (k base) as [c' ps'] eqn:Ek; cbn [fst snd] in Hal.
            apply (IH c' ps' s').
            eapply rt_trans; [exact Hmr | apply rt_step; exact Hal].
          * cbn; unfold refusal; intros Hnr; apply Hnr; left; reflexivity. }
    intros steps; exact (Hdrv steps _ _ _ (rt_refl _ _ _)).
Qed.

(** ## The two heaps and weakest preconditions

    A write may change a byte's value and the ways it can be used.
    The proof tracks both changes and checks that neither affects bytes
    owned by other callers. Two [[ghost-state|ghost heaps]] keep these records. *)

Section logic.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ, !gen_heapGS ppiece ppval Σ}.

(** Both shared maps must agree with physical memory. Collector steps
    preserve the poison map. *)
Definition poison_heap_interp (σ : plstate) : iProp Σ :=
  ∃ (h : gmap piece pval) (ph : gmap ppiece ppval),
    gen_heap_interp h ∗ gen_heap_interp ph ∗
    ⌜agrees (pl_mem σ) h /\ agrees_p (pl_mem σ) (pl_pm σ) (pl_paux σ) ph /\
      live_disjoint (pl_mem σ) /\ R.ready (pl_rt σ) (pl_mem σ)⌝.

(** The language uses the joint state interpretation and does not fork. *)
Local Instance poison_irisGS pol ge : irisGS_gen hlc (poison_lang pol ge) Σ :=
  IrisG _ (fun σ _ _ _ => poison_heap_interp σ) (fun _ => True%I) (fun _ => 0%nat)
    (fun _ _ _ _ => fupd_intro _ _).

(** An integer cell owns its physical bytes and their poison restrictions.
    Mutable cells can use any [pb_normal] state, including sticky taint. *)
Definition picell b o x pb : iProp Σ := pts (cell b o x) ∗ ppts (pcell_ps b o pb).

(** A byte assertion pairs one physical byte with its poison state. *)
Definition pibyte b o x pb : iProp Σ :=
  pts [(PByte b o, VByte x)] ∗ ppts [(PPByte b o, VPByte pb)].

(** A pointer cell owns both the address bytes and the capability slot,
    with separate poison for its address and its shadow capability. *)
Definition ppcell b o (p : ptr) pb tc : iProp Σ :=
  pts ((PAux b o, VAux (ptr_cap p)) :: cell b o (ptr_addr p)) ∗
  ppts ((PPAux b o, VPAux tc) :: pcell_ps b o pb).

(** Fractional memory ownership reveals the physical facts needed by a
    read, without granting permission to change the poison heap. *)
Lemma poison_ptsq_facts σ dq ps :
  poison_heap_interp σ -∗ ptsq dq ps -∗ ⌜owned_facts ps (pl_mem σ)⌝.
Proof.
  iIntros "Hσ Hps". iDestruct "Hσ" as (h ph) "(Hh & Hph & %Hσ)".
  destruct Hσ as (Ha & Hp & Hd & Hr).
  iDestruct (ptsq_lookup with "Hh Hps") as %Hl. iPureIntro.
  split; [|split; [exact Hd|exact (R.address_space _ _ Hr)]].
  apply all_agree_intro. intros l v Hin. apply Ha, Hl, Hin.
Qed.

(** Fractional poison ownership reveals the restrictions on the owned
    bytes and shadow slots. *)
Lemma poison_pptsq_facts σ dq pps :
  poison_heap_interp σ -∗ pptsq dq pps -∗
  ⌜all_p_agree (pl_mem σ) (pl_pm σ) (pl_paux σ) pps⌝.
Proof.
  iIntros "Hσ Hpps". iDestruct "Hσ" as (h ph) "(Hh & Hph & %Hσ)".
  destruct Hσ as (Ha & Hp & Hd & Hr).
  iDestruct (pptsq_lookup with "Hph Hpps") as %Hl. iPureIntro.
  induction pps as [|[l v] pps IH]; [exact I|].
  split; [apply Hp, Hl; by left|]. apply IH. intros l' v' Hin. apply Hl; by right.
Qed.

(** A collector preserves both heaps, including poison tokens belonging
    to objects that have already been freed. *)
Lemma poison_heap_safepoint m pm paux s fuel m' s' :
  R.safepoint s m s' m' ->
  poison_heap_interp (mkPLstate m pm paux s fuel) -∗
  poison_heap_interp (mkPLstate m' pm paux s' fuel).
Proof.
  intros Hsp. iIntros "Hσ". iDestruct "Hσ" as (h ph) "(Hh & Hph & %Hσ)".
  destruct Hσ as (Ha & Hp & Hd & Hr).
  destruct (SS.safepoint_shape _ _ _ _ Hsp) as (Hreg & Hb & Haux).
  iExists h, ph. iFrame. iPureIntro. cbn in *.
  split; [|split; [|split]].
  - intros l v Hl. exact (agree_piece_safepoint _ _ _ _ Hreg Hb Haux (Ha l v Hl)).
  - intros l v Hl. exact (agree_ppiece_safepoint _ _ _ _ _ _ Hreg (Hp l v Hl)).
  - exact (SS.live_disjoint_safepoint _ _ _ _ Hsp Hd).
  - exact (R.safepoint_ready _ _ _ _ Hsp Hr).
Qed.

Section wp.
Context (pol : poison_policy) (ge : genv).
Local Notation pexprL := (language.expr (poison_lang pol ge)).
Implicit Types Φ : (outcome * list word_taint) -> iProp Σ.

(** Instruction steps advance the program or finish a call. Allocation
    refusals, nonreturning stops, and collector steps instead preserve the
    resources needed to retry the proof. *)
Definition pmoves fr te σ e2 σ2 : Prop :=
  let c0 := mkConfig fr [] (pl_mem σ) (pl_fuel σ) in
  let ps0 := mkPState te [] (pl_pm σ) (pl_paux σ) in
  (exists c' ps' pcs', pstep pol ge c0 ps0 = PNext c' ps' /\
    pcs_callers pcs' = c_callers c' /\ pcs_tcallers pcs' = ps_callers ps' /\
    e2 = pstack_expr (PRun (c_frame c') (ps_tenv ps')) pcs' /\
    σ2 = mkPLstate (c_mem c') (ps_mem ps') (ps_aux ps') (pl_rt σ) (c_fuel c')) \/
  (exists q k base s', pstep pol ge c0 ps0 = PFresh q k /\ 0 <= req_extent q /\
    R.alloc (pl_rt σ) q = Some (base, s') /\
    e2 = PRun (c_frame (fst (k base))) (ps_tenv (snd (k base))) /\
    σ2 = mkPLstate (c_mem (fst (k base))) (ps_mem (snd (k base))) (ps_aux (snd (k base)))
      s' (c_fuel (fst (k base)))) \/
  (exists o ots m', pstep pol ge c0 ps0 = PDone o ots /\ returning o /\
    invalidate_locals (fr_locals fr) (pl_mem σ) = Some m' /\
    e2 = PEnd o ots /\ σ2 = mkPLstate m' (pl_pm σ) (pl_paux σ) (pl_rt σ) (pl_fuel σ)).

(** A running frame is safe when the owned resources exclude faults and
    each moving step reestablishes both heaps and its continuation. This
    rule also applies at allocation and return instructions. *)
Lemma wp_lift_prun (Q : iProp Σ) fr te Φ :
  (forall σ, poison_heap_interp σ -∗ Q -∗
    ⌜~ pfails pol ge (mkConfig fr [] (pl_mem σ) (pl_fuel σ))
      (mkPState te [] (pl_pm σ) (pl_paux σ))⌝) ->
  (forall σ, poison_heap_interp σ -∗ Q -∗
    ▷ ∀ e2 σ2, ⌜pmoves fr te σ e2 σ2⌝ ==∗
      poison_heap_interp σ2 ∗ WP (e2 : pexprL) {{ Φ }}) ->
  Q -∗ WP (PRun fr te : pexprL) {{ Φ }}.
Proof.
  intros Hnf Hst. iLöb as "IH". iIntros "HQ".
  iApply wp_lift_base_step; [done|]. iIntros (σ ns κ κs nt) "Hσ".
  iDestruct (Hnf with "Hσ HQ") as %Hnf'.
  iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
  iSplitR; [iPureIntro; by apply prun_reducible|].
  iAssert ((▷ ∀ e2 σ2, ⌜pmoves fr te σ e2 σ2⌝ ==∗
      poison_heap_interp σ2 ∗ WP (e2 : pexprL) {{ Φ }}) ∧ (poison_heap_interp σ ∗ Q))%I
    with "[Hσ HQ]" as "H".
  { iSplit; [iApply (Hst with "Hσ HQ")|iFrame]. }
  iNext. iIntros (e2 σ2 efs Hstep) "_". iMod "Hclose" as "_".
  destruct (phead_step_run_inv _ _ _ _ _ _ _ _ _ Hstep) as (_ & -> & Hc).
  destruct Hc as [Hn | [Ha | [(q & k & _ & _ & _ & -> & ->) |
    [Hr | [(o & ots & _ & _ & _ & -> & ->) | (s' & m' & _ & _ & Hsp & -> & ->)]]]]].
  - iDestruct "H" as "[H _]". iMod ("H" with "[%]") as "[Hσ Hwp]"; [by left|].
    iModIntro. iFrame. done.
  - iDestruct "H" as "[H _]". iMod ("H" with "[%]") as "[Hσ Hwp]"; [by (right; left)|].
    iModIntro. iFrame. done.
  - iDestruct "H" as "[_ [Hσ HQ]]". iModIntro. iFrame "Hσ".
    iSplitL; [iApply ("IH" with "HQ")|done].
  - iDestruct "H" as "[H _]". iMod ("H" with "[%]") as "[Hσ Hwp]"; [by (right; right)|].
    iModIntro. iFrame. done.
  - iDestruct "H" as "[_ [Hσ HQ]]". iModIntro. iFrame "Hσ".
    iSplitL; [iApply ("IH" with "HQ")|done].
  - iDestruct "H" as "[_ [Hσ HQ]]". iModIntro. destruct σ as [m pm paux s fuel].
    iSplitL "Hσ"; [iApply (poison_heap_safepoint with "Hσ"); exact Hsp|].
    iSplitL; [iApply ("IH" with "HQ")|done].
Qed.

(** A read borrows ownership without changing memory or restrictions.
    After both access checks pass, the caller receives the same ownership back. *)
Lemma wp_pread dq pdq ps pps fr te fr' te' pcs Φ :
  (forall m pm paux fuel, owned_facts ps m -> all_p_agree m pm paux pps ->
    pstep pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux) =
      PNext (mkConfig fr' (pcs_callers pcs) m fuel)
            (mkPState te' (pcs_tcallers pcs) pm paux)) ->
  ptsq dq ps -∗ pptsq pdq pps -∗
  ▷ (ptsq dq ps -∗ pptsq pdq pps -∗
     WP (pstack_expr (PRun fr' te') pcs : pexprL) {{ Φ }}) -∗
  WP (PRun fr te : pexprL) {{ Φ }}.
Proof.
  intros Hs. iIntros "Hps Hpps HK". iCombine "Hps Hpps HK" as "H".
  iApply (wp_lift_prun with "H").
  - iIntros (σ) "Hσ [Hps [Hpps _]]".
    iDestruct (poison_ptsq_facts with "Hσ Hps") as %Hf.
    iDestruct (poison_pptsq_facts with "Hσ Hpps") as %Hpf.
    iPureIntro. unfold pfails. rewrite (Hs _ _ _ _ Hf Hpf). auto.
  - iIntros ([m pm paux s fuel]) "Hσ [Hps [Hpps HK]]".
    iDestruct (poison_ptsq_facts with "Hσ Hps") as %Hf.
    iDestruct (poison_pptsq_facts with "Hσ Hpps") as %Hpf.
    cbn [pl_mem pl_pm pl_paux pl_fuel] in Hf, Hpf.
    pose proof (Hs m pm paux fuel Hf Hpf) as E.
    iNext. iIntros (e2 σ2 Hm).
    destruct Hm as [(c' & ps' & pcs' & E' & Hcs & Htcs & -> & ->) |
      [(q & k & b & s' & E' & _) | (o & ots & m' & E' & _)]];
      cbn [pl_mem pl_pm pl_paux pl_rt pl_fuel] in E'; rewrite E in E'; try discriminate E'.
    injection E' as <- <-.
    assert (pcs' = pcs) as ->.
    { exact (pcs_sync_inj _ _ Hcs Htcs). }
    cbn [c_frame c_mem c_fuel ps_tenv ps_mem ps_aux].
    iModIntro. iFrame "Hσ". iApply ("HK" with "Hps Hpps").
Qed.

(** A pure step needs neither heap. This includes arithmetic, checked
    public control flow, and helper-call entry when their operational
    premises do not depend on memory. *)
Lemma wp_ppure_next fr te fr' te' pcs Φ :
  (forall m pm paux fuel,
    pstep pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux) =
      PNext (mkConfig fr' (pcs_callers pcs) m fuel)
            (mkPState te' (pcs_tcallers pcs) pm paux)) ->
  ▷ WP (pstack_expr (PRun fr' te') pcs : pexprL) {{ Φ }} -∗
  WP (PRun fr te : pexprL) {{ Φ }}.
Proof.
  intros Hs. iIntros "HK".
  iApply (wp_pread (DfracOwn 1) (DfracOwn 1) [] [] with "[] [] [HK]");
    [intros; apply Hs|by rewrite /ptsq|by rewrite /pptsq|].
  iNext. iIntros "_ _". iExact "HK".
Qed.

(** A write updates only pieces owned in the two heaps. The frame
    conditions protect every other object's bytes and poison restrictions;
    [kept] preserves the runtime's readiness across the physical write. *)
Lemma wp_pwrite ps ps' pps pps' fr te fr' te' pcs
    (upd : mem -> mem) (upm : (Z -> poison_byte) -> Z -> poison_byte)
    (upa : (Z -> taint) -> Z -> taint) Φ :
  ps'.*1 = ps.*1 -> pps'.*1 = pps.*1 ->
  (forall m pm paux fuel, owned_facts ps m -> all_p_agree m pm paux pps ->
    pstep pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux) =
      PNext (mkConfig fr' (pcs_callers pcs) (upd m) fuel)
            (mkPState te' (pcs_tcallers pcs) (upm pm) (upa paux)) /\
    kept m (upd m) /\ live_disjoint (upd m) /\
    all_agree (upd m) ps' /\ frame_ok ps'.*1 m (upd m) /\
    all_p_agree (upd m) (upm pm) (upa paux) pps' /\
    pframe_ok pps'.*1 m (upd m) pm (upm pm) paux (upa paux)) ->
  pts ps -∗ ppts pps -∗
  ▷ (pts ps' -∗ ppts pps' -∗ WP (pstack_expr (PRun fr' te') pcs : pexprL) {{ Φ }}) -∗
  WP (PRun fr te : pexprL) {{ Φ }}.
Proof.
  intros Hk Hpk Hs. iIntros "Hps Hpps HK". iCombine "Hps Hpps HK" as "H".
  iApply (wp_lift_prun with "H").
  - iIntros (σ) "Hσ [Hps [Hpps _]]".
    iDestruct (poison_ptsq_facts with "Hσ Hps") as %Hf.
    iDestruct (poison_pptsq_facts with "Hσ Hpps") as %Hpf.
    destruct (Hs _ _ _ (pl_fuel σ) Hf Hpf) as (E & _).
    iPureIntro. unfold pfails. rewrite E. auto.
  - iIntros ([m pm paux s fuel]) "Hσ [Hps [Hpps HK]]".
    iDestruct (poison_ptsq_facts with "Hσ Hps") as %Hf.
    iDestruct (poison_pptsq_facts with "Hσ Hpps") as %Hpf.
    destruct (Hs _ _ _ fuel Hf Hpf) as (E & Hkept & Hd' & Hag & Hfr & Hpag & Hpfr).
    iNext. iIntros (e2 σ2 Hm).
    destruct Hm as [(c' & ps0 & pcs' & E' & Hcs & Htcs & -> & ->) |
      [(q & k & b & s' & E' & _) | (o & ots & m' & E' & _)]];
      cbn [pl_mem pl_pm pl_paux pl_rt pl_fuel] in E'; rewrite E in E'; try discriminate E'.
    injection E' as <- <-.
    assert (pcs' = pcs) as ->.
    { exact (pcs_sync_inj _ _ Hcs Htcs). }
    cbn [c_frame c_mem c_fuel ps_tenv ps_mem ps_aux].
    iDestruct "Hσ" as (h ph) "(Hh & Hph & %Hσ)".
    destruct Hσ as (Ha & Hpa & Hd & Hr).
    iMod (pts_update with "Hh Hps") as "[Hh Hps]"; [exact Hk|].
    iMod (ppts_update with "Hph Hpps") as "[Hph Hpps]"; [exact Hpk|].
    iModIntro. iSplitL "Hh Hph".
    + iExists (overwrite ps' h), (poverwrite pps' ph). iFrame. iPureIntro.
      split; [|split; [|split; [exact Hd'|exact (R.ready_kept _ _ _ Hr Hkept)]]].
      * intros l v Hl. destruct (lookup_overwrite _ _ _ _ Hl) as [Hin | [Hn Hh]].
        -- exact (all_agree_elem _ _ _ _ Hag Hin).
        -- exact (Hfr l v Hn (Ha l v Hh)).
      * intros l v Hl. destruct (lookup_poverwrite _ _ _ _ Hl) as [Hin | [Hn Hph]].
        -- exact (all_p_agree_elem _ _ _ _ _ _ Hpag Hin).
        -- exact (Hpfr l v Hn (Hpa l v Hph)).
    + iApply ("HK" with "Hps Hpps").
Qed.

(** Allocation grants ownership of the fresh bytes, capabilities, and
    poison slots. Both poison maps are cleared across the requested
    extent, including stale shadow taint at a reused address. *)
Lemma wp_palloc fr te q (fr' : Z -> frame) (te' : Z -> tenv) Φ :
  0 < req_align q -> 0 <= req_extent q ->
  (forall m pm paux fuel,
    pstep pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux) =
      PFresh q (fun base =>
        (mkConfig (fr' base) [] (allocated m q base) fuel,
         mkPState (te' base) [] (unpoison_range pm base (req_extent q))
           (unpoison_aux paux base (req_extent q))))) ->
  ▷ (∀ base, ⌜0 < base /\ base mod req_align q = 0 /\ base + req_extent q <= 2 ^ 48⌝ -∗
     pts (obj_ps base q) -∗ ppts (pobj_ps base q) -∗
     WP (PRun (fr' base) (te' base) : pexprL) {{ Φ }}) -∗
  WP (PRun fr te : pexprL) {{ Φ }}.
Proof.
  intros Hal Hex Hs. iIntros "HK". iApply (wp_lift_prun with "HK").
  - iIntros (σ) "_ _". iPureIntro. unfold pfails. rewrite Hs. lia.
  - iIntros ([m pm paux s fuel]) "Hσ HK". iNext. iIntros (e2 σ2 Hm).
    destruct Hm as [(c' & ps' & pcs' & E' & _) |
      [(q' & k & base & s' & E' & _ & Ha & -> & ->) | (o & ots & m' & E' & _)]];
      cbn [pl_mem pl_pm pl_paux pl_rt pl_fuel] in E'; rewrite Hs in E'; try discriminate E'.
    injection E' as <- <-. cbn [fst snd c_frame c_mem c_fuel ps_tenv ps_mem ps_aux].
    iDestruct "Hσ" as (h ph) "(Hh & Hph & %Hσ)".
    destruct Hσ as (Hag & Hpag & Hd & Hr).
    destruct (R.fresh_allocation _ _ _ _ _ Hr Hal Hex Ha) as [Hf Hr'].
    pose proof Hf as (Hpos & Hmod & _ & Hnone & _).
    iMod (pts_alloc h (obj_ps base q) with "Hh") as "[Hh Hps]".
    { apply obj_ps_nodup. }
    { intros l v Hin. destruct (h !! l) as [v'|] eqn:E; [|reflexivity]. exfalso.
      pose proof (agree_piece_registered _ _ _ (obj_ps_mem _ _ _ _ Hin) (Hag l v' E)) as Hreg.
      rewrite (obj_ps_id _ _ _ _ Hin) in Hreg. exact (Hreg Hnone). }
    iMod (ppts_alloc ph (pobj_ps base q) with "Hph") as "[Hph Hpps]".
    { apply pobj_ps_nodup. }
    { intros l v Hin. destruct (ph !! l) as [v'|] eqn:E; [|reflexivity]. exfalso.
      pose proof (agree_ppiece_registered _ _ _ _ _ (Hpag l v' E)) as Hreg.
      rewrite (pobj_ps_id _ _ _ _ Hin) in Hreg. exact (Hreg Hnone). }
    iModIntro. iSplitL "Hh Hph".
    + iExists (overwrite (obj_ps base q) h), (poverwrite (pobj_ps base q) ph). iFrame.
      iPureIntro. split; [|split; [|split]].
      * intros l v Hl. destruct (lookup_overwrite _ _ _ _ Hl) as [Hin | [_ Hh]].
        -- exact (obj_ps_agree _ _ _ _ _ Hf Hex Hin).
        -- exact (agree_piece_allocated _ _ _ _ _ Hnone (Hag l v Hh)).
      * intros l v Hl. destruct (lookup_poverwrite _ _ _ _ Hl) as [Hin | [_ Hph]].
        -- exact (pobj_ps_agree _ _ _ _ _ _ _ Hf Hex Hin).
        -- exact (agree_ppiece_allocated _ _ _ _ _ _ _ Hf (Hpag l v Hph)).
      * exact (live_disjoint_allocated _ _ _ Hd Hf Hex).
      * exact Hr'.
    + iApply ("HK" with "[%] Hps Hpps"). split; [exact Hpos|]. split; [exact Hmod|].
      destruct (R.address_space _ _ Hr' base (mkRegion base (base + req_extent q) (req_kind q) Live))
        as [_ Hend]; [rewrite object_region_allocated Z.eqb_refl; reflexivity|]. exact Hend.
Qed.

(** Heap allocation checks a public size and clears both poison maps.
    The continuation owns all value and poison pieces of the new object. *)
Lemma wp_palloc_heap f e te ls l d k al v rest j size Φ :
  value_x ge e L v = Some (WInt size) -> value_t te L v = Some (WTInt taint_bot) ->
  0 <= size -> size <= max_allocation_size ->
  ▷ (∀ base, ⌜0 < base /\ base mod req_align (heap_req al size) = 0 /\
              base + req_extent (heap_req al size) <= 2 ^ 48⌝ -∗
     pts (obj_ps base (heap_req al size)) -∗ ppts (pobj_ps base (heap_req al size)) -∗
     WP (PRun (mkFrame f (put d (WPtr (mkPtr base (Obj base))) e) ls None (Exec l rest j))
       (put d (WTPtr taint_bot taint_bot) te) : pexprL) {{ Φ }}) -∗
  WP (PRun (mkFrame f e ls None (Exec l (Let d k (Alloc al) [v] :: rest) j)) te : pexprL) {{ Φ }}.
Proof.
  intros Hv Ht Hs0 Hs. apply wp_palloc.
  - cbn. lia.
  - cbn. apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia.
  - intros m pm paux fuel. unfold pstep.
    change (tstep pol ge _ _) with
      (let_tstep pol ge e (mkPState te [] pm paux) d k (Alloc al) [v]).
    assert (Hz : is_zero_idiom (Alloc al) k [v] = false)
      by (unfold is_zero_idiom; apply andb_false_r).
    unfold let_tstep. rewrite Hz. cbn [ps_tenv ps_callers ps_mem ps_aux].
    rewrite Hv Ht. cbn [taint_bot t_branch t_index].
    rewrite (proj2 (Z.ltb_ge _ _) Hs).
    rewrite (rule_alloc ge f e ls l d k al [v] rest j [] m fuel size);
      [reflexivity|cbn [map2_option]; rewrite Hv; reflexivity|exact Hs].
Qed.

(** A return with no local allocations preserves both heaps. The result
    carries its taints to the caller rather than silently discarding them. *)
Lemma wp_preturn fr te o ots Φ :
  fr_locals fr = [] -> returning o ->
  (forall m pm paux fuel,
    pstep pol ge (mkConfig fr [] m fuel) (mkPState te [] pm paux) = PDone o ots) ->
  ▷ Φ (o, ots) -∗ WP (PRun fr te : pexprL) {{ Φ }}.
Proof.
  intros Hls Hret Hs. iIntros "HK". iApply (wp_lift_prun with "HK").
  - iIntros (σ) "_ _". iPureIntro. unfold pfails. rewrite Hs.
    destruct o; cbn in *; tauto.
  - iIntros ([m pm paux s fuel]) "Hσ HK". iNext. iIntros (e2 σ2 Hm).
    destruct Hm as [(c' & ps' & pcs' & E' & _) |
      [(q & k & base & s' & E' & _) | (o' & ots' & m' & E' & _ & Hi & -> & ->)]];
      cbn [pl_mem pl_pm pl_paux pl_rt pl_fuel] in E'; rewrite Hs in E'; try discriminate E'.
    injection E' as <- <-. rewrite Hls in Hi. cbn in Hi. injection Hi as <-.
    iModIntro. iFrame "Hσ". iApply (wp_value' _ _ _ (o, ots)). iExact "HK".
Qed.

(** A caller resumes only if both the returned value and its taint fit
    the call result. This rules out mismatched taint stacks in adequacy. *)
Lemma wp_presume o ots cf cte r cf' cte' Φ :
  presume cf cte r o ots = Some (cf', cte') ->
  ▷ WP (PRun cf' cte' : pexprL) {{ Φ }} -∗
  WP (PWait (PEnd o ots) cf cte r : pexprL) {{ Φ }}.
Proof.
  intros Hr. iIntros "HK". iApply wp_lift_base_step; [done|].
  iIntros (σ ns κ κs nt) "Hσ". iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
  iSplitR; [iPureIntro; do 4 eexists; exact (phs_resume pol ge o ots cf cte r cf' cte' σ Hr)|].
  iNext. iIntros (e2 σ2 efs Hs) "_". iMod "Hclose" as "_". inversion Hs; subst.
  simplify_eq.
  iModIntro. iFrame "Hσ". iSplitL; [iExact "HK"|done].
Qed.

(** A suspended caller is an evaluation context, so a helper can be
    verified once and used through its own Hoare triple. *)
Local Instance pwait_ctx cf cte r :
  LanguageCtx (Λ := poison_lang pol ge) (fun e => PWait e cf cte r).
Proof. exact (ectxi_lang_ctx_item (Λ := poison_ectxi_lang pol ge) (KPWait cf cte r)). Qed.

(** A memory-independent operation checks its ordinary result and its
    taint transfer separately. In particular, [Select] joins all three
    operands' taints but does not impose a branch restriction. *)
Lemma wp_plet f e te ls l d k o args rest j classes xs w wt Φ :
  general_op o = true -> op_arg_classes o k = Some classes ->
  map2_option (value_x ge e) classes args = Some xs ->
  (forall m, op_res o k xs m = Some (OpRes (RVal w) m)) ->
  (forall pm paux,
    let_tstep pol ge e (mkPState te [] pm paux) d k o args =
      TNext (mkPState (put d wt te) [] pm paux)) ->
  ▷ WP (PRun (mkFrame f (put d w e) ls None (Exec l rest j)) (put d wt te) : pexprL) {{ Φ }} -∗
  WP (PRun (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) te : pexprL) {{ Φ }}.
Proof.
  intros Hg Hc Hx Ho Ht. apply (wp_ppure_next _ _ _ _ []).
  intros m pm paux fuel. unfold pstep.
  change (tstep pol ge _ _) with (let_tstep pol ge e (mkPState te [] pm paux) d k o args).
  rewrite Ht. rewrite (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg Hc Hx (Ho m)). reflexivity.
Qed.

(** A byte load borrows its object's life, value byte, and poison byte.
    It rejects load poison and carries the byte's taint into the result. *)
Lemma wp_praw_load_byte f e te ls l d k n off av rest j p b reg o x y pb ta tc dq pdq Φ :
  op_arg_classes (RawLoad (LdNarrow n) off) k = Some [A] ->
  value_x ge e A av = Some (WPtr p) -> value_t te A av = Some (WTPtr ta tc) ->
  fst (narrow_type n) = 1 -> extended n k x = Some y ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b -> raw_address (ptr_addr p) off = b + o ->
  t_index ta = false -> pol_check_branches pol && (t_branch ta || t_branch tc || t_index tc) = false ->
  pb_no_load pb = false ->
  ptsq dq [(PLive b, VLive reg); (PByte b o, VByte x)] -∗
  pptsq pdq [(PPByte b o, VPByte pb)] -∗
  ▷ (ptsq dq [(PLive b, VLive reg); (PByte b o, VByte x)] -∗
     pptsq pdq [(PPByte b o, VPByte pb)] -∗
     WP (PRun (mkFrame f (put d y e) ls None (Exec l rest j))
       (put d (WTInt (pb_taint pb)) te) : pexprL) {{ Φ }}) -∗
  WP (PRun (mkFrame f e ls None (Exec l (Let d k (RawLoad (LdNarrow n) off) [av] :: rest) j))
    te : pexprL) {{ Φ }}.
Proof.
  intros Hc Ha Hta Hn Hy Hp Hoff Hi Hb Hload.
  apply (wp_pread dq pdq _ _ _ _ _ _ []).
  intros m pm paux fuel (Hf & _) Hpf.
  cbn [all_agree agree_piece fst snd] in Hf.
  destruct Hf as [Hlv [[_ Hin] _]].
  destruct (Hin reg (proj1 Hlv) (proj2 Hlv)) as (Ho & He & Hv).
  cbn [all_p_agree agree_ppiece fst snd] in Hpf.
  destruct Hpf as [[_ Hpin] _].
  destruct (Hpin reg (proj1 Hlv) (proj2 Hlv)) as (_ & _ & Hpb).
  destruct (mem_1_facts _ _ _ Hpb) as (Hnl & _ & Htl).
  assert (E : Semantics.step ge
    (mkConfig (mkFrame f e ls None (Exec l (Let d k (RawLoad (LdNarrow n) off) [av] :: rest) j)) [] m fuel) =
    Next (mkConfig (mkFrame f (put d y e) ls None (Exec l rest j)) [] m fuel)).
  { apply rule_let with (classes := [A]) (xs := [WPtr p]); [reflexivity|exact Hc| |].
    - cbn [map2_option]. rewrite Ha. reflexivity.
    - rewrite (op_raw_load_byte m k n p off Hn).
      + rewrite Hoff Hv Hy. reflexivity.
      + rewrite Hoff. apply (access_read _ b reg); [exact Hp|exact (proj1 Hlv)|lia|lia|apply Z.mod_1_r]. }
  unfold pstep.
  change (tstep pol ge _ _) with
    (let_tstep pol ge e (mkPState te [] pm paux) d k (RawLoad (LdNarrow n) off) [av]).
  assert (Hz : is_zero_idiom (RawLoad (LdNarrow n) off) k [av] = false)
    by (unfold is_zero_idiom; apply andb_false_r).
  unfold let_tstep. rewrite Hz. cbn [ps_tenv ps_callers ps_mem ps_aux].
  rewrite Ha Hta Hi Hb.
  cbn [load_type_bytes]. rewrite Hn Hoff Hnl Hload Htl E.
  reflexivity.
Qed.

(** A byte store updates the value and poison heaps together. Its frame
    conditions preserve every unowned byte and capability-taint slot. *)
Lemma wp_praw_store_byte f e te ls l off v a rest j p b reg o x y pb tv ta tc Φ :
  value_x ge e W v = Some (WInt y) -> value_x ge e A a = Some (WPtr p) ->
  value_t te W v = Some (WTInt tv) -> value_t te A a = Some (WTPtr ta tc) ->
  ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o ->
  t_index ta = false -> pol_check_branches pol && (t_branch ta || t_branch tc || t_index tc) = false ->
  pb_no_store pb = false ->
  pts [(PLive b, VLive reg); (PByte b o, VByte x)] -∗
  ppts [(PPByte b o, VPByte pb)] -∗
  ▷ (pts [(PLive b, VLive reg); (PByte b o, VByte (y mod 256))] -∗
     ppts [(PPByte b o, VPByte (note_store_byte tv pb))] -∗
     WP (PRun (mkFrame f e ls None (Exec l rest j)) te : pexprL) {{ Φ }}) -∗
  WP (PRun (mkFrame f e ls None (Exec l (RawStore Wb off v a :: rest) j)) te : pexprL) {{ Φ }}.
Proof.
  intros Hv Ha Htv Hta Hp Hoff Hi Hb Hstore.
  apply (wp_pwrite _ _ _ _ _ _ _ _ []
    (fun m => store_bytes m (b + o) 1 y)
    (fun pm => mem_store_taint pm (b + o) 1 tv) (fun paux => paux));
    [reflexivity|reflexivity|].
  intros m pm paux fuel (Hf & Hd & Hfit) Hpf.
  cbn [all_agree agree_piece fst snd] in Hf.
  destruct Hf as [Hlv [[Hreg Hin] _]].
  destruct (Hin reg (proj1 Hlv) (proj2 Hlv)) as (Ho & He & _).
  cbn [all_p_agree agree_ppiece fst snd] in Hpf.
  destruct Hpf as [[Hpreg Hpin] _].
  destruct (Hpin reg (proj1 Hlv) (proj2 Hlv)) as (_ & _ & Hpb).
  destruct (mem_1_facts _ _ _ Hpb) as (_ & Hns & _).
  assert (E : Semantics.step ge
    (mkConfig (mkFrame f e ls None (Exec l (RawStore Wb off v a :: rest) j)) [] m fuel) =
    Next (mkConfig (mkFrame f e ls None (Exec l rest j)) [] (store_bytes m (b + o) 1 y) fuel)).
  { apply rule_raw_store with (vk := W) (x := WInt y) (p := p);
      [reflexivity|exact Hv|exact Ha|].
    rewrite Hoff. cbn -[access_res store_bytes]. rewrite Hp.
    rewrite (access_obj _ _ reg); [reflexivity|exact (proj1 Hlv)|lia|lia|apply Z.mod_1_r]. }
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - unfold pstep.
    change (tstep pol ge _ _) with
      (inst_tstep pol ge (mkFrame f e ls None (Exec l (RawStore Wb off v a :: rest) j))
        (mkPState te [] pm paux) (RawStore Wb off v a)).
    cbn [inst_tstep fr_env ps_tenv width_value_class ps_mem ps_aux ps_callers width_bytes].
    rewrite Ha Hta Hi Hb Hoff Hns Hstore Htv E. reflexivity.
  - apply store_bytes_kept. intros a' Ha'. exists b, reg. split; [exact (proj1 Hlv)|lia].
  - exact Hd.
  - cbn [all_agree agree_piece fst snd]. split; [exact Hlv|]. split; [|exact I].
    split; [exact Hreg|]. intros reg' E' L'. rewrite regions_store_bytes in E'.
    destruct Hlv as [E0 _]. rewrite E' in E0. injection E0 as <-.
    split; [exact Ho|]. split; [exact He|]. cbn.
    rewrite Z.leb_refl. replace (b + o <? b + o + 1) with true by (symmetry; apply Z.ltb_lt; lia).
    unfold byte_of. rewrite Z.sub_diag Z.mul_0_r Z.pow_0_r Z.div_1_r. reflexivity.
  - apply (frame_within _ _ _ b reg); [reflexivity|exact Hd|exact Hlv| |].
    + intros a' H. cbn. destruct ((b + o <=? a') && (a' <? b + o + 1)) eqn:Hr; [|reflexivity].
      exfalso. apply andb_true_iff in Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      apply H; [lia|]. replace (a' - b) with o by lia. cbn. right. left.
    + intros a' _. reflexivity.
  - cbn [all_p_agree agree_ppiece fst snd]. split; [|exact I].
    split; [exact Hpreg|]. intros reg' E' L'. rewrite regions_store_bytes in E'.
    destruct Hlv as [E0 _]. rewrite E' in E0. injection E0 as <-.
    split; [exact Ho|]. split; [exact He|]. unfold mem_store_taint.
    rewrite Z.leb_refl. replace (b + o <? b + o + 1) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn. rewrite Hpb. reflexivity.
  - apply (pframe_within _ _ _ b reg); [reflexivity|exact Hd|exact Hlv| |].
    + intros a' H. unfold mem_store_taint in H.
      destruct ((b + o <=? a') && (a' <? b + o + 1)) eqn:Hr; [|contradiction].
      apply andb_true_iff in Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      split; [lia|]. replace (a' - b) with o by lia. cbn. left.
    + intros a' H. contradiction.
Qed.

(** Free consumes the object's live token. Poison pieces remain valid
    because their byte and aux agreements are conditional on liveness. *)
Lemma wp_pfree_sym fnm f e te ls l v rest j b reg Φ :
  is_free_name fnm = true -> frees_heap (ge_free ge) ->
  find_fn ge fnm = None -> lookup fnm (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr (mkPtr b (Obj b))) ->
  arg_t te (Arg P v) = Some (WTPtr taint_bot taint_bot) ->
  r_kind reg = Heap -> b <> 0 ->
  pts [(PLive b, VLive reg)] -∗
  ▷ WP (PRun (mkFrame f e ls None (Exec l rest j)) te : pexprL) {{ Φ }} -∗
  WP (PRun (mkFrame f e ls None (Exec l (Call CVoid (Global fnm) [Arg P v] :: rest) j)) te : pexprL) {{ Φ }}.
Proof.
  intros Hfnm [_ Hfh] Hfn Hdata Hx Ht Hk Hb.
  assert (Hs : forall m pm paux fuel, live_at m b reg -> exists rs,
    replace_region b (mkRegion b b Heap Freed) (m_regions m) = Some rs /\
    pstep pol ge
      (mkConfig (mkFrame f e ls None (Exec l (Call CVoid (Global fnm) [Arg P v] :: rest) j)) [] m fuel)
      (mkPState te [] pm paux) =
    PNext (mkConfig (mkFrame f e ls None (Exec l rest j)) [] (mkMem (m_bytes m) rs (m_aux m)) fuel)
      (mkPState te [] pm paux)).
  { intros m pm paux fuel Hl. destruct (Hfh _ _ _ Hl Hk Hb) as (rs & Hrs & Hfree).
    exists rs. split; [exact Hrs|]. unfold pstep.
    change (tstep pol ge _ _) with
      (inst_tstep pol ge (mkFrame f e ls None (Exec l (Call CVoid (Global fnm) [Arg P v] :: rest) j))
        (mkPState te [] pm paux) (Call CVoid (Global fnm) [Arg P v])).
    cbn [inst_tstep fr_env ps_tenv map_option]. rewrite Ht Hfn Hdata Hfnm.
    cbn [taint_bot t_branch t_index].
    rewrite (rule_free_sym _ _ _ _ _ _ _ _ _ [] _ fuel _ _ Hfnm Hfn Hdata Hx Hfree). reflexivity. }
  iIntros "Hl HK". iCombine "Hl HK" as "H". iApply (wp_lift_prun with "H").
  - iIntros (σ) "Hσ [Hl _]".
    iDestruct (poison_ptsq_facts with "Hσ Hl") as %(Hf & _).
    cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [Hlv _].
    destruct (Hs _ (pl_pm σ) (pl_paux σ) (pl_fuel σ) Hlv) as (rs & _ & E).
    iPureIntro. unfold pfails. rewrite E. auto.
  - iIntros ([m pm paux s fuel]) "Hσ [Hl HK]".
    iDestruct (poison_ptsq_facts with "Hσ Hl") as %(Hf & _).
    cbn [all_agree agree_piece fst snd pl_mem] in Hf. destruct Hf as [Hlv _].
    destruct (Hs _ pm paux fuel Hlv) as (rs & Hrs & E).
    iNext. iIntros (e2 σ2 Hm).
    destruct Hm as [(c' & ps' & pcs & E' & Hcs & Htcs & -> & ->) |
      [(q & kk & base & s' & E' & _) | (o & ots & m' & E' & _)]];
      cbn [pl_mem pl_pm pl_paux pl_rt pl_fuel] in E'; rewrite E in E'; try discriminate E'.
    injection E' as <- <-.
    assert (pcs = []) as -> by (apply pcs_sync_inj; assumption).
    cbn [c_frame c_mem c_fuel ps_tenv ps_mem ps_aux pstack_expr].
    iDestruct "Hσ" as (h ph) "(Hh & Hph & %Hσ)".
    destruct Hσ as (Ha & Hpa & Hd & Hr).
    iMod (pts_update _ _ [(PLive b, VFreed)] with "Hh Hl") as "[Hh _]"; [reflexivity|].
    iModIntro. iSplitL "Hh Hph"; [|iExact "HK"].
    iExists (overwrite [(PLive b, VFreed)] h), ph. iFrame. iPureIntro.
    split; [|split; [|split]].
    + intros l' v' Hl'. destruct (lookup_overwrite _ _ _ _ Hl') as [Hin | [Hn Hh]].
      * apply list_elem_of_singleton in Hin. injection Hin as -> ->.
        cbn [agree_piece]. unfold registered. cbn [m_regions].
        rewrite (object_region_replace _ _ _ _ b Hrs eq_refl) Z.eqb_refl. discriminate.
      * apply (agree_piece_free m b reg rs); [exact Hlv|exact Hk|exact Hrs| |exact (Ha l' v' Hh)].
        intros ->. apply Hn. cbn. left.
    + intros l' v' Hl'. exact (agree_ppiece_free _ _ _ _ _ _ _ Hrs (Hpa l' v' Hl')).
    + exact (live_disjoint_free _ _ _ Hrs Hd).
    + exact (R.ready_kept _ _ _ Hr (free_heap_kept _ _ _ _ Hlv Hk Hrs)).
Qed.

(** A public goto enters its target without changing either heap. *)
Lemma wp_pgoto f e te ls l t Φ :
  ▷ WP (PRun (mkFrame f e ls None (Enter (edge_label t) (Some l))) te : pexprL) {{ Φ }} -∗
  WP (PRun (mkFrame f e ls None (Exec l [] (JGoto t))) te : pexprL) {{ Φ }}.
Proof.
  apply (wp_ppure_next _ _ _ _ []). intros m pm paux fuel.
  unfold pstep. change (tstep pol ge _ _) with (TNext (mkPState te [] pm paux)).
  rewrite rule_goto. reflexivity.
Qed.

(** Entering a block chooses values and taints from the same predecessor.
    Running out of block fuel stops safely; the proof does not assume
    that the program terminates. *)
Lemma wp_penter f e te ls l from b e' te' Φ :
  find_block l (fn_blocks f) = Some b ->
  phis_env ge (b_phis b) from e = Some e' -> phis_tenv (b_phis b) from te = Some te' ->
  ▷ WP (PRun (mkFrame f e' ls None (Exec l (b_insts b) (b_jump b))) te' : pexprL) {{ Φ }} -∗
  WP (PRun (mkFrame f e ls None (Enter l from)) te : pexprL) {{ Φ }}.
Proof.
  intros Hb He Ht.
  assert (Hs : forall m pm paux fuel,
    pstep pol ge (mkConfig (mkFrame f e ls None (Enter l from)) [] m fuel)
      (mkPState te [] pm paux) =
    if fuel =? 0 then PDone OutOfFuel [] else
      PNext (mkConfig (mkFrame f e' ls None (Exec l (b_insts b) (b_jump b))) [] m (fuel - 1))
        (mkPState te' [] pm paux)).
  { intros m pm paux fuel. unfold pstep.
    cbn [tstep c_frame fr_doomed fr_at c_fuel ps_tenv ps_callers ps_mem ps_aux fr_fn].
    destruct (Z.eqb_spec fuel 0) as [->|Hnz].
    - rewrite rule_out_of_fuel. reflexivity.
    - rewrite Hb Ht. rewrite (rule_enter _ _ _ _ _ _ _ _ _ _ _ Hnz Hb He). reflexivity. }
  iIntros "HK". iApply (wp_lift_prun with "HK").
  - iIntros (σ) "_ _". iPureIntro. unfold pfails. rewrite Hs.
    destruct (pl_fuel σ =? 0); cbn; auto.
  - iIntros ([m pm paux s fuel]) "Hσ HK". iNext. iIntros (e2 σ2 Hm).
    destruct (Z.eqb fuel 0) eqn:Ef.
    + exfalso. destruct Hm as [(c' & ps' & pcs' & E & _) |
        [(q & k & base & s' & E & _) | (o & ots & m' & E & Hr & _)]];
        cbn [pl_mem pl_pm pl_paux pl_fuel] in E; rewrite Hs Ef in E; try discriminate E.
      injection E as <-. exact Hr.
    + destruct Hm as [(c' & ps' & pcs' & E & Hcs & Htcs & -> & ->) |
        [(q & k & base & s' & E & _) | (o & ots & m' & E & _)]];
        cbn [pl_mem pl_pm pl_paux pl_fuel] in E; rewrite Hs Ef in E; try discriminate E.
      injection E as <- <-.
      assert (pcs' = []) as -> by exact (pcs_sync_inj pcs' [] Hcs Htcs).
      cbn [c_frame c_mem c_fuel ps_tenv ps_mem ps_aux pstack_expr].
      iModIntro. iFrame "HK". rewrite /poison_heap_interp /=. iExact "Hσ".
Qed.

(** A branch requires a public condition even if the chosen target is
    known from the current value. Secret conditions belong in [Select]. *)
Lemma wp_pbranch f e te ls l v t1 t2 n tv Φ :
  value_x ge e W v = Some (WInt n) -> value_t te W v = Some (WTInt tv) -> t_branch tv = false ->
  ▷ WP (PRun (mkFrame f e ls None
    (Enter (edge_label (if n =? 0 then t2 else t1)) (Some l))) te : pexprL) {{ Φ }} -∗
  WP (PRun (mkFrame f e ls None (Exec l [] (JBranch v t1 t2))) te : pexprL) {{ Φ }}.
Proof.
  intros Hv Ht Hb. apply (wp_ppure_next _ _ _ _ []). intros m pm paux fuel.
  unfold pstep. cbn [tstep c_frame fr_doomed fr_at jump_tstep ps_tenv]. rewrite Ht Hb.
  rewrite (rule_branch _ _ _ _ _ _ _ _ _ _ _ _ Hv). reflexivity.
Qed.

(** A call passes the arguments' taints to the helper and suspends both
    caller environments until the helper returns. *)
Lemma wp_pcall f e te ls l r g args rest j xs wts gf callee cte Φ :
  map_option (arg_x ge e) args = Some xs -> map_option (arg_t te) args = Some wts ->
  find_fn ge g = Some (Defined gf) -> variadic_func gf = false ->
  call_frame gf xs = Some callee -> call_tenv gf wts = Some cte ->
  ▷ WP (PWait (PRun callee cte) (mkFrame f e ls None (Exec l rest j)) te r : pexprL) {{ Φ }} -∗
  WP (PRun (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) te : pexprL) {{ Φ }}.
Proof.
  intros Hx Ht Hf Hvar Hfr Hte.
  apply (wp_ppure_next _ _ _ _ [(mkFrame f e ls None (Exec l rest j), te, r)]).
  intros m pm paux fuel. unfold pstep.
  cbn [tstep c_frame fr_doomed fr_at inst_tstep ps_tenv ps_callers ps_mem ps_aux fr_env].
  rewrite Ht Hf Hvar Hte. rewrite (rule_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx Hf Hfr).
  reflexivity.
Qed.

(** To verify a call without inlining the helper, the caller proves the
    helper's specification once and checks that the returned value and taint
    both fit the call site. *)
Lemma wp_pcall_bind f e te ls l r g args rest j xs wts gf callee cte Φ :
  map_option (arg_x ge e) args = Some xs -> map_option (arg_t te) args = Some wts ->
  find_fn ge g = Some (Defined gf) -> variadic_func gf = false ->
  call_frame gf xs = Some callee -> call_tenv gf wts = Some cte ->
  ▷ WP (PRun callee cte : pexprL) {{ v, ∃ cf' te',
    ⌜presume (mkFrame f e ls None (Exec l rest j)) te r v.1 v.2 = Some (cf', te')⌝ ∗
    ▷ WP (PRun cf' te' : pexprL) {{ Φ }} }} -∗
  WP (PRun (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) te : pexprL) {{ Φ }}.
Proof.
  intros Hx Ht Hf Hvar Hfr Hte. iIntros "HK".
  iApply (wp_pcall with "[HK]"); [exact Hx|exact Ht|exact Hf|exact Hvar|exact Hfr|exact Hte|].
  iNext. iApply (wp_bind (fun ex => PWait ex (mkFrame f e ls None (Exec l rest j)) te r)
    NotStuck ⊤ (PRun callee cte : pexprL)).
  iApply (wp_mono with "HK"). iIntros ([o ots]) "HK".
  iDestruct "HK" as (cf' te') "[%Hr HK]". iApply (wp_presume with "HK"). exact Hr.
Qed.

(** A scalar return hands its value and taint to the postcondition. *)
Lemma wp_pret f e te l v k x wt Φ :
  fn_ret f = RClass k -> value_x ge e k v = Some x -> value_t te k v = Some wt ->
  ▷ Φ (Ret x, [wt]) -∗
  WP (PRun (mkFrame f e [] None (Exec l [] (JRet v))) te : pexprL) {{ Φ }}.
Proof.
  intros Hk Hv Ht. apply wp_preturn; [reflexivity|exact I|].
  intros m pm paux fuel. unfold pstep.
  cbn [tstep c_frame fr_doomed fr_at jump_tstep fr_fn ps_tenv]. rewrite Hk Ht.
  cbn [return_tstep ps_callers].
  rewrite (rule_ret _ _ _ _ _ _ _ _ _ _ _ Hk Hv).
  rewrite (rule_return_top (mkFrame f e [] None (Exec l [] (JRet v)))
    m fuel _ m (invalidate_none m)). reflexivity.
Qed.

(** A void return finishes with an empty taint list once the function's
    signature declares no return value. *)
Lemma wp_pret_void f e te l Φ :
  fn_ret f = RVoid ->
  ▷ Φ (RetVoid, []) -∗
  WP (PRun (mkFrame f e [] None (Exec l [] JRetVoid)) te : pexprL) {{ Φ }}.
Proof.
  intros Hk. apply wp_preturn; [reflexivity | exact I |].
  intros m pm paux fuel. unfold pstep.
  cbn [tstep c_frame fr_doomed fr_at jump_tstep fr_fn return_tstep ps_callers].
  rewrite Hk rule_ret_void.
  rewrite (rule_return_top (mkFrame f e [] None (Exec l [] JRetVoid)) m fuel _ m (invalidate_none m)).
  reflexivity.
Qed.

(** Pure address computation through [[flight]] propagates address and
    capability taints without faulting on an index-tainted offset, matching
    native `lea`. *)
Lemma wp_pflight f e te ls l d o args lw rest j xs ts n c tc Φ :
  map_option (flight_arg_x ge e) args = Some xs ->
  map_option (flight_arg_t te) args = Some ts ->
  alu o L xs = Some (WInt n) ->
  flight_cap ge e lw = Some c ->
  flight_cap_t te lw = Some tc ->
  op_checks_vartime pol o L && t_vartime (join_taints ts) = false ->
  ▷ WP (PRun (mkFrame f (put d (WPtr (mkPtr n c)) e) ls None (Exec l rest j))
    (put d (WTPtr (join_taints ts) tc) te) : pexprL) {{ Φ }} -∗
  WP (PRun (mkFrame f e ls None (Exec l (Flight d o args lw :: rest) j)) te : pexprL) {{ Φ }}.
Proof.
  intros Hx Ht Ha Hc Htc Hvt. apply (wp_ppure_next _ _ _ _ []).
  intros m pm paux fuel. unfold pstep.
  cbn [tstep c_frame fr_doomed fr_at inst_tstep ps_tenv ps_callers ps_mem ps_aux].
  rewrite Ht Htc Hvt (rule_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx Ha Hc).
  reflexivity.
Qed.

(** Before a raw store or load, compiled code runs a bounds [[check]] that
    produces a proven address temporary while enforcing the policy's branch
    and header-index taint guards on the pointer. *)
Lemma wp_pcheck f e te ls l d lo hi r al v rest j p ta tc b reg dq Φ :
  value_x ge e P v = Some (WPtr p) ->
  value_t te P v = Some (WTPtr ta tc) ->
  check_ptr_bounds_taint pol ta tc = None ->
  ptr_cap p = Obj b ->
  b <= raw_address (ptr_addr p) lo ->
  raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg ->
  raw_address (ptr_addr p) lo mod al = 0 ->
  ptsq dq [(PLive b, VLive reg)] -∗
  ▷ (ptsq dq [(PLive b, VLive reg)] -∗
     WP (PRun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j))
       (put d (WTPtr ta tc) te) : pexprL) {{ Φ }}) -∗
  WP (PRun (mkFrame f e ls None (Exec l (Let d A (Check lo hi r al) [v] :: rest) j)) te : pexprL) {{ Φ }}.
Proof.
  intros Hv Ht Hchk Hp Hlo Hhi Hal. iIntros "Hl HK".
  iApply (wp_pread dq (DfracOwn 1) [(PLive b, VLive reg)] [] _ _ _ _ [] with "Hl [] [HK]");
    [|by rewrite /pptsq|iNext; iIntros "Hl _"; iApply ("HK" with "Hl")].
  intros m pm paux fuel (Hf & _) _.
  cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E _] _].
  assert (Es : Semantics.step ge
    (mkConfig (mkFrame f e ls None (Exec l (Let d A (Check lo hi r al) [v] :: rest) j)) [] m fuel) =
    Next (mkConfig (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) [] m fuel)).
  { apply rule_let with (classes := [P]) (xs := [WPtr p]); [reflexivity | reflexivity | cbn; rewrite Hv; reflexivity |].
    apply op_check. rewrite Hp. exact (access_obj _ _ _ _ _ _ _ E Hlo Hhi Hal). }
  unfold pstep.
  change (tstep pol ge _ _) with (let_tstep pol ge e (mkPState te [] pm paux) d A (Check lo hi r al) [v]).
  unfold let_tstep. cbn [is_zero_idiom andb ps_tenv ps_callers ps_mem ps_aux].
  rewrite Ht Hchk Es. reflexivity.
Qed.

(** A read-only bounds [[check]] accepts either a writable or a read-only
    object capability once the pointer's taint passes the policy guard. *)
Lemma wp_pcheck_read f e te ls l d lo hi al v rest j p ta tc b reg dq Φ :
  value_x ge e P v = Some (WPtr p) ->
  value_t te P v = Some (WTPtr ta tc) ->
  check_ptr_bounds_taint pol ta tc = None ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  b <= raw_address (ptr_addr p) lo ->
  raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg ->
  raw_address (ptr_addr p) lo mod al = 0 ->
  ptsq dq [(PLive b, VLive reg)] -∗
  ▷ (ptsq dq [(PLive b, VLive reg)] -∗
     WP (PRun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j))
       (put d (WTPtr ta tc) te) : pexprL) {{ Φ }}) -∗
  WP (PRun (mkFrame f e ls None (Exec l (Let d A (Check lo hi Read al) [v] :: rest) j)) te : pexprL) {{ Φ }}.
Proof.
  intros Hv Ht Hchk Hp Hlo Hhi Hal. iIntros "Hl HK".
  iApply (wp_pread dq (DfracOwn 1) [(PLive b, VLive reg)] [] _ _ _ _ [] with "Hl [] [HK]");
    [|by rewrite /pptsq|iNext; iIntros "Hl _"; iApply ("HK" with "Hl")].
  intros m pm paux fuel (Hf & _) _.
  cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E _] _].
  assert (Es : Semantics.step ge
    (mkConfig (mkFrame f e ls None (Exec l (Let d A (Check lo hi Read al) [v] :: rest) j)) [] m fuel) =
    Next (mkConfig (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) [] m fuel)).
  { apply rule_let with (classes := [P]) (xs := [WPtr p]); [reflexivity | reflexivity | cbn; rewrite Hv; reflexivity |].
    apply op_check. exact (access_read _ _ _ _ _ _ _ Hp E Hlo Hhi Hal). }
  unfold pstep.
  change (tstep pol ge _ _) with (let_tstep pol ge e (mkPState te [] pm paux) d A (Check lo hi Read al) [v]).
  unfold let_tstep. cbn [is_zero_idiom andb ps_tenv ps_callers ps_mem ps_aux].
  rewrite Ht Hchk Es. reflexivity.
Qed.

(** Across a loop back-edge or call, [[renew]] reuses an earlier dominating
    check for the same object while checking the joined taints of both
    operands. *)
Lemma wp_prenew f e te ls l d lo hi r al q1 v rest j p1 p qa qc ta tc b reg dq Φ :
  value_x ge e A q1 = Some (WPtr p1) ->
  value_x ge e P v = Some (WPtr p) ->
  value_t te A q1 = Some (WTPtr qa qc) ->
  value_t te P v = Some (WTPtr ta tc) ->
  check_ptr_bounds_taint pol (taint_join qa ta) (taint_join qc tc) = None ->
  ptr_cap p1 = ptr_cap p ->
  ptr_cap p = Obj b ->
  b <= raw_address (ptr_addr p) lo ->
  raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg ->
  raw_address (ptr_addr p) lo mod al = 0 ->
  ptsq dq [(PLive b, VLive reg)] -∗
  ▷ (ptsq dq [(PLive b, VLive reg)] -∗
     WP (PRun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j))
       (put d (WTPtr ta tc) te) : pexprL) {{ Φ }}) -∗
  WP (PRun (mkFrame f e ls None (Exec l (Let d A (Renew lo hi r al) [q1; v] :: rest) j)) te : pexprL) {{ Φ }}.
Proof.
  intros Hq1 Hv Htq1 Htv Hchk Hcap Hp Hlo Hhi Hal. iIntros "Hl HK".
  iApply (wp_pread dq (DfracOwn 1) [(PLive b, VLive reg)] [] _ _ _ _ [] with "Hl [] [HK]");
    [|by rewrite /pptsq|iNext; iIntros "Hl _"; iApply ("HK" with "Hl")].
  intros m pm paux fuel (Hf & _) _.
  cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E _] _].
  assert (Es : Semantics.step ge
    (mkConfig (mkFrame f e ls None (Exec l (Let d A (Renew lo hi r al) [q1; v] :: rest) j)) [] m fuel) =
    Next (mkConfig (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) [] m fuel)).
  { apply rule_let with (classes := [A; P]) (xs := [WPtr p1; WPtr p]);
      [reflexivity | reflexivity | cbn; rewrite Hq1 Hv; reflexivity |].
    apply op_renew; [exact Hcap |]. rewrite Hp. exact (access_obj _ _ _ _ _ _ _ E Hlo Hhi Hal). }
  unfold pstep.
  change (tstep pol ge _ _) with (let_tstep pol ge e (mkPState te [] pm paux) d A (Renew lo hi r al) [q1; v]).
  unfold let_tstep. cbn [is_zero_idiom andb ps_tenv ps_callers ps_mem ps_aux].
  rewrite Htq1 Htv Hchk Es. reflexivity.
Qed.

(** When a public allocation size exceeds Fil-C's size limit, the machine
    stops cleanly with a refusal trap, so callers need not bound the
    requested size from above. *)
Lemma wp_palloc_any f e te ls l d k al v rest j size tsz Φ :
  value_x ge e L v = Some (WInt size) ->
  value_t te L v = Some (WTInt tsz) ->
  t_branch tsz = false ->
  t_index tsz = false ->
  0 <= size ->
  ▷ (∀ base, ⌜0 < base /\ base mod req_align (heap_req al size) = 0 /\
              base + req_extent (heap_req al size) <= 2 ^ 48⌝ -∗
     pts (obj_ps base (heap_req al size)) -∗ ppts (pobj_ps base (heap_req al size)) -∗
     WP (PRun (mkFrame f (put d (WPtr (mkPtr base (Obj base))) e) ls None (Exec l rest j))
       (put d (WTPtr taint_bot taint_bot) te) : pexprL) {{ Φ }}) -∗
  WP (PRun (mkFrame f e ls None (Exec l (Let d k (Alloc al) [v] :: rest) j)) te : pexprL) {{ Φ }}.
Proof.
  intros Hv Ht Hb Hi Hs0.
  destruct (Z.le_gt_cases size max_allocation_size) as [Hs | Hs].
  - apply wp_palloc.
    + cbn; lia.
    + cbn; apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia.
    + intros m pm paux fuel. unfold pstep.
      change (tstep pol ge _ _) with (let_tstep pol ge e (mkPState te [] pm paux) d k (Alloc al) [v]).
      assert (Hz : is_zero_idiom (Alloc al) k [v] = false) by (unfold is_zero_idiom; apply andb_false_r).
      unfold let_tstep; rewrite Hz; cbn [ps_tenv ps_callers ps_mem ps_aux].
      rewrite Hv Ht Hb Hi (proj2 (Z.ltb_ge _ _) Hs).
      rewrite (rule_alloc ge f e ls l d k al [v] rest j [] m fuel size);
        [reflexivity | cbn; rewrite Hv; reflexivity | exact Hs].
  - assert (Hpst : forall m pm paux fuel,
              pstep pol ge
                (mkConfig (mkFrame f e ls None (Exec l (Let d k (Alloc al) [v] :: rest) j)) [] m fuel)
                (mkPState te [] pm paux) = PDone (Trap TooBig) []).
    { intros m pm paux fuel. unfold pstep.
      change (tstep pol ge _ _) with (let_tstep pol ge e (mkPState te [] pm paux) d k (Alloc al) [v]).
      assert (Hz : is_zero_idiom (Alloc al) k [v] = false) by (unfold is_zero_idiom; apply andb_false_r).
      unfold let_tstep; rewrite Hz; cbn [ps_tenv ps_callers ps_mem ps_aux].
      rewrite Hv Ht Hb Hi (proj2 (Z.ltb_lt _ _) Hs).
      rewrite (rule_alloc_too_big ge f e ls l d k al [v] rest j [] m fuel size);
        [reflexivity | cbn; rewrite Hv; reflexivity | exact Hs]. }
    iIntros "HK". iApply (wp_lift_prun with "HK").
    + iIntros (σ) "_ _". iPureIntro. unfold pfails; rewrite Hpst; cbn; unfold refusal; tauto.
    + iIntros (σ) "_ _". iNext. iIntros (e2 σ2 Hm). exfalso.
      destruct Hm as [(c' & ps' & pcs' & E & _) | [(q & kk & base & s' & E & _) | (o & ots & m' & E & Hr & _)]];
        rewrite Hpst in E; try discriminate E.
      injection E as <- _; exact Hr.
Qed.

(** Freeing a null pointer with untainted branch and capability-index bits
    is a safe no-op that leaves both heaps unchanged. *)
Lemma wp_pfree_null fnm f e te ls l v rest j ta tc Φ :
  is_free_name fnm = true ->
  frees_heap (ge_free ge) ->
  find_fn ge fnm = None ->
  lookup fnm (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr null) ->
  arg_t te (Arg P v) = Some (WTPtr ta tc) ->
  t_branch ta = false ->
  t_branch tc = false ->
  t_index tc = false ->
  ▷ WP (PRun (mkFrame f e ls None (Exec l rest j)) te : pexprL) {{ Φ }} -∗
  WP (PRun (mkFrame f e ls None (Exec l (Call CVoid (Global fnm) [Arg P v] :: rest) j)) te : pexprL) {{ Φ }}.
Proof.
  intros Hfnm [Hnull _] Hfn Hdata Hx Ht Hba Hbc Hic.
  apply (wp_ppure_next _ _ _ _ []).
  intros m pm paux fuel. unfold pstep.
  cbn [tstep c_frame fr_doomed fr_at inst_tstep ps_tenv ps_callers ps_mem ps_aux fr_env map_option].
  rewrite Ht; cbn [map_option]; rewrite Hfn Hdata Hfnm Hba Hbc Hic; cbn [orb].
  rewrite (rule_free_sym _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hfnm Hfn Hdata Hx (Hnull m)).
  reflexivity.
Qed.

(** Loading an 8-byte integer from a uniform poison cell borrows the cell's
    value and poison shares and binds the loaded word together with the
    cell's taint. *)
Lemma wp_praw_load f e te ls l d k off av rest j p b reg o v pb ta tc dq pdq Φ :
  op_arg_classes (RawLoad LdL off) k = Some [A] ->
  value_x ge e A av = Some (WPtr p) ->
  value_t te A av = Some (WTPtr ta tc) ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  raw_address (ptr_addr p) off = b + o ->
  t_index ta = false ->
  pol_check_branches pol && (t_branch ta || t_branch tc || t_index tc) = false ->
  pb_no_load pb = false ->
  ptsq dq ([(PLive b, VLive reg)] ++ cell b o v) -∗
  pptsq pdq (pcell_ps b o pb) -∗
  ▷ (ptsq dq ([(PLive b, VLive reg)] ++ cell b o v) -∗
     pptsq pdq (pcell_ps b o pb) -∗
     WP (PRun (mkFrame f (put d (WInt (v mod 2 ^ 64)) e) ls None (Exec l rest j))
       (put d (WTInt (pb_taint pb)) te) : pexprL) {{ Φ }}) -∗
  WP (PRun (mkFrame f e ls None (Exec l (Let d k (RawLoad LdL off) [av] :: rest) j)) te : pexprL) {{ Φ }}.
Proof.
  intros Hc Ha Hta Hp Hoff Hi Hb Hload.
  apply (wp_pread dq pdq _ _ _ _ _ _ []).
  intros m pm paux fuel (Hf & _) Hpf.
  apply all_agree_app in Hf as [[Hlv _] Hcl]; cbn [agree_piece fst snd] in Hlv.
  destruct (pcell_ps_facts m pm paux b reg o pb Hlv Hpf) as (Ho & He & Hnl & _ & Htl).
  assert (Es : Semantics.step ge
    (mkConfig (mkFrame f e ls None (Exec l (Let d k (RawLoad LdL off) [av] :: rest) j)) [] m fuel) =
    Next (mkConfig (mkFrame f (put d (WInt (v mod 2 ^ 64)) e) ls None (Exec l rest j)) [] m fuel)).
  { apply rule_let with (classes := [A]) (xs := [WPtr p]); [reflexivity | exact Hc | cbn; rewrite Ha; reflexivity |].
    rewrite (op_raw_load m k p off).
    - rewrite Hoff (cell_load m b reg o v (b + o) Hlv Hcl eq_refl). reflexivity.
    - rewrite Hoff. apply (access_read _ b reg); [exact Hp | exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r]. }
  unfold pstep.
  change (tstep pol ge _ _) with (let_tstep pol ge e (mkPState te [] pm paux) d k (RawLoad LdL off) [av]).
  assert (Hz : is_zero_idiom (RawLoad LdL off) k [av] = false) by (unfold is_zero_idiom; apply andb_false_r).
  unfold let_tstep; rewrite Hz; cbn [ps_tenv ps_callers ps_mem ps_aux load_type_bytes].
  rewrite Ha Hta Hi Hb Hoff Hnl Hload Htl Es. reflexivity.
Qed.

(** Storing an 8-byte integer updates all eight bytes of the cell in both
    heaps while preserving every unowned byte and capability taint slot. *)
Lemma wp_praw_store f e te ls l off v a rest j p b reg o w w' pb tv ta tc Φ :
  value_x ge e L v = Some (WInt w') ->
  value_x ge e A a = Some (WPtr p) ->
  value_t te L v = Some (WTInt tv) ->
  value_t te A a = Some (WTPtr ta tc) ->
  ptr_cap p = Obj b ->
  raw_address (ptr_addr p) off = b + o ->
  t_index ta = false ->
  pol_check_branches pol && (t_branch ta || t_branch tc || t_index tc) = false ->
  pb_no_store pb = false ->
  pts ([(PLive b, VLive reg)] ++ cell b o w) -∗
  ppts (pcell_ps b o pb) -∗
  ▷ (pts ([(PLive b, VLive reg)] ++ cell b o w') -∗
     ppts (pcell_ps b o (note_store_byte tv pb)) -∗
     WP (PRun (mkFrame f e ls None (Exec l rest j)) te : pexprL) {{ Φ }}) -∗
  WP (PRun (mkFrame f e ls None (Exec l (RawStore Wl off v a :: rest) j)) te : pexprL) {{ Φ }}.
Proof.
  intros Hv Ha Htv Hta Hp Hoff Hi Hb Hstore.
  apply (wp_pwrite
    ([(PLive b, VLive reg)] ++ cell b o w)
    ([(PLive b, VLive reg)] ++ cell b o w')
    (pcell_ps b o pb)
    (pcell_ps b o (note_store_byte tv pb))
    _ _ _ _ []
    (fun m => store_bytes m (b + o) 8 w')
    (fun pm => mem_store_taint pm (b + o) 8 tv)
    (fun paux => paux));
    [reflexivity | reflexivity |].
  intros m pm paux fuel (Hf & Hd & _) Hpf.
  apply all_agree_app in Hf as [[Hlv _] Hcl]; cbn [agree_piece fst snd] in Hlv.
  destruct (pcell_ps_facts m pm paux b reg o pb Hlv Hpf) as (Ho & He & _ & Hns & _).
  destruct (cell_store_ok m b reg o (b + o) w' Hd Hlv Ho He eq_refl) as [Hcs Hfr].
  destruct (pcell_ps_store_ok m (store_bytes m (b + o) 8 w') pm paux b reg o pb tv eq_refl Hd Hlv Hpf)
    as [Hpcs Hpfr].
  assert (Es : Semantics.step ge
    (mkConfig (mkFrame f e ls None (Exec l (RawStore Wl off v a :: rest) j)) [] m fuel) =
    Next (mkConfig (mkFrame f e ls None (Exec l rest j)) [] (store_bytes m (b + o) 8 w') fuel)).
  { apply rule_raw_store with (vk := L) (x := WInt w') (p := p); [reflexivity | exact Hv | exact Ha |].
    rewrite Hoff. apply store_res_long. rewrite Hp.
    apply (access_obj _ _ reg); [exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r]. }
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - unfold pstep.
    change (tstep pol ge _ _) with
      (inst_tstep pol ge (mkFrame f e ls None (Exec l (RawStore Wl off v a :: rest) j))
        (mkPState te [] pm paux) (RawStore Wl off v a)).
    cbn [inst_tstep fr_env ps_tenv width_value_class ps_mem ps_aux ps_callers width_bytes].
    rewrite Ha Hta Hi Hb Hoff Hns Hstore Htv Es. reflexivity.
  - apply store_bytes_kept. exact (in_object_live _ _ _ (b + o) Hlv ltac:(lia) ltac:(lia)).
  - exact Hd.
  - apply all_agree_app; split; [|exact Hcs].
    cbn [all_agree agree_piece fst snd]; split; [apply (live_at_regions m); [reflexivity | exact Hlv] | exact I].
  - eapply frame_ok_mono; [|exact Hfr]. intros key Hin; rewrite fmap_app; apply elem_of_app; by right.
  - exact Hpcs.
  - exact Hpfr.
Qed.

(** Loading a pointer from an aligned 8-byte slot reads its address taint
    from the byte poison map and its capability taint from the [[aux]]
    poison map, provided the target capability has not been freed. *)
Lemma wp_praw_load_pointer f e te ls l d off av rest j p b reg o x reg' pb txc ta tc dq pdq cdq Φ :
  value_x ge e A av = Some (WPtr p) ->
  value_t te A av = Some (WTPtr ta tc) ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  raw_address (ptr_addr p) off = b + o ->
  (b + o) mod 8 = 0 ->
  0 <= ptr_addr x < 2 ^ 64 ->
  t_index ta || t_index tc = false ->
  pol_check_branches pol && (t_branch ta || t_branch tc) = false ->
  pb_no_load pb = false ->
  ptsq dq ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x)) -∗
  pptsq pdq ((PPAux b o, VPAux txc) :: pcell_ps b o pb) -∗
  ptsq cdq (cap_live_ps (ptr_cap x) reg') -∗
  ▷ (ptsq dq ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x)) -∗
     pptsq pdq ((PPAux b o, VPAux txc) :: pcell_ps b o pb) -∗
     ptsq cdq (cap_live_ps (ptr_cap x) reg') -∗
     WP (PRun (mkFrame f (put d (WPtr x) e) ls None (Exec l rest j))
       (put d (WTPtr (pb_taint pb) txc) te) : pexprL) {{ Φ }}) -∗
  WP (PRun (mkFrame f e ls None
       (Exec l (Let d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) [av] :: rest) j))
       te : pexprL) {{ Φ }}.
Proof.
  intros Ha Hta Hp Hoff Hal Hrange Hi Hb Hload.
  iIntros "Hv Hp Hcap HK". iCombine "Hv Hp Hcap HK" as "H".
  iApply (wp_lift_prun with "H").
  - iIntros (σ) "Hσ [Hv [Hp [Hcap _]]]".
    iDestruct (poison_ptsq_facts with "Hσ Hv") as %(Hf & _).
    iDestruct (poison_pptsq_facts with "Hσ Hp") as %Hpf.
    iDestruct (poison_ptsq_facts with "Hσ Hcap") as %(Hcf & _).
    iPureIntro.
    apply all_agree_app in Hf as [[Hlv _] [Hax Hcl]]; cbn [agree_piece fst snd] in Hlv.
    cbn [all_p_agree agree_ppiece fst snd] in Hpf; destruct Hpf as [[_ Hpaux] Hpb_all].
    destruct (Hpaux reg (proj1 Hlv) (proj2 Hlv)) as (_ & _ & Epaux).
    destruct (pcell_ps_facts _ _ _ b reg o pb Hlv Hpb_all) as (Ho & He & Hnl & _ & Htl).
    pose proof (cap_live_ps_not_freed _ _ _ Hcf) as Hkept.
    assert (Es : Semantics.step ge
      (mkConfig (mkFrame f e ls None
        (Exec l (Let d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) [av] :: rest) j))
        [] (pl_mem σ) (pl_fuel σ)) =
      Next (mkConfig (mkFrame f (put d (WPtr x) e) ls None (Exec l rest j)) [] (pl_mem σ) (pl_fuel σ))).
    { apply rule_let with (classes := [A]) (xs := [WPtr p]);
        [reflexivity | reflexivity | cbn; rewrite Ha; reflexivity |].
      apply op_raw_load_pointer.
      - rewrite Hoff. apply (access_read _ b reg); [exact Hp | exact (proj1 Hlv) | lia | lia | exact Hal].
      - rewrite pointer_load_plain Hoff (cell_load _ b reg o (ptr_addr x) (b + o) Hlv Hcl eq_refl).
        rewrite Z.mod_small; [|exact Hrange]. unfold aux_at.
        rewrite (aux_holds_kept _ _ _ (aux_piece_holds _ _ _ _ _ Hlv Hax) Hkept).
        destruct x; reflexivity. }
    unfold pfails, pstep.
    change (tstep pol ge _ _) with
      (let_tstep pol ge e (mkPState te [] (pl_pm σ) (pl_paux σ))
        d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) [av]).
    unfold let_tstep; cbn [is_zero_idiom andb ps_tenv ps_callers ps_mem ps_aux].
    rewrite Ha Hta Hi Hb Hoff Hnl Hload Htl Epaux Es. auto.
  - iIntros ([m pm paux s fuel]) "Hσ [Hv [Hp [Hcap HK]]]".
    iDestruct (poison_ptsq_facts with "Hσ Hv") as %(Hf & _).
    iDestruct (poison_pptsq_facts with "Hσ Hp") as %Hpf.
    iDestruct (poison_ptsq_facts with "Hσ Hcap") as %(Hcf & _).
    cbn [pl_mem pl_pm pl_paux pl_fuel] in *.
    apply all_agree_app in Hf as [[Hlv _] [Hax Hcl]]; cbn [agree_piece fst snd] in Hlv.
    cbn [all_p_agree agree_ppiece fst snd] in Hpf; destruct Hpf as [[_ Hpaux] Hpb_all].
    destruct (Hpaux reg (proj1 Hlv) (proj2 Hlv)) as (_ & _ & Epaux).
    destruct (pcell_ps_facts _ _ _ b reg o pb Hlv Hpb_all) as (Ho & He & Hnl & _ & Htl).
    pose proof (cap_live_ps_not_freed _ _ _ Hcf) as Hkept.
    assert (Ep : pstep pol ge
      (mkConfig (mkFrame f e ls None
        (Exec l (Let d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) [av] :: rest) j)) [] m fuel)
      (mkPState te [] pm paux) =
      PNext (mkConfig (mkFrame f (put d (WPtr x) e) ls None (Exec l rest j)) [] m fuel)
            (mkPState (put d (WTPtr (pb_taint pb) txc) te) [] pm paux)).
    { assert (Es : Semantics.step ge
        (mkConfig (mkFrame f e ls None
          (Exec l (Let d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) [av] :: rest) j))
          [] m fuel) =
        Next (mkConfig (mkFrame f (put d (WPtr x) e) ls None (Exec l rest j)) [] m fuel)).
      { apply rule_let with (classes := [A]) (xs := [WPtr p]);
          [reflexivity | reflexivity | cbn; rewrite Ha; reflexivity |].
        apply op_raw_load_pointer.
        - rewrite Hoff. apply (access_read _ b reg); [exact Hp | exact (proj1 Hlv) | lia | lia | exact Hal].
        - rewrite pointer_load_plain Hoff (cell_load _ b reg o (ptr_addr x) (b + o) Hlv Hcl eq_refl).
          rewrite Z.mod_small; [|exact Hrange]. unfold aux_at.
          rewrite (aux_holds_kept _ _ _ (aux_piece_holds _ _ _ _ _ Hlv Hax) Hkept).
          destruct x; reflexivity. }
      unfold pstep.
      change (tstep pol ge _ _) with
        (let_tstep pol ge e (mkPState te [] pm paux)
          d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) [av]).
      unfold let_tstep; cbn [is_zero_idiom andb ps_tenv ps_callers ps_mem ps_aux].
      rewrite Ha Hta Hi Hb Hoff Hnl Hload Htl Epaux Es; reflexivity. }
    iNext. iIntros (e2 σ2 Hm).
    destruct Hm as [(c' & ps' & pcs & E' & Hcs & Htcs & -> & ->) |
      [(q & k & base & s' & E' & _) | (o' & ots & m' & E' & _)]];
      cbn [pl_mem pl_pm pl_paux pl_rt pl_fuel] in E'; rewrite Ep in E'; try discriminate E'.
    injection E' as <- <-.
    cbn [c_callers ps_callers] in Hcs, Htcs; assert (pcs = []) as -> by exact (pcs_sync_inj pcs [] Hcs Htcs).
    cbn [c_frame c_mem c_fuel ps_tenv ps_mem ps_aux pstack_expr].
    iModIntro. iFrame "Hσ". iApply ("HK" with "Hv Hp Hcap").
Qed.

(** Storing a pointer into an aligned 8-byte slot writes both its address
    taint into the eight byte entries and its capability taint into the
    [[aux]] slot while preserving every unowned piece. *)
Lemma wp_praw_store_pointer f e te ls l off v a rest j xp p b reg o x pb txc tva tvc ta tc Φ :
  value_x ge e P v = Some (WPtr xp) ->
  value_x ge e A a = Some (WPtr p) ->
  value_t te P v = Some (WTPtr tva tvc) ->
  value_t te A a = Some (WTPtr ta tc) ->
  ptr_cap p = Obj b ->
  raw_address (ptr_addr p) off = b + o ->
  (b + o) mod 8 = 0 ->
  t_index ta || t_index tc = false ->
  pol_check_branches pol && (t_branch ta || t_branch tc) = false ->
  pb_no_store pb = false ->
  pts ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x)) -∗
  ppts ((PPAux b o, VPAux txc) :: pcell_ps b o pb) -∗
  ▷ (pts ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap xp)) :: cell b o (ptr_addr xp)) -∗
     ppts ((PPAux b o, VPAux tvc) :: pcell_ps b o (note_store_byte tva pb)) -∗
     WP (PRun (mkFrame f e ls None (Exec l rest j)) te : pexprL) {{ Φ }}) -∗
  WP (PRun (mkFrame f e ls None
       (Exec l (RawStorePointer off v a [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]
                :: rest) j)) te : pexprL) {{ Φ }}.
Proof.
  intros Hv Ha Htv Hta Hp Hoff Hal Hi Hb Hstore.
  apply (wp_pwrite
    ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x))
    ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap xp)) :: cell b o (ptr_addr xp))
    ((PPAux b o, VPAux txc) :: pcell_ps b o pb)
    ((PPAux b o, VPAux tvc) :: pcell_ps b o (note_store_byte tva pb))
    _ _ _ _ []
    (fun m => store_bytes (store_aux m (b + o) (ptr_cap xp)) (b + o) 8 (ptr_addr xp))
    (fun pm => mem_store_taint pm (b + o) 8 tva)
    (fun paux b' => if b' =? b + o then tvc else paux b'));
    [reflexivity | reflexivity |].
  intros m pm paux fuel (Hf & Hd & _) Hpf.
  apply all_agree_app in Hf as [[Hlv _] [_ Hcl]]; cbn [agree_piece fst snd] in Hlv.
  cbn [all_p_agree fst snd] in Hpf; destruct Hpf as [_ Hpb_all].
  destruct (pcell_ps_facts m pm paux b reg o pb Hlv Hpb_all) as (Ho & He & _ & Hns & _).
  destruct (pcell_store_ok m b reg o (b + o) (ptr_cap xp) (ptr_addr xp) Hd Hlv Ho He eq_refl) as [Hcs Hfr].
  destruct (ppcell_ps_store_ok m
    (store_bytes (store_aux m (b + o) (ptr_cap xp)) (b + o) 8 (ptr_addr xp))
    pm paux b reg o pb tva tvc eq_refl Hd Hlv Hpb_all) as [Hpcs Hpfr].
  assert (Hin := in_object_live _ _ _ (b + o) Hlv ltac:(lia) ltac:(lia)).
  assert (Es : Semantics.step ge
    (mkConfig (mkFrame f e ls None
      (Exec l (RawStorePointer off v a [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]
               :: rest) j)) [] m fuel) =
    Next (mkConfig (mkFrame f e ls None (Exec l rest j)) []
      (store_bytes (store_aux m (b + o) (ptr_cap xp)) (b + o) 8 (ptr_addr xp)) fuel)).
  { apply rule_raw_store_pointer with (xp := xp) (p := p); [exact Hv | exact Ha | |].
    - rewrite Hoff Hp. apply (access_obj _ _ reg); [exact (proj1 Hlv) | lia | lia | exact Hal].
    - rewrite Hoff. apply pointer_store_plain. }
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - unfold pstep.
    change (tstep pol ge _ _) with
      (inst_tstep pol ge (mkFrame f e ls None
        (Exec l (RawStorePointer off v a [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]
                 :: rest) j)) (mkPState te [] pm paux)
        (RawStorePointer off v a [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])).
    cbn [inst_tstep fr_env ps_tenv ps_mem ps_aux ps_callers effects_eqb effect_eqb andb orb].
    rewrite Ha Hta Htv Hi Hb Hoff Hns Hstore Es. reflexivity.
  - exact (pointer_store_effects_kept _ _ _ _ _ Hin (pointer_store_plain m (b + o) xp)).
  - exact Hd.
  - apply all_agree_app; split; [|exact Hcs].
    cbn [all_agree agree_piece fst snd]; split; [apply (live_at_regions m); [reflexivity | exact Hlv] | exact I].
  - eapply frame_ok_mono; [|exact Hfr]. intros key Hin'; rewrite fmap_app; apply elem_of_app; by right.
  - exact Hpcs.
  - exact Hpfr.
Qed.

End wp.
End logic.

(** ## Adequacy of heap proofs

    Once a function's body has been verified against owned bytes and poison
    records, callers want guarantees about real machine runs rather than
    logical assertions. The theorems below prove that every reachable
    machine state avoids panics and poison faults, and that two secret-related
    runs emit identical leakage traces under a deterministic allocator. *)

(** A caller starts with distinct value and poison records that match memory,
    then proves the entry frame never gets stuck. *)
Theorem poison_pieces_adequate Σ
    {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    {HpoisonP : gen_heapGpreS ppiece ppval Σ}
    pol ge fr te m pm paux s fuel ps pps (φ : outcome * list word_taint -> Prop) :
  R.ready s m -> live_disjoint m -> all_agree m ps -> all_p_agree m pm paux pps ->
  NoDup ps.*1 -> NoDup pps.*1 ->
  (forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ)
      (HpoisonG : gen_heapGS ppiece ppval Σ),
    let _ : irisGS_gen HasNoLc (poison_lang pol ge) Σ := poison_irisGS pol ge in
    pts ps -∗ ppts pps -∗
      WP (PRun fr te : language.expr (poison_lang pol ge)) {{ v, ⌜φ v⌝ }}) ->
  @adequate (poison_lang pol ge) NotStuck (PRun fr te) (mkPLstate m pm paux s fuel)
    (fun v _ => φ v).
Proof.
  intros Hr Hd Ha Hpa Hn Hpn Hwp.
  apply (wp_adequacy_gen HasNoLc Σ (poison_lang pol ge) NotStuck _ _ φ).
  intros HinvG κs.
  iMod (gen_heap_init (list_to_map ps : gmap piece pval)) as (HheapG) "(Hh & Hps & _)".
  iMod (gen_heap_init (list_to_map pps : gmap ppiece ppval)) as (HpoisonG) "(Hph & Hpps & _)".
  iModIntro. iExists (fun σ _ => poison_heap_interp σ), (fun _ => True%I).
  iSplitL "Hh Hph".
  - iExists (list_to_map ps), (list_to_map pps). iFrame. iPureIntro.
    split; [|split; [|split; assumption]].
    + intros l v Hl. exact (all_agree_elem _ _ _ _ Ha (elem_of_list_to_map_2 _ _ _ Hl)).
    + intros l v Hl. exact (all_p_agree_elem _ _ _ _ _ _ Hpa (elem_of_list_to_map_2 _ _ _ Hl)).
  - iApply (Hwp HinvG HheapG HpoisonG with "[Hps] [Hpps]").
    + rewrite /pts -(big_sepM_list_to_map (fun l v => pointsto l (DfracOwn 1) v));
        [iExact "Hps"|exact Hn].
    + rewrite /ppts -(big_sepM_list_to_map (fun l v => pointsto l (DfracOwn 1) v));
        [iExact "Hpps"|exact Hpn].
Qed.

(** A safe poisoned execution avoids faults in every machine-reachable
    state, also with collector steps, and in every finite driver run. *)
Definition poison_safe pol ge fr te m pm paux s fuel : Prop :=
  (forall c ps s',
    pmreachable pol ge (mkConfig fr [] m fuel, mkPState te [] pm paux, s) (c, ps, s') ->
    ~ pfails pol ge c ps) /\
  (forall st, RM.mreachable ge (mkConfig fr [] m fuel, s) st -> ~ fails ge (fst st)) /\
  (forall steps,
    match PD.pdriver_run pol ge steps (mkConfig fr [] m fuel) (mkPState te [] pm paux) s with
    | PD.PDriverNext _ _ _ => True
    | PD.PDriverDone o _ => ~ failure o
    | PD.PDriverTrap _ | PD.PDriverBad _ => False
    end).

(** Execution adequacy implies that the program avoids poison faults and
    memory panics across all reachable machine states and finite driver runs. *)
Lemma wp_poison_safe pol ge fr te m pm paux s fuel φ :
  @adequate (poison_lang pol ge) NotStuck (PRun fr te) (mkPLstate m pm paux s fuel) φ ->
  poison_safe pol ge fr te m pm paux s fuel.
Proof. exact (adequate_poison_all pol ge fr te m pm paux s fuel φ). Qed.

(** One safe heap proof suffices for both runs: the second may contain
    different secrets wherever [ct_rel] permits them. The conclusion is
    equality of abstract IR leakage traces, not native timing adequacy. *)
Theorem wp_ct_driver pol ge fr1 fr2 te m1 m2 pm paux s fuel :
  pol_check_branches pol = true -> ge_free ge = free_res ->
  R.ready s m1 -> R.ready s m2 ->
  ct_rel (mkConfig fr1 [] m1 fuel) (mkConfig fr2 [] m2 fuel) (mkPState te [] pm paux) ->
  poison_safe pol ge fr1 te m1 pm paux s fuel ->
  forall steps, exists tr,
    PD.pdriver_trace pol ge steps (mkConfig fr1 [] m1 fuel) (mkPState te [] pm paux) s = Some tr /\
    PD.pdriver_trace pol ge steps (mkConfig fr2 [] m2 fuel) (mkPState te [] pm paux) s = Some tr.
Proof.
  intros Hcb Hfree Hr1 Hr2 Hrel (_ & _ & Hsafe) steps.
  destruct (PD.pdriver_run_has_trace pol ge steps (mkConfig fr1 [] m1 fuel)
    (mkPState te [] pm paux) s ltac:(specialize (Hsafe steps);
    destruct (PD.pdriver_run pol ge steps (mkConfig fr1 [] m1 fuel)
      (mkPState te [] pm paux) s); cbn in *; tauto)) as [tr Htr].
  exists tr. split; [exact Htr|].
  exact (proj1 (PD.pdriver_ct_sound pol ge steps (mkConfig fr1 [] m1 fuel)
    (mkConfig fr2 [] m2 fuel) (mkPState te [] pm paux) s tr
    Hcb Hfree Hr1 Hr2 Hrel (Hsafe steps) Htr)).
Qed.

(** Two runs that differ only in secret object bytes share allocator
    readiness, emit equal traces, and return related results. *)
Theorem wp_ct_driver_ret pol ge fr1 fr2 te m1 m2 pm paux s fuel :
  pol_check_branches pol = true -> ge_free ge = free_res ->
  R.ready s m1 ->
  (forall a, ~ in_object m1 a -> m_bytes m2 a = m_bytes m1 a /\ m_aux m2 a = m_aux m1 a) ->
  ct_rel (mkConfig fr1 [] m1 fuel) (mkConfig fr2 [] m2 fuel) (mkPState te [] pm paux) ->
  poison_safe pol ge fr1 te m1 pm paux s fuel ->
  forall steps, exists tr,
    PD.pdriver_trace pol ge steps (mkConfig fr1 [] m1 fuel) (mkPState te [] pm paux) s = Some tr /\
    PD.pdriver_trace pol ge steps (mkConfig fr2 [] m2 fuel) (mkPState te [] pm paux) s = Some tr /\
    match PD.pdriver_run pol ge steps (mkConfig fr1 [] m1 fuel) (mkPState te [] pm paux) s,
          PD.pdriver_run pol ge steps (mkConfig fr2 [] m2 fuel) (mkPState te [] pm paux) s with
    | PD.PDriverDone o1 ots1, PD.PDriverDone o2 ots2 =>
        ots1 = ots2 /\ ~ failure o2 /\
        (forall w1 wt, o1 = Ret w1 -> ots1 = [wt] -> exists w2, o2 = Ret w2 /\ word_rel wt w1 w2)
    | PD.PDriverNext c1' ps1' rt1', PD.PDriverNext c2' ps2' rt2' =>
        ps1' = ps2' /\ rt1' = rt2' /\ ct_rel c1' c2' ps1'
    | _, _ => False
    end.
Proof.
  intros Hcb Hfree Hr1 Hout Hrel (_ & _ & Hsafe) steps.
  assert (Hreg : m_regions m1 = m_regions m2)
    by (destruct Hrel as (_ & _ & _ & _ & _ & _ & Hreg & _); exact Hreg).
  pose proof (R.ready_kept _ _ _ Hr1 (ct_kept_ready m1 m2 Hreg Hout)) as Hr2.
  destruct (PD.pdriver_run_has_trace pol ge steps (mkConfig fr1 [] m1 fuel)
    (mkPState te [] pm paux) s ltac:(specialize (Hsafe steps);
    destruct (PD.pdriver_run pol ge steps (mkConfig fr1 [] m1 fuel)
      (mkPState te [] pm paux) s); cbn in *; tauto)) as [tr Htr].
  exists tr. split; [exact Htr|].
  exact (PD.pdriver_ct_sound pol ge steps (mkConfig fr1 [] m1 fuel)
    (mkConfig fr2 [] m2 fuel) (mkPState te [] pm paux) s tr
    Hcb Hfree Hr1 Hr2 Hrel (Hsafe steps) Htr).
Qed.

(** A closed module never panics when its entry has a two-heap proof for
    every admitted argument list. Its initial poison maps and taint
    environment can depend on that list. *)
Theorem poison_pieces_never_panics Σ
    {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    {HpoisonP : gen_heapGpreS ppiece ppval Σ}
    pol md entry (input : list word -> Prop) globals m f ps :
  initial_memory md = Some (globals, m) ->
  find_fn (P.program_genv md globals) entry = Some (Defined f) ->
  live_disjoint m -> all_agree m ps -> NoDup ps.*1 ->
  (forall xs, input xs -> exists fr te pm paux pps,
    call_frame f xs = Some fr /\ all_p_agree m pm paux pps /\ NoDup pps.*1 /\
    forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ)
      (HpoisonG : gen_heapGS ppiece ppval Σ),
      let _ : irisGS_gen HasNoLc (poison_lang pol (P.program_genv md globals)) Σ :=
        poison_irisGS pol (P.program_genv md globals) in
      pts ps -∗ ppts pps -∗
        WP (PRun fr te : language.expr (poison_lang pol (P.program_genv md globals))) {{ _, True }}) ->
  P.never_panics md entry input.
Proof.
  intros Hm Hf Hd Ha Hn Hwp. exists globals, m, f.
  split; [exact Hm|]. split; [exact Hf|]. intros xs Hxs.
  destruct (Hwp xs Hxs) as (fr & te & pm & paux & pps & Hfr & Hpa & Hpn & Hw).
  exists fr. split; [exact Hfr|]. intros Hr fuel st Hreach.
  pose proof (poison_pieces_adequate Σ pol (P.program_genv md globals)
    fr te m pm paux R.start fuel ps pps (fun _ => True) Hr Hd Ha Hpa Hn Hpn Hw) as Had.
  exact (proj1 (proj2 (wp_poison_safe _ _ _ _ _ _ _ _ _ _ Had)) st Hreach).
Qed.

End PoisonLogic.
