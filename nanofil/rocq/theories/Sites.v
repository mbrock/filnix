(** Where a name is defined, and what `definitions_dominate/3` says of
    its uses (docs/formal.md, Campaign 3; docs/rocq.md, "Where a name is
    defined").

    ir.pl reads a function's definitions twice: as the list of
    definitions `single_definitions/3` filters (Validate.v's
    `all_defs`), and as the sites `block_sites//1` records for strict
    SSA (`temp_sites`). The run-level invariant needs both at once:
    the relation a single definition states holds wherever its site
    dominates the running point. This file joins them through one list
    of every definition with its site, `def_positions`, and proves:

    | Lemma | Says |
    |---|---|
    | `all_defs_positions` | `all_defs` is `def_positions` without the sites |
    | `temp_sites_sound` | every site `temp_sites` records for a name is a position defining it |
    | `once_position` | a name with a single definition has exactly one position, and it holds that definition |
    | `use_dominated` | in a valid function, a single-definition name an instruction of a reachable block uses is defined at a site that dominates the use |
    | `position_inst`, `inst_position`, `phi_position` | an instruction's or phi's position is its index in its block |
    | `no_use_redefined` | where a single definition's site dominates a point of a reachable block, no single-definition operand of it is defined at that point |

    ## Decisions

    | Decision | Why |
    |---|---|
    | positions are `site`s, the validator's own | `site_dominates/4` is then the order the invariant uses, with no second notion of position |
    | `def_positions` is a new list, proved equal to `all_defs` without sites | Validate.v, the transcription the gates compare, stays as it is |
    | a single definition is unique by counting | `single_definitions/3` keeps a name defined once in the list; two positions would be two entries | *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Cfg Validate Dominance.
Import ListNotations.
Local Open Scope Z_scope.

(** ## Every definition with its site *)

(** The definitions of instructions from index j on, each at its index. *)
Fixpoint inst_positions (l : name) (j : Z) (is : list inst) : list (name * site * def) :=
  match is with
  | [] => []
  | i :: rest =>
      map (fun dk => (fst dk, SAt l j, DInst i)) (inst_temp_defs i) ++ inst_positions l (j + 1) rest
  end.

(** A block's definitions: its phis at -1, then its instructions. *)
Definition block_positions (b : block) : list (name * site * def) :=
  map (fun ph => match ph with Phi d _ _ => (d, SAt (b_label b) (-1), DPhi ph) end) (b_phis b) ++
  inst_positions (b_label b) 0 (b_insts b).

(** `def_positions f`: every definition of f with its site. *)
Definition def_positions (f : func) : list (name * site * def) :=
  map (fun p => (snd p, SParam, DParam)) (fn_params f) ++ flat_map block_positions (fn_blocks f).

Definition drop_site (t : name * site * def) : name * def := (fst (fst t), snd t).

Lemma inst_positions_defs : forall l j is,
  flat_map (fun i => map (fun dk => (fst dk, DInst i)) (inst_temp_defs i)) is
  = map drop_site (inst_positions l j is).
Proof.
  intros l j is. revert j. induction is as [|i rest IH]; intros j; [reflexivity|].
  simpl. rewrite map_app, (IH (j + 1)), map_map. reflexivity.
Qed.

(** `all_defs_positions`: `all_defs` is `def_positions` without sites. *)
Lemma all_defs_positions : forall f, all_defs f = map drop_site (def_positions f).
Proof.
  intros f. unfold all_defs, def_positions. rewrite map_app, map_map. f_equal.
  induction (fn_blocks f) as [|b bs IH]; [reflexivity|]. simpl. rewrite map_app, <- IH. f_equal.
  unfold block_positions. rewrite map_app, map_map, <- (inst_positions_defs (b_label b) 0). f_equal.
  apply map_ext. intros [d k pairs]. reflexivity.
Qed.

(** ## The sites `temp_sites` records *)

Definition sites_ok (f : func) (m : nmap (list site)) : Prop :=
  forall n ss s, nm_find n m = Some ss -> In s ss -> exists d, In (n, s, d) (def_positions f).

Definition add_site (m : nmap (list site)) (n : name) (s : site) : nmap (list site) :=
  nm_add n (s :: match nm_find n m with Some ss => ss | None => [] end) m.

Lemma add_site_ok : forall f m n s d, sites_ok f m -> In (n, s, d) (def_positions f) ->
  sites_ok f (add_site m n s).
Proof.
  intros f m n s d Hm Hd k ss s' E Hin. unfold add_site in E. rewrite nm_find_add in E.
  destruct (name_eqb k n) eqn:Ek.
  - apply name_eqb_true in Ek. subst k. injection E as <-. destruct Hin as [<- | Hin]; [eauto|].
    destruct (nm_find n m) as [ss0|] eqn:E0; [exact (Hm _ _ _ E0 Hin) | destruct Hin].
  - exact (Hm _ _ _ E Hin).
Qed.

Lemma fold_sites_ok : forall (A : Type) f (g : A -> name * site) xs m,
  sites_ok f m -> (forall x, In x xs -> exists d, In (fst (g x), snd (g x), d) (def_positions f)) ->
  sites_ok f (fold_left (fun m x => add_site m (fst (g x)) (snd (g x))) xs m).
Proof.
  intros A f g xs. induction xs as [|x xs IH]; intros m Hm Hx; [exact Hm|].
  simpl. apply IH; [|intros y Hy; apply Hx; right; exact Hy].
  destruct (Hx x (or_introl eq_refl)) as [d Hd]. exact (add_site_ok _ _ _ _ _ Hm Hd).
Qed.

Lemma inst_fold_sites_ok : forall f l is j m,
  sites_ok f m -> (forall t, In t (inst_positions l j is) -> In t (def_positions f)) ->
  sites_ok f (fst (fold_left (fun (acc : nmap (list site) * Z) ins =>
                                let (m, j) := acc in
                                (fold_left (fun m dk => add_site m (fst dk) (SAt l j))
                                           (inst_temp_defs ins) m, j + 1)) is (m, j))).
Proof.
  intros f l is. induction is as [|i rest IH]; intros j m Hm Hp; [exact Hm|].
  simpl. apply IH; [|intros t Ht; apply Hp; simpl; apply in_or_app; right; exact Ht].
  apply (fold_sites_ok _ f (fun dk => (fst dk, SAt l j))); [exact Hm|].
  intros dk Hdk. exists (DInst i). apply Hp. simpl. apply in_or_app. left.
  apply in_map_iff. exists dk. auto.
Qed.

(** `temp_sites_sound`: every site `block_sites//1` records for a name
    is a position that defines it. *)
Theorem temp_sites_sound : forall f n ss s,
  nm_find n (temp_sites f) = Some ss -> In s ss -> exists d, In (n, s, d) (def_positions f).
Proof.
  intros f. unfold temp_sites. fold add_site.
  assert (Hp : sites_ok f (fold_left (fun m p => add_site m (snd p) SParam) (fn_params f) nm_empty)).
  { apply (fold_sites_ok _ f (fun p => (snd p, SParam))).
    - intros n ss s E. rewrite nm_find_empty in E. discriminate E.
    - intros p Hp. exists DParam. unfold def_positions. apply in_or_app. left.
      apply in_map_iff. exists p. auto. }
  assert (Hb : forall bs m, sites_ok f m -> (forall b, In b bs -> In b (fn_blocks f)) ->
    sites_ok f (fold_left (fun m b =>
      let m1 := fold_left (fun m ph => match ph with Phi d _ _ => add_site m d (SAt (b_label b) (-1)) end)
                          (b_phis b) m in
      fst (fold_left (fun (acc : nmap (list site) * Z) ins =>
                        let (m, j) := acc in
                        (fold_left (fun m dk => add_site m (fst dk) (SAt (b_label b) j))
                                   (inst_temp_defs ins) m, j + 1)) (b_insts b) (m1, 0))) bs m)).
  { intros bs. induction bs as [|b bs IH]; intros m Hm Hin; [exact Hm|].
    simpl. apply IH; [|intros b' Hb'; apply Hin; right; exact Hb'].
    assert (Hpos : forall t, In t (block_positions b) -> In t (def_positions f)).
    { intros t Ht. unfold def_positions. apply in_or_app. right. apply in_flat_map.
      exists b. split; [apply Hin; left; reflexivity | exact Ht]. }
    apply inst_fold_sites_ok; [|intros t Ht; apply Hpos; unfold block_positions; apply in_or_app; right; exact Ht].
    assert (Hph : forall xs m0, sites_ok f m0 -> (forall ph, In ph xs -> In ph (b_phis b)) ->
      sites_ok f (fold_left (fun m ph => match ph with Phi d _ _ => add_site m d (SAt (b_label b) (-1)) end)
                            xs m0)).
    { intros xs. induction xs as [|[d k pairs] xs IHx]; intros m0 Hm0 Hx; [exact Hm0|].
      simpl. apply IHx; [|intros ph Hph; apply Hx; right; exact Hph].
      apply (add_site_ok _ _ _ _ (DPhi (Phi d k pairs)) Hm0). apply Hpos.
      unfold block_positions. apply in_or_app. left. apply in_map_iff.
      exists (Phi d k pairs). split; [reflexivity | apply Hx; left; reflexivity]. }
    exact (Hph _ _ Hm (fun ph H => H)). }
  intros n ss s E Hin. exact (Hb _ _ Hp (fun b H => H) n ss s E Hin).
Qed.

(** ## A single definition has one position *)

Lemma filter_map_length : forall (A B : Type) (p : B -> bool) (g : A -> B) l,
  length (filter p (map g l)) = length (filter (fun x => p (g x)) l).
Proof. intros A B p g l. induction l as [|x l IH]; simpl; [reflexivity|]. destruct (p (g x)); simpl; auto. Qed.

(** `once_position`: a name `single_definitions/3` keeps has exactly
    one position, and it holds the definition kept. *)
Theorem once_position : forall f n d,
  lookup n (single_definitions f) = Some d ->
  exists s, In (n, s, d) (def_positions f) /\
    forall s' d', In (n, s', d') (def_positions f) -> s' = s /\ d' = d.
Proof.
  intros f n d H. destruct (lookup_some_in _ _ _ _ H) as (n' & En & Hin).
  apply name_eqb_true in En. subst n'. unfold single_definitions in Hin.
  apply filter_In in Hin as [Hall Hcount]. apply Nat.eqb_eq in Hcount. simpl in Hcount.
  rewrite all_defs_positions in Hall, Hcount. rewrite filter_map_length in Hcount.
  apply in_map_iff in Hall as ([[n0 s] d0] & Ed & Hs).
  unfold drop_site in Ed. simpl in Ed. injection Ed as -> ->.
  set (L := filter (fun t => name_eqb n (fst (drop_site t))) (def_positions f)) in Hcount.
  assert (HL : forall s' d', In (n, s', d') (def_positions f) -> In (n, s', d') L).
  { intros s' d' Hs'. apply filter_In. split; [exact Hs'|]. apply name_eqb_true. reflexivity. }
  exists s. split; [exact Hs|]. intros s' d' Hs'.
  pose proof (HL _ _ Hs) as H1. pose proof (HL _ _ Hs') as H2.
  destruct L as [|t [|t' L']]; simpl in Hcount; try discriminate Hcount.
  destruct H1 as [E1 | []]. destruct H2 as [E2 | []]. rewrite E1 in E2. injection E2 as E3 E4. auto.
Qed.

(** ## A use is dominated by its single definition *)

(** `use_dominated`: in a function whose definitions dominate their
    uses, a single-definition name an instruction of a reachable block
    uses is defined at a site that dominates that instruction. *)
Theorem use_dominated : forall f doms b k ins o d,
  definitions_dominate f doms = true -> In b (fn_blocks f) -> is_reachable doms (b_label b) = true ->
  nth_error (b_insts b) k = Some ins -> In o (inst_uses ins) ->
  lookup o (single_definitions f) = Some d ->
  exists s, In (o, s, d) (def_positions f) /\ site_dominates doms (b_label b) (Z.of_nat k) s = true.
Proof.
  intros f doms b k ins o d H Hb Hr Hk Hu Ho. unfold definitions_dominate in H.
  rewrite forallb_forall in H. specialize (H b Hb). rewrite Hr in H. simpl in H.
  apply andb_true_iff in H as [Hi _].
  assert (Hdu : dominated_use (temp_sites f) doms (b_label b) (Z.of_nat k) o = true).
  { match type of Hi with ?F (b_insts b) 0 = true =>
      assert (G : forall is i k ins, F is i = true -> nth_error is k = Some ins -> In o (inst_uses ins) ->
                    dominated_use (temp_sites f) doms (b_label b) (i + Z.of_nat k) o = true)
    end.
    { intros is. induction is as [|ins0 rest IH]; intros i k0 ins1 Hf Hn Hin; [destruct k0; discriminate Hn|].
      cbn in Hf. apply andb_true_iff in Hf as [Hf1 Hf2]. destruct k0 as [|k0]; simpl in Hn.
      - injection Hn as <-. rewrite forallb_forall in Hf1. rewrite Z.add_0_r. exact (Hf1 _ Hin).
      - rewrite Nat2Z.inj_succ. replace (i + Z.succ (Z.of_nat k0)) with (i + 1 + Z.of_nat k0) by lia.
        exact (IH _ _ _ Hf2 Hn Hin). }
    exact (G _ _ _ _ Hi Hk Hu). }
  unfold dominated_use in Hdu. destruct (nm_find o (temp_sites f)) as [ss|] eqn:Es; [|discriminate Hdu].
  apply existsb_exists in Hdu as (s & Hin & Hd).
  destruct (temp_sites_sound _ _ _ _ Es Hin) as [d' Hd'].
  destruct (once_position _ _ _ Ho) as (s0 & Hs0 & Huniq).
  destruct (Huniq _ _ Hd') as [-> ->]. exists s0. auto.
Qed.

(** ## Positions and instructions *)

Lemma name_eqb_sym_d : forall a b, name_eqb a b = name_eqb b a.
Proof.
  intros a b. destruct (name_eqb a b) eqn:E; symmetry.
  - apply name_eqb_true in E. subst. apply name_eqb_true. reflexivity.
  - apply name_eqb_false. intros ->. apply name_eqb_false in E. exact (E eq_refl).
Qed.

Lemma inst_positions_in : forall l j is n s d,
  In (n, s, d) (inst_positions l j is) ->
  exists k i, nth_error is k = Some i /\ s = SAt l (j + Z.of_nat k) /\ d = DInst i /\
    In n (map fst (inst_temp_defs i)).
Proof.
  intros l j is. revert j. induction is as [|i rest IH]; intros j n s d H; [destruct H|].
  simpl in H. apply in_app_or in H as [H | H].
  - apply in_map_iff in H as (dk & E & Hdk). injection E as <- <- <-.
    exists O, i. split; [reflexivity|]. split; [replace (j + Z.of_nat 0) with j by lia; reflexivity|].
    split; [reflexivity|].
    apply in_map. exact Hdk.
  - destruct (IH _ _ _ _ H) as (k & i' & Hk & -> & -> & Hn).
    exists (S k), i'. split; [exact Hk|]. split; [replace (j + Z.of_nat (S k)) with (j + 1 + Z.of_nat k) by lia; reflexivity|].
    auto.
Qed.

Lemma inst_positions_nth : forall l j is k i dk,
  nth_error is k = Some i -> In dk (inst_temp_defs i) ->
  In (fst dk, SAt l (j + Z.of_nat k), DInst i) (inst_positions l j is).
Proof.
  intros l j is. revert j. induction is as [|i0 rest IH]; intros j k i dk Hk Hdk; [destruct k; discriminate Hk|].
  simpl. apply in_or_app. destruct k as [|k]; simpl in Hk.
  - injection Hk as <-. left. apply in_map_iff. exists dk. split; [|exact Hdk].
    replace (j + Z.of_nat 0) with j by lia. reflexivity.
  - right. replace (j + Z.of_nat (S k)) with (j + 1 + Z.of_nat k) by lia. exact (IH _ _ _ _ Hk Hdk).
Qed.

(** `position_inst`: an instruction's position is its index in its
    block, and it defines the name. *)
Lemma position_inst : forall f n d j i,
  In (n, SAt d j, DInst i) (def_positions f) ->
  exists b k, In b (fn_blocks f) /\ b_label b = d /\ nth_error (b_insts b) k = Some i /\
    j = Z.of_nat k /\ In n (map fst (inst_temp_defs i)).
Proof.
  intros f n d j i H. unfold def_positions in H. apply in_app_or in H as [H | H].
  - apply in_map_iff in H as (p & E & _). discriminate E.
  - apply in_flat_map in H as (b & Hb & H). unfold block_positions in H.
    apply in_app_or in H as [H | H].
    + apply in_map_iff in H as ([d' k' pairs] & E & _). discriminate E.
    + destruct (inst_positions_in _ _ _ _ _ _ H) as (k & i' & Hk & Es & Ed & Hn).
      injection Es as Ed' Ej. injection Ed as <-. exists b, k. split; [exact Hb|].
      split; [exact (eq_sym Ed')|]. split; [exact Hk|]. split; [lia | exact Hn].
Qed.

(** `inst_position`: an instruction defines its names at its index. *)
Lemma inst_position : forall f b k i dk,
  In b (fn_blocks f) -> nth_error (b_insts b) k = Some i -> In dk (inst_temp_defs i) ->
  In (fst dk, SAt (b_label b) (Z.of_nat k), DInst i) (def_positions f).
Proof.
  intros f b k i dk Hb Hk Hdk. unfold def_positions. apply in_or_app. right.
  apply in_flat_map. exists b. split; [exact Hb|]. unfold block_positions. apply in_or_app. right.
  exact (inst_positions_nth _ 0 _ _ _ _ Hk Hdk).
Qed.

(** `phi_position`: a phi defines its name at -1 of its block. *)
Lemma phi_position : forall f b d k pairs,
  In b (fn_blocks f) -> In (Phi d k pairs) (b_phis b) ->
  In (d, SAt (b_label b) (-1), DPhi (Phi d k pairs)) (def_positions f).
Proof.
  intros f b d k pairs Hb Hp. unfold def_positions. apply in_or_app. right.
  apply in_flat_map. exists b. split; [exact Hb|]. unfold block_positions. apply in_or_app. left.
  apply in_map_iff. exists (Phi d k pairs). auto.
Qed.

(** ## A single definition's operands are not redefined under it *)

(** `site_strict`: a site that dominates another one, which dominates a
    point, is not that point. *)
Lemma site_strict : forall doms,
  (forall a b, dominates doms a b = true -> dominates doms b a = true -> a = b) ->
  forall d j l k s, site_dominates doms d j s = true -> site_dominates doms l k (SAt d j) = true ->
  s <> SAt l k.
Proof.
  intros doms Hanti d j l k s H1 H2 ->. unfold site_dominates in H1, H2.
  rewrite (name_eqb_sym_d l d) in H1.
  destruct (name_eqb d l) eqn:E.
  - apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
  - apply name_eqb_false in E. exact (E (eq_sym (Hanti _ _ H1 H2))).
Qed.

(** `no_use_redefined`: where a single definition's site dominates a
    point of a reachable block, no single-definition operand of it is
    defined at that point. So defining a name at a point leaves every
    relation in scope there between a definition and its operands'
    values as it was. *)
Theorem no_use_redefined : forall f b0 rest doms n d j i x l k D,
  fn_blocks f = b0 :: rest -> block_intervals (b0 :: rest) = Some doms ->
  definitions_dominate f doms = true ->
  lookup n (single_definitions f) = Some (DInst i) -> In (n, SAt d j, DInst i) (def_positions f) ->
  is_reachable doms l = true -> site_dominates doms l k (SAt d j) = true ->
  In (x, SAt l k, D) (def_positions f) -> once_has (single_definitions f) x = true ->
  In x (inst_uses i) -> False.
Proof.
  intros f b0 rest doms n d j i x l k D Hf Hdoms Hdd Hn Hpos Hr Hsd Hx Honce Hu.
  destruct (position_inst _ _ _ _ _ Hpos) as (b & kk & Hb & Hl & Hkk & -> & _).
  assert (Hrd : is_reachable doms d = true).
  { unfold site_dominates in Hsd. destruct (name_eqb d l) eqn:E.
    - apply name_eqb_true in E. subst. exact Hr.
    - exact (proj1 (dominates_reachable _ _ _ Hdoms _ _ Hsd)). }
  unfold once_has in Honce. destruct (lookup x (single_definitions f)) as [dx|] eqn:Ex; [|discriminate Honce].
  subst d.
  destruct (use_dominated _ _ _ _ _ _ _ Hdd Hb Hrd Hkk Hu Ex) as (s & Hs & Hsdom).
  destruct (once_position _ _ _ Ex) as (s0 & Hs0 & Huniq).
  destruct (Huniq _ _ Hs) as [-> _]. destruct (Huniq _ _ Hx) as [Esite _].
  exact (site_strict doms (dom_antisym _ _ _ Hdoms) _ _ _ _ _ Hsdom Hsd (eq_sym Esite)).
Qed.
