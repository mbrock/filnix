(** ImageErase.v shows that erasing unselected bodies leaves every
    symbol and region where it was, and that equal addresses still allow
    different memory. This file names the conditions under which the
    loader's memory also agrees. When no two items share a name, the
    loader writes each object at the base that the placement pass gave
    it. When no initializer has a negative run of zeros, every write of
    an object stays inside that object's own region. Under those two
    conditions, and when the loader succeeds on the original module, it
    also succeeds on the erased one with the same symbols and regions.
    The two memories then agree on every byte and every capability slot
    of each kept object, padding included.

    The theorem assumes that the original loader succeeds and does not
    derive it, because erasing an invalid initializer can turn failure
    into success. It says nothing about running either module, and
    nothing about which module the program actually loads. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Maps Run Semantics Pieces.
From Glibc Require Import ImageErase.
Import ListNotations.
Open Scope Z_scope.

(** ## The conditions and the region of a kept object *)

(** Every item has one name: a function's, an outside function's, a data
    object's or an alias's. The uniqueness condition asks that no two
    items share it. *)
Definition item_key (it : item) : name :=
  match it with IFunc f => fn_name f | IOutside n _ => n | IData n _ _ _ => n | IAlias n _ _ => n end.

(** A run of zeros may not be negative, because a negative run moves the
    write address backwards into the objects before it. *)
Definition zero_ok (d : data_item) : bool := match d with Zero n => 0 <=? n | _ => true end.

Definition item_zero_ok (it : item) : bool :=
  match it with IData _ _ _ its => forallb zero_ok its | _ => true end.

Definition zero_nonneg (md : module) : bool := forallb item_zero_ok md.

(** The placement pass rounds an object's size up to whole words, and the
    agreement covers the rounded size, because a word read at the end of
    a string reads the padding after it. *)
Definition rounded (its : list data_item) : Z := (items_size its + 7) / 8 * 8.

(** An empty weak declaration is the only data item that the loader
    neither places nor writes. *)
Definition ew (lk : linkage) (its : list data_item) : bool :=
  match lk, its with LExternWeak, [] => true | _, _ => false end.

(** An address belongs to a kept item when the item is a kept data object
    and the address lies in the rounded region at the base that the final
    symbol table gives the object's name. *)
Definition kept_item (keep : name -> bool) (g : list (name * ptr)) (it : item) (x : Z) : Prop :=
  exists k lk al its q, it = IData k lk al its /\ keep k = true /\ lookup k g = Some q /\
    ptr_addr q <= x < ptr_addr q + rounded its.

Definition kept_at (keep : name -> bool) (md : module) (g : list (name * ptr)) (x : Z) : Prop :=
  exists it, In it md /\ kept_item keep g it x.

(** Two memories agree at an address when they hold the same byte there
    and the same capability in its slot. *)
Definition agree (m1 m2 : mem) (x : Z) : Prop := m_bytes m1 x = m_bytes m2 x /\ m_aux m1 x = m_aux m2 x.

(** ## Small facts *)

Lemma agree_refl m x : agree m m x.
Proof. split; reflexivity. Qed.

Lemma agree_sym m1 m2 x : agree m1 m2 x -> agree m2 m1 x.
Proof. intros [A B]. split; congruence. Qed.

Lemma agree_trans m1 m2 m3 x : agree m1 m2 x -> agree m2 m3 x -> agree m1 m3 x.
Proof. intros [A B] [C D]. split; congruence. Qed.

(** A store of bytes or of a capability treats every address on its own,
    so it keeps agreement and leaves other addresses alone. *)
Lemma store_bytes_agree m1 m2 a s v x :
  m_bytes m1 x = m_bytes m2 x -> m_bytes (store_bytes m1 a s v) x = m_bytes (store_bytes m2 a s v) x.
Proof. intros H. unfold store_bytes. cbn [m_bytes]. destruct ((a <=? x) && (x <? a + s)); [reflexivity | exact H]. Qed.

Lemma store_aux_other m a c x : x <> a -> m_aux (store_aux m a c) x = m_aux m x.
Proof. intros H. unfold store_aux. cbn [m_aux]. destruct (Z.eqb_spec x a); [contradiction | reflexivity]. Qed.

Lemma store_aux_agree m1 m2 a c x : m_aux m1 x = m_aux m2 x -> m_aux (store_aux m1 a c) x = m_aux (store_aux m2 a c) x.
Proof. intros H. unfold store_aux. cbn [m_aux]. destruct (x =? a); [reflexivity | exact H]. Qed.

Lemma lookup_put_self {A : Type} n (v : A) ps : lookup n (put n v ps) = Some v.
Proof. rewrite lookup_put_name. unfold name_eqb. rewrite term_eqb_refl. reflexivity. Qed.

Lemma lookup_put_other {A : Type} n k (v : A) ps : n <> k -> lookup n (put k v ps) = lookup n ps.
Proof. intros H. rewrite lookup_put_name. destruct (name_eqb n k) eqn:E; [apply term_eqb_eq in E; contradiction | reflexivity]. Qed.

Lemma align_up_ge a k : 0 < k -> a <= align_up a k.
Proof. intros Hk. unfold align_up. pose proof (Z.div_mod (a + k - 1) k ltac:(lia)). pose proof (Z.mod_pos_bound (a + k - 1) k Hk). nia. Qed.

Lemma rounded_ge its : items_size its <= rounded its.
Proof. unfold rounded. pose proof (Z.div_mod (items_size its + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (items_size its + 7) 8 ltac:(lia)). lia. Qed.

Lemma items_size_cons d ds : items_size (d :: ds) = item_size d + items_size ds.
Proof.
  unfold items_size. cbn [fold_left].
  assert (A : forall l s, fold_left (fun s it => s + item_size it) l s = s + fold_left (fun s it => s + item_size it) l 0).
  { induction l as [|y l IH]; intros s; cbn [fold_left]; [lia|]. rewrite (IH (s + item_size y)), (IH (0 + item_size y)). lia. }
  rewrite (A ds (0 + item_size d)). lia.
Qed.

Lemma item_size_nonneg d : zero_ok d = true -> 0 <= item_size d.
Proof.
  destruct d as [w n|cs|s off|n|t]; cbn [zero_ok item_size]; intros H.
  - destruct w; cbn; lia.
  - lia.
  - lia.
  - apply Z.leb_le. exact H.
  - lia.
Qed.

Lemma items_size_nonneg its : forallb zero_ok its = true -> 0 <= items_size its.
Proof.
  induction its as [|d ds IH]; intros H; [reflexivity|]. cbn [forallb] in H. apply andb_true_iff in H as [H1 H2].
  rewrite items_size_cons. pose proof (item_size_nonneg d H1). pose proof (IH H2). lia.
Qed.

Lemma ew_nil lk its : ew lk its = true -> its = [].
Proof. destruct lk, its; cbn; intros H; try discriminate H; reflexivity. Qed.

Lemma ew_erase lk its : ew lk (erase_items its) = ew lk its.
Proof. destruct its; [reflexivity|]. destruct lk; reflexivity. Qed.

Lemma erase_keep keep n lk al its : keep n = true -> erase_item keep (IData n lk al its) = IData n lk al its.
Proof. intros H. cbn [erase_item]. rewrite H. reflexivity. Qed.

Lemma erase_drop keep n lk al its :
  keep n = false -> erase_item keep (IData n lk al its) = IData n lk al (erase_items its).
Proof. intros H. cbn [erase_item]. rewrite H. reflexivity. Qed.

Lemma erase_cons keep it md : erase keep (it :: md) = erase_item keep it :: erase keep md.
Proof. reflexivity. Qed.

Lemma zero_nonneg_cons it md : zero_nonneg (it :: md) = item_zero_ok it && zero_nonneg md.
Proof. reflexivity. Qed.

Lemma layout_fold_none md : fold_left layout md None = None.
Proof. induction md as [|it md IH]; [reflexivity | exact IH]. Qed.

Lemma contents_fold_none g md : fold_left (contents g) md None = None.
Proof. induction md as [|it md IH]; [reflexivity | exact IH]. Qed.

Lemma item_fold_none g its : fold_left (item_contents g) its None = None.
Proof. induction its as [|d ds IH]; [reflexivity | exact IH]. Qed.

Lemma alias_fold_none md : fold_left alias_global md None = None.
Proof. induction md as [|it md IH]; [reflexivity | exact IH]. Qed.

(** ## Writing one object *)

(** This is the step that writes one byte of a string. *)
Definition sfold (a : Z) (mi : mem * Z) (c : Z) : mem * Z := let (m', i) := mi in (store_bytes m' (a + i) 1 c, i + 1).

(** Writing a string changes only its own bytes. *)
Lemma str_fold a cs : forall m i,
  m_regions (fst (fold_left (sfold a) cs (m, i))) = m_regions m /\
  m_aux (fst (fold_left (sfold a) cs (m, i))) = m_aux m /\
  (forall x, ~ (a + i <= x < a + i + Z.of_nat (length cs)) -> m_bytes (fst (fold_left (sfold a) cs (m, i))) x = m_bytes m x).
Proof.
  induction cs as [|c cs IH]; intros m i; cbn [fold_left length].
  - split; [reflexivity|]. split; [reflexivity|]. intros x _. reflexivity.
  - destruct (IH (store_bytes m (a + i) 1 c) (i + 1)) as (R & A & B). split; [exact R|]. split; [exact A|].
    intros x Hx. rewrite B by lia. apply store_bytes_other. lia.
Qed.

Lemma str_fold_agree a cs : forall m1 m2 i x, m_bytes m1 x = m_bytes m2 x ->
  m_bytes (fst (fold_left (sfold a) cs (m1, i))) x = m_bytes (fst (fold_left (sfold a) cs (m2, i))) x.
Proof.
  induction cs as [|c cs IH]; intros m1 m2 i x H; cbn [fold_left]; [exact H|].
  apply IH. apply store_bytes_agree. exact H.
Qed.

(** One initializer item writes only inside the bytes it occupies, and it
    writes the same values whatever the memory held before. *)
Lemma item_step g a m d a' m' :
  item_contents g (Some (a, m)) d = Some (a', m') ->
  a' = a + item_size d /\ m_regions m' = m_regions m /\
  (forall x, ~ (a <= x < a + item_size d) -> agree m' m x) /\
  (forall m2, exists m2', item_contents g (Some (a, m2)) d = Some (a', m2') /\
     forall x, agree m m2 x -> agree m' m2' x).
Proof.
  destruct d as [w n|cs|s off|n|t]; cbn [item_contents item_size]; intros H.
  - injection H as <- <-. split; [reflexivity|]. split; [reflexivity|]. split.
    + intros x Hx. split; [apply store_bytes_other; exact Hx | reflexivity].
    + intros m2. eexists. split; [reflexivity|]. intros x [Hb Ha]. split; [apply store_bytes_agree; exact Hb | exact Ha].
  - injection H as <- <-. change (fun (mi : mem * Z) (c : Z) => let (m', i) := mi in (store_bytes m' (a + i) 1 c, i + 1))
      with (sfold a). destruct (str_fold a cs m 0) as (R & A & B). split; [reflexivity|]. split; [exact R|]. split.
    + intros x Hx. split; [apply B; lia | rewrite A; reflexivity].
    + intros m2. eexists. split; [reflexivity|]. intros x [Hb Ha]. split; [apply str_fold_agree; exact Hb|].
      destruct (str_fold a cs m2 0) as (_ & A2 & _). rewrite A, A2. exact Ha.
  - destruct (a mod 8 =? 0); cbn [negb] in H |- *; [|discriminate H].
    injection H as <- <-. split; [reflexivity|]. split; [reflexivity|]. split.
    + intros x Hx. split; [apply store_bytes_other; exact Hx | rewrite store_aux_other by lia; reflexivity].
    + intros m2. eexists. split; [reflexivity|]. intros x [Hb Ha].
      split; [apply store_bytes_agree; exact Hb | apply store_aux_agree; exact Ha].
  - injection H as <- <-. split; [reflexivity|]. split; [reflexivity|]. split.
    + intros x _. apply agree_refl.
    + intros m2. exists m2. split; [reflexivity|]. intros x Hx. exact Hx.
  - discriminate H.
Qed.

(** A whole initializer without negative runs writes only inside the
    object's raw size, starting at its base. *)
Lemma items_step g its : forall a m e m',
  forallb zero_ok its = true ->
  fold_left (item_contents g) its (Some (a, m)) = Some (e, m') ->
  e = a + items_size its /\ m_regions m' = m_regions m /\
  (forall x, ~ (a <= x < e) -> agree m' m x) /\
  (forall m2, exists m2', fold_left (item_contents g) its (Some (a, m2)) = Some (e, m2') /\
     forall x, agree m m2 x -> agree m' m2' x).
Proof.
  induction its as [|d ds IH]; intros a m e m' Hz H; cbn [fold_left] in H |- *.
  - injection H as <- <-. split; [unfold items_size; cbn; lia|]. split; [reflexivity|].
    split; [intros x _; apply agree_refl|]. intros m2. exists m2. split; [reflexivity|]. intros x Hx. exact Hx.
  - cbn [forallb] in Hz. apply andb_true_iff in Hz as [Hz1 Hz2].
    destruct (item_contents g (Some (a, m)) d) as [[a1 m1]|] eqn:E1; [|rewrite item_fold_none in H; discriminate H].
    pose proof (item_size_nonneg d Hz1). pose proof (items_size_nonneg ds Hz2).
    destruct (item_step g a m d a1 m1 E1) as (-> & R1 & O1 & S1).
    destruct (IH _ _ _ _ Hz2 H) as (-> & R & O & S).
    rewrite items_size_cons. split; [lia|]. split; [congruence|]. split.
    + intros x Hx. eapply agree_trans; [apply O; lia | apply O1; lia].
    + intros m2. destruct (S1 m2) as (m21 & E2 & A1). destruct (S m21) as (m2' & E2' & A2).
      exists m2'. rewrite E2. split; [exact E2'|]. intros x Hx. apply A2, A1, Hx.
Qed.

(** ## The placement pass *)

Lemma layout_data_ew a gs rs n lk al its :
  ew lk its = true -> layout (Some (a, gs, rs)) (IData n lk al its) = Some (a, gs, rs).
Proof. destruct lk, its; cbn [ew]; intros H; try discriminate H; reflexivity. Qed.

Lemma layout_data_place a gs rs n lk al its :
  ew lk its = false -> layout (Some (a, gs, rs)) (IData n lk al its) =
  match data_cap lk (align_up a (Z.max al 16)) with
  | Some c => Some (align_up a (Z.max al 16) + rounded its + 16, put n (mkPtr (align_up a (Z.max al 16)) c) gs,
                    mkRegion (align_up a (Z.max al 16)) (align_up a (Z.max al 16) + rounded its) GlobalData Live :: rs)
  | None => None
  end.
Proof. destruct lk, its; cbn [ew]; intros H; try discriminate H; reflexivity. Qed.

Lemma contents_data_ew g m n lk al its : ew lk its = true -> contents g (Some m) (IData n lk al its) = Some m.
Proof. destruct lk, its; cbn [ew]; intros H; try discriminate H; reflexivity. Qed.

Lemma contents_data_place g m n lk al its :
  ew lk its = false -> contents g (Some m) (IData n lk al its) =
  match lookup n g with
  | Some p => match fold_left (item_contents g) its (Some (ptr_addr p, m)) with Some r => Some (snd r) | None => None end
  | None => None
  end.
Proof. destruct lk, its; cbn [ew]; intros H; try discriminate H; reflexivity. Qed.

(** Placing an item binds at most its own name, only adds regions, and
    never moves the next address backwards. *)
Lemma layout_step a gs rs it a1 gs1 rs1 :
  layout (Some (a, gs, rs)) it = Some (a1, gs1, rs1) ->
  (forall n, n <> item_key it -> lookup n gs1 = lookup n gs) /\ incl rs rs1 /\ (item_zero_ok it = true -> a <= a1).
Proof.
  intros H. destruct it as [f|o t|d lk al its|d lk t]; cbn [item_key item_zero_ok].
  - cbn [layout] in H. injection H as <- <- <-. split; [intros n Hn; apply lookup_put_other, Hn|].
    split; [apply incl_refl|]. intros _. assert (a <= align_up a 16) by (apply align_up_ge; lia). lia.
  - cbn [layout] in H. injection H as <- <- <-. split; [intros n Hn; apply lookup_put_other, Hn|].
    split; [apply incl_refl|]. intros _. assert (a <= align_up a 16) by (apply align_up_ge; lia). lia.
  - destruct (ew lk its) eqn:Ew.
    + rewrite layout_data_ew in H by exact Ew. injection H as <- <- <-.
      split; [intros; reflexivity|]. split; [apply incl_refl|]. intros _. lia.
    + rewrite layout_data_place in H by exact Ew. destruct (data_cap lk (align_up a (Z.max al 16))) as [c|]; [|discriminate H].
      injection H as <- <- <-. split; [intros n Hn; apply lookup_put_other, Hn|].
      split; [intros r Hr; right; exact Hr|]. intros Hz. pose proof (items_size_nonneg its Hz). pose proof (rounded_ge its).
      assert (a <= align_up a (Z.max al 16)) by (apply align_up_ge; lia). lia.
  - cbn [layout] in H. injection H as <- <- <-. split; [intros; reflexivity|]. split; [apply incl_refl|]. intros _. lia.
Qed.

(** A name that no later item carries keeps its binding to the end of the
    placement pass. *)
Lemma layout_fold_lookup n : forall md a gs rs a' g0 rs',
  fold_left layout md (Some (a, gs, rs)) = Some (a', g0, rs') -> ~ In n (map item_key md) -> lookup n g0 = lookup n gs.
Proof.
  induction md as [|it md IH]; intros a gs rs a' g0 rs' H Hn; cbn [fold_left map In] in H, Hn.
  - injection H as _ <- _. reflexivity.
  - destruct (layout (Some (a, gs, rs)) it) as [[[a1 gs1] rs1]|] eqn:E; [|rewrite layout_fold_none in H; discriminate H].
    rewrite (IH _ _ _ _ _ _ H) by tauto. destruct (layout_step _ _ _ _ _ _ _ E) as (L & _ & _).
    apply L. intros ->. tauto.
Qed.

(** A data object keeps its region in every later list of regions. *)
Lemma layout_fold_incl : forall md a gs rs a' g0 rs',
  fold_left layout md (Some (a, gs, rs)) = Some (a', g0, rs') -> incl rs rs'.
Proof.
  induction md as [|it md IH]; intros a gs rs a' g0 rs' H; cbn [fold_left] in H.
  - injection H as _ _ <-. apply incl_refl.
  - destruct (layout (Some (a, gs, rs)) it) as [[[a1 gs1] rs1]|] eqn:E; [|rewrite layout_fold_none in H; discriminate H].
    destruct (layout_step _ _ _ _ _ _ _ E) as (_ & I & _). eapply incl_tran; [exact I | exact (IH _ _ _ _ _ _ H)].
Qed.

(** The alias pass binds only alias names. *)
Lemma alias_fold_lookup n : forall md gs g,
  fold_left alias_global md (Some gs) = Some g ->
  (forall a lk t, In (IAlias a lk t) md -> a <> n) -> lookup n g = lookup n gs.
Proof.
  induction md as [|it md IH]; intros gs g H Hn; cbn [fold_left] in H.
  - injection H as <-. reflexivity.
  - assert (Hn' : forall a lk t, In (IAlias a lk t) md -> a <> n) by (intros a lk t Hi; exact (Hn a lk t (or_intror Hi))).
    destruct it as [f|o t|d lk al its|a lk t].
    + exact (IH gs g H Hn').
    + exact (IH gs g H Hn').
    + exact (IH gs g H Hn').
    + cbn [alias_global] in H. destruct (lookup t gs) as [p|]; [|rewrite alias_fold_none in H; discriminate H].
      rewrite (IH _ _ H Hn'). apply lookup_put_other. intros E. exact (Hn a lk t (or_introl eq_refl) (eq_sym E)).
Qed.

(** With unique names, two items in the module that share a name are the
    same item. *)
Lemma key_inj md x y : NoDup (map item_key md) -> In x md -> In y md -> item_key x = item_key y -> x = y.
Proof.
  induction md as [|it md IH]; cbn [map In]; [tauto|]. intros Hd Hx Hy E. apply NoDup_cons_iff in Hd as [Hn Hd].
  destruct Hx as [<-|Hx], Hy as [<-|Hy].
  - reflexivity.
  - exfalso. apply Hn. rewrite E. apply in_map. exact Hy.
  - exfalso. apply Hn. rewrite <- E. apply in_map. exact Hx.
  - exact (IH Hd Hx Hy E).
Qed.

(** ## Writing the module

    To compare the two memories, the proof follows the loader as it
    writes the original and the erased module side by side, one item at
    a time. At each item it knows the address where the loader will
    place that item. Both runs have written only below that address so
    far, and above it the two memories still agree. *)

(** An item that is not a data object writes nothing in either module. *)
Lemma head_skip keep g it a a1 m1 m2 m11 :
  (forall n lk al its, it <> IData n lk al its) -> a <= a1 ->
  contents g (Some m1) it = Some m11 -> (forall x, a <= x -> agree m1 m2 x) ->
  exists m21, contents g (Some m2) (erase_item keep it) = Some m21 /\
    m_regions m11 = m_regions m1 /\ m_regions m21 = m_regions m2 /\
    (forall x, a1 <= x -> agree m11 m21 x) /\
    (forall x, kept_item keep g it x -> agree m11 m21 x /\ x < a1) /\
    (forall x, x < a -> agree m11 m1 x /\ agree m21 m2 x).
Proof.
  intros Hnd Ha1 Ec Hm.
  assert (E : forall m, contents g (Some m) it = Some m /\ contents g (Some m) (erase_item keep it) = Some m).
  { intros m. destruct it as [f|o t|n lk al its|n lk t].
    - split; reflexivity.
    - split; reflexivity.
    - exfalso. exact (Hnd n lk al its eq_refl).
    - split; reflexivity. }
  rewrite (proj1 (E m1)) in Ec. injection Ec as <-. exists m2. split; [exact (proj2 (E m2))|].
  split; [reflexivity|]. split; [reflexivity|]. split; [intros x Hx; apply Hm; lia|]. split.
  - intros x (k & lk & al & its & q & Hit & _). exfalso. exact (Hnd k lk al its Hit).
  - intros x _. split; apply agree_refl.
Qed.

(** This lemma handles one item. A kept object writes the same values
    into both memories, all of them inside its own region. A dropped
    object writes only inside its own region in the original and writes
    nothing in the erased module. *)
Lemma head_step keep g it a gs rs a1 gs1 rs1 m1 m2 m11 :
  item_zero_ok it = true ->
  layout (Some (a, gs, rs)) it = Some (a1, gs1, rs1) ->
  (forall n lk al its, it = IData n lk al its -> lookup n g = lookup n gs1) ->
  contents g (Some m1) it = Some m11 ->
  (forall x, a <= x -> agree m1 m2 x) ->
  exists m21, contents g (Some m2) (erase_item keep it) = Some m21 /\
    m_regions m11 = m_regions m1 /\ m_regions m21 = m_regions m2 /\
    (forall x, a1 <= x -> agree m11 m21 x) /\
    (forall x, kept_item keep g it x -> agree m11 m21 x /\ x < a1) /\
    (forall x, x < a -> agree m11 m1 x /\ agree m21 m2 x).
Proof.
  intros Hz El HL Ec Hm. destruct (layout_step _ _ _ _ _ _ _ El) as (_ & _ & Hmono). pose proof (Hmono Hz) as Ha1.
  destruct it as [f|o t|n lk al its|n lk t].
  - apply head_skip; [intros ? ? ? ? H; discriminate H | exact Ha1 | exact Ec | exact Hm].
  - apply head_skip; [intros ? ? ? ? H; discriminate H | exact Ha1 | exact Ec | exact Hm].
  - cbn [item_zero_ok] in Hz. pose proof (items_size_nonneg its Hz). pose proof (rounded_ge its).
    destruct (ew lk its) eqn:Ew.
    + rewrite layout_data_ew in El by exact Ew. rewrite contents_data_ew in Ec by exact Ew.
      injection El as <- <- <-. injection Ec as <-. pose proof (ew_nil _ _ Ew) as ->.
      exists m2. split.
      { destruct (keep n) eqn:Hk; [rewrite erase_keep by exact Hk | rewrite erase_drop by exact Hk];
          apply contents_data_ew; exact Ew. }
      split; [reflexivity|]. split; [reflexivity|]. split; [exact Hm|]. split.
      * intros x (k & lk' & al' & its' & q & Hit & _ & _ & Hx). injection Hit as <- <- <- <-.
        assert (rounded [] = 0) by reflexivity. lia.
      * intros x _. split; apply agree_refl.
    + rewrite layout_data_place in El by exact Ew. rewrite contents_data_place in Ec by exact Ew.
      destruct (data_cap lk (align_up a (Z.max al 16))) as [c|]; [|discriminate El].
      injection El as <- <- <-.
      assert (Hb : a <= align_up a (Z.max al 16)) by (apply align_up_ge; lia).
      assert (Hlk : lookup n g = Some (mkPtr (align_up a (Z.max al 16)) c)).
      { rewrite (HL n lk al its eq_refl). apply lookup_put_self. }
      rewrite Hlk in Ec. cbn [ptr_addr] in Ec.
      destruct (fold_left (item_contents g) its (Some (align_up a (Z.max al 16), m1))) as [[e m1i]|] eqn:Ef;
        [|discriminate Ec].
      injection Ec as <-. cbn [snd].
      destruct (items_step g its _ m1 e m1i Hz Ef) as (He & R1 & O1 & S1).
      destruct (keep n) eqn:Hk.
      * destruct (S1 m2) as (m2i & Ef2 & A12).
        destruct (items_step g its _ m2 e m2i Hz Ef2) as (_ & R2 & O2 & _).
        exists m2i. split.
        { rewrite erase_keep by exact Hk. rewrite contents_data_place by exact Ew. rewrite Hlk. cbn [ptr_addr].
          rewrite Ef2. reflexivity. }
        split; [exact R1|]. split; [exact R2|]. split.
        { intros x Hx. apply A12, Hm. lia. }
        split.
        { intros x (k & lk' & al' & its' & q & Hit & _ & Hq & Hx). injection Hit as <- <- <- <-.
          rewrite Hlk in Hq. injection Hq as <-. cbn [ptr_addr] in Hx. split; [apply A12, Hm; lia | lia]. }
        intros x Hx. split; [apply O1 | apply O2]; lia.
      * exists m2. split.
        { rewrite erase_drop by exact Hk. rewrite contents_data_place by (rewrite ew_erase; exact Ew).
          rewrite Hlk. cbn [ptr_addr]. destruct its as [|d ds]; reflexivity. }
        split; [exact R1|]. split; [reflexivity|]. split.
        { intros x Hx. eapply agree_trans; [apply O1; lia | apply Hm; lia]. }
        split.
        { intros x (k & lk' & al' & its' & q & Hit & Hk' & _). injection Hit as <- <- <- <-. congruence. }
        intros x Hx. split; [apply O1; lia | apply agree_refl].
  - apply head_skip; [intros ? ? ? ? H; discriminate H | exact Ha1 | exact Ec | exact Hm].
Qed.

(** This lemma follows the loader over the whole module. Every kept
    object ends with the same bytes and capabilities in both memories,
    and neither run writes below the address where it started. *)
Lemma contents_sim keep g : forall md a gs rs a' g0 rs' m1 m2 m1',
  NoDup (map item_key md) -> zero_nonneg md = true ->
  fold_left layout md (Some (a, gs, rs)) = Some (a', g0, rs') ->
  (forall n lk al its, In (IData n lk al its) md -> lookup n g = lookup n g0) ->
  fold_left (contents g) md (Some m1) = Some m1' ->
  (forall x, a <= x -> agree m1 m2 x) ->
  exists m2', fold_left (contents g) (erase keep md) (Some m2) = Some m2' /\
    m_regions m1' = m_regions m1 /\ m_regions m2' = m_regions m2 /\
    (forall x, kept_at keep md g x -> agree m1' m2' x) /\
    (forall x, x < a -> agree m1' m1 x /\ agree m2' m2 x).
Proof.
  induction md as [|it md IH]; intros a gs rs a' g0 rs' m1 m2 m1' Hd Hz Hl Hg Hc Hm.
  { cbn [fold_left] in Hc. injection Hc as <-. exists m2. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [intros x (it & [] & _)|]. intros x _. split; apply agree_refl. }
  apply NoDup_cons_iff in Hd as [Hn Hd]. rewrite zero_nonneg_cons in Hz. apply andb_true_iff in Hz as [Hz1 Hz].
  cbn [fold_left] in Hl, Hc.
  destruct (layout (Some (a, gs, rs)) it) as [[[a1 gs1] rs1]|] eqn:El; [|rewrite layout_fold_none in Hl; discriminate Hl].
  destruct (contents g (Some m1) it) as [m11|] eqn:Ec; [|rewrite contents_fold_none in Hc; discriminate Hc].
  destruct (layout_step _ _ _ _ _ _ _ El) as (_ & _ & Hmono). pose proof (Hmono Hz1) as Ha1.
  assert (Hg' : forall n lk al its, In (IData n lk al its) md -> lookup n g = lookup n g0).
  { intros n lk al its Hin. apply (Hg n lk al its). right. exact Hin. }
  assert (HL : forall n lk al its, it = IData n lk al its -> lookup n g = lookup n gs1).
  { intros n lk al its ->. rewrite (Hg n lk al its (or_introl eq_refl)). exact (layout_fold_lookup n md _ _ _ _ _ _ Hl Hn). }
  destruct (head_step keep g it a gs rs a1 gs1 rs1 m1 m2 m11 Hz1 El HL Ec Hm) as (m21 & E2 & R1 & R2 & P1 & P4 & P2).
  destruct (IH a1 gs1 rs1 a' g0 rs' m11 m21 m1' Hd Hz Hl Hg' Hc P1) as (m2' & F & R1' & R2' & K & C).
  exists m2'. rewrite erase_cons. cbn [fold_left]. rewrite E2. split; [exact F|].
  split; [congruence|]. split; [congruence|]. split.
  - intros x (it' & [<-|Hin] & Hh).
    + destruct (P4 x Hh) as [A Hlt]. destruct (C x Hlt) as [C1 C2].
      eapply agree_trans; [exact C1|]. eapply agree_trans; [exact A|]. apply agree_sym. exact C2.
    + apply K. exists it'. split; [exact Hin | exact Hh].
  - intros x Hx. assert (Hx1 : x < a1) by lia. destruct (P2 x Hx) as [A1 A2]. destruct (C x Hx1) as [C1 C2].
    split; eapply agree_trans; eauto.
Qed.

(** ## The theorem *)

(** Assume the loader succeeds on a module whose items have distinct
    names and whose zero runs are not negative. Then the loader succeeds
    on its erasure with the same symbols and the same regions. Each kept
    object has the same bytes in both memories over its whole rounded
    region, and the same capability slots there. *)
Theorem erase_memory keep md g m :
  initial_memory md = Some (g, m) -> NoDup (map item_key md) -> zero_nonneg md = true ->
  exists m', initial_memory (erase keep md) = Some (g, m') /\ m_regions m' = m_regions m /\
    (forall x, kept_at keep md g x -> m_bytes m' x = m_bytes m x) /\
    (forall x, kept_at keep md g x -> m_aux m' x = m_aux m x).
Proof.
  intros Hi Hd Hz. unfold initial_memory in *. rewrite layout_fold_erase.
  destruct (fold_left layout md (Some (data_base, [], []))) as [[[a' g0] rs]|] eqn:El; [|discriminate Hi].
  cbv beta iota zeta in Hi |- *. rewrite alias_fold_erase.
  destruct (fold_left alias_global md (Some g0)) as [g1|] eqn:Ea; [|discriminate Hi].
  cbv beta iota zeta in Hi |- *.
  destruct (fold_left (contents g1) md _) as [m1|] eqn:Ec; [|discriminate Hi]. injection Hi as <- <-.
  assert (Hg : forall n lk al its, In (IData n lk al its) md -> lookup n g1 = lookup n g0).
  { intros n lk al its Hin. apply (alias_fold_lookup n md g0 g1 Ea). intros a lk' t Ha E. subst a.
    pose proof (key_inj md _ _ Hd Hin Ha eq_refl) as Heq. discriminate Heq. }
  destruct (contents_sim keep g1 md _ _ _ _ _ _ _ _ _ Hd Hz El Hg Ec (fun x _ => agree_refl _ x))
    as (m2' & F & R1 & R2 & K & _).
  exists m2'. rewrite F. split; [reflexivity|]. split; [congruence|].
  split; intros x Hx; destruct (K x Hx) as [A B]; symmetry; assumption.
Qed.

(** The interval that the theorem covers is the region that the loader
    registered for the object. Its base is the object's final symbol and
    its length is the rounded size. *)
Lemma kept_region md g m n lk al its :
  initial_memory md = Some (g, m) -> NoDup (map item_key md) -> zero_nonneg md = true ->
  In (IData n lk al its) md -> ew lk its = false ->
  exists q, lookup n g = Some q /\ In (mkRegion (ptr_addr q) (ptr_addr q + rounded its) GlobalData Live) (m_regions m).
Proof.
  intros Hi Hd Hz Hin Ew. unfold initial_memory in Hi.
  destruct (fold_left layout md (Some (data_base, [], []))) as [[[a' g0] rs]|] eqn:El; [|discriminate Hi].
  cbv beta iota zeta in Hi. destruct (fold_left alias_global md (Some g0)) as [g1|] eqn:Ea; [|discriminate Hi].
  cbv beta iota zeta in Hi. destruct (fold_left (contents g1) md _) as [m1|] eqn:Ec; [|discriminate Hi].
  injection Hi as <- <-.
  assert (Hg : forall n lk al its, In (IData n lk al its) md -> lookup n g1 = lookup n g0).
  { intros n' lk' al' its' Hin'. apply (alias_fold_lookup n' md g0 g1 Ea). intros a lk2 t Ha E. subst a.
    pose proof (key_inj md _ _ Hd Hin' Ha eq_refl) as Heq. discriminate Heq. }
  destruct (contents_sim (fun _ => true) g1 md _ _ _ _ _ _ _ _ _ Hd Hz El Hg Ec (fun x _ => agree_refl _ x))
    as (_ & _ & R & _). rewrite R. cbn [m_regions]. rewrite (Hg n lk al its Hin).
  clear Ec Ea Hg R Hz. revert Hd El Hin. generalize (@nil region) as rs0. generalize (@nil (name * ptr)) as gs. generalize data_base as a.
  induction md as [|it md IH]; intros a gs rs0 Hd El Hin; [destruct Hin|].
  apply NoDup_cons_iff in Hd as [Hn Hd]. cbn [fold_left] in El.
  destruct (layout (Some (a, gs, rs0)) it) as [[[a1 gs1] rs1]|] eqn:E1; [|rewrite layout_fold_none in El; discriminate El].
  destruct Hin as [->|Hin]; [|exact (IH a1 gs1 rs1 Hd El Hin)].
  rewrite layout_data_place in E1 by exact Ew. destruct (data_cap lk (align_up a (Z.max al 16))) as [c|]; [|discriminate E1].
  injection E1 as <- <- <-. exists (mkPtr (align_up a (Z.max al 16)) c). split.
  - rewrite (layout_fold_lookup n md _ _ _ _ _ _ El Hn). apply lookup_put_self.
  - apply (layout_fold_incl md _ _ _ _ _ _ El). left. reflexivity.
Qed.

(** Uniqueness of names can be checked by computation. *)
Fixpoint names_distinct (ns : list name) : bool :=
  match ns with [] => true | n :: ns' => negb (existsb (name_eqb n) ns') && names_distinct ns' end.

Lemma names_distinct_sound ns : names_distinct ns = true -> NoDup ns.
Proof.
  induction ns as [|n ns IH]; cbn [names_distinct]; intros H; [constructor|].
  apply andb_true_iff in H as [H1 H2]. constructor; [|exact (IH H2)]. intros Hin. apply negb_true_iff in H1.
  assert (existsb (name_eqb n) ns = true) by (apply existsb_exists; exists n; split; [exact Hin | apply term_eqb_refl]).
  congruence.
Qed.

(** ## Controls

    A theorem with unneeded premises would hide a gap, so these small
    modules show what each premise rules out. The first module meets
    both conditions. Its kept constant k holds a pointer to x and one
    byte, so k's rounded region of 16 bytes ends in seven bytes of
    padding. The theorem applies to it: x's byte changes under the
    erasure, and k's pointer, capability and padding do not. Each later
    module breaks one condition, and then either the memories differ or
    only the erased module loads. *)

Local Definition tx (s : string) : name := TAtom s.

Local Definition pos : module :=
  [IData (tx "x") LExport 8 [Item Wl 5];
   IData (tx "k") (LRo (tx "local")) 1 [Sym (tx "x") 0; Str [67]];
   IData (tx "w") LExternWeak 8 [];
   IFunc (mkFunc (tx "f") (tx "export") RVoid [] []);
   IAlias (tx "a") (tx "export") (tx "x")].

Local Definition keep_k (n : name) : bool := name_eqb n (tx "k").
Local Definition keep_x (n : name) : bool := name_eqb n (tx "x").

(** Computing a whole memory would unfold its byte functions, so the
    controls compute only the symbols or single bytes. *)
Local Lemma some_of_map {A B : Type} (f : A -> B) (o : option A) : option_map f o <> None -> exists v, o = Some v.
Proof. destruct o as [v|]; cbn [option_map]; intros H; [exists v; reflexivity | contradiction]. Qed.

(** The theorem's premises hold for the small module, so its conclusion
    is available there. *)
Lemma pos_agrees : exists g m m', initial_memory pos = Some (g, m) /\
  initial_memory (erase keep_k pos) = Some (g, m') /\
  forall x, kept_at keep_k pos g x -> m_bytes m' x = m_bytes m x /\ m_aux m' x = m_aux m x.
Proof.
  assert (Hd : NoDup (map item_key pos)) by (apply names_distinct_sound; vm_compute; reflexivity).
  assert (Hz : zero_nonneg pos = true) by (vm_compute; reflexivity).
  assert (Hs : option_map fst (initial_memory pos) <> None) by (vm_compute; discriminate).
  destruct (some_of_map _ _ Hs) as [[g m] E].
  destruct (erase_memory keep_k pos g m E Hd Hz) as (m' & E' & _ & B & A).
  exists g, m, m'. split; [exact E|]. split; [exact E'|]. intros x Hx. split; [apply B | apply A]; exact Hx.
Qed.

(** The loader places k at 65568 with a region of 16 bytes. The erasure
    clears x's byte at 65536 and keeps k's pointer capability at 65568 and
    its padding byte at 65580. *)
Lemma pos_witness :
  rounded [Sym (tx "x") 0; Str [67]] = 16 /\
  option_map (fun gm => (lookup (tx "k") (fst gm), m_bytes (snd gm) 65536, m_aux (snd gm) 65568, m_bytes (snd gm) 65580))
    (initial_memory pos) = Some (Some (mkPtr 65568 (Ro 65568)), 5, Obj 65536, 0) /\
  option_map (fun gm => (m_bytes (snd gm) 65536, m_aux (snd gm) 65568, m_bytes (snd gm) 65580))
    (initial_memory (erase keep_k pos)) = Some (0, Obj 65536, 0).
Proof. vm_compute. split; [reflexivity|]. split; reflexivity. Qed.

(** The earlier module whose alias steers y's bytes into x gives the
    alias the name of a data object, so it breaks the uniqueness
    condition. *)
Lemma redirect_names_repeat : names_distinct (map item_key ImageErase.redirect) = false.
Proof. vm_compute. reflexivity. Qed.

(** A negative run of zeros sends y's word back into x even though every
    name is distinct, and the erasure then changes a byte of the kept x. *)
Local Definition backwards : module :=
  [IData (tx "x") LExport 8 [Zero 8]; IData (tx "y") LExport 8 [Zero (-32); Item Wl 7; Zero 32]].

Lemma backwards_writes_x :
  names_distinct (map item_key backwards) = true /\ zero_nonneg backwards = false /\
  option_map (fun gm => m_bytes (snd gm) 65536) (initial_memory backwards) = Some 7 /\
  option_map (fun gm => m_bytes (snd gm) 65536) (initial_memory (erase keep_x backwards)) = Some 0.
Proof. vm_compute. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. Qed.

(** A misaligned pointer and an unrecognized initializer each make the
    loader fail on the original, while their erasures load. Success of
    the erased module therefore says nothing about the original. *)
Local Definition misaligned : module :=
  [IData (tx "x") LExport 8 [Zero 8]; IData (tx "y") LExport 8 [Item Wb 1; Sym (tx "x") 0]].

Local Definition unknown : module :=
  [IData (tx "x") LExport 8 [Zero 8]; IData (tx "y") LExport 8 [ItemOther (TAtom "bad")]].

Lemma failure_erased_away :
  names_distinct (map item_key misaligned) = true /\ zero_nonneg misaligned = true /\
  initial_memory misaligned = None /\ option_map fst (initial_memory (erase keep_x misaligned)) <> None /\
  names_distinct (map item_key unknown) = true /\ zero_nonneg unknown = true /\
  initial_memory unknown = None /\ option_map fst (initial_memory (erase keep_x unknown)) <> None.
Proof. vm_compute. repeat (split; [first [reflexivity | discriminate] |]). discriminate. Qed.

(** ## A name that no item carries has no symbol *)

(** The loader binds only the names of items: placement binds functions,
    outside functions and data objects, and alias resolution binds
    aliases. A name that no item carries therefore has no symbol. *)
Lemma loaded_absent md g m n :
  initial_memory md = Some (g, m) -> ~ In n (map item_key md) -> lookup n g = None.
Proof.
  intros Hi Hn. unfold initial_memory in Hi.
  destruct (fold_left layout md (Some (data_base, [], []))) as [[[a g0] rs]|] eqn:El; [|discriminate Hi].
  cbv beta iota zeta in Hi. destruct (fold_left alias_global md (Some g0)) as [g1|] eqn:Ea; [|discriminate Hi].
  cbv beta iota zeta in Hi. destruct (fold_left (contents g1) md _); [|discriminate Hi]. injection Hi as <- _.
  rewrite (alias_fold_lookup n md g0 g1 Ea).
  - exact (layout_fold_lookup n md _ _ _ _ _ _ El Hn).
  - intros a' lk t Hin E. subst a'. apply Hn. exact (in_map item_key _ _ Hin).
Qed.

(** A name that no item of a module carries finds no function and has
    no symbol, so a check of the decoded items settles both. *)
Definition absent_ok (md : module) (s : string) : bool :=
  match find_direct (TAtom s) md, find_alias (TAtom s) md with
  | None, None => negb (existsb (name_eqb (TAtom s)) (map item_key md))
  | _, _ => false
  end.

Lemma absent_ok_sound md g m fr s : initial_memory md = Some (g, m) -> absent_ok md s = true ->
  find_fn (mkGenv md g fr) (TAtom s) = None /\ lookup (TAtom s) g = None.
Proof.
  intros Hi. unfold absent_ok. destruct (find_direct (TAtom s) md) eqn:Hd; [discriminate|].
  destruct (find_alias (TAtom s) md) eqn:Ha; [discriminate|]. intros Hk. split.
  - unfold find_fn. cbn [ge_module]. rewrite Hd, Ha. reflexivity.
  - apply (loaded_absent _ _ m _ Hi). intros Hin.
    assert (E : existsb (name_eqb (TAtom s)) (map item_key md) = true).
    { apply existsb_exists. exists (TAtom s). split; [exact Hin | apply term_eqb_refl]. }
    rewrite E in Hk. discriminate.
Qed.
