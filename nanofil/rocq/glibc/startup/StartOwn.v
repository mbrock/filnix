(** A whole-program proof that starts in [start_state] must turn the
    memory that the runtime hands over into separation-logic ownership.
    Most of that memory is the linked image, which the start state keeps
    unchanged except for the constructor table. The image proofs describe
    it as lists of pieces that agree with the image's initial memory.
    This module states once, for every image, that such a list also
    agrees with the start memory, and that a list without duplicates
    gives ownership of each of its pieces. The assemblies for hi_atexit
    and Hello both use it.

    ## From the image to the start memory

    A piece keeps its meaning when its object keeps its region and the
    byte or capability under it keeps its value. The start state
    promises both for every object of the image, except inside the
    constructor table. The table is one live object, and the start
    memory's live objects do not overlap, so a piece of any other object
    never lies inside it. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List Lia.
From stdpp Require Import list fin_maps.
From Nanofil Require Import Values Memory Runtime Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import StartState StartLibcStartMain.
From Glibc Require FileInv.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** A region found by its base is one of the regions in the list. *)
Lemma object_region_in b rs reg : object_region b rs = Some reg -> List.In reg rs /\ r_base reg = b.
Proof.
  induction rs as [|r rs IH]; cbn; [discriminate|].
  destruct (Z.eqb_spec (r_base r) b) as [E|_].
  - intros [= <-]. auto.
  - intros H. destruct (IH H). auto.
Qed.

(** A piece is off the table at tb when it is not a byte or a
    capability slot of the table's own object. *)
Definition piece_off (tb : Z) (l : piece) : Prop :=
  match l with PByte b _ | PAux b _ => b <> tb | _ => True end.

(** A capability that traps as freed in the image still does in the
    start memory, because its object keeps its region. *)
Lemma traps_as_freed_kept m0 m tb tsize c :
  keeps_image m0 m tb tsize -> traps_as_freed (m_regions m0) c -> traps_as_freed (m_regions m) c.
Proof.
  intros (Hr & _) H a size r al Hs. pose proof (H a size r al Hs) as H'. unfold cap_access_res in *.
  destruct c; try exact H';
    match type of H' with context [object_region ?b (m_regions m0)] =>
      destruct (object_region b (m_regions m0)) as [reg|] eqn:E; [rewrite (Hr _ _ E); exact H' | discriminate] end.
Qed.

(** A capability that names a freed object of the image names the same
    freed object in the start memory. *)
Lemma freed_in_kept m0 m tb tsize c :
  keeps_image m0 m tb tsize -> freed_in (m_regions m0) c -> freed_in (m_regions m) c.
Proof. intros (Hr & _) (b & reg & Hc & E & L). exists b, reg. rewrite (Hr _ _ E). auto. Qed.

(** An image proof checks its pieces against the image's memory m0, but
    the program starts in a memory m that the runtime has changed. This
    lemma says those checks still hold in m, as long as no piece is a
    byte or capability slot of the constructor table and the table is a
    live object of the image that is large enough. *)
Lemma keeps_image_agree m0 m tb tsize treg ps :
  keeps_image m0 m tb tsize -> live_disjoint m ->
  live_at m0 tb treg -> tb + tsize <= r_end treg ->
  all_agree m0 ps -> Forall (fun lv => piece_off tb lv.1) ps -> all_agree m ps.
Proof.
  intros Hk Hd [Ht Htl] Hte Ha Hoff. pose proof Hk as (Hr & _ & Hb).
  assert (Lt : live_at m tb treg) by (split; [exact (Hr _ _ Ht) | exact Htl]).
  (* A live offset of an object other than the table lies outside it. *)
  assert (Out : forall b o reg, b <> tb -> object_region b (m_regions m0) = Some reg -> r_life reg = Live ->
                  0 <= o -> b + o < r_end reg -> in_image m0 (b + o) /\ ~ (tb <= b + o < tb + tsize)).
  { intros b o reg Hne E L Ho He. destruct (object_region_in _ _ _ E) as [Hin Hbase]. split.
    - exists reg. split; [exact Hin | lia].
    - destruct (Hd b reg tb treg (conj (Hr _ _ E) L) Lt Hne); lia. }
  apply all_agree_intro. intros l v Hlv.
  pose proof (all_agree_elem _ _ _ _ Ha Hlv) as A.
  pose proof (proj1 (Forall_forall _ _) Hoff _ Hlv) as Hl. cbn in Hl.
  destruct l as [b|b o|b o|n]; destruct v; cbn in A |- *; try exact A.
  - destruct A as [E L]. split; [exact (Hr _ _ E) | exact L].
  - unfold registered in *. intros E. apply A.
    destruct (object_region b (m_regions m0)) as [reg|] eqn:E0; [rewrite (Hr _ _ E0) in E; discriminate | reflexivity].
  - destruct A as [Hreg Hl0]. destruct (object_region b (m_regions m0)) as [reg|] eqn:E; [|done].
    split; [unfold registered; rewrite (Hr _ _ E); discriminate|].
    intros reg' E' L'. rewrite (Hr _ _ E) in E'. injection E' as <-.
    destruct (Hl0 reg E L') as (Ho & He & Hx). split_and!; [exact Ho | exact He |].
    destruct (Out b o reg Hl E L' Ho He) as [Hi Hn]. rewrite (proj1 (Hb _ Hi Hn)). exact Hx.
  - destruct A as [Hreg Hl0]. destruct (object_region b (m_regions m0)) as [reg|] eqn:E; [|done].
    split; [unfold registered; rewrite (Hr _ _ E); discriminate|].
    intros reg' E' L'. rewrite (Hr _ _ E) in E'. injection E' as <-.
    destruct (Hl0 reg E L') as (Ho & He & Hx). split_and!; [exact Ho | exact He |].
    destruct (Out b o reg Hl E L' Ho He) as [Hi Hn]. unfold aux_holds. rewrite (proj2 (Hb _ Hi Hn)).
    destruct Hx as [Hx|[Hf Ht']]; [left; exact Hx|].
    right. split; [exact (freed_in_kept _ _ _ _ _ Hk Hf) | exact (traps_as_freed_kept _ _ _ _ _ Hk Ht')].
Qed.

(** ## How a proof owns the start memory

    A safety proof begins by owning the memory it starts in, so it needs
    one points-to assertion for each piece. The adequacy theorem gives
    these for a heap map that agrees with memory. A piece list without
    duplicates is such a map, and its assertions are [pts] of the list. *)

(** A list that agrees with memory gives a map that agrees with it. *)
Lemma all_agree_map m ps : all_agree m ps -> agrees m (list_to_map ps).
Proof.
  intros A l v Hl. exact (all_agree_elem _ _ _ _ A (elem_of_list_to_map_2 _ _ _ Hl)).
Qed.

Section own.
Context `{!gen_heapGS piece pval Σ}.

(** The points-to assertions of a list without duplicates are those of
    its map. *)
Lemma pts_map ps : NoDup ps.*1 ->
  ([∗ map] l ↦ v ∈ list_to_map ps, pointsto l (DfracOwn 1) v) ⊣⊢ pts ps.
Proof using Type. intros Hnd. rewrite big_sepM_list_to_map; [done | exact Hnd]. Qed.

End own.

(** ## The objects that the runtime allocates

    Besides the image, the runtime hands `c: __libc_start_main` five
    heap objects of its own kinds: the argument array, the environment
    array, their strings and the auxiliary vector. The image lists do
    not describe them, because their addresses and contents vary from
    run to run. The lists below describe them from the facts of
    [start_state], for any image. *)

(** This function gives the region that memory m registers at base b. *)
Definition reg_of (m : mem) (b : Z) : region :=
  match object_region b (m_regions m) with Some r => r | None => mkRegion 0 0 Heap Live end.

(** A stored pointer is its capability slot and its eight bytes, as in a
    [pcell]. *)
Definition ptr_cell_ps (b o : Z) (p : ptr) : list (piece * pval) :=
  (PAux b o, VAux (ptr_cap p)) :: cell b o (ptr_addr p).

(** An array of strings holds one pointer per string and then a null
    pointer. *)
Fixpoint slots_ps (b o : Z) (ss : list (Z * list Z)) : list (piece * pval) :=
  match ss with
  | [] => ptr_cell_ps b o (mkPtr 0 CNone)
  | (sb, _) :: ss => ptr_cell_ps b o (mkPtr sb (Obj sb)) ++ slots_ps b (o + 8) ss
  end.

(** A string object holds its characters and a final NUL. *)
Definition str_ps (m : mem) (q : Z * list Z) : list (piece * pval) :=
  (PLive q.1, VLive (reg_of m q.1)) :: byte_ps q.1 0 (q.2 ++ [0]).

(** An array of strings is its own life, its pointers and every string
    it points to. *)
Definition array_ps (m : mem) (a : Z * list (Z * list Z)) : list (piece * pval) :=
  (PLive a.1, VLive (reg_of m a.1)) :: slots_ps a.1 0 a.2 ++ concat (map (str_ps m) a.2).

(** The auxiliary vector holds each key and value as an integer word, and
    then a zero key. *)
Fixpoint pairs_ps (b o : Z) (ps : list (Z * Z)) : list (piece * pval) :=
  match ps with
  | [] => cell b o 0
  | kv :: ps => cell b o kv.1 ++ cell b (o + 8) kv.2 ++ pairs_ps b (o + 16) ps
  end.

(** This list describes the auxiliary vector by its life and by every
    word that it holds. *)
Definition auxv_ps (m : mem) (av : Z) (ps : list (Z * Z)) : list (piece * pval) :=
  (PLive av, VLive (reg_of m av)) :: pairs_ps av 0 ps.

(** This list joins the runtime's three objects for one start, which
    are argv, environ and the auxiliary vector. *)
Definition start_heap_ps (m : mem) (argv env : Z * list (Z * list Z)) (av : Z) (ps : list (Z * Z)) :
    list (piece * pval) :=
  array_ps m argv ++ array_ps m env ++ auxv_ps m av ps.

(** ## Why these lists agree with the start memory

    Each fact of [start_state] about a slot or a string speaks of single
    bytes inside a live heap object, which is exactly what a piece
    records. The lemmas below go from those facts to agreement, one
    shape at a time. *)

(** A heap object of the start state is live under its own region. *)
Lemma heap_object_live m b n : heap_object m b n -> live_at m b (reg_of m b).
Proof. intros (reg & [E L] & _). unfold live_at, reg_of. rewrite E. split; [reflexivity | exact L]. Qed.

(** A byte inside a heap object agrees when memory holds its value. *)
Lemma ho_byte m b n o x : heap_object m b n -> 0 <= o < n -> m_bytes m (b + o) = x ->
  agree_piece m (PByte b o) (VByte x).
Proof.
  intros (reg & [E L] & _ & _ & _ & He & _) Ho Hx. cbn. unfold registered. rewrite E. split; [discriminate|].
  intros reg' E' _. rewrite E in E'. injection E' as <-. split; [lia|]. split; [|exact Hx].
  assert (n <= (n + 15) / 16 * 16) by (Z.div_mod_to_equations; lia). lia.
Qed.

(** A capability slot inside a heap object agrees when memory holds its
    capability. *)
Lemma ho_aux m b n o c : heap_object m b n -> 0 <= o < n -> m_aux m (b + o) = c ->
  agree_piece m (PAux b o) (VAux c).
Proof.
  intros (reg & [E L] & _ & _ & _ & He & _) Ho Hx. cbn. unfold registered. rewrite E. split; [discriminate|].
  intros reg' E' _. rewrite E in E'. injection E' as <-. split; [lia|]. split; [|left; exact Hx].
  assert (n <= (n + 15) / 16 * 16) by (Z.div_mod_to_equations; lia). lia.
Qed.

(** An integer word inside a heap object agrees when memory holds its
    eight bytes. *)
Lemma ho_cell m b n o v : heap_object m b n -> 0 <= o -> o + 8 <= n ->
  (forall i, 0 <= i < 8 -> m_bytes m (b + o + i) = byte_of v i) -> all_agree m (cell b o v).
Proof.
  intros H Ho He Hb. apply all_agree_cell. intros i Hi. apply (ho_byte _ _ n); [exact H | lia |].
  rewrite Z.add_assoc. exact (Hb i Hi).
Qed.

(** A stored pointer inside a heap object agrees when its slot holds it. *)
Lemma ho_ptr_cell m b n o p : heap_object m b n -> 0 <= o -> o + 8 <= n -> ptr_slot m (b + o) p ->
  all_agree m (ptr_cell_ps b o p).
Proof.
  intros H Ho He (_ & Hb & Ha). cbn [ptr_cell_ps all_agree fst snd]. split.
  - apply (ho_aux _ _ n); [exact H | lia | exact Ha].
  - exact (ho_cell _ _ _ _ _ H Ho He Hb).
Qed.

(** The pointers of an array agree when each slot holds its string's
    pointer and the last slot holds null. *)
Lemma slots_agree m b n ss : forall o, heap_object m b n -> 0 <= o -> o + 8 * (Z.of_nat (length ss) + 1) <= n ->
  (forall i sb s, nth_error ss i = Some (sb, s) -> ptr_slot m (b + o + 8 * Z.of_nat i) (mkPtr sb (Obj sb))) ->
  ptr_slot m (b + o + 8 * Z.of_nat (length ss)) (mkPtr 0 CNone) -> all_agree m (slots_ps b o ss).
Proof.
  induction ss as [|[sb s] ss IH]; intros o H Ho He Hs Hn; cbn [slots_ps].
  - apply (ho_ptr_cell _ _ n); [exact H | exact Ho | cbn [length] in He; lia |].
    cbn [length] in Hn. rewrite Z.mul_0_r Z.add_0_r in Hn. exact Hn.
  - apply (proj2 (all_agree_app _ _ _)). split.
    + apply (ho_ptr_cell _ _ n); [exact H | exact Ho | cbn [length] in He; lia |].
      specialize (Hs 0%nat sb s eq_refl). rewrite Z.mul_0_r Z.add_0_r in Hs. exact Hs.
    + apply (IH (o + 8) H); [lia | cbn [length] in He; lia | |].
      * intros i sb' s' Hi. specialize (Hs (S i) sb' s' Hi).
        replace (b + (o + 8) + 8 * Z.of_nat i) with (b + o + 8 * Z.of_nat (S i)) by lia. exact Hs.
      * replace (b + (o + 8) + 8 * Z.of_nat (length ss)) with (b + o + 8 * Z.of_nat (length ((sb, s) :: ss)))
          by (cbn [length]; lia). exact Hn.
Qed.

(** Bytes inside a heap object agree when memory holds each of them. *)
Lemma bytes_agree m b n xs : forall o, heap_object m b n -> 0 <= o -> o + Z.of_nat (length xs) <= n ->
  (forall i x, nth_error xs i = Some x -> m_bytes m (b + o + Z.of_nat i) = x) -> all_agree m (byte_ps b o xs).
Proof.
  induction xs as [|x xs IH]; intros o H Ho He Hx; [cbn; exact I|].
  rewrite byte_ps_cons. cbn [all_agree fst snd]. split.
  - apply (ho_byte _ _ n); [exact H | cbn [length] in He; lia |].
    specialize (Hx 0%nat x eq_refl). rewrite Z.add_0_r in Hx. exact Hx.
  - apply (IH (o + 1) H); [lia | cbn [length] in He; lia |].
    intros i y Hi. specialize (Hx (S i) y Hi). rewrite <- Hx. f_equal. lia.
Qed.

(** A string of the start state agrees as its life and its bytes. *)
Lemma str_agree m q : c_string m q.1 q.2 -> all_agree m (str_ps m q).
Proof.
  destruct q as [sb s]. cbn [fst snd]. intros (H & Hc & Hz). cbn [str_ps fst snd all_agree]. split.
  - exact (heap_object_live _ _ _ H).
  - apply (bytes_agree _ _ _ _ 0 H); [lia | rewrite length_app; cbn [length]; lia |].
    intros i x Hi. rewrite Z.add_0_r.
    destruct (Nat.lt_ge_cases i (length s)) as [Hl|Hl].
    + rewrite (nth_error_app1 _ _ Hl) in Hi. destruct (Hc i Hl) as (y & Hy & _ & Hm).
      rewrite Hi in Hy. injection Hy as ->. exact Hm.
    + assert (Hlt : (i < length (s ++ [0%Z]))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
      rewrite length_app in Hlt. cbn [length] in Hlt. assert (i = length s) by lia. subst i.
      rewrite (nth_error_app2 _ _ (Nat.le_refl _)) Nat.sub_diag in Hi. cbn in Hi. injection Hi as <-. exact Hz.
Qed.

(** Every string of a list agrees when each one is a string of the start
    state. *)
Lemma strs_agree m ss : (forall q, In q ss -> c_string m q.1 q.2) -> all_agree m (concat (map (str_ps m) ss)).
Proof.
  induction ss as [|q ss IH]; intros H; [exact I|]. cbn [map concat].
  apply (proj2 (all_agree_app _ _ _)). split; [apply str_agree, H; left; reflexivity|].
  apply IH. intros q' Hq. apply H. right. exact Hq.
Qed.

(** When the start state says that an array holds strings, the array's
    life, its pointers and every string agree with memory. *)
Lemma array_agree m a : string_array m a.1 a.2 -> all_agree m (array_ps m a).
Proof.
  destruct a as [b ss]. cbn [fst snd]. intros (H & Hs & Hn). cbn [array_ps fst snd all_agree]. split.
  - exact (heap_object_live _ _ _ H).
  - apply (proj2 (all_agree_app _ _ _)). split.
    + apply (slots_agree _ _ _ _ 0 H); [lia | lia | |].
      * intros i sb s Hi. rewrite Z.add_0_r. exact (proj1 (Hs i sb s Hi)).
      * rewrite Z.add_0_r. exact Hn.
    + apply strs_agree. intros [sb s] Hq. destruct (In_nth_error _ _ Hq) as [i Hi].
      exact (proj2 (Hs i sb s Hi)).
Qed.

(** The words of an auxiliary vector agree when each slot holds its key
    or value and the slot after the last pair holds zero. *)
Lemma pairs_agree m b n ps : forall o, heap_object m b n -> 0 <= o -> o + 16 * Z.of_nat (length ps) + 8 <= n ->
  (forall i k v, nth_error ps i = Some (k, v) ->
     int_slot m (b + o + 16 * Z.of_nat i) k /\ int_slot m (b + o + 16 * Z.of_nat i + 8) v) ->
  int_slot m (b + o + 16 * Z.of_nat (length ps)) 0 -> all_agree m (pairs_ps b o ps).
Proof.
  induction ps as [|[k v] ps IH]; intros o H Ho He Hs Hz; cbn [pairs_ps fst snd].
  - destruct Hz as (_ & Hb & _). apply (ho_cell _ _ n); [exact H | exact Ho | cbn [length] in He; lia |].
    intros i Hi. rewrite <- (Hb i Hi). f_equal. cbn [length]. lia.
  - destruct (Hs 0%nat k v eq_refl) as [(_ & Hk & _) (_ & Hv & _)].
    apply (proj2 (all_agree_app _ _ _)). split.
    { apply (ho_cell _ _ n); [exact H | exact Ho | cbn [length] in He; lia |].
      intros i Hi. rewrite <- (Hk i Hi). f_equal. lia. }
    apply (proj2 (all_agree_app _ _ _)). split.
    { apply (ho_cell _ _ n); [exact H | lia | cbn [length] in He; lia |].
      intros i Hi. rewrite <- (Hv i Hi). f_equal. lia. }
    apply (IH (o + 16) H); [lia | cbn [length] in He; lia | |].
    + intros i k' v' Hi. destruct (Hs (S i) k' v' Hi) as [A B].
      replace (b + (o + 16) + 16 * Z.of_nat i) with (b + o + 16 * Z.of_nat (S i)) by lia. split; [exact A|].
      replace (b + (o + 16) + 16 * Z.of_nat i + 8) with (b + o + 16 * Z.of_nat (S i) + 8) in B by lia. exact B.
    + replace (b + (o + 16) + 16 * Z.of_nat (length ps)) with (b + o + 16 * Z.of_nat (length ((k, v) :: ps)))
        by (cbn [length]; lia). exact Hz.
Qed.

(** The startup body reads the auxiliary vector that the runtime built.
    Its life and its words agree with the start memory. *)
Lemma auxv_agree m av ps : auxv_array m av ps -> all_agree m (auxv_ps m av ps).
Proof.
  intros (H & _ & _ & Hs & Hz). cbn [auxv_ps all_agree fst snd]. split.
  - exact (heap_object_live _ _ _ H).
  - apply (pairs_agree _ _ _ _ 0 H); [lia | lia | |].
    + intros i k v Hi. rewrite Z.add_0_r. exact (Hs i k v Hi).
    + rewrite Z.add_0_r. exact Hz.
Qed.

(** All the runtime's objects of a start state agree with its memory. *)
Lemma start_heap_agree m argv env av ps :
  string_array m argv.1 argv.2 -> string_array m env.1 env.2 -> auxv_array m av ps ->
  all_agree m (start_heap_ps m argv env av ps).
Proof.
  intros Ha He Hv. unfold start_heap_ps.
  apply (proj2 (all_agree_app _ (array_ps m argv) _)). split; [exact (array_agree _ _ Ha)|].
  apply (proj2 (all_agree_app _ (array_ps m env) _)). split; [exact (array_agree _ _ He) | exact (auxv_agree _ _ _ Hv)].
Qed.

(** ## How a proof uses the runtime's objects

    The startup body loads the auxiliary vector one word at a time, and
    main reads each argument string one byte at a time. Each of those
    loads needs its own small assertion. The lemmas below split each
    list of pieces into those assertions. *)

Section heap_own.
Context `{!gen_heapGS piece pval Σ}.

(** The words of an auxiliary vector are its pairs and the zero key
    after them. *)
Lemma pairs_own av o ps :
  pts (pairs_ps av o ps) ⊢ auxv_cells av o ps ∗ icell av (o + 16 * Z.of_nat (length ps)) 0.
Proof using Type.
  revert o. induction ps as [|kv ps IH]; intros o; cbn [pairs_ps length].
  - rewrite Z.mul_0_r Z.add_0_r. iIntros "H". iSplitR; [by rewrite /auxv_cells|]. iExact "H".
  - rewrite !pts_app auxv_cells_cons IH. iIntros "(Hk & Hv & Hr & Hz)". iFrame "Hk Hv Hr".
    replace (o + 16 + 16 * Z.of_nat (length ps)) with (o + 16 * Z.of_nat (S (length ps))) by lia. iExact "Hz".
Qed.

(** Owning the auxiliary vector's list gives its life, its pairs and
    the zero key after them, as the startup body expects. *)
Lemma auxv_own m av ps :
  pts (auxv_ps m av ps) ⊢ live av (reg_of m av) ∗ auxv_cells av 0 ps ∗ icell av (16 * Z.of_nat (length ps)) 0.
Proof using Type.
  rewrite /auxv_ps (pts_app [_] (pairs_ps av 0 ps)) pairs_own Z.add_0_l. auto.
Qed.

(** The pointers of an array are one stored pointer per string and a
    stored null pointer. *)
Lemma slots_own b o ss :
  pts (slots_ps b o ss) ⊢
  ([∗ list] i ↦ q ∈ ss, pcell b (o + 8 * Z.of_nat i) (mkPtr q.1 (Obj q.1))) ∗
  pcell b (o + 8 * Z.of_nat (length ss)) (mkPtr 0 CNone).
Proof using Type.
  revert o. induction ss as [|[sb s] ss IH]; intros o; cbn [slots_ps length].
  - rewrite Z.mul_0_r Z.add_0_r. iIntros "H". iSplitR; [done|]. iExact "H".
  - rewrite pts_app IH. iIntros "(H0 & Hs & Hn)". rewrite big_sepL_cons. cbn [fst].
    rewrite Z.mul_0_r Z.add_0_r. iFrame "H0".
    iSplitL "Hs".
    + iApply (big_sepL_mono with "Hs"). intros i q _. cbn beta.
      by replace (o + 8 + 8 * Z.of_nat i) with (o + 8 * Z.of_nat (S i)) by lia.
    + by replace (o + 8 + 8 * Z.of_nat (length ss)) with (o + 8 * Z.of_nat (S (length ss))) by lia.
Qed.

(** A string object is its life and its bytes with the final NUL. *)
Lemma str_own m q : pts (str_ps m q) ⊢ live q.1 (reg_of m q.1) ∗ bytes q.1 0 (q.2 ++ [0]).
Proof using Type. rewrite /str_ps (pts_app [_] (byte_ps _ _ _)). auto. Qed.

(** Owning an array's list gives the array's life, one stored pointer
    per string, the final null pointer, and each string's life and
    bytes. *)
Lemma array_own m a :
  pts (array_ps m a) ⊢
  live a.1 (reg_of m a.1) ∗
  ([∗ list] i ↦ q ∈ a.2, pcell a.1 (8 * Z.of_nat i) (mkPtr q.1 (Obj q.1))) ∗
  pcell a.1 (8 * Z.of_nat (length a.2)) (mkPtr 0 CNone) ∗
  ([∗ list] q ∈ a.2, live q.1 (reg_of m q.1) ∗ bytes q.1 0 (q.2 ++ [0])).
Proof using Type.
  rewrite /array_ps (pts_app [_] (slots_ps _ _ _ ++ _)) pts_app slots_own.
  iIntros "($ & [Hs $] & Hq)". iSplitL "Hs".
  - iApply (big_sepL_mono with "Hs"). intros i q _. by rewrite Z.add_0_l.
  - iInduction (a.2) as [|q qs] "IH"; [done|]. cbn [map concat]. rewrite pts_app big_sepL_cons str_own.
    iDestruct "Hq" as "[$ Hq]". by iApply "IH".
Qed.

End heap_own.
