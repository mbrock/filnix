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
From Glibc Require Import OsWorld OsStart StartState StartLibcStartMain.
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

(** String routines read a string in whole 8-byte words, so a proof
    must own the zero bytes after the NUL up to the next word boundary.
    This list holds the characters of s and then zeros up to that
    boundary. *)
Definition str_bytes (s : list Z) : list Z :=
  s ++ repeat 0 (Z.to_nat (8 * ((Z.of_nat (length s) + 8) / 8)) - length s).

(** A string object holds its characters, a final NUL and the zeros
    after it up to the next word boundary. *)
Definition str_ps (m : mem) (q : Z * list Z) : list (piece * pval) :=
  (PLive q.1, VLive (reg_of m q.1)) :: byte_ps q.1 0 (str_bytes q.2).

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

(** A string's words fill whole words and stay inside its 16-byte
    granules. *)
Lemma length_str_bytes s : Z.of_nat (length (str_bytes s)) = 8 * ((Z.of_nat (length s) + 8) / 8).
Proof.
  unfold str_bytes. rewrite length_app repeat_length.
  assert (Z.of_nat (length s) < 8 * ((Z.of_nat (length s) + 8) / 8)) by (Z.div_mod_to_equations; lia). lia.
Qed.

(** A heap object has room for any size up to its rounded size. *)
Lemma heap_object_within m b n n' : heap_object m b n -> 0 <= n' <= (n + 15) / 16 * 16 -> heap_object m b n'.
Proof.
  intros (reg & Hl & Hk & H0 & Ha & He & Hs) Hn. exists reg. split_and!; try assumption.
  assert ((n' + 15) / 16 * 16 <= (n + 15) / 16 * 16) by (Z.div_mod_to_equations; lia). lia.
Qed.

(** Each argument and environment string matches memory: the object is
    alive, and its characters, its NUL and the zeros after it are the
    bytes that memory holds. *)
Lemma str_agree m q : c_string m q.1 q.2 -> all_agree m (str_ps m q).
Proof.
  destruct q as [sb s]. cbn [fst snd]. intros (H & Hc & Hz & Hp). cbn [str_ps fst snd all_agree]. split.
  - exact (heap_object_live _ _ _ H).
  - pose proof (length_str_bytes s) as Ls.
    assert (Hr : 8 * ((Z.of_nat (length s) + 8) / 8) <= (Z.of_nat (length s) + 16) / 16 * 16)
      by (Z.div_mod_to_equations; lia).
    assert (Hw : 0 <= 8 * ((Z.of_nat (length s) + 8) / 8) <= (Z.of_nat (length s) + 1 + 15) / 16 * 16)
      by (Z.div_mod_to_equations; lia).
    apply (bytes_agree _ _ _ _ 0 (heap_object_within _ _ _ _ H Hw)); [lia | lia |].
    intros i x Hi. rewrite Z.add_0_r. unfold str_bytes in Hi.
    destruct (Nat.lt_ge_cases i (length s)) as [Hl|Hl].
    + rewrite (nth_error_app1 _ _ Hl) in Hi. destruct (Hc i Hl) as (y & Hy & _ & Hm).
      rewrite Hi in Hy. injection Hy as ->. exact Hm.
    + rewrite (nth_error_app2 _ _ Hl) in Hi.
      pose proof (nth_error_In _ _ Hi) as Hin. apply repeat_spec in Hin as ->.
      assert (Hk : (i - length s < length (repeat 0%Z (Z.to_nat (8 * ((Z.of_nat (length s) + 8) / 8)) - length s)))%nat)
        by (apply nth_error_Some; intros E; rewrite E in Hi; discriminate).
      rewrite repeat_length in Hk.
      destruct (Nat.eq_dec i (length s)) as [->|Hne]; [exact Hz|].
      apply Hp. lia.
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
Lemma str_own m q : pts (str_ps m q) ⊢ live q.1 (reg_of m q.1) ∗ bytes q.1 0 (str_bytes q.2).
Proof using Type. rewrite /str_ps (pts_app [_] (byte_ps _ _ _)). auto. Qed.

(** Owning an array's list gives the array's life, one stored pointer
    per string, the final null pointer, and each string's life and
    bytes. *)
Lemma array_own m a :
  pts (array_ps m a) ⊢
  live a.1 (reg_of m a.1) ∗
  ([∗ list] i ↦ q ∈ a.2, pcell a.1 (8 * Z.of_nat i) (mkPtr q.1 (Obj q.1))) ∗
  pcell a.1 (8 * Z.of_nat (length a.2)) (mkPtr 0 CNone) ∗
  ([∗ list] q ∈ a.2, live q.1 (reg_of m q.1) ∗ bytes q.1 0 (str_bytes q.2)).
Proof using Type.
  rewrite /array_ps (pts_app [_] (slots_ps _ _ _ ++ _)) pts_app slots_own.
  iIntros "($ & [Hs $] & Hq)". iSplitL "Hs".
  - iApply (big_sepL_mono with "Hs"). intros i q _. by rewrite Z.add_0_l.
  - iInduction (a.2) as [|q qs] "IH"; [done|]. cbn [map concat]. rewrite pts_app big_sepL_cons str_own.
    iDestruct "Hq" as "[$ Hq]". by iApply "IH".
Qed.

End heap_own.

(** ## Why each piece of the runtime's objects has one owner

    A proof can own a list of pieces only when no piece occurs twice in
    it. The runtime's objects are distinct from each other, as
    [start_state] requires, and they are heap objects while the image
    has none. Inside one object, every word and byte has its own
    offset. The lemmas below turn those three facts into the absence of
    duplicates. *)

(** This function gives the object that a memory piece belongs to. *)
Definition piece_obj (l : piece) : option Z :=
  match l with PLive b | PByte b _ | PAux b _ => Some b | PName _ => None end.

(** This function gives the offset of a byte or capability piece. A
    life sits before every offset, at -1. *)
Definition piece_at (l : piece) : Z :=
  match l with PByte _ o | PAux _ o => o | _ => -1 end.

(** Every piece of the list belongs to object b, at an offset from lo up
    to but not including hi. *)
Definition ranged (b lo hi : Z) (L : list (piece * pval)) : Prop :=
  Forall (fun lv => piece_obj lv.1 = Some b /\ lo <= piece_at lv.1 < hi) L.

(** Every piece of the list belongs to one of the objects in S. *)
Definition in_objs (S : list Z) (L : list (piece * pval)) : Prop :=
  Forall (fun lv => exists b, piece_obj lv.1 = Some b /\ In b S) L.

(** Two lists share no key when every pair of their keys differs. *)
Lemma keys_apart (P Q : piece -> Prop) (L1 L2 : list (piece * pval)) :
  Forall (fun lv => P lv.1) L1 -> Forall (fun lv => Q lv.1) L2 -> (forall l, P l -> Q l -> False) ->
  forall l, l ∈ L1.*1 -> l ∉ L2.*1.
Proof.
  intros H1 H2 HPQ l Hl Hl2.
  apply list_elem_of_fmap in Hl as ([l1 v1] & -> & Hin1). apply list_elem_of_fmap in Hl2 as ([l2 v2] & E & Hin2).
  cbn in E |- *. subst l2. apply (HPQ l1).
  - exact (proj1 (Forall_forall _ _) H1 _ Hin1).
  - exact (proj1 (Forall_forall _ _) H2 _ Hin2).
Qed.

(** Two lists in the same object share no key when their offsets lie in
    ranges that do not meet. *)
Lemma ranged_apart b lo1 hi1 (L1 : list (piece * pval)) lo2 hi2 L2 :
  ranged b lo1 hi1 L1 -> ranged b lo2 hi2 L2 -> hi1 <= lo2 -> forall l, l ∈ L1.*1 -> l ∉ L2.*1.
Proof.
  intros H1 H2 Hr.
  apply (keys_apart (fun l => piece_obj l = Some b /\ lo1 <= piece_at l < hi1)
                    (fun l => piece_obj l = Some b /\ lo2 <= piece_at l < hi2) _ _ H1 H2).
  intros l [_ A] [_ B]. lia.
Qed.

(** Two lists of objects share no key when no object is in both. *)
Lemma objs_apart S1 S2 (L1 L2 : list (piece * pval)) :
  in_objs S1 L1 -> in_objs S2 L2 -> (forall b, In b S1 -> In b S2 -> False) -> forall l, l ∈ L1.*1 -> l ∉ L2.*1.
Proof.
  intros H1 H2 HS.
  apply (keys_apart (fun l => exists b, piece_obj l = Some b /\ In b S1)
                    (fun l => exists b, piece_obj l = Some b /\ In b S2) _ _ H1 H2).
  intros l (b & E & B) (b' & E' & B').
  rewrite E in E'. injection E' as <-. exact (HS b B B').
Qed.

(** Joining two lists without duplicates that share no key gives a list
    without duplicates. *)
Lemma nodup_join (L1 L2 : list (piece * pval)) : NoDup L1.*1 -> NoDup L2.*1 -> (forall l, l ∈ L1.*1 -> l ∉ L2.*1) -> NoDup (L1 ++ L2).*1.
Proof. intros A B C. rewrite fmap_app. apply NoDup_app. auto. Qed.

(** A range can always be widened. *)
Lemma ranged_widen b lo hi lo' hi' L : lo' <= lo -> hi <= hi' -> ranged b lo hi L -> ranged b lo' hi' L.
Proof. intros A B H. apply (Forall_impl _ _ _ H). intros lv [E C]. split; [exact E | lia]. Qed.

(** Two lists in one range form a list in that range. *)
Lemma ranged_app b lo hi L1 L2 : ranged b lo hi L1 -> ranged b lo hi L2 -> ranged b lo hi (L1 ++ L2).
Proof. apply Forall_app_2. Qed.

(** A list in one object lies among any objects that include it. *)
Lemma ranged_objs b lo hi S L : In b S -> ranged b lo hi L -> in_objs S L.
Proof. intros Hb H. apply (Forall_impl _ _ _ H). intros lv [E _]. exists b. auto. Qed.

(** A list among some objects lies among any objects that include them. *)
Lemma objs_widen S S' L : (forall b, In b S -> In b S') -> in_objs S L -> in_objs S' L.
Proof. intros HS H. apply (Forall_impl _ _ _ H). intros lv (b & E & B). exists b. auto. Qed.

(** This tactic proves that a short list of byte and capability keys
    at distinct offsets has no duplicates. *)
Local Ltac nodup_offsets :=
  repeat (apply NoDup_cons_2;
    [let H := fresh in intros H;
     repeat (apply elem_of_cons in H as [H|H]; [first [discriminate H | injection H; intros; lia]|]);
     exact (not_elem_of_nil _ H) |]);
  apply NoDup_nil_2.

(** An integer word fills offsets o to o + 8 of its object. *)
Lemma cell_ranged b o x : ranged b o (o + 8) (cell b o x).
Proof.
  unfold ranged, cell. cbn [List.map].
  repeat (apply List.Forall_cons; [cbn; split; [reflexivity | lia]|]). apply List.Forall_nil.
Qed.

(** An integer word has eight distinct byte keys. *)
Lemma cell_nodup b o x : NoDup (cell b o x).*1.
Proof. unfold cell. cbn. nodup_offsets. Qed.

(** A stored pointer fills offsets o to o + 8 of its object. *)
Lemma ptr_cell_ranged b o p : ranged b o (o + 8) (ptr_cell_ps b o p).
Proof. apply List.Forall_cons; [cbn; split; [reflexivity | lia] | apply cell_ranged]. Qed.

(** A stored pointer has nine distinct keys. *)
Lemma ptr_cell_nodup b o p : NoDup (ptr_cell_ps b o p).*1.
Proof. unfold ptr_cell_ps, cell. cbn. nodup_offsets. Qed.

(** An array's pointers fill one word per string and one more. *)
Lemma slots_ranged b o ss : ranged b o (o + 8 * (Z.of_nat (length ss) + 1)) (slots_ps b o ss).
Proof.
  revert o. induction ss as [|[sb s] ss IH]; intros o; cbn [slots_ps length].
  - apply (ranged_widen _ o (o + 8)); [lia | lia | apply ptr_cell_ranged].
  - apply ranged_app.
    + apply (ranged_widen _ o (o + 8)); [lia | lia | apply ptr_cell_ranged].
    + apply (ranged_widen _ (o + 8) (o + 8 + 8 * (Z.of_nat (length ss) + 1))); [lia | lia | apply IH].
Qed.

(** An array's pointers have no duplicate keys. *)
Lemma slots_nodup b o ss : NoDup (slots_ps b o ss).*1.
Proof.
  revert o. induction ss as [|[sb s] ss IH]; intros o; cbn [slots_ps]; [apply ptr_cell_nodup|].
  apply nodup_join; [apply ptr_cell_nodup | apply IH |].
  exact (ranged_apart _ _ _ _ _ _ _ (ptr_cell_ranged b o _) (slots_ranged b (o + 8) ss) ltac:(lia)).
Qed.

(** A run of bytes fills one offset per byte. *)
Lemma bytes_ranged b o xs : ranged b o (o + Z.of_nat (length xs)) (byte_ps b o xs).
Proof.
  revert o. induction xs as [|x xs IH]; intros o; [cbn; apply List.Forall_nil|].
  rewrite byte_ps_cons. cbn [length]. apply List.Forall_cons; [cbn; split; [reflexivity | lia]|].
  apply (ranged_widen _ (o + 1) (o + 1 + Z.of_nat (length xs))); [lia | lia | apply IH].
Qed.

(** A run of bytes has no duplicate keys. *)
Lemma bytes_nodup b o xs : NoDup (byte_ps b o xs).*1.
Proof.
  revert o. induction xs as [|x xs IH]; intros o; [cbn; apply NoDup_nil_2|].
  rewrite byte_ps_cons. apply (nodup_join [(PByte b o, VByte x)] (byte_ps b (o + 1) xs)).
  - cbn. nodup_offsets.
  - apply IH.
  - apply (ranged_apart b o (o + 1) _ (o + 1) (o + 1 + Z.of_nat (length xs))); [| apply bytes_ranged | lia].
    apply List.Forall_cons; [cbn; split; [reflexivity | lia] | apply List.Forall_nil].
Qed.

(** The words of an auxiliary vector fill two words per pair and one
    more. *)
Lemma pairs_ranged b o ps : ranged b o (o + 16 * Z.of_nat (length ps) + 8) (pairs_ps b o ps).
Proof.
  revert o. induction ps as [|kv ps IH]; intros o; cbn [pairs_ps length].
  - apply (ranged_widen _ o (o + 8)); [lia | lia | apply cell_ranged].
  - apply ranged_app; [apply (ranged_widen _ o (o + 8)); [lia | lia | apply cell_ranged]|].
    apply ranged_app; [apply (ranged_widen _ (o + 8) (o + 8 + 8)); [lia | lia | apply cell_ranged]|].
    apply (ranged_widen _ (o + 16) (o + 16 + 16 * Z.of_nat (length ps) + 8)); [lia | lia | apply IH].
Qed.

(** The words of an auxiliary vector have no duplicate keys. *)
Lemma pairs_nodup b o ps : NoDup (pairs_ps b o ps).*1.
Proof.
  revert o. induction ps as [|kv ps IH]; intros o; cbn [pairs_ps]; [apply cell_nodup|].
  apply nodup_join; [apply cell_nodup | apply nodup_join; [apply cell_nodup | apply IH |] |].
  - exact (ranged_apart _ _ _ _ _ _ _ (cell_ranged b (o + 8) _) (pairs_ranged b (o + 16) ps) ltac:(lia)).
  - apply (ranged_apart b o (o + 8) _ (o + 8) (o + 16 + 16 * Z.of_nat (length ps) + 8)); [apply cell_ranged| |lia].
    apply ranged_app; [apply (ranged_widen _ (o + 8) (o + 8 + 8)); [lia | lia | apply cell_ranged]|].
    apply (ranged_widen _ (o + 16) (o + 16 + 16 * Z.of_nat (length ps) + 8)); [lia | lia | apply pairs_ranged].
Qed.

(** An object's life sits at offset -1, before all its bytes. *)
Lemma life_ranged b reg : ranged b (-1) 0 [(PLive b, VLive reg)].
Proof. apply List.Forall_cons; [cbn; split; [reflexivity | lia] | apply List.Forall_nil]. Qed.

(** An object made of a life and pieces at offsets from zero has no
    duplicate keys when those pieces have none. *)
Lemma life_join b reg hi L : ranged b 0 hi L -> NoDup L.*1 -> NoDup ((PLive b, VLive reg) :: L).*1.
Proof.
  intros Hr Hn. apply (nodup_join [(PLive b, VLive reg)] L); [cbn; nodup_offsets | exact Hn |].
  exact (ranged_apart _ _ _ _ _ _ _ (life_ranged b reg) Hr ltac:(lia)).
Qed.

(** A string object lies in its own object and has no duplicate keys. *)
Lemma str_ranged m q : ranged q.1 (-1) (Z.of_nat (length (str_bytes q.2)) + 1) (str_ps m q).
Proof.
  apply List.Forall_cons; [cbn; split; [reflexivity | lia]|].
  apply (ranged_widen _ 0 (0 + Z.of_nat (length (str_bytes q.2)))); [lia | lia | apply bytes_ranged].
Qed.

Lemma str_nodup m q : NoDup (str_ps m q).*1.
Proof. apply (life_join _ _ _ _ (bytes_ranged q.1 0 _) (bytes_nodup _ _ _)). Qed.

(** The strings of an array lie in their own objects, and with distinct
    objects they have no duplicate keys. *)
Lemma strs_objs m ss : in_objs (map fst ss) (concat (map (str_ps m) ss)).
Proof.
  induction ss as [|q ss IH]; [apply List.Forall_nil|]. cbn [map concat]. apply Forall_app_2.
  - apply (ranged_objs q.1 (-1) _ (q.1 :: map fst ss) _ (or_introl eq_refl) (str_ranged m q)).
  - apply (objs_widen (map fst ss)); [intros b Hb; right; exact Hb | exact IH].
Qed.

Lemma strs_nodup m ss : List.NoDup (map fst ss) -> NoDup (concat (map (str_ps m) ss)).*1.
Proof.
  induction ss as [|q ss IH]; intros Hn; [cbn; apply NoDup_nil_2|]. cbn [map concat] in *.
  inversion Hn as [|? ? Hq Hn']; subst.
  apply nodup_join; [apply str_nodup | exact (IH Hn') |].
  apply (objs_apart [q.1] (map fst ss)); [| apply strs_objs |].
  - apply (ranged_objs q.1 (-1) _ [q.1] _ (or_introl eq_refl) (str_ranged m q)).
  - intros b [<-|[]] Hb. exact (Hq Hb).
Qed.

(** An array of strings lies in its own object and its strings' objects,
    and with all of those distinct it has no duplicate keys. *)
Lemma array_objs m a : in_objs (a.1 :: map fst a.2) (array_ps m a).
Proof.
  apply List.Forall_cons; [exists a.1; split; [reflexivity | left; reflexivity]|]. apply Forall_app_2.
  - apply (ranged_objs a.1 0 _ (a.1 :: map fst a.2) _ (or_introl eq_refl) (slots_ranged a.1 0 a.2)).
  - apply (objs_widen (map fst a.2)); [intros b Hb; right; exact Hb | apply strs_objs].
Qed.

Lemma array_nodup m a : List.NoDup (a.1 :: map fst a.2) -> NoDup (array_ps m a).*1.
Proof.
  intros Hn. inversion Hn as [|? ? Ha Hn']; subst.
  assert (Hrest : NoDup (slots_ps a.1 0 a.2 ++ concat (map (str_ps m) a.2)).*1).
  { apply nodup_join; [apply slots_nodup | exact (strs_nodup m _ Hn') |].
    apply (objs_apart [a.1] (map fst a.2)); [| apply strs_objs |].
    - apply (ranged_objs a.1 0 _ [a.1] _ (or_introl eq_refl) (slots_ranged a.1 0 a.2)).
    - intros b [<-|[]] Hb. exact (Ha Hb). }
  apply (nodup_join [(PLive a.1, VLive (reg_of m a.1))] _); [cbn; nodup_offsets | exact Hrest |].
  (* The life is the only piece at offset -1 of the array's object, and
     the strings belong to other objects. *)
  apply (keys_apart (fun l => l = PLive a.1) (fun l => l <> PLive a.1)).
  - apply List.Forall_cons; [reflexivity | apply List.Forall_nil].
  - apply Forall_app_2.
    + apply (Forall_impl _ _ _ (slots_ranged a.1 0 a.2)). intros lv [_ H] E. rewrite E in H. cbn in H. lia.
    + apply (Forall_impl _ _ _ (strs_objs m a.2)). intros lv (b & Hb & Hin) E.
      rewrite E in Hb. cbn in Hb. injection Hb as <-. exact (Ha Hin).
  - intros l -> H. exact (H eq_refl).
Qed.

(** The auxiliary vector lies in its own object and has no duplicate
    keys. *)
Lemma auxv_objs m av ps : in_objs [av] (auxv_ps m av ps).
Proof.
  apply List.Forall_cons; [exists av; split; [reflexivity | left; reflexivity]|].
  exact (ranged_objs av 0 _ [av] _ (or_introl eq_refl) (pairs_ranged av 0 ps)).
Qed.

Lemma auxv_nodup m av ps : NoDup (auxv_ps m av ps).*1.
Proof. exact (life_join _ _ _ _ (pairs_ranged av 0 ps) (pairs_nodup _ _ _)). Qed.

(** These are the bases of all the runtime's objects for one start. *)
Definition start_bases (argv env : Z * list (Z * list Z)) (av : Z) : list Z :=
  (argv.1 :: map fst argv.2) ++ (env.1 :: map fst env.2) ++ [av].

(** All the runtime's objects lie among their bases. *)
Lemma start_heap_objs m argv env av ps : in_objs (start_bases argv env av) (start_heap_ps m argv env av ps).
Proof.
  unfold start_heap_ps, start_bases. apply Forall_app_2; [|apply Forall_app_2].
  - apply (objs_widen _ _ _ (fun b H => in_or_app _ _ _ (or_introl H)) (array_objs m argv)).
  - apply (objs_widen _ _ _ (fun b H => in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl H))))
      (array_objs m env)).
  - apply (objs_widen _ _ _ (fun b H => in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror H))))
      (auxv_objs m av ps)).
Qed.

(** The bases that [start_state] lists distinct are the same bases in
    another order. *)
Lemma start_bases_perm (argv env : Z * list (Z * list Z)) av :
  Permutation (argv.1 :: env.1 :: av :: map fst argv.2 ++ map fst env.2) (start_bases argv env av).
Proof. unfold start_bases. cbn [app]. solve_Permutation. Qed.

(** When the runtime's objects are distinct, as [start_state] requires,
    their pieces have no duplicate keys. *)
Lemma start_heap_nodup m argv env av ps :
  List.NoDup (fst argv :: fst env :: av :: map fst (snd argv) ++ map fst (snd env)) ->
  NoDup (start_heap_ps m argv env av ps).*1.
Proof.
  intros Hn. apply (Permutation_NoDup (start_bases_perm argv env av)) in Hn. unfold start_bases in Hn.
  apply NoDup_ListNoDup, NoDup_app in Hn as (Ha & Hae & Hn). apply NoDup_app in Hn as (He & Hev & _).
  apply NoDup_ListNoDup in Ha, He.
  unfold start_heap_ps. apply nodup_join; [exact (array_nodup m _ Ha) | apply nodup_join |].
  - exact (array_nodup m _ He).
  - apply auxv_nodup.
  - apply (objs_apart _ _ _ _ (array_objs m env) (auxv_objs m av ps)).
    intros b Hb Hb'. apply (Hev b); apply list_elem_of_In; assumption.
  - apply (objs_apart (argv.1 :: map fst argv.2) ((env.1 :: map fst env.2) ++ [av]) _ _ (array_objs m argv)).
    + apply Forall_app_2.
      * apply (objs_widen _ _ _ (fun b H => in_or_app _ _ _ (or_introl H)) (array_objs m env)).
      * apply (objs_widen _ _ _ (fun b H => in_or_app _ _ _ (or_intror H)) (auxv_objs m av ps)).
    + intros b Hb Hb'. apply (Hae b); apply list_elem_of_In; assumption.
Qed.

(** ## Why the runtime's objects never meet the image

    A whole run owns the image's memory and the runtime's objects at
    the same time, so the two must never overlap. They cannot, because
    the runtime allocates its objects on the heap, the start state keeps
    every image object under its image region, and an image has no heap
    regions. *)

(** No region of the image's memory is a heap region. Each image proves
    this by computation. *)
Definition no_heap_regions (m0 : mem) : Prop := Forall (fun r => r_kind r <> Heap) (m_regions m0).

(** Every base of the runtime's objects names a heap object of the start
    memory. *)
Lemma start_bases_heap m argv env av ps :
  string_array m argv.1 argv.2 -> string_array m env.1 env.2 -> auxv_array m av ps ->
  forall b, In b (start_bases argv env av) -> exists n, heap_object m b n.
Proof.
  intros Ha He Hv b Hb. unfold start_bases in Hb.
  assert (Arr : forall a, string_array m a.1 a.2 -> In b (a.1 :: map fst a.2) -> exists n, heap_object m b n).
  { intros a (H & Hs & _) [<-|Hin]; [eexists; exact H|].
    apply in_map_iff in Hin as ([sb s] & <- & Hq). destruct (In_nth_error _ _ Hq) as [i Hi].
    destruct (Hs i sb s Hi) as [_ (Hc & _)]. eexists; exact Hc. }
  apply in_app_or in Hb as [Hb|Hb]; [exact (Arr _ Ha Hb)|].
  apply in_app_or in Hb as [Hb|[<-|[]]]; [exact (Arr _ He Hb)|]. destruct Hv as (H & _). eexists; exact H.
Qed.

(** A proof may own an image list and the runtime's objects side by
    side. This lemma shows they never name the same piece, for any list
    that the image's memory holds, when the image has no heap regions. *)
Lemma image_heap_apart m0 m tb tsize ps argv env av aps :
  keeps_image m0 m tb tsize -> no_heap_regions m0 -> all_agree m0 ps ->
  string_array m argv.1 argv.2 -> string_array m env.1 env.2 -> auxv_array m av aps ->
  forall l, l ∈ ps.*1 -> l ∉ (start_heap_ps m argv env av aps).*1.
Proof.
  intros (Hr & _) Hn A Ha He Hv.
  apply (keys_apart (fun l => forall b, piece_obj l = Some b -> registered m0 b)
                    (fun l => exists b, piece_obj l = Some b /\ In b (start_bases argv env av))).
  - apply List.Forall_forall. intros [l v] Hin b Hb. cbn in Hb |- *.
    pose proof (all_agree_elem _ _ _ _ A (proj2 (list_elem_of_In _ _) Hin)) as P.
    destruct l as [b'|b' o|b' o|k]; cbn in Hb; try discriminate; injection Hb as <-;
      destruct v; cbn in P; try contradiction.
    + destruct P as [E _]. unfold registered. rewrite E. discriminate.
    + exact P.
    + exact (proj1 P).
    + exact (proj1 P).
  - apply start_heap_objs.
  - intros l HP (b & Hb & Hin). specialize (HP b Hb). unfold registered in HP.
    destruct (object_region b (m_regions m0)) as [r0|] eqn:E; [|exact (HP eq_refl)].
    destruct (start_bases_heap _ _ _ _ _ Ha He Hv b Hin) as (n & reg & [E' _] & Hk & _).
    rewrite (Hr _ _ E) in E'. injection E' as ->.
    apply (proj1 (Forall_forall _ _) Hn reg (proj2 (list_elem_of_In _ _) (proj1 (object_region_in _ _ _ E))) Hk).
Qed.

(** ## What the OS world knows when a run begins

    Calling errno's setter twice, or before its handler exists, makes
    the runtime panic, so the proof must know which startup calls have
    already happened. It keeps that record in one [[ghost-state]] key.
    When the runtime first calls into glibc, none of those calls has
    happened, and the lemmas below give the proof that first record. *)

(** A run must begin with the key saying that startup has done nothing
    yet. This list holds key k with no cookie and no handler. *)
Definition start_key_ps (k : Z) : list (piece * pval) := [(PName k, start_ghost (mkPtr 0 CNone) false false)].

(** The ghost key agrees with any memory. *)
Lemma start_key_agree m k : all_agree m (start_key_ps k).
Proof. cbn. split; exact I. Qed.

(** The ghost key is no piece of the runtime's objects, which all
    belong to memory objects. *)
Lemma start_key_heap_apart k m argv env av ps :
  forall l, l ∈ (start_key_ps k).*1 -> l ∉ (start_heap_ps m argv env av ps).*1.
Proof.
  apply (keys_apart (fun l => piece_obj l = None)
                    (fun l => exists b, piece_obj l = Some b /\ In b (start_bases argv env av))).
  - apply List.Forall_cons; [reflexivity | apply List.Forall_nil].
  - apply start_heap_objs.
  - intros l E (b & E' & _). rewrite E in E'. discriminate.
Qed.

(** Adequacy asks that the first world and memory satisfy the world
    interpretation. Startup's interpretation accepts them when the key
    says that nothing has happened yet, as in every start state. *)
Lemma start_os_wi g w0 w k m h :
  start_os g w0 w -> h !! PName k = Some (start_ghost (mkPtr 0 CNone) false false) -> os_wi_start w0 k m w h.
Proof.
  intros (_ & Hfd & ->) Hk. exists (mkPtr 0 CNone), false, false. split; [exact Hk|].
  split; [reflexivity|]. split; [intros p E; discriminate E|]. split; [|exact Hfd].
  intros Hz. cbn in Hz. lia.
Qed.
