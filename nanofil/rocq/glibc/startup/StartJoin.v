(** A never-panics theorem that starts at `c: __libc_start_main` must
    hand its proof the whole first heap at once: the image's memory,
    the constructor table that the runtime fills in, the runtime's own
    objects and the startup key. Earlier modules describe each of these
    as a list of pieces. This module joins them into one list for any
    image, and shows that the joined list is a heap that adequacy
    accepts. The heap has no duplicate keys, it agrees with the start
    memory, and startup's world interpretation holds of it.

    ## The four parts

    When the program starts, four kinds of memory already hold data
    that startup will read. The linked image holds its globals. The
    runtime has written the saved arguments and the constructor
    pointers into the table. The runtime has also allocated argv,
    environ and the auxiliary vector, as [StartOwn](StartOwn.v)
    describes. Finally, the proof keeps one [[ghost-state]] key that
    says that startup has done nothing yet. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List Lia.
From stdpp Require Import list fin_maps.
From Nanofil Require Import Term Values Memory Runtime Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import OsWorld OsStart StartCtors StartState StartLibcStartMain StartOwn.
From Glibc Require FileInv.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** ## Pieces of a live object

    The runtime writes the saved arguments into a global of the image,
    not into memory that it allocates. So we need to say when a byte or
    a pointer inside any live object matches what memory holds, not
    only inside a heap object. *)

(** A byte inside a live object agrees when memory holds its value. *)
Lemma lv_byte m b reg o x : live_at m b reg -> 0 <= o -> b + o < r_end reg -> m_bytes m (b + o) = x ->
  agree_piece m (PByte b o) (VByte x).
Proof.
  intros [E L] Ho He Hx. cbn. unfold registered. rewrite E. split; [discriminate|].
  intros reg' E' _. rewrite E in E'. injection E' as <-. auto.
Qed.

(** A capability slot inside a live object agrees when memory holds its
    capability. *)
Lemma lv_aux m b reg o c : live_at m b reg -> 0 <= o -> b + o < r_end reg -> m_aux m (b + o) = c ->
  agree_piece m (PAux b o) (VAux c).
Proof.
  intros [E L] Ho He Hx. cbn. unfold registered. rewrite E. split; [discriminate|].
  intros reg' E' _. rewrite E in E'. injection E' as <-. split; [lia|]. split; [lia|]. left. exact Hx.
Qed.

(** A stored pointer inside a live object agrees when its slot holds it. *)
Lemma lv_ptr_cell m b reg o p : live_at m b reg -> 0 <= o -> b + o + 8 <= r_end reg -> ptr_slot m (b + o) p ->
  all_agree m (ptr_cell_ps b o p).
Proof.
  intros H Ho He (_ & Hb & Ha). cbn [ptr_cell_ps all_agree fst snd]. split.
  - apply (lv_aux _ _ reg); [exact H | lia | lia | exact Ha].
  - apply all_agree_cell. intros i Hi. apply (lv_byte _ _ reg); [exact H | lia | lia |].
    rewrite Z.add_assoc. exact (Hb i Hi).
Qed.

(** ## The constructor table

    The runner reads the first four bytes of the saved count, the two
    array pointers and the constructor pointers. This section lists
    those pieces and shows that every start state holds them. *)

(** This function gives the pointer that the image's symbol table g
    holds for the constructor f. *)
Definition ctor_ptr (g : list (name * ptr)) (f : name) : ptr :=
  match lookup f g with Some p => p | None => mkPtr 0 CNone end.

(** These are the constructor pointers of the table, in its order. *)
Definition ctor_ptrs (g : list (name * ptr)) (order : list name) : list ptr := map (ctor_ptr g) order.

(** A run of stored pointers fills one word each. *)
Fixpoint ptrs_ps (b o : Z) (ps : list ptr) : list (piece * pval) :=
  match ps with
  | [] => []
  | p :: ps => ptr_cell_ps b o p ++ ptrs_ps b (o + 8) ps
  end.

(** The table at tb holds the low four bytes of argc, the argument and
    environment pointers, and then the constructor pointers ps. *)
Definition table_ps (tb argc : Z) (argv env : ptr) (ps : list ptr) : list (piece * pval) :=
  byte_ps tb 0 (le_bytes argc 4) ++ ptr_cell_ps tb 8 argv ++ ptr_cell_ps tb 16 env ++ ptrs_ps tb 24 ps.

(** A run of stored pointers agrees when each slot holds its pointer. *)
Lemma ptrs_agree m b reg ps : forall o, live_at m b reg -> 0 <= o -> b + o + 8 * Z.of_nat (length ps) <= r_end reg ->
  (forall i p, nth_error ps i = Some p -> ptr_slot m (b + o + 8 * Z.of_nat i) p) -> all_agree m (ptrs_ps b o ps).
Proof.
  induction ps as [|p ps IH]; intros o H Ho He Hs; cbn [ptrs_ps]; [exact I|].
  apply (proj2 (all_agree_app _ _ _)). split.
  - apply (lv_ptr_cell _ _ reg); [exact H | exact Ho | cbn [length] in He; lia |].
    specialize (Hs 0%nat p eq_refl). rewrite Z.mul_0_r Z.add_0_r in Hs. exact Hs.
  - apply (IH (o + 8) H); [lia | cbn [length] in He; lia |].
    intros i q Hi. specialize (Hs (S i) q Hi).
    replace (b + (o + 8) + 8 * Z.of_nat i) with (b + o + 8 * Z.of_nat (S i)) by lia. exact Hs.
Qed.

(** Every start state's table agrees with the table's pieces, given the
    table's region in the start memory. *)
Lemma table_agree m g tb reg argc argv env order :
  live_at m tb reg -> tb + ctor_table_size (length order) <= r_end reg ->
  ctor_table m g tb argc argv env order -> all_agree m (table_ps tb argc argv env (ctor_ptrs g order)).
Proof.
  intros H He ((_ & Hab & _) & Hv & Hn & Hs). unfold ctor_table_size in He.
  unfold table_ps. apply (proj2 (all_agree_app _ _ _)). split; [|apply (proj2 (all_agree_app _ _ _)); split;
    [|apply (proj2 (all_agree_app _ _ _)); split]].
  - change (le_bytes argc 4) with [byte_of argc 0; byte_of argc 1; byte_of argc 2; byte_of argc 3].
    rewrite !byte_ps_cons. cbn [all_agree fst snd].
    refine (conj _ (conj _ (conj _ (conj _ I)))).
    all: apply (lv_byte _ _ reg); [exact H | lia | lia | rewrite Hab; [reflexivity | lia]].
  - apply (lv_ptr_cell _ _ reg); [exact H | lia | lia | exact Hv].
  - apply (lv_ptr_cell _ _ reg); [exact H | lia | lia | exact Hn].
  - apply (ptrs_agree _ _ reg); [exact H | lia | unfold ctor_ptrs; rewrite length_map; lia |].
    intros i p Hi. unfold ctor_ptrs in Hi. rewrite nth_error_map in Hi.
    destruct (nth_error order i) as [f|] eqn:Ef; [|discriminate]. injection Hi as <-.
    destruct (Hs i f Ef) as (p & Hl & Hp). unfold ctor_ptr. rewrite Hl. exact Hp.
Qed.

(** A run of stored pointers lies at its offsets. *)
Lemma ptrs_ranged b o ps : ranged b o (o + 8 * Z.of_nat (length ps)) (ptrs_ps b o ps).
Proof.
  revert o. induction ps as [|p ps IH]; intros o; cbn [ptrs_ps length]; [apply List.Forall_nil|].
  apply ranged_app.
  - apply (ranged_widen _ o (o + 8)); [lia | lia | apply ptr_cell_ranged].
  - apply (ranged_widen _ (o + 8) (o + 8 + 8 * Z.of_nat (length ps))); [lia | lia | apply IH].
Qed.

(** A run of stored pointers has no duplicate keys. *)
Lemma ptrs_nodup b o ps : NoDup (ptrs_ps b o ps).*1.
Proof.
  revert o. induction ps as [|p ps IH]; intros o; cbn [ptrs_ps]; [apply NoDup_nil_2|].
  apply nodup_join; [apply ptr_cell_nodup | apply IH |].
  exact (ranged_apart _ _ _ _ _ _ _ (ptr_cell_ranged b o _) (ptrs_ranged b (o + 8) ps) ltac:(lia)).
Qed.

(** The table's pieces lie in the table and have no duplicate keys. *)
Lemma table_ranged tb argc argv env ps :
  ranged tb 0 (24 + 8 * Z.of_nat (length ps)) (table_ps tb argc argv env ps).
Proof.
  unfold table_ps. apply ranged_app; [|apply ranged_app; [|apply ranged_app]].
  - apply (ranged_widen _ 0 (0 + Z.of_nat (length (le_bytes argc 4)))); [lia | rewrite length_le_bytes; lia |].
    apply bytes_ranged.
  - apply (ranged_widen _ 8 (8 + 8)); [lia | lia | apply ptr_cell_ranged].
  - apply (ranged_widen _ 16 (16 + 8)); [lia | lia | apply ptr_cell_ranged].
  - apply (ranged_widen _ 24 (24 + 8 * Z.of_nat (length ps))); [lia | lia | apply ptrs_ranged].
Qed.

Lemma table_nodup tb argc argv env ps : NoDup (table_ps tb argc argv env ps).*1.
Proof.
  unfold table_ps.
  assert (B : ranged tb 0 4 (byte_ps tb 0 (le_bytes argc 4))).
  { apply (ranged_widen _ 0 (0 + Z.of_nat (length (le_bytes argc 4)))); [lia | rewrite length_le_bytes; lia |].
    apply bytes_ranged. }
  apply nodup_join; [apply bytes_nodup | apply nodup_join; [apply ptr_cell_nodup | apply nodup_join |] |].
  - apply ptr_cell_nodup.
  - apply ptrs_nodup.
  - exact (ranged_apart _ _ _ _ _ _ _ (ptr_cell_ranged tb 16 _) (ptrs_ranged tb 24 ps) ltac:(lia)).
  - apply (ranged_apart tb 8 (8 + 8) _ 16 (24 + 8 * Z.of_nat (length ps))); [apply ptr_cell_ranged | | lia].
    apply ranged_app; [apply (ranged_widen _ 16 (16 + 8)); [lia | lia | apply ptr_cell_ranged]|].
    apply (ranged_widen _ 24 (24 + 8 * Z.of_nat (length ps))); [lia | lia | apply ptrs_ranged].
  - apply (ranged_apart tb 0 4 _ 8 (24 + 8 * Z.of_nat (length ps))); [exact B | | lia].
    apply ranged_app; [apply (ranged_widen _ 8 (8 + 8)); [lia | lia | apply ptr_cell_ranged]|].
    apply ranged_app; [apply (ranged_widen _ 16 (16 + 8)); [lia | lia | apply ptr_cell_ranged]|].
    apply (ranged_widen _ 24 (24 + 8 * Z.of_nat (length ps))); [lia | lia | apply ptrs_ranged].
Qed.

(** ## The first heap

    A proof can own two pieces of memory separately only if they are
    different pieces. So before the four parts can be owned side by
    side, we must show that none of them names a piece that another
    one names. *)

(** A list that shares no key with two lists shares none with their
    join. *)
Lemma apart_app (L1 L2 L3 : list (piece * pval)) :
  (forall l, l ∈ L1.*1 -> l ∉ L2.*1) -> (forall l, l ∈ L1.*1 -> l ∉ L3.*1) -> forall l, l ∈ L1.*1 -> l ∉ (L2 ++ L3)%list.*1.
Proof.
  intros A B l H Hin. rewrite fmap_app in Hin. apply elem_of_app in Hin as [Hin|Hin]; [exact (A l H Hin) | exact (B l H Hin)].
Qed.

(** This list is the first heap of a run: the image's list L, the
    table, the runtime's objects and the startup key. *)
Definition start_ps (L : list (piece * pval)) (m : mem) (g : list (name * ptr)) (tb argc : Z)
    (argv env : Z * list (Z * list Z)) (av : Z) (aps : list (Z * Z)) (order : list name) (k : Z) :
    list (piece * pval) :=
  (L ++ table_ps tb argc (mkPtr argv.1 (Obj argv.1)) (mkPtr env.1 (Obj env.1)) (ctor_ptrs g order) ++
   start_heap_ps m argv env av aps ++ start_key_ps k)%list.

(** Every start state gives a first heap that the safety theorem can
    begin from. For that, the image's list L must match both the image
    and the start memory, name each piece once, stay off the table's
    bytes and hold no ghost key. The table must be a live global of the
    image that is large enough for its constructors. Every other fact
    comes from [start_state]. *)
Theorem start_ps_ok m0 m g w0 w tb treg tsize argc argv env av aps order L k :
  keeps_image m0 m tb tsize -> no_heap_regions m0 ->
  live_at m0 tb treg -> r_kind treg <> Heap -> tb + ctor_table_size (length order) <= r_end treg ->
  string_array m argv.1 argv.2 -> string_array m env.1 env.2 -> auxv_array m av aps ->
  List.NoDup (fst argv :: fst env :: av :: map fst (snd argv) ++ map fst (snd env)) ->
  ctor_table m g tb argc (mkPtr argv.1 (Obj argv.1)) (mkPtr env.1 (Obj env.1)) order ->
  start_os g w0 w ->
  all_agree m0 L -> all_agree m L -> NoDup L.*1 -> Forall (fun lv => piece_off tb lv.1) L ->
  (forall l, l ∈ (start_key_ps k).*1 -> l ∉ L.*1) ->
  let H := start_ps L m g tb argc argv env av aps order k in
  NoDup H.*1 /\ agrees m (list_to_map H) /\ os_wi_start w0 k m w (list_to_map H).
Proof.
  intros Hk Hn Ht Htk Hte Ha He Hv Hd Hc Ho A0 A Ln Loff Lk H.
  pose proof Hk as (Hr & _).
  assert (Lt : live_at m tb treg) by (split; [exact (Hr _ _ (proj1 Ht)) | exact (proj2 Ht)]).
  set (T := table_ps tb argc (mkPtr argv.1 (Obj argv.1)) (mkPtr env.1 (Obj env.1)) (ctor_ptrs g order)).
  set (S := start_heap_ps m argv env av aps).
  assert (Tr : ranged tb 0 (24 + 8 * Z.of_nat (length (ctor_ptrs g order))) T) by apply table_ranged.
  (* The table's pieces are bytes and capability slots of tb. *)
  assert (Tb : Forall (fun lv => match lv.1 with PByte b _ | PAux b _ => b = tb | _ => False end) T).
  { apply (Forall_impl _ _ _ Tr). intros [l v] [E R]. cbn in E, R |- *.
    destruct l as [b|b o|b o|n]; cbn in E, R; try discriminate; try lia; injection E as ->; reflexivity. }
  assert (Nd : NoDup H.*1).
  { unfold H, start_ps. fold T S. apply nodup_join; [exact Ln | apply nodup_join; [apply table_nodup |
      apply nodup_join; [exact (start_heap_nodup _ _ _ _ _ Hd) | cbn; apply NoDup_singleton |
        intros l Hl Hin; exact (start_key_heap_apart k m argv env av aps l Hin Hl)] |] |].
    - (* The table is not on the heap, and it is not the key. *)
      apply apart_app.
      + apply (keys_apart (fun l => piece_obj l = Some tb)
                          (fun l => exists b, piece_obj l = Some b /\ In b (start_bases argv env av))).
        * apply (Forall_impl _ _ _ Tr). intros lv [E _]. exact E.
        * apply start_heap_objs.
        * intros l E (b & E' & Hin). rewrite E in E'. injection E' as <-.
          destruct (start_bases_heap _ _ _ _ _ Ha He Hv tb Hin) as (n & reg & [E1 _] & Hkind & _).
          rewrite (proj1 Lt) in E1. injection E1 as <-. exact (Htk Hkind).
      + apply (keys_apart (fun l => piece_obj l = Some tb) (fun l => piece_obj l = None)).
        * apply (Forall_impl _ _ _ Tr). intros lv [E _]. exact E.
        * apply List.Forall_cons; [reflexivity | apply List.Forall_nil].
        * intros l E E'. rewrite E in E'. discriminate.
    - (* The image's list keeps off the table, the heap and the key. *)
      apply apart_app; [|apply apart_app].
      + apply (keys_apart (fun l => piece_off tb l)
          (fun l => match l with PByte b _ | PAux b _ => b = tb | _ => False end) _ _ Loff Tb).
        intros l0 P Q. destruct l0; cbn in P, Q; tauto.
      + exact (image_heap_apart _ _ _ _ _ _ _ _ _ Hk Hn A0 Ha He Hv).
      + intros l Hl Hin. exact (Lk l Hin Hl). }
  split; [exact Nd|]. split.
  - apply all_agree_map. unfold H, start_ps. fold T S.
    apply (proj2 (all_agree_app _ _ _)). split; [exact A|].
    apply (proj2 (all_agree_app _ _ _)). split.
    + apply (table_agree _ _ _ treg); [exact Lt | exact Hte | exact Hc].
    + apply (proj2 (all_agree_app _ _ _)). split; [exact (start_heap_agree _ _ _ _ _ Ha He Hv) |].
      apply start_key_agree.
  - apply (start_os_wi g); [exact Ho|]. apply elem_of_list_to_map_1; [exact Nd|].
    unfold H, start_ps. apply elem_of_app. right. apply elem_of_app. right. apply elem_of_app. right.
    apply list_elem_of_singleton. reflexivity.
Qed.

(** ## Owning the first heap

    At the start of the run the proof owns every piece of the first
    heap, one at a time. Startup's contracts ask for larger shapes, such
    as a whole stored pointer or a whole array. This section groups the
    pieces into those shapes. *)

Section own.
Context `{!gen_heapGS piece pval Σ}.

(** A run of stored pointers is one [pcell] per pointer. *)
Lemma ptrs_own b o ps :
  pts (ptrs_ps b o ps) ⊢ [∗ list] i ↦ p ∈ ps, pcell b (o + 8 * Z.of_nat i) p.
Proof using Type.
  revert o. induction ps as [|p ps IH]; intros o; cbn [ptrs_ps]; [auto|].
  rewrite pts_app IH big_sepL_cons. iIntros "[H Hs]". rewrite Z.mul_0_r Z.add_0_r. iFrame "H".
  iApply (big_sepL_mono with "Hs"). intros i q _. cbn beta.
  by replace (o + 8 + 8 * Z.of_nat i) with (o + 8 * Z.of_nat (S i)) by lia.
Qed.

(** The table's pieces are the count's low bytes and one [pcell] per
    stored pointer. *)
Lemma table_own tb argc argv env ps :
  pts (table_ps tb argc argv env ps) ⊢
  bytes tb 0 (le_bytes argc 4) ∗ pcell tb 8 argv ∗ pcell tb 16 env ∗
  [∗ list] i ↦ p ∈ ps, pcell tb (24 + 8 * Z.of_nat i) p.
Proof using Type.
  rewrite /table_ps !pts_app ptrs_own. auto.
Qed.

(** Owning every piece of the first heap means owning the image's
    list, the table's words, argv, environ, the auxiliary vector and the
    startup key, each on its own. *)
Lemma start_ps_own L m g tb argc argv env av aps order k :
  NoDup (start_ps L m g tb argc argv env av aps order k).*1 ->
  ([∗ map] l ↦ v ∈ list_to_map (start_ps L m g tb argc argv env av aps order k), pointsto l (DfracOwn 1) v) ⊢
  pts L ∗
  (bytes tb 0 (le_bytes argc 4) ∗ pcell tb 8 (mkPtr argv.1 (Obj argv.1)) ∗ pcell tb 16 (mkPtr env.1 (Obj env.1)) ∗
   [∗ list] i ↦ p ∈ ctor_ptrs g order, pcell tb (24 + 8 * Z.of_nat i) p) ∗
  pts (array_ps m argv) ∗ pts (array_ps m env) ∗
  (live av (reg_of m av) ∗ auxv_cells av 0 aps ∗ icell av (16 * Z.of_nat (length aps)) 0) ∗
  pointsto (PName k) (DfracOwn 1) (start_ghost (mkPtr 0 CNone) false false).
Proof using Type.
  intros Nd. rewrite (pts_map _ Nd) /start_ps (pts_app L) (pts_app (table_ps _ _ _ _ _))
    (pts_app (start_heap_ps _ _ _ _ _)) /start_heap_ps (pts_app (array_ps m argv)) (pts_app (array_ps m env))
    table_own auxv_own.
  iIntros "($ & $ & ($ & $ & $) & H)". iEval (rewrite /start_key_ps /pts big_sepL_singleton) in "H". iExact "H".
Qed.

End own.
