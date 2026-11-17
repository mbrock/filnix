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
From Nanofil Require Import Values Memory Runtime Pieces Heap.
From Glibc Require Import StartState.
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
