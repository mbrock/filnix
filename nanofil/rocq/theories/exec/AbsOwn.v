(** The program logic owns memory as a list of pieces: one piece for an
    object's lifetime, one for each byte and one for each shadow slot.
    The checker's proofs in [AbsMem](AbsMem.v) and [AbsStep](AbsStep.v)
    speak about a memory directly, through the predicate [holds]. This
    module connects the two views. It lists the pieces of the objects
    that a state owns, and it shows that a memory agrees with those
    pieces exactly when the objects hold their contents. It also shows
    that a store into one object satisfies what the program logic asks
    of a write. *)

From stdpp Require Import list.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap StringLogic MemLogic
  AbsRun AbsDen AbsMem AbsStep.
Import ListNotations.
Open Scope Z_scope.

(** * The pieces of a state *)

(** An object with contents is owned whole: its lifetime, all its
    bytes and all its shadow slots. *)
Definition place_ps (pl : place) (xs : list Z) (cs : list cap) : list (piece * pval) :=
  block_ps (pl_base pl) (pl_reg pl) 0 xs cs.

(** The pieces of a state are the pieces of every object that has
    contents, each at the place with its number. *)
Fixpoint all_ps (B : list place) (X : cont) : list (piece * pval) :=
  match B, X with
  | pl :: B', Some (xs, cs) :: X' => place_ps pl xs cs ++ all_ps B' X'
  | _ :: B', None :: X' => all_ps B' X'
  | _, _ => []
  end.

Lemma lookup_nth_error {A : Type} (l : list A) i : l !! i = nth_error l i.
Proof. revert i. induction l as [|x l IH]; intros [|i]; cbn; auto. Qed.

(** * Agreement with a memory *)

Lemma place_ps_holds m pl xs cs : all_agree m (place_ps pl xs cs) -> holds m pl xs cs.
Proof.
  unfold place_ps, block_ps. cbn [all_agree fst snd agree_piece]. intros [Hl Ha].
  apply all_agree_app in Ha as [Hx Hc]. split; [exact Hl|]. split.
  - intros j x Hj. rewrite <- lookup_nth_error in Hj.
    destruct (byte_ps_agree m _ _ 0 xs j x Hl Hx Hj) as (H1 & H2 & H3). rewrite Z.add_0_l in *. auto.
  - intros j c Hj. rewrite <- lookup_nth_error in Hj.
    assert (Hin : (PAux (pl_base pl) (0 + Z.of_nat j), VAux c) ∈ aux_ps (pl_base pl) 0 cs).
    { apply list_elem_of_lookup. exists j. unfold aux_ps. apply lookup_zip_with_Some.
      exists (0 + Z.of_nat j), c. split; [reflexivity|]. split; [|exact Hj]. apply lookup_seqZ.
      split; [reflexivity|]. apply lookup_lt_Some in Hj. lia. }
    destruct (all_agree_elem _ _ _ _ Hc Hin) as [_ Hlive]. destruct Hl as [E L].
    destruct (Hlive _ E L) as (_ & H2 & H3). rewrite Z.add_0_l in *. auto.
Qed.

Lemma holds_place_ps m pl xs cs : holds m pl xs cs -> all_agree m (place_ps pl xs cs).
Proof.
  intros (Hl & Hx & Hc). unfold place_ps, block_ps. cbn [all_agree fst snd agree_piece]. split; [exact Hl|].
  assert (Hreg : registered m (pl_base pl)) by (unfold registered; destruct Hl as [E _]; rewrite E; discriminate).
  assert (Hreg' : forall reg, object_region (pl_base pl) (m_regions m) = Some reg -> reg = pl_reg pl)
    by (intros reg E; destruct Hl as [E' _]; congruence).
  apply all_agree_app. split; apply all_agree_intro; intros l v Hin.
  - apply byte_ps_elem in Hin as (i & x & Hi & -> & ->). rewrite lookup_nth_error in Hi.
    destruct (Hx i x Hi) as [H1 H2]. split; [exact Hreg|]. intros reg E L. rewrite (Hreg' reg E).
    rewrite Z.add_0_l. split; [lia|]. split; assumption.
  - apply aux_ps_elem in Hin as (i & c & Hi & -> & ->). rewrite lookup_nth_error in Hi.
    destruct (Hc i c Hi) as [H1 H2]. split; [exact Hreg|]. intros reg E L. rewrite (Hreg' reg E).
    rewrite Z.add_0_l. split; [lia|]. split; assumption.
Qed.

(** A memory that agrees with the pieces of a state holds the contents
    of every object of the state. *)
Lemma all_ps_mholds m : forall B X, all_agree m (all_ps B X) -> mholds B X m.
Proof.
  induction B as [|pl B IH]; intros X Ha i pl' xs cs Hp Hx; [destruct i; discriminate|].
  destruct X as [|[[xs0 cs0]|] X]; [destruct i; discriminate| |]; cbn [all_ps] in Ha.
  - apply all_agree_app in Ha as [H1 H2]. destruct i; cbn [nth_error] in *.
    + injection Hp as <-. injection Hx as <- <-. apply place_ps_holds. exact H1.
    + exact (IH X H2 i pl' xs cs Hp Hx).
  - destruct i; cbn [nth_error] in *; [discriminate | exact (IH X Ha i pl' xs cs Hp Hx)].
Qed.
(** * Stores

    A store that [AbsStep](AbsStep.v) describes by [writes] changes
    bytes and shadow slots only inside one owned object. The program
    logic asks three things of such a write, and they follow. *)
Lemma writes_facts m m' pl xs cs xs' cs' :
  live_disjoint m -> holds m pl xs cs -> length xs' = length xs -> length cs' = length cs ->
  writes m m' pl xs cs xs' cs' ->
  kept m m' /\ all_agree m' (place_ps pl xs' cs') /\ frame_ok (place_ps pl xs' cs').*1 m m'.
Proof.
  intros Hd (Hl & Hx & Hc) Lx Lc (Hr & Hh & Hb & Ha).
  assert (Bx : forall a, pl_base pl <= a < pl_base pl + Z.of_nat (length xs) -> a < r_end (pl_reg pl)).
  { intros a Ha'. destruct (nth_error xs (Z.to_nat (a - pl_base pl))) as [x|] eqn:E.
    - destruct (Hx _ x E) as [H _]. lia.
    - apply nth_error_None in E. lia. }
  assert (Bc : forall a, pl_base pl <= a < pl_base pl + Z.of_nat (length cs) -> a < r_end (pl_reg pl)).
  { intros a Ha'. destruct (nth_error cs (Z.to_nat (a - pl_base pl))) as [c|] eqn:E.
    - destruct (Hc _ c E) as [H _]. lia.
    - apply nth_error_None in E. lia. }
  split; [|split; [exact (holds_place_ps m' pl xs' cs' Hh)|]].
  - split.
    + intros b reg' E. rewrite Hr in E. exists reg'. auto.
    + intros a Hout. split; [apply Hb | apply Ha]; intros Hin; apply Hout;
        exists (pl_base pl), (pl_reg pl); (split; [exact (proj1 Hl)|]); [specialize (Bx a Hin) | specialize (Bc a Hin)]; lia.
  - apply (frame_within _ m m' (pl_base pl) (pl_reg pl) Hr Hd Hl).
    + intros a H. apply Hb. intros Hin. apply H; [specialize (Bx a Hin); lia|].
      unfold place_ps, block_ps. cbn [fmap list_fmap fst]. apply elem_of_cons. right. rewrite fmap_app.
      apply elem_of_app. left. replace (a - pl_base pl) with (0 + (a - pl_base pl)) by lia. apply byte_ps_key. lia.
    + intros a H. apply Ha. intros Hin. apply H; [specialize (Bc a Hin); lia|].
      unfold place_ps, block_ps. cbn [fmap list_fmap fst]. apply elem_of_cons. right. rewrite fmap_app.
      apply elem_of_app. right. replace (a - pl_base pl) with (0 + (a - pl_base pl)) by lia. apply aux_ps_key. lia.
Qed.

(** * Allocation

    When the program allocates memory, it receives an object filled
    with zero bytes. The program logic and the checker describe that
    object in two ways, and this lemma shows that the two
    descriptions are the same list of pieces. *)
Lemma repeat_replicate {A : Type} (x : A) n : repeat x n = replicate n x.
Proof. induction n as [|n IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma alloc_place_ps al n base :
  0 <= n ->
  obj_ps base (heap_req al n) =
  place_ps (mkPlace base (mkRegion base (base + (n + 15) / 16 * 16) Heap Live) false)
           (repeat 0 (Z.to_nat ((n + 15) / 16 * 16))) (repeat CNone (Z.to_nat ((n + 15) / 16 * 16))).
Proof.
  intros Hn. assert (Hex : 0 <= (n + 15) / 16 * 16) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia).
  unfold obj_ps, place_ps, block_ps. cbn [pl_base pl_reg heap_req req_extent req_kind].
  rewrite !repeat_replicate, byte_ps_replicate, aux_ps_replicate, Z2Nat.id by exact Hex. reflexivity.
Qed.

(** * Lists of pieces *)

Lemma all_ps_nil_r B : all_ps B [] = [].
Proof. destruct B; reflexivity. Qed.

Lemma all_ps_app B X B1 X1 :
  length X = length B -> all_ps (B ++ B1) (X ++ X1) = all_ps B X ++ all_ps B1 X1.
Proof.
  revert X. induction B as [|pl B IH]; intros [|x X] HL; try discriminate; [reflexivity|].
  injection HL as HL. cbn [app all_ps]. rewrite (IH X HL). destruct x as [[xs cs]|]; [|reflexivity].
  rewrite app_assoc. reflexivity.
Qed.

Lemma all_ps_firstn n : forall B X,
  all_ps B X = all_ps (firstn n B) (firstn n X) ++ all_ps (skipn n B) (skipn n X).
Proof.
  induction n as [|n IH]; intros B X; [reflexivity|].
  destruct B as [|pl B]; [reflexivity|]. destruct X as [|x X]; [cbn [firstn skipn all_ps]; rewrite all_ps_nil_r; reflexivity|].
  cbn [firstn skipn all_ps]. rewrite (IH B X). destruct x as [[xs cs]|]; [|reflexivity].
  rewrite app_assoc. reflexivity.
Qed.
