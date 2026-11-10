(** The ghost heap of the program logic (Logic.v): what each piece of
    memory holds, when a ghost heap of pieces agrees with the memory, and
    the ownership of a list of pieces in Iris's [gen_heap]. Taken from
    the logic spike's IrisHeap.v, which keeps the parts about its own
    language of whole configurations.

    The ghost heap is Iris's [gen_heap] from Pieces.v's [piece] to a
    [pval]: an object's life with its region, a byte, or a capability in
    an aux slot. It [agrees] with a memory when a life token names a
    live object, and a byte or aux piece names a registered object and,
    while that object is live, is inside its bounds and holds what the
    memory holds there, an aux slot up to the collector's rewriting of
    dead capabilities ([agree_piece]). Since every piece names a
    registered object, a fresh base has no pieces yet.

    The lemmas say what keeps agreement: a [[poll|safepoint]]
    ([agree_piece_safepoint]), a store into a live object, which keeps
    every piece it does not write ([frame_ok], [cell_store_ok],
    [ptr_store_ok]), and an allocation, whose new pieces agree
    ([obj_ps_agree]) and which keeps the old ones
    ([agree_piece_allocated]). [pts] ps owns the pieces ps;
    [pts_lookup], [pts_update] and [pts_alloc] read, write and allocate
    them against the authoritative heap. Nothing here is about one
    runtime or one language. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime ExternalCalls Pieces.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Pieces and their values *)

(** What a piece holds: an object's life with its region, a byte, the
    capability in an aux slot, or, for a life token, the end of the
    object's life: a [free] turns a [VLive] token into [VFreed], since
    the ghost heap has no way to give a piece up. A name holds the
    pointer p and the text t of the string the world lends; the
    memory has nothing to say about it, and the world interpretation
    ties it to the world. A codec, under a name key, holds the world's
    multibyte codec, which the memory has nothing to say about either. *)
Inductive pval : Type :=
  VLive (reg : region) | VByte (v : Z) | VAux (c : cap) | VFreed | VName (p : ptr) (t : list Z)
  | VCodec (c : term).

(** Pieces have decidable equality. *)
Instance piece_eq_dec : EqDecision piece.
Proof. solve_decision. Qed.

(** Pieces are countable, by an injection into sums of integers. *)
Instance piece_countable : Countable piece.
Proof.
  refine (inj_countable'
    (fun p => match p with
              | PLive b => inl b
              | PByte b o => inr (inl (b, o))
              | PAux b o => inr (inr (inl (b, o)))
              | PName k => inr (inr (inr k))
              end)
    (fun t => match t with
              | inl b => PLive b
              | inr (inl (b, o)) => PByte b o
              | inr (inr (inl (b, o))) => PAux b o
              | inr (inr (inr k)) => PName k
              end) _).
  by intros [].
Qed.

(** ## Agreement with the memory *)

(** The object of identity b is registered in m, live or freed. *)
Definition registered (m : mem) (b : Z) : Prop := object_region b (m_regions m) <> None.

(** While the object b is live in m, offset o is inside its bounds and
    P holds. *)
Definition in_live (m : mem) (b o : Z) (P : Prop) : Prop :=
  forall reg, object_region b (m_regions m) = Some reg -> r_life reg = Live ->
    0 <= o /\ b + o < r_end reg /\ P.

(** The piece l with the value v agrees with the memory m: a life token
    names a live object with its region, or, ended, a registered one; a byte or aux piece names a
    registered object and, while it is live, is inside its bounds and
    holds the memory's byte, or the capability up to [aux_holds]; a
    name or a codec agrees with every memory. *)
Definition agree_piece (m : mem) (l : piece) (v : pval) : Prop :=
  match l, v with
  | PLive b, VLive reg => live_at m b reg
  | PLive b, VFreed => registered m b
  | PByte b o, VByte x => registered m b /\ in_live m b o (m_bytes m (b + o) = x)
  | PAux b o, VAux c => registered m b /\ in_live m b o (aux_holds m (b + o) c)
  | PName _, VName _ _ => True
  | PName _, VCodec _ => True
  | _, _ => False
  end.

(** Every piece of the ghost heap h agrees with the memory m. *)
Definition agrees (m : mem) (h : gmap piece pval) : Prop :=
  forall l v, h !! l = Some v -> agree_piece m l v.

(** Every piece of the list ps agrees with the memory m. *)
Fixpoint all_agree (m : mem) (ps : list (piece * pval)) : Prop :=
  match ps with
  | [] => True
  | lv :: ps' => agree_piece m lv.1 lv.2 /\ all_agree m ps'
  end.

(** What owning the pieces ps tells a step about the memory m: they
    agree with it, live objects do not overlap, and every object fits
    the address space. *)
Definition owned_facts (ps : list (piece * pval)) (m : mem) : Prop :=
  all_agree m ps /\ live_disjoint m /\ objects_fit (m_regions m).

(** From m to m', every piece whose key is not among ks keeps agreeing:
    a step that writes only the pieces ks. *)
Definition frame_ok (ks : list piece) (m m' : mem) : Prop :=
  forall l v, l ∉ ks -> agree_piece m l v -> agree_piece m' l v.

(** The eight byte pieces of the little-endian x at offset o of the
    object b. *)
Definition cell (b o x : Z) : list (piece * pval) :=
  map (fun i => (PByte b (o + i), VByte (byte_of x i))) [0; 1; 2; 3; 4; 5; 6; 7].

(** The ghost heap h with the pieces ps written over it, the first of a
    key winning. *)
Fixpoint overwrite (ps : list (piece * pval)) (h : gmap piece pval) : gmap piece pval :=
  match ps with
  | [] => h
  | lv :: ps' => <[lv.1 := lv.2]> (overwrite ps' h)
  end.

(** The pieces of a new object of the request q at base: its life, a
    zero byte and an empty aux slot at each offset. *)
Definition obj_ps (base : Z) (q : alloc_req) : list (piece * pval) :=
  (PLive base, VLive (mkRegion base (base + req_extent q) (req_kind q) Live)) ::
  ((fun i => (PByte base i, VByte 0)) <$> seqZ 0 (req_extent q)) ++
  ((fun i => (PAux base i, VAux CNone)) <$> seqZ 0 (req_extent q)).

(** ## Facts about agreement *)

(** A byte store keeps every region. *)
Lemma regions_store_bytes m a s x : m_regions (store_bytes m a s x) = m_regions m.
Proof. reflexivity. Qed.

(** An aux store keeps every region. *)
Lemma regions_store_aux m a c : m_regions (store_aux m a c) = m_regions m.
Proof. reflexivity. Qed.

(** A byte store keeps every aux slot. *)
Lemma aux_store_bytes m a s x : m_aux (store_bytes m a s x) = m_aux m.
Proof. reflexivity. Qed.

(** An aux store changes only its own slot. *)
Lemma aux_store_aux m a c a' : m_aux (store_aux m a c) a' = if a' =? a then c else m_aux m a'.
Proof. reflexivity. Qed.

(** [all_agree] of two lists is [all_agree] of each. *)
Lemma all_agree_app m ps qs : all_agree m (ps ++ qs) <-> all_agree m ps /\ all_agree m qs.
Proof. induction ps as [|lv ps IH]; cbn; [tauto|]. rewrite IH. tauto. Qed.

(** A piece of a list that agrees agrees. *)
Lemma all_agree_elem m ps l v : all_agree m ps -> (l, v) ∈ ps -> agree_piece m l v.
Proof.
  induction ps as [|[l' v'] ps IH]; cbn; intros H Hin.
  - by apply not_elem_of_nil in Hin.
  - apply elem_of_cons in Hin as [[= -> ->] | Hin]; [tauto|]. apply IH; tauto.
Qed.

(** A list agrees if each of its pieces does. *)
Lemma all_agree_intro m ps : (forall l v, (l, v) ∈ ps -> agree_piece m l v) -> all_agree m ps.
Proof.
  induction ps as [|[l v] ps IH]; cbn; intros H; [done|]. split.
  - apply H. apply elem_of_cons. by left.
  - apply IH. intros l' v' Hin. apply H. apply elem_of_cons. by right.
Qed.

(** A cell agrees when each of its eight bytes does. *)
Lemma all_agree_cell m b o x :
  all_agree m (cell b o x) <-> forall i, 0 <= i < 8 -> agree_piece m (PByte b (o + i)) (VByte (byte_of x i)).
Proof.
  unfold cell; cbn [map all_agree fst snd]. split.
  - intros H i Hi.
    assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) as Hc by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; tauto.
  - intros H. repeat (split; [apply H; lia|]). exact I.
Qed.

(** Byte i of a cell is one of its keys. *)
Lemma cell_keys b o x i : 0 <= i < 8 -> PByte b (o + i) ∈ (cell b o x).*1.
Proof.
  intros Hi. apply list_elem_of_In. unfold cell. cbn.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) as Hc by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
    repeat (first [left; reflexivity | right]).
Qed.

(** A piece of memory that agrees names a registered object. *)
Lemma agree_piece_registered m l v : mem_piece l -> agree_piece m l v -> registered m (piece_id l).
Proof.
  destruct l as [b|b o|b o|k], v as [reg|x|c| |q t|cd]; cbn; unfold live_at, registered; try tauto.
  intros _ [E _]. congruence.
Qed.

(** A live object stays live while regions are kept. *)
Lemma live_at_regions m m' b reg : m_regions m' = m_regions m -> live_at m b reg -> live_at m' b reg.
Proof. unfold live_at. intros ->. auto. Qed.

(** Live objects stay apart while regions are kept. *)
Lemma live_disjoint_regions m m' : m_regions m' = m_regions m -> live_disjoint m -> live_disjoint m'.
Proof. intros E Hd b1 r1 b2 r2. unfold live_at. rewrite E. apply Hd. Qed.

(** What a safepoint may do keeps a piece's agreement. *)
Lemma agree_piece_safepoint m m' l v :
  same_regions m m' -> m_bytes m' = m_bytes m -> aux_moves m m' -> agree_piece m l v -> agree_piece m' l v.
Proof.
  intros Hr Hb Ha. pose proof Hr as Hr'. unfold same_regions in Hr'.
  destruct l as [b|b o|b o|k], v as [reg|x|c| |q t|cd]; cbn; try tauto; unfold live_at, registered, in_live;
    rewrite !Hr'; try tauto.
  - rewrite Hb. tauto.
  - intros [Hreg Hin]. split; [exact Hreg|]. intros reg E L.
    destruct (Hin reg E L) as (Ho & He & Hx). split; [exact Ho|]. split; [exact He|].
    exact (aux_holds_moves m m' (b + o) c Hr Ha Hx).
Qed.

(** Two live objects' addresses differ. *)
Lemma live_apart m b reg b' reg' a a' :
  live_disjoint m -> live_at m b reg -> live_at m b' reg' -> b <> b' ->
  b <= a < r_end reg -> b' <= a' < r_end reg' -> a <> a'.
Proof. intros Hd H H' Hne Ha Ha'. destruct (Hd b reg b' reg' H H' Hne); lia. Qed.

(** An 8-byte store inside the live object b, whose bytes are among
    the keys ks, keeps every other piece's agreement. *)
Lemma frame_store_bytes ks m b reg o a x :
  live_disjoint m -> live_at m b reg -> 0 <= o -> b + o + 8 <= r_end reg -> a = b + o ->
  (forall i, 0 <= i < 8 -> PByte b (o + i) ∈ ks) ->
  frame_ok ks m (store_bytes m a 8 x).
Proof.
  intros Hd Hl Ho He -> Hks l v Hn Ha.
  destruct l as [b'|b' o'|b' o'|k], v as [reg'|y|c| |q t|cd]; cbn [agree_piece] in Ha |- *; try contradiction;
    try exact I.
  - exact (live_at_regions _ _ _ _ (regions_store_bytes _ _ _ _) Ha).
  - unfold registered in *. rewrite regions_store_bytes. exact Ha.
  - unfold registered, in_live in *. rewrite !regions_store_bytes.
    destruct Ha as [Hr Hin]. split; [exact Hr|]. intros reg' E L.
    destruct (Hin reg' E L) as (Ho' & He' & Hb). split; [exact Ho'|]. split; [exact He'|].
    rewrite store_bytes_other; [exact Hb|]. intros Hin'.
    destruct (Z.eq_dec b' b) as [->|Hne].
    + apply Hn. replace o' with (o + (o' - o)) by lia. apply Hks. lia.
    + apply (live_apart m b reg b' reg' (b' + o') (b' + o') Hd Hl (conj E L)); [congruence|lia|lia|].
      destruct Hl as [El Ll]. destruct (Hd b reg b' reg' (conj El Ll) (conj E L)); [congruence| |]; lia.
  - unfold registered, in_live, aux_holds in *. rewrite !regions_store_bytes aux_store_bytes. exact Ha.
Qed.

(** An aux store inside the live object b, whose slot is among the keys
    ks, keeps every other piece's agreement. *)
Lemma frame_store_aux ks m b reg o a c :
  live_disjoint m -> live_at m b reg -> 0 <= o -> b + o < r_end reg -> a = b + o -> PAux b o ∈ ks ->
  frame_ok ks m (store_aux m a c).
Proof.
  intros Hd Hl Ho He -> Hk l v Hn Ha.
  destruct l as [b'|b' o'|b' o'|k], v as [reg'|y|c'| |q t|cd]; cbn [agree_piece] in Ha |- *; try contradiction;
    try exact I.
  - exact (live_at_regions _ _ _ _ (regions_store_aux _ _ _) Ha).
  - unfold registered in *. rewrite regions_store_aux. exact Ha.
  - unfold registered, in_live in *. rewrite !regions_store_aux. exact Ha.
  - unfold registered, in_live, aux_holds in *. rewrite !regions_store_aux.
    destruct Ha as [Hr Hin]. split; [exact Hr|]. intros reg' E L.
    destruct (Hin reg' E L) as (Ho' & He' & Hx). split; [exact Ho'|]. split; [exact He'|].
    rewrite aux_store_aux.
    assert (Hne : (b' + o' =? b + o) = false).
    { apply Z.eqb_neq. destruct (Z.eq_dec b' b) as [->|Hne].
      - intros Heq. apply Hn. replace o' with o by lia. exact Hk.
      - destruct Hl as [El Ll]. destruct (Hd b reg b' reg' (conj El Ll) (conj E L)); [congruence| |]; lia. }
    rewrite Hne. exact Hx.
Qed.

(** A change that keeps every region and writes bytes and aux slots
    only inside the live object b, at offsets whose pieces are among
    the keys ks, keeps every other piece's agreement: a byte or aux
    slot of another live object lies outside b, since live objects do
    not overlap. *)
Lemma frame_within ks m m' b reg :
  m_regions m' = m_regions m -> live_disjoint m -> live_at m b reg ->
  (forall a, (b <= a < r_end reg -> PByte b (a - b) ∉ ks) -> m_bytes m' a = m_bytes m a) ->
  (forall a, (b <= a < r_end reg -> PAux b (a - b) ∉ ks) -> m_aux m' a = m_aux m a) ->
  frame_ok ks m m'.
Proof.
  intros Hr Hd Hl Hb Hx l v Hn Ha.
  assert (Hout : forall b' o' reg', live_at m b' reg' -> 0 <= o' -> b' + o' < r_end reg' ->
            b <= b' + o' < r_end reg -> b' = b /\ b' + o' - b = o').
  { intros b' o' reg' Hl' Ho He Hin. destruct (Z.eq_dec b' b) as [->|Hne]; [split; [reflexivity|lia]|].
    exfalso. exact (live_apart m b reg b' reg' (b' + o') (b' + o') Hd Hl Hl' (not_eq_sym Hne) Hin
                      ltac:(lia) eq_refl). }
  destruct l as [b'|b' o'|b' o'|k], v as [reg'|y|c| |q t|cd]; cbn [agree_piece] in Ha |- *; try contradiction;
    try exact I.
  - exact (live_at_regions _ _ _ _ Hr Ha).
  - unfold registered in *. rewrite Hr. exact Ha.
  - unfold registered, in_live in *. rewrite Hr.
    destruct Ha as [Hreg Hin]. split; [exact Hreg|]. intros reg' E L.
    destruct (Hin reg' E L) as (Ho & He & Hy). split; [exact Ho|]. split; [exact He|].
    rewrite Hb; [exact Hy|]. intros Hin'. destruct (Hout b' o' reg' (conj E L) Ho He Hin') as [-> ->].
    exact Hn.
  - unfold registered, in_live, aux_holds in *. rewrite Hr.
    destruct Ha as [Hreg Hin]. split; [exact Hreg|]. intros reg' E L.
    destruct (Hin reg' E L) as (Ho & He & Hy). split; [exact Ho|]. split; [exact He|].
    rewrite Hx; [exact Hy|]. intros Hin'. destruct (Hout b' o' reg' (conj E L) Ho He Hin') as [-> ->].
    exact Hn.
Qed.

(** Framing composes. *)
Lemma frame_ok_trans ks m1 m2 m3 : frame_ok ks m1 m2 -> frame_ok ks m2 m3 -> frame_ok ks m1 m3.
Proof. intros H1 H2 l v Hn Ha. apply H2, H1; assumption. Qed.

(** Framing over fewer keys frames over more. *)
Lemma frame_ok_mono ks ks' m m' : (forall l, l ∈ ks -> l ∈ ks') -> frame_ok ks m m' -> frame_ok ks' m m'.
Proof. intros Hs H l v Hn Ha. apply H; [|exact Ha]. intros Hin. apply Hn, Hs, Hin. Qed.

(** The eight bytes of a cell of the live object b read back as its
    value modulo 2^64. *)
Lemma cell_load m b reg o x a :
  live_at m b reg -> all_agree m (cell b o x) -> a = b + o -> load_bytes m a 8 = x mod 2 ^ 64.
Proof.
  intros [E L] Hc ->. rewrite all_agree_cell in Hc.
  assert (Hagree : forall i, 0 <= i < 8 ->
            m_bytes m (b + o + i) = m_bytes (store_bytes m (b + o) 8 x) (b + o + i)).
  { intros i Hi. rewrite stored_byte; [|exact Hi]. destruct (Hc i Hi) as [_ Hin].
    destruct (Hin reg E L) as (_ & _ & Hb). replace (b + o + i) with (b + (o + i)) by lia. exact Hb. }
  rewrite (load_bytes_agree m (store_bytes m (b + o) 8 x) (b + o) 8); [|lia|exact Hagree].
  rewrite stored_bytes_value; [|lia]. reflexivity.
Qed.

(** An 8-byte store at offset o of the live object b: its cell holds
    the new value, and nothing else changes. *)
Lemma cell_store_ok m b reg o a x :
  live_disjoint m -> live_at m b reg -> 0 <= o -> b + o + 8 <= r_end reg -> a = b + o ->
  all_agree (store_bytes m a 8 x) (cell b o x) /\ frame_ok (cell b o x).*1 m (store_bytes m a 8 x).
Proof.
  intros Hd Hl Ho He Ha. split.
  - apply all_agree_cell. intros i Hi. cbn [agree_piece]. unfold registered, in_live.
    rewrite regions_store_bytes. destruct Hl as [E L]. split; [congruence|].
    intros reg' E' _. rewrite E in E'. injection E' as <-.
    split; [lia|]. split; [lia|]. subst a. replace (b + (o + i)) with (b + o + i) by lia.
    apply stored_byte. exact Hi.
  - eapply frame_store_bytes; [exact Hd|exact Hl|exact Ho|exact He|exact Ha|].
    intros i Hi. apply cell_keys, Hi.
Qed.

(** A pointer store (aux then address bytes, at offset 0) into the live
    object b: its aux slot and first cell hold the pointer, and nothing
    else changes. *)
Lemma ptr_store_ok m b reg a c x :
  live_disjoint m -> live_at m b reg -> b + 8 <= r_end reg -> a = b ->
  m_regions (store_bytes (store_aux m a c) a 8 x) = m_regions m /\
  all_agree (store_bytes (store_aux m a c) a 8 x) ([(PLive b, VLive reg); (PAux b 0, VAux c)] ++ cell b 0 x) /\
  frame_ok ([(PLive b, VLive reg); (PAux b 0, VAux c)] ++ cell b 0 x).*1 m (store_bytes (store_aux m a c) a 8 x).
Proof.
  intros Hd Hl He ->. set (m1 := store_aux m b c).
  assert (Hd1 : live_disjoint m1) by (apply (live_disjoint_regions m); [reflexivity|exact Hd]).
  assert (Hl1 : live_at m1 b reg) by (apply (live_at_regions m); [reflexivity|exact Hl]).
  destruct (cell_store_ok m1 b reg 0 b x Hd1 Hl1 ltac:(lia) ltac:(lia) ltac:(lia)) as [Hc Hf].
  split; [reflexivity|]. split.
  - apply all_agree_app. split; [|exact Hc]. cbn [all_agree fst snd agree_piece].
    split; [|split; [|exact I]].
    + apply (live_at_regions m); [reflexivity|exact Hl].
    + unfold registered, in_live, aux_holds. rewrite regions_store_bytes aux_store_bytes.
      unfold m1. rewrite regions_store_aux aux_store_aux. destruct Hl as [E L].
      split; [congruence|]. intros reg' E' _. rewrite E in E'. injection E' as <-.
      split; [lia|]. split; [lia|]. left. replace (b + 0 =? b) with true; [reflexivity|].
      symmetry. apply Z.eqb_eq. lia.
  - apply (frame_ok_trans _ m m1).
    + apply (frame_store_aux _ m b reg 0); [exact Hd|exact Hl|lia|lia|lia|].
      rewrite fmap_app. apply elem_of_app. left. cbn. apply elem_of_cons. right.
      apply elem_of_cons. left. reflexivity.
    + eapply frame_ok_mono; [|exact Hf]. intros l Hin. rewrite fmap_app. apply elem_of_app.
      right. exact Hin.
Qed.

(** A key of [overwrite] ps h comes from ps, or from h when ps does not
    name it. *)
Lemma lookup_overwrite ps h l v :
  overwrite ps h !! l = Some v -> (l, v) ∈ ps \/ (l ∉ ps.*1 /\ h !! l = Some v).
Proof.
  induction ps as [|[l' v'] ps IH]; cbn.
  - intros H. right. split; [apply not_elem_of_nil | exact H].
  - rewrite lookup_insert. destruct (decide (l' = l)) as [->|Hne].
    + intros [= ->]. left. apply elem_of_cons. by left.
    + intros H. destruct (IH H) as [Hin | [Hn Hh]].
      * left. apply elem_of_cons. by right.
      * right. split; [|exact Hh]. apply not_elem_of_cons. split; [congruence|exact Hn].
Qed.

(** Every piece of a new object at base names base. *)
Lemma obj_ps_id base q l v : (l, v) ∈ obj_ps base q -> piece_id l = base.
Proof.
  unfold obj_ps. intros Hin. apply elem_of_cons in Hin as [[= -> ->] | Hin]; [reflexivity|].
  apply elem_of_app in Hin as [Hin | Hin]; apply list_elem_of_fmap in Hin as (i & [= -> ->] & _);
    reflexivity.
Qed.

(** A new object's pieces are pieces of memory. *)
Lemma obj_ps_mem base q l v : (l, v) ∈ obj_ps base q -> mem_piece l.
Proof.
  unfold obj_ps. intros Hin. apply elem_of_cons in Hin as [[= -> ->] | Hin]; [exact I|].
  apply elem_of_app in Hin as [Hin | Hin]; apply list_elem_of_fmap in Hin as (i & [= -> ->] & _);
    exact I.
Qed.

(** The keys of a new object's pieces are distinct. *)
Lemma obj_ps_nodup base q : NoDup (obj_ps base q).*1.
Proof.
  unfold obj_ps. pose proof (NoDup_seqZ 0 (req_extent q)) as Hl. revert Hl.
  generalize (seqZ 0 (req_extent q)) as ns. intros ns Hl.
  rewrite fmap_cons fmap_app -!list_fmap_compose.
  apply NoDup_cons. split.
  - rewrite elem_of_app !list_elem_of_fmap. intros [(i & Hi & _) | (i & Hi & _)]; discriminate Hi.
  - apply NoDup_app. split; [|split].
    + apply NoDup_fmap_2_strong; [|exact Hl]. intros i j _ _ Hij. by injection Hij.
    + intros l. rewrite !list_elem_of_fmap. intros (i & -> & _) (j & Hj & _). discriminate Hj.
    + apply NoDup_fmap_2_strong; [|exact Hl]. intros i j _ _ Hij. by injection Hij.
Qed.

(** Each piece of a new object at a [fresh] base agrees with the memory
    after the allocation. *)
Lemma obj_ps_agree m q base l v :
  Memory.fresh m q base -> 0 <= req_extent q -> (l, v) ∈ obj_ps base q -> agree_piece (allocated m q base) l v.
Proof.
  intros Hf Hq Hin. destruct Hf as (_ & _ & _ & _ & _ & Hz). unfold obj_ps in Hin.
  apply elem_of_cons in Hin as [[= -> ->] | Hin].
  - cbn [agree_piece]. unfold live_at. rewrite object_region_allocated Z.eqb_refl. split; reflexivity.
  - apply elem_of_app in Hin as [Hin | Hin]; apply list_elem_of_fmap in Hin as (i & [= -> ->] & Hi);
      apply elem_of_seqZ in Hi; cbn [agree_piece]; unfold registered, in_live;
      rewrite object_region_allocated Z.eqb_refl; (split; [discriminate|]);
      intros reg' [= <-] _; cbn [r_end]; (split; [lia|]); (split; [lia|]);
      destruct (Hz (base + i) ltac:(lia)) as [Hb Ha].
    + exact Hb.
    + left. exact Ha.
Qed.

(** A freed capability stays freed after an allocation at a new base. *)
Lemma freed_in_allocated m q base c :
  object_region base (m_regions m) = None -> freed_in (m_regions m) c -> freed_in (m_regions (allocated m q base)) c.
Proof.
  intros Hn (b & reg & Hc & E & L). exists b, reg. split; [exact Hc|]. split; [|exact L].
  rewrite object_region_allocated. destruct (Z.eqb_spec base b) as [<-|]; [congruence|exact E].
Qed.

(** A capability that traps as a freed one still does after an
    allocation at a new base. *)
Lemma traps_as_freed_allocated m q base c :
  object_region base (m_regions m) = None -> traps_as_freed (m_regions m) c ->
  traps_as_freed (m_regions (allocated m q base)) c.
Proof.
  intros Hn H a size r align Hs. rewrite <- (H a size r align Hs). unfold cap_access_res.
  destruct c as [|b|b|f|n]; try reflexivity;
    (rewrite object_region_allocated; destruct (Z.eqb_spec base b) as [<-|]; [|reflexivity]);
    specialize (H a size r align Hs); unfold cap_access_res in H; rewrite Hn in H; discriminate.
Qed.

(** An allocation at a new base keeps every old piece's agreement. *)
Lemma agree_piece_allocated m q base l v :
  object_region base (m_regions m) = None -> agree_piece m l v -> agree_piece (allocated m q base) l v.
Proof.
  intros Hn.
  assert (Ho : forall b, object_region b (m_regions m) <> None ->
            object_region b (m_regions (allocated m q base)) = object_region b (m_regions m)).
  { intros b Hb. rewrite object_region_allocated. destruct (Z.eqb_spec base b) as [<-|]; [contradiction|reflexivity]. }
  destruct l as [b|b o|b o|k], v as [reg|x|c| |p t|cd]; cbn [agree_piece]; try tauto;
    unfold live_at, registered, in_live.
  - intros [E L]. rewrite Ho; [|congruence]. auto.
  - intros Hr. rewrite Ho; exact Hr.
  - intros [Hr Hin]. rewrite Ho; [|exact Hr]. split; [exact Hr | exact Hin].
  - intros [Hr Hin]. rewrite Ho; [|exact Hr]. split; [exact Hr|]. intros reg E L.
    destruct (Hin reg E L) as (Ho' & He & Hx). split; [exact Ho'|]. split; [exact He|].
    destruct Hx as [Hx | [Hf Ht]]; [left; exact Hx|right].
    split; [exact (freed_in_allocated _ _ _ _ Hn Hf) | exact (traps_as_freed_allocated _ _ _ _ Hn Ht)].
Qed.

(** ## Owning pieces *)

Section pts.
Context `{!gen_heapGS piece pval Σ}.

(** Ownership of each piece of the list ps with its value. *)
Definition pts (ps : list (piece * pval)) : iProp Σ := [∗ list] lv ∈ ps, pointsto (fst lv) (DfracOwn 1) (snd lv).

(** Owning two lists of pieces is owning their concatenation. *)
Lemma pts_app ps qs : pts (ps ++ qs) ⊣⊢ pts ps ∗ pts qs.
Proof. by rewrite /pts big_sepL_app. Qed.

(** Owned pieces are in the authoritative heap. *)
Lemma pts_lookup h ps : gen_heap_interp h -∗ pts ps -∗ ⌜forall l v, (l, v) ∈ ps -> h !! l = Some v⌝.
Proof.
  induction ps as [|[l v] ps IH]; iIntros "Hh Hps".
  - iPureIntro. intros l v Hin. by apply not_elem_of_nil in Hin.
  - rewrite /pts /=. iDestruct "Hps" as "[Hl Hps]".
    iDestruct (gen_heap_valid with "Hh Hl") as %Hl.
    iDestruct (IH with "Hh Hps") as %Hps. iPureIntro.
    intros l' v' Hin. apply elem_of_cons in Hin as [[= -> ->] | Hin]; auto.
Qed.

(** Owned pieces can be given new values with the same keys. *)
Lemma pts_update h ps ps' : ps'.*1 = ps.*1 ->
  gen_heap_interp h -∗ pts ps ==∗ gen_heap_interp (overwrite ps' h) ∗ pts ps'.
Proof.
  revert ps'. induction ps as [|[l v] ps IH]; intros [|[l' v'] ps'] Hk; try discriminate Hk.
  - iIntros "Hh _". iModIntro. iFrame. by rewrite /pts.
  - cbn in Hk. injection Hk as -> Hk. iIntros "Hh Hps". rewrite /pts /=.
    iDestruct "Hps" as "[Hl Hps]".
    iMod (IH ps' Hk with "Hh Hps") as "[Hh Hps]".
    iMod (gen_heap_update with "Hh Hl") as "[Hh Hl]". iModIntro. iFrame.
Qed.

(** Pieces with distinct keys, none in the heap, can be allocated. *)
Lemma pts_alloc h ps : NoDup ps.*1 -> (forall l v, (l, v) ∈ ps -> h !! l = None) ->
  gen_heap_interp h ==∗ gen_heap_interp (overwrite ps h) ∗ pts ps.
Proof.
  induction ps as [|[l v] ps IH]; intros Hnd Hfr.
  - iIntros "Hh". iModIntro. iFrame. by rewrite /pts.
  - cbn in Hnd. apply NoDup_cons in Hnd as [Hn Hnd]. iIntros "Hh".
    iMod (IH Hnd with "Hh") as "[Hh Hps]".
    { intros l' v' Hin. apply (Hfr l' v'). apply elem_of_cons. by right. }
    iMod (gen_heap_alloc _ l v with "Hh") as "(Hh & Hl & _)".
    { destruct (overwrite ps h !! l) as [v'|] eqn:E; [|reflexivity].
      destruct (lookup_overwrite _ _ _ _ E) as [Hin | [_ Hh]].
      - exfalso. apply Hn. exact (list_elem_of_fmap_2 fst _ (l, v') Hin).
      - rewrite (Hfr l v) in Hh; [discriminate|]. apply elem_of_cons. by left. }
    iModIntro. rewrite /pts /=. iFrame.
Qed.

End pts.
