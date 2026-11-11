(** When a C function writes through a pointer into a struct or array, a
    proof should only have to update its record of that buffer without
    re-checking every other variable in the program. To make that local
    reasoning sound, we pair the machine's physical memory with a logical
    map that records the contents of each memory [piece] from
    [Pieces](Pieces.v). This module defines the values stored in that map,
    proves that stores, allocations, and garbage collection leave untouched
    entries valid, and packages map entries as
    [[separation-logic|separation-logic]] ownership assertions for
    [Logic](Logic.v).

    ## How the logical map matches physical memory

    In Fil-C, an allocated object has bounds and liveness in the region
    table, data bytes in primary memory, and pointer
    [[capability|capabilities]] in its shadow [[aux]] allocation. Our
    logical map records one [pval] for each owned piece: whether an object
    is live or freed, what byte sits at an offset, or what capability sits
    in a shadow slot. The map [agrees] with physical memory when every
    recorded value matches what the machine currently stores for that
    object. Because every entry in the map belongs to an object that has
    already been allocated, a [[fresh]] allocation at an unused base address
    never collides with any existing entry in the map.

    ## Preserving agreement across stores and allocations

    In Fil-C, live objects never overlap in address space. When a C
    instruction writes an 8-byte integer or a pointer into a live object,
    the store only changes the byte and capability entries at those offsets
    and leaves every other entry in the map matching physical memory.
    Likewise, allocating a new object at a fresh address or running a
    garbage-collection [[poll|safepoint]] preserves all existing entries. On
    top of that map, [pts] represents exclusive ownership of a list of
    pieces for reading and writing, while [ptsq] splits ownership into
    read-only shares. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.bi.lib Require Import fractional.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime ExternalCalls Pieces.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Pieces and their values

    Each entry in the separation-logic state pairs a [piece] key from
    [Pieces](Pieces.v) with the value recorded for that piece. This section
    defines the value type [pval] and registers the decidable-equality and
    countability instances that Iris's map library requires for piece keys. *)

(** A [pval] records what a [piece] currently holds in the separation-logic
    state. For memory pieces, [VLive] holds a live object's [[region]],
    [VFreed] marks an object that has been deallocated by `c: free`, [VByte]
    holds a single byte, and [VAux] holds a shadow [[capability]]. For
    non-memory [PName] keys, the remaining constructors record external
    library state—such as a borrowed string, a multibyte codec, a `c: FILE`
    stream, or `c: getopt` state—that the world interpretation ties to the
    external world. *)
Inductive pval : Type :=
  VLive (reg : region) | VByte (v : Z) | VAux (c : cap) | VFreed | VName (p : ptr) (t : list Z)
  | VCodec (c : term) | VStream (p : ptr) (pending : option (Z * list Z))
  | VGetopt (optarg : ptr) (optind : Z) | VStreamOpen (p : ptr).

(** To use [piece] as the key type of a finite map, we first show that
    equality on pieces is decidable. *)
Instance piece_eq_dec : EqDecision piece.
Proof. solve_decision. Qed.

(** To store piece keys in a finite map, we also show that the [piece] type
    is countable by encoding each constructor as a tagged integer pair. *)
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

(** ## Agreement with the memory

    An assertion in separation logic is only useful if the values recorded
    in the [[ghost-state|ghost heap]] match the actual bytes, capabilities,
    and regions in physical memory. This section defines piece-by-piece
    agreement between the ghost heap and physical memory, along with helper
    operations for 8-byte cells, map updates, and newly allocated objects. *)

(** An object identity satisfies [registered] when it has an entry in the
    memory's region table, whether that object is currently live or has
    already been freed. *)
Definition registered (m : mem) (b : Z) : Prop := object_region b (m_regions m) <> None.

(** When an object is freed in Fil-C, its region bounds collapse so later
    accesses trap, even though assertions may still hold leftover byte or
    capability pieces for it. The helper [in_live] requires a byte offset to
    lie within the object's bounds and satisfy a property only while the
    object remains live. *)
Definition in_live (m : mem) (b o : Z) (P : Prop) : Prop :=
  forall reg, object_region b (m_regions m) = Some reg -> r_life reg = Live ->
    0 <= o /\ b + o < r_end reg /\ P.

(** A single piece and its recorded value satisfy [agree_piece] when they
    match physical memory. A live token must name a live object with that
    exact region, a freed token must name a registered object, and a byte or
    capability piece must name a registered object and match the byte or
    capability at that offset while the object is live. Non-memory [PName]
    entries represent external world state and therefore agree with any
    memory. *)
Definition agree_piece (m : mem) (l : piece) (v : pval) : Prop :=
  match l, v with
  | PLive b, VLive reg => live_at m b reg
  | PLive b, VFreed => registered m b
  | PByte b o, VByte x => registered m b /\ in_live m b o (m_bytes m (b + o) = x)
  | PAux b o, VAux c => registered m b /\ in_live m b o (aux_holds m (b + o) c)
  | PName _, VName _ _ => True
  | PName _, VCodec _ => True
  | PName _, VStream _ _ => True
  | PName _, VGetopt _ _ => True
  | PName _, VStreamOpen _ => True
  | _, _ => False
  end.

(** The entire separation-logic map satisfies [agrees] when every piece
    recorded in the map satisfies [agree_piece] in the current physical
    memory. *)
Definition agrees (m : mem) (h : gmap piece pval) : Prop :=
  forall l v, h !! l = Some v -> agree_piece m l v.

(** For a concrete list of piece-value pairs, [all_agree] checks that every
    entry in the list satisfies [agree_piece] in memory. *)
Fixpoint all_agree (m : mem) (ps : list (piece * pval)) : Prop :=
  match ps with
  | [] => True
  | lv :: ps' => agree_piece m lv.1 lv.2 /\ all_agree m ps'
  end.

(** Before stepping a C instruction that reads or writes a buffer, we need
    three facts about physical memory: the buffer's pieces match memory,
    live objects do not overlap, and every object fits in the 64-bit address
    space. The predicate [owned_facts] bundles those three conditions
    together. *)
Definition owned_facts (ps : list (piece * pval)) (m : mem) : Prop :=
  all_agree m ps /\ live_disjoint m /\ objects_fit (m_regions m).

(** When a memory store updates a known list of piece keys, [frame_ok]
    states that every piece outside that modified key list continues to
    agree with the new memory. *)
Definition frame_ok (ks : list piece) (m m' : mem) : Prop :=
  forall l v, l ∉ ks -> agree_piece m l v -> agree_piece m' l v.

(** In 64-bit C code, an 8-byte integer or pointer address at offset o of
    object b spans eight consecutive byte pieces. The helper [cell] pairs
    those eight byte keys with the little-endian bytes of the 64-bit integer
    x. *)
Definition cell (b o x : Z) : list (piece * pval) :=
  map (fun i => (PByte b (o + i), VByte (byte_of x i))) [0; 1; 2; 3; 4; 5; 6; 7].

(** When a step allocates or updates a list of pieces, [overwrite] inserts
    each piece-value pair into the separation-logic map, with earlier
    entries in the list taking precedence. *)
Fixpoint overwrite (ps : list (piece * pval)) (h : gmap piece pval) : gmap piece pval :=
  match ps with
  | [] => h
  | lv :: ps' => <[lv.1 := lv.2]> (overwrite ps' h)
  end.

(** When the allocator creates a new object at a base address, [obj_ps]
    builds its initial piece list: a live token for its region, together
    with a zero byte and an empty capability slot at every byte offset. *)
Definition obj_ps (base : Z) (q : alloc_req) : list (piece * pval) :=
  (PLive base, VLive (mkRegion base (base + req_extent q) (req_kind q) Live)) ::
  ((fun i => (PByte base i, VByte 0)) <$> seqZ 0 (req_extent q)) ++
  ((fun i => (PAux base i, VAux CNone)) <$> seqZ 0 (req_extent q)).

(** ## Facts about agreement

    Whenever a C instruction reads or writes memory, allocates a heap
    object, or passes a garbage-collection [[poll|safepoint]], the proof
    must re-establish agreement between the separation-logic map and
    physical memory. This section proves that stores, allocations, and
    safepoints preserve agreement for all untouched pieces, and provides a
    computable check for verifying initial memory images. *)

(** Writing data bytes into memory leaves the region table unchanged. *)
Lemma regions_store_bytes m a s x : m_regions (store_bytes m a s x) = m_regions m.
Proof. reflexivity. Qed.

(** Writing a capability into shadow memory leaves the region table
    unchanged. *)
Lemma regions_store_aux m a c : m_regions (store_aux m a c) = m_regions m.
Proof. reflexivity. Qed.

(** Writing data bytes into primary memory leaves all shadow capability
    slots unchanged. *)
Lemma aux_store_bytes m a s x : m_aux (store_bytes m a s x) = m_aux m.
Proof. reflexivity. Qed.

(** Writing a capability into shadow memory updates the slot at the target
    address and leaves every other shadow slot unchanged. *)
Lemma aux_store_aux m a c a' : m_aux (store_aux m a c) a' = if a' =? a then c else m_aux m a'.
Proof. reflexivity. Qed.

(** A concatenated list of piece-value pairs satisfies [all_agree] if and
    only if both sublists satisfy [all_agree]. *)
Lemma all_agree_app m ps qs : all_agree m (ps ++ qs) <-> all_agree m ps /\ all_agree m qs.
Proof. induction ps as [|lv ps IH]; cbn; [tauto|]. rewrite IH. tauto. Qed.

(** If a list of piece-value pairs satisfies [all_agree], then every
    individual entry in the list satisfies [agree_piece]. *)
Lemma all_agree_elem m ps l v : all_agree m ps -> (l, v) ∈ ps -> agree_piece m l v.
Proof.
  induction ps as [|[l' v'] ps IH]; cbn; intros H Hin.
  - by apply not_elem_of_nil in Hin.
  - apply elem_of_cons in Hin as [[= -> ->] | Hin]; [tauto|]. apply IH; tauto.
Qed.

(** Conversely, if every entry in a list of piece-value pairs satisfies
    [agree_piece], then the whole list satisfies [all_agree]. *)
Lemma all_agree_intro m ps : (forall l v, (l, v) ∈ ps -> agree_piece m l v) -> all_agree m ps.
Proof.
  induction ps as [|[l v] ps IH]; cbn; intros H; [done|]. split.
  - apply H. apply elem_of_cons. by left.
  - apply IH. intros l' v' Hin. apply H. apply elem_of_cons. by right.
Qed.

(** To verify a fixed initial memory image by computation, we need a
    decidable version of [agree_piece] that avoids quantifying over
    arbitrary regions or collector rewrites. The predicate [checked_piece]
    looks up the object's unique region directly and checks for exact
    capability equality in shadow memory. *)
Definition checked_piece (m : mem) (l : piece) (v : pval) : Prop :=
  match l, v with
  | PLive b, VLive reg => live_at m b reg
  | PByte b o, VByte x =>
    match object_region b (m_regions m) with
    | Some reg => r_life reg = Live -> 0 <= o /\ b + o < r_end reg /\ m_bytes m (b + o) = x
    | None => False
    end
  | PAux b o, VAux c =>
    match object_region b (m_regions m) with
    | Some reg => r_life reg = Live -> 0 <= o /\ b + o < r_end reg /\ m_aux m (b + o) = c
    | None => False
    end
  | PName _, VName _ _ | PName _, VCodec _ | PName _, VGetopt _ _ => True
  | _, _ => False
  end.

(** Any piece that passes the computable [checked_piece] test also satisfies
    the general [agree_piece] relation. *)
Lemma checked_piece_sound m l v : checked_piece m l v -> agree_piece m l v.
Proof.
  destruct l, v; cbn [checked_piece agree_piece]; try tauto.
  - destruct (object_region b (m_regions m)) as [reg|] eqn:E; [|tauto].
    intros H. split; [unfold registered; congruence|].
    intros reg' E' Hlive. rewrite E in E'. injection E' as <-. exact (H Hlive).
  - destruct (object_region b (m_regions m)) as [reg|] eqn:E; [|tauto].
    intros H. split; [unfold registered; congruence|].
    intros reg' E' Hlive. rewrite E in E'. injection E' as <-.
    destruct (H Hlive) as (Ho & Hb & Ha). repeat split; try assumption. left. exact Ha.
Qed.

(** Because [checked_piece] only inspects finite records and integer
    comparisons, it is decidable by computation on any concrete memory
    image. *)
Instance checked_piece_dec m l v : Decision (checked_piece m l v).
Proof.
  pose (eqr := (ltac:(intros x y; change ({x = y} + {x <> y});
    decide equality; try apply Z.eq_dec; decide equality) : EqDecision region)).
  pose (eql := (ltac:(intros x y; change ({x = y} + {x <> y});
    decide equality) : EqDecision life)).
  pose (eqt := (ltac:(intros x y; change ({x = y} + {x <> y});
    destruct (term_eqb x y) eqn:E;
      [left; apply term_eqb_eq; exact E |
       right; intros ->; rewrite term_eqb_refl in E; discriminate]) : EqDecision term)).
  pose (eqc := (ltac:(intros x y; change ({x = y} + {x <> y});
    decide equality; first [apply eqt | apply Z.eq_dec]) : EqDecision cap)).
  destruct l, v; cbn [checked_piece]; try apply _;
    destruct (object_region b (m_regions m)); apply _.
Defined.

(** When a program starts from a concrete initial memory image, checking
    each entry of a piece list by computation suffices to show that the
    entire list matches physical memory. *)
Lemma checked_pieces_all_agree m ps :
  forallb (fun lv => bool_decide (checked_piece m lv.1 lv.2)) ps = true -> all_agree m ps.
Proof.
  intros Hcheck. apply all_agree_intro. intros l v Hin. apply checked_piece_sound.
  rewrite forallb_forall in Hcheck.
  apply (bool_decide_eq_true_1 (checked_piece m l v)).
  apply (Hcheck (l, v)). clear Hcheck. induction Hin; cbn; auto.
Qed.

(** An 8-byte [cell] agrees with memory if and only if each of its eight
    little-endian byte pieces agrees with memory. *)
Lemma all_agree_cell m b o x :
  all_agree m (cell b o x) <-> forall i, 0 <= i < 8 -> agree_piece m (PByte b (o + i)) (VByte (byte_of x i)).
Proof.
  unfold cell; cbn [map all_agree fst snd]. split.
  - intros H i Hi.
    assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) as Hc by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; tauto.
  - intros H. repeat (split; [apply H; lia|]). exact I.
Qed.

(** Each of the eight byte offsets of an 8-byte [cell] appears in the cell's
    key list. *)
Lemma cell_keys b o x i : 0 <= i < 8 -> PByte b (o + i) ∈ (cell b o x).*1.
Proof.
  intros Hi. apply list_elem_of_In. unfold cell. cbn.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) as Hc by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
    repeat (first [left; reflexivity | right]).
Qed.

(** Any memory piece that matches physical memory belongs to an object that
    has already been allocated and registered in the region table. *)
Lemma agree_piece_registered m l v : mem_piece l -> agree_piece m l v -> registered m (piece_id l).
Proof.
  destruct l as [b|b o|b o|k], v as [reg|x|c| |q t|cd|sq sp|ga gi|op]; cbn; unfold live_at, registered; try tauto.
  intros _ [E _]. congruence.
Qed.

(** Any step that leaves the region table unchanged preserves every live
    object and its bounds. *)
Lemma live_at_regions m m' b reg : m_regions m' = m_regions m -> live_at m b reg -> live_at m' b reg.
Proof. unfold live_at. intros ->. auto. Qed.

(** Because the byte bounds of live objects come from the region table, any
    memory step that leaves the region table unchanged keeps all live
    objects non-overlapping. *)
Lemma live_disjoint_regions m m' : m_regions m' = m_regions m -> live_disjoint m -> live_disjoint m'.
Proof. intros E Hd b1 r1 b2 r2. unfold live_at. rewrite E. apply Hd. Qed.

(** At a garbage-collection [[poll|safepoint]], the collector preserves
    regions and data bytes and only sweeps dead capabilities according to
    [aux_moves]. Every piece that agreed with memory before the safepoint
    therefore continues to agree after it. *)
Lemma agree_piece_safepoint m m' l v :
  same_regions m m' -> m_bytes m' = m_bytes m -> aux_moves m m' -> agree_piece m l v -> agree_piece m' l v.
Proof.
  intros Hr Hb Ha. pose proof Hr as Hr'. unfold same_regions in Hr'.
  destruct l as [b|b o|b o|k], v as [reg|x|c| |q t|cd|sq sp|ga gi|op]; cbn; try tauto; unfold live_at, registered, in_live;
    rewrite !Hr'; try tauto.
  - rewrite Hb. tauto.
  - intros [Hreg Hin]. split; [exact Hreg|]. intros reg E L.
    destruct (Hin reg E L) as (Ho & He & Hx). split; [exact Ho|]. split; [exact He|].
    exact (aux_holds_moves m m' (b + o) c Hr Ha Hx).
Qed.

(** Because distinct live objects never overlap in memory, an in-bounds byte
    address of one live object can never equal an in-bounds byte address of
    another live object. *)
Lemma live_apart m b reg b' reg' a a' :
  live_disjoint m -> live_at m b reg -> live_at m b' reg' -> b <> b' ->
  b <= a < r_end reg -> b' <= a' < r_end reg' -> a <> a'.
Proof. intros Hd H H' Hne Ha Ha'. destruct (Hd b reg b' reg' H H' Hne); lia. Qed.

(** Because live objects in Fil-C never overlap, writing an 8-byte integer
    into a live object only alters those eight byte offsets. Every recorded
    piece outside those eight byte keys therefore continues to match
    physical memory after the store. *)
Lemma frame_store_bytes ks m b reg o a x :
  live_disjoint m -> live_at m b reg -> 0 <= o -> b + o + 8 <= r_end reg -> a = b + o ->
  (forall i, 0 <= i < 8 -> PByte b (o + i) ∈ ks) ->
  frame_ok ks m (store_bytes m a 8 x).
Proof.
  intros Hd Hl Ho He -> Hks l v Hn Ha.
  destruct l as [b'|b' o'|b' o'|k], v as [reg'|y|c| |q t|cd|sq sp|ga gi|op]; cbn [agree_piece] in Ha |- *; try contradiction;
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

(** Writing a pointer capability into a shadow slot of a live object only
    alters that single offset in shadow memory. Every recorded piece outside
    that capability key therefore continues to match physical memory. *)
Lemma frame_store_aux ks m b reg o a c :
  live_disjoint m -> live_at m b reg -> 0 <= o -> b + o < r_end reg -> a = b + o -> PAux b o ∈ ks ->
  frame_ok ks m (store_aux m a c).
Proof.
  intros Hd Hl Ho He -> Hk l v Hn Ha.
  destruct l as [b'|b' o'|b' o'|k], v as [reg'|y|c'| |q t|cd|sq sp|ga gi|op]; cbn [agree_piece] in Ha |- *; try contradiction;
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

(** More generally, if a memory operation preserves all object regions and
    only modifies bytes and capabilities at listed offsets inside one live
    object, then every recorded piece outside that list still matches
    physical memory. *)
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
  destruct l as [b'|b' o'|b' o'|k], v as [reg'|y|c| |q t|cd|sq sp|ga gi|op]; cbn [agree_piece] in Ha |- *; try contradiction;
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

(** If two consecutive memory updates each preserve agreement outside a key
    list, their composition also preserves agreement outside that key list. *)
Lemma frame_ok_trans ks m1 m2 m3 : frame_ok ks m1 m2 -> frame_ok ks m2 m3 -> frame_ok ks m1 m3.
Proof. intros H1 H2 l v Hn Ha. apply H2, H1; assumption. Qed.

(** If a memory update preserves agreement outside a smaller list of
    modified keys, it also preserves agreement outside any larger key list
    that contains them. *)
Lemma frame_ok_mono ks ks' m m' : (forall l, l ∈ ks -> l ∈ ks') -> frame_ok ks m m' -> frame_ok ks' m m'.
Proof. intros Hs H l v Hn Ha. apply H; [|exact Ha]. intros Hin. apply Hn, Hs, Hin. Qed.

(** When all eight byte pieces of a [cell] inside a live object agree with
    memory, loading 8 bytes from that offset returns the cell's 64-bit
    integer value modulo 2^64. *)
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

(** Loading the first n bytes (for n at most 8) from an agreeing 8-byte
    [cell] inside a live object returns the low n bytes of the cell's
    integer value. *)
Lemma cell_load_low m b reg o x a n :
  live_at m b reg -> all_agree m (cell b o x) -> a = b + o -> 0 <= n <= 8 ->
  load_bytes m a n = x mod 2 ^ (8 * n).
Proof.
  intros [E L] Hc -> Hn. rewrite all_agree_cell in Hc.
  rewrite (load_bytes_agree m (store_bytes m (b + o) n x) (b + o) n); [|lia|].
  - rewrite stored_bytes_value; [|lia]. rewrite Z.pow_mul_r; [reflexivity|lia|lia].
  - intros i Hi. rewrite stored_byte; [|exact Hi]. destruct (Hc i ltac:(lia)) as [_ Hin].
    destruct (Hin reg E L) as (_ & _ & Hb). replace (b + o + i) with (b + (o + i)); [exact Hb|lia].
Qed.

(** Writing an 8-byte integer at an in-bounds offset of a live object makes
    the updated [cell] agree with the new memory while preserving agreement
    for every piece outside those eight byte keys. *)
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

(** In Fil-C, storing a pointer writes its capability into the shadow slot
    and its 8-byte address into primary memory. When performed at offset 0
    of a live object of at least 8 bytes, that store makes the shadow slot
    and 8-byte cell agree with the new pointer while leaving all other
    pieces unchanged. *)
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

(** Looking up a key in an overwritten map either finds a new pair from the
    written list or, when the key does not appear in that list, returns its
    previous value from the map. *)
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

(** Overwriting a map with the concatenation of two piece lists is the same
    as overwriting with the second list and then the first. *)
Lemma overwrite_app ps qs h : overwrite (ps ++ qs) h = overwrite ps (overwrite qs h).
Proof. induction ps as [|[l v] ps IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

(** Every piece created by [obj_ps] for a newly allocated object has that
    object's base address as its identity. *)
Lemma obj_ps_id base q l v : (l, v) ∈ obj_ps base q -> piece_id l = base.
Proof.
  unfold obj_ps. intros Hin. apply elem_of_cons in Hin as [[= -> ->] | Hin]; [reflexivity|].
  apply elem_of_app in Hin as [Hin | Hin]; apply list_elem_of_fmap in Hin as (i & [= -> ->] & _);
    reflexivity.
Qed.

(** Every piece created by [obj_ps] for a newly allocated object is a memory
    piece rather than a ghost name. *)
Lemma obj_ps_mem base q l v : (l, v) ∈ obj_ps base q -> mem_piece l.
Proof.
  unfold obj_ps. intros Hin. apply elem_of_cons in Hin as [[= -> ->] | Hin]; [exact I|].
  apply elem_of_app in Hin as [Hin | Hin]; apply list_elem_of_fmap in Hin as (i & [= -> ->] & _);
    exact I.
Qed.

(** The initial piece list [obj_ps] of a newly allocated object contains no
    duplicate piece keys. *)
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

(** When a new object is allocated at a [[fresh]] base address, every
    initial piece in [obj_ps] agrees with the post-allocation memory. *)
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

(** Allocating a new object at an unregistered base address leaves all
    existing regions unchanged, so any capability that pointed to a freed
    object before the allocation still points to a freed object afterward. *)
Lemma freed_in_allocated m q base c :
  object_region base (m_regions m) = None -> freed_in (m_regions m) c -> freed_in (m_regions (allocated m q base)) c.
Proof.
  intros Hn (b & reg & Hc & E & L). exists b, reg. split; [exact Hc|]. split; [|exact L].
  rewrite object_region_allocated. destruct (Z.eqb_spec base b) as [<-|]; [congruence|exact E].
Qed.

(** Likewise, if dereferencing a capability already trapped like a freed
    object before a new allocation at an unused base address, it continues
    to trap after the allocation. *)
Lemma traps_as_freed_allocated m q base c :
  object_region base (m_regions m) = None -> traps_as_freed (m_regions m) c ->
  traps_as_freed (m_regions (allocated m q base)) c.
Proof.
  intros Hn H a size r align Hs. rewrite <- (H a size r align Hs). unfold cap_access_res.
  destruct c as [|b|b|f|n]; try reflexivity;
    (rewrite object_region_allocated; destruct (Z.eqb_spec base b) as [<-|]; [|reflexivity]);
    specialize (H a size r align Hs); unfold cap_access_res in H; rewrite Hn in H; discriminate.
Qed.

(** Allocating a new object at an unused base address leaves every
    previously allocated object's bounds, bytes, and capabilities untouched.
    Every recorded piece from before the allocation therefore still matches
    physical memory. *)
Lemma agree_piece_allocated m q base l v :
  object_region base (m_regions m) = None -> agree_piece m l v -> agree_piece (allocated m q base) l v.
Proof.
  intros Hn.
  assert (Ho : forall b, object_region b (m_regions m) <> None ->
            object_region b (m_regions (allocated m q base)) = object_region b (m_regions m)).
  { intros b Hb. rewrite object_region_allocated. destruct (Z.eqb_spec base b) as [<-|]; [contradiction|reflexivity]. }
  destruct l as [b|b o|b o|k], v as [reg|x|c| |p t|cd|sq sp|ga gi|op]; cbn [agree_piece]; try tauto;
    unfold live_at, registered, in_live.
  - intros [E L]. rewrite Ho; [|congruence]. auto.
  - intros Hr. rewrite Ho; exact Hr.
  - intros [Hr Hin]. rewrite Ho; [|exact Hr]. split; [exact Hr | exact Hin].
  - intros [Hr Hin]. rewrite Ho; [|exact Hr]. split; [exact Hr|]. intros reg E L.
    destruct (Hin reg E L) as (Ho' & He & Hx). split; [exact Ho'|]. split; [exact He|].
    destruct Hx as [Hx | [Hf Ht]]; [left; exact Hx|right].
    split; [exact (freed_in_allocated _ _ _ _ Hn Hf) | exact (traps_as_freed_allocated _ _ _ _ Hn Ht)].
Qed.

(** ## Owning pieces

    Passing a global memory map explicitly through every lemma would force
    each function proof to mention all of memory. Using [[iris|Iris]]
    [[separation-logic|separation logic]], we instead let each part of a
    proof claim exclusive ownership of just the pieces it uses. Because two
    assertions joined with `∗` always own disjoint piece keys, a function
    that owns the pieces of a buffer can read and write that buffer locally
    while knowing that all other owned buffers remain unchanged. *)

(** This section defines the ownership assertion [pts] for exclusive
    read-write access to a list of pieces, and [ptsq] for shared read-only
    access. *)
Section pts.
Context `{!gen_heapGS piece pval Σ}.

(** The assertion [pts] claims exclusive ownership of every piece-value pair
    in the list, giving full permission to read and update each piece. *)
Definition pts (ps : list (piece * pval)) : iProp Σ := [∗ list] lv ∈ ps, pointsto (fst lv) (DfracOwn 1) (snd lv).

(** Exclusive ownership of a concatenated piece list splits into separate
    ownership of the two sublists. *)
Lemma pts_app ps qs : pts (ps ++ qs) ⊣⊢ pts ps ∗ pts qs.
Proof. by rewrite /pts big_sepL_app. Qed.

(** When a caller owns a list of pieces with [pts], each piece in that list
    is guaranteed to have its recorded value in the current memory map. *)
Lemma pts_lookup h ps : gen_heap_interp h -∗ pts ps -∗ ⌜forall l v, (l, v) ∈ ps -> h !! l = Some v⌝.
Proof.
  induction ps as [|[l v] ps IH]; iIntros "Hh Hps".
  - iPureIntro. intros l v Hin. by apply not_elem_of_nil in Hin.
  - rewrite /pts /=. iDestruct "Hps" as "[Hl Hps]".
    iDestruct (gen_heap_valid with "Hh Hl") as %Hl.
    iDestruct (IH with "Hh Hps") as %Hps. iPureIntro.
    intros l' v' Hin. apply elem_of_cons in Hin as [[= -> ->] | Hin]; auto.
Qed.

(** Because [pts] grants exclusive ownership of its piece keys, the owner
    can update those entries in the memory map to new values after a store
    without affecting any other owned pieces. *)
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

(** Because exclusive ownership of a single key cannot be duplicated in
    separation logic, any list of pieces owned by [pts] has pairwise
    distinct keys. *)
Lemma pts_keys_nodup ps : pts ps -∗ ⌜NoDup ps.*1⌝.
Proof.
  induction ps as [|[l v] ps IH]; [iIntros "_"; iPureIntro; constructor |].
  rewrite /pts big_sepL_cons. iIntros "[Hl Hps]".
  iDestruct (IH with "Hps") as %Hnd.
  destruct (decide (l ∈ ps.*1)) as [Hin | Hnot].
  - apply list_elem_of_fmap in Hin as ([k u] & Hkey & Hin). cbn in Hkey. subst k.
    iDestruct (big_sepL_elem_of _ _ _ Hin with "Hps") as "Hk".
    iDestruct (pointsto_ne with "Hl Hk") as %Hne. contradiction.
  - iPureIntro. apply NoDup_cons. auto.
Qed.

(** When a new object is allocated with a list of distinct piece keys that
    are not yet in the memory map, [pts_alloc] adds those entries to the map
    and hands back exclusive ownership [pts] of the new object. *)
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

(** ## Fractions of pieces

    Some memory objects, such as string literals or shared lookup tables,
    are read by many parts of a program and never modified. Iris's
    fractional permissions let a proof split ownership of a piece list into
    smaller read-only shares or discard write permission permanently so that
    the assertion can be freely duplicated. *)

(** The assertion [ptsq] claims ownership of each piece-value pair in a list
    at a given fractional permission. Any fraction is sufficient to read the
    pieces, while the full fraction is required to update them. *)
Definition ptsq (dq : dfrac) (ps : list (piece * pval)) : iProp Σ :=
  [∗ list] lv ∈ ps, pointsto (fst lv) dq (snd lv).

(** Full exclusive ownership [pts] is definitionally equal to fractional
    ownership [ptsq] with the whole fraction 1. *)
Lemma pts_ptsq ps : pts ps ⊣⊢ ptsq (DfracOwn 1) ps.
Proof. reflexivity. Qed.

(** Fractional ownership of a concatenated list of pieces splits into
    fractional ownership of each sublist at the same fraction. *)
Lemma ptsq_app dq ps qs : ptsq dq (ps ++ qs) ⊣⊢ ptsq dq ps ∗ ptsq dq qs.
Proof. by rewrite /ptsq big_sepL_app. Qed.

(** Ownership of a piece list at a sum of two fractions splits into two
    separate assertions for the two component fractions. *)
Lemma ptsq_split q1 q2 ps :
  ptsq (DfracOwn (q1 + q2)) ps ⊣⊢ ptsq (DfracOwn q1) ps ∗ ptsq (DfracOwn q2) ps.
Proof.
  rewrite /ptsq -big_sepL_sep. apply big_sepL_proper. intros _ lv _.
  exact (@fractional _ (fun q => pointsto (fst lv) (DfracOwn q) (snd lv)) _ q1 q2).
Qed.

(** Any fractional share of a piece list can be permanently frozen by
    discarding its write permission, which yields a persistent, freely
    duplicable read-only assertion. *)
Lemma ptsq_persist dq ps : ptsq dq ps ==∗ □ ptsq DfracDiscarded ps.
Proof.
  induction ps as [|lv ps IH]; rewrite /ptsq /=; iIntros "H"; [by iModIntro|].
  iDestruct "H" as "[Hl H]". iMod (pointsto_persist with "Hl") as "#Hl".
  iMod (IH with "H") as "#H". iModIntro. iModIntro. iFrame "#".
Qed.

(** Once write permission for a piece list has been discarded, the resulting
    read-only assertion is persistent, so any number of functions can share
    and copy it freely. *)
Instance ptsq_persistent ps : Persistent (ptsq DfracDiscarded ps).
Proof. rewrite /ptsq. apply _. Qed.

(** Even a fractional or read-only share of a piece list in [ptsq]
    guarantees that every piece in the list holds its recorded value in the
    memory map. *)
Lemma ptsq_lookup h dq ps : gen_heap_interp h -∗ ptsq dq ps -∗ ⌜forall l v, (l, v) ∈ ps -> h !! l = Some v⌝.
Proof.
  induction ps as [|[l v] ps IH]; iIntros "Hh Hps".
  - iPureIntro. intros l v Hin. by apply not_elem_of_nil in Hin.
  - rewrite /ptsq /=. iDestruct "Hps" as "[Hl Hps]".
    iDestruct (gen_heap_valid with "Hh Hl") as %Hl.
    iDestruct (IH with "Hh Hps") as %Hps. iPureIntro.
    intros l' v' Hin. apply elem_of_cons in Hin as [[= -> ->] | Hin]; auto.
Qed.

End pts.
