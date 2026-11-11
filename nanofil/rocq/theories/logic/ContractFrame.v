(** When a C function calls an [[external call|external contract]], the
    call does not step through IR instructions. Instead, the contract
    changes physical memory in a series of steps
    ([ExternalCalls](../external/ExternalCalls.v)). A [local_effect] step
    writes bytes and [[aux]] capability slots within the address spans the
    call is allowed to touch, and may free heap objects the contract is
    allowed to release. A fresh allocation step creates a new heap object
    at an unregistered [[fresh]] address.

    In the program logic ([Logic](Logic.v)), a proof tracks the memory
    pieces the caller owns in a side map ([[ghost-state|ghost state]])
    that must match physical memory between steps. This module proves the
    [[separation-logic|frame rule]] for external calls: every piece of
    caller memory outside the addresses and objects the call is allowed to
    touch still matches physical memory when the call finishes.

    ## Disjoint calls and borrowed buffers

    The simplest case is an external call that does not write into any
    caller-owned object, such as `c: puts` or `c: write`, which only read
    the caller's string. For such a call, we state separation by physical
    address rather than by object [[identity]]: none of the contract's
    writable byte spans may overlap a live object owned by the caller, and
    the contract may not free any object the caller owns. Even if the call
    allocates new heap objects internally, each new allocation starts at
    an unregistered address and cannot overlap an existing live object.
    Under those two conditions, [local_agrees] shows that all caller-owned
    memory still matches physical memory after each step.

    Many library and system calls also write results into buffers that the
    caller passes in, such as `c: fstat`'s `c: struct stat` buffer or the
    calling thread's `c: errno` variable. During such a call, the bytes
    inside the borrowed buffer change in physical memory while the
    caller's map still holds their old pre-call values. We describe that
    intermediate state with [agrees_except], which says that every piece
    the caller owns outside the borrowed buffer still matches physical
    memory. Lemma [local_agrees_out] proves that a local-effect step
    preserves [agrees_except], so the caller can refresh the borrowed
    buffer to its new memory values once the call returns. *)

From iris.proofmode Require Import proofmode.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Identity ExternalCalls Pieces Heap.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Separation of a call from the program's pieces

    A contract specifies which memory addresses it may overwrite in two
    ways: a list of writable byte spans that existed before the call, and
    a list of objects that the call allocated itself. To show that a call
    leaves the caller's memory alone, we first define when an address
    belongs to a live object owned by the caller, and when the call's
    writable spans and new allocations avoid those objects. *)

(** An address falls in [owned_live] when it lies within the bounds of a
    live object that the caller tracks in the separation-logic state. *)
Definition owned_live (h : gmap piece pval) (m : mem) (a : Z) : Prop :=
  exists l v reg, h !! l = Some v /\ mem_piece l /\ live_at m (piece_id l) reg /\
    piece_id l <= a < r_end reg.

(** A call's writable spans satisfy [roots_apart] when none of them cover
    an address inside a live object owned by the caller. *)
Definition roots_apart (roots : list span) (h : gmap piece pval) (m : mem) : Prop :=
  forall s a, In s roots -> span_contains s a -> ~ owned_live h m a.

(** A list of object identities satisfies [ids_apart] when none of those
    objects own a memory piece in the caller's state. *)
Definition ids_apart (bs : list Z) (h : gmap piece pval) : Prop :=
  forall b l v, In b bs -> h !! l = Some v -> mem_piece l -> piece_id l <> b.

(** If a call's writable spans and newly allocated objects are both apart
    from the caller's state, then the call has no write authority over any
    live address the caller owns. This is because any live heap object
    allocated by the call has an identity the caller does not own, and
    live objects in memory never overlap. *)
Lemma owned_not_authority : forall roots born h m a,
  live_disjoint m -> roots_apart roots h m -> ids_apart born h ->
  owned_live h m a -> ~ write_authority roots born m a.
Proof.
  intros roots born h m a Hd Hr Hb Ho [(s & Hin & _ & Hs) | (base & reg & Hin & E & _ & L & Ha)].
  - exact (Hr s a Hin Hs Ho).
  - destruct Ho as (l & v & reg0 & Hl & Hm & Hlive & Ha0).
    specialize (Hb base l v Hin Hl Hm).
    destruct (Hd (piece_id l) reg0 base reg Hlive (conj E L) Hb); lia.
Qed.

(** ## Steps that keep old identities

    In Fil-C, freeing a heap object sets its upper bound equal to its
    lower bound and marks its [[region]] as freed, so any later
    dereference of a capability to that object traps. In [Heap](Heap.v),
    a capability slot in a live object may hold either its original
    capability or, if that capability pointed to a freed object, any
    capability that traps as freed. The two lemmas below show that once a
    capability points to a freed object—or traps as freed—it keeps doing
    so across any step that preserves existing object identities and only
    changes existing regions by freeing live objects. *)

(** A capability that points to a freed object continues to point to a
    freed object after any step that keeps existing object identities
    registered and only changes regions by freeing live objects. *)
Lemma freed_in_step : forall m m' c,
  ids m m' -> region_step m m' -> freed_in (m_regions m) c -> freed_in (m_regions m') c.
Proof.
  intros m m' c Hi Hs (b & reg & Hc & E & L). destruct (Hi b reg E) as [reg' E'].
  destruct (Hs b reg' E') as (reg0 & E0 & [-> | (L0 & _)]); rewrite E in E0; injection E0 as <-.
  - exists b, reg. auto.
  - congruence.
Qed.

(** Freeing a heap object empties its bounds so any dereference through
    its capability traps. If a capability already traps as a freed access,
    it continues to trap after any step that preserves existing object
    identities and only frees live regions. *)
Lemma traps_as_freed_step : forall m m' c,
  ids m m' -> region_step m m' -> traps_as_freed (m_regions m) c -> traps_as_freed (m_regions m') c.
Proof.
  intros m m' c Hi Hs H a size r align Hsz. specialize (H a size r align Hsz).
  assert (Hempty : forall b, (b <=? a) && (a + size <=? b) = false).
  { intros b. destruct (Z.leb_spec b a); cbn [andb]; [apply Z.leb_gt; lia | reflexivity]. }
  assert (Hreg : forall b reg, object_region b (m_regions m) = Some reg ->
            object_region b (m_regions m') = Some reg \/
            object_region b (m_regions m') = Some (mkRegion b b (r_kind reg) Freed)).
  { intros b reg E. destruct (Hi b reg E) as [reg' E'].
    destruct (Hs b reg' E') as (reg0 & E0 & [-> | (_ & ->)]); rewrite E in E0; injection E0 as <-; auto. }
  destruct c as [|b|b|f|n]; cbn [cap_access_res] in H |- *; try exact H;
    (destruct (object_region b (m_regions m)) as [reg|] eqn:E; [|discriminate H]);
    (destruct (Hreg b reg E) as [E'|E']; rewrite E'; [exact H|]);
    cbn [r_end]; rewrite Hempty; reflexivity.
Qed.

(** ## A call into owned blocks

    When a caller lends an output buffer to an external call, the call's
    writable spans overlap the caller's live objects inside that buffer.
    To keep the rest of the caller's memory intact, we name the set of
    handed-over physical addresses and the list of borrowed keys that
    cover those addresses. *)

(** When a call is allowed to overwrite a borrowed list of keys,
    [agrees_except] states that every other piece owned by the caller
    still matches physical memory. *)
Definition agrees_except (ks : list piece) (m : mem) (h : gmap piece pval) : Prop :=
  forall l v, h !! l = Some v -> l ∉ ks -> agree_piece m l v.

(** When the caller hands an output buffer to a call, [roots_out] states
    that the call's writable spans overlap the caller's live objects only
    within the handed-over address range. *)
Definition roots_out (roots : list span) (h : gmap piece pval) (m : mem) (out : Z -> Prop) : Prop :=
  forall s a, In s roots -> span_contains s a -> owned_live h m a -> out a.

(** To ensure that no unborrowed caller piece is overwritten, [pieces_off]
    requires every in-bounds byte and capability slot at a handed-over
    address to belong to the borrowed key list. *)
Definition pieces_off (ks : list piece) (h : gmap piece pval) (m : mem) (out : Z -> Prop) : Prop :=
  forall l v, h !! l = Some v -> l ∉ ks ->
    match l with
    | PByte b o | PAux b o => forall reg, live_at m b reg -> 0 <= o -> b + o < r_end reg -> ~ out (b + o)
    | _ => True
    end.

(** When the caller hands no output addresses to the call, [roots_apart]
    directly implies [roots_out]. *)
Lemma roots_out_apart roots h m : roots_apart roots h m -> roots_out roots h m (fun _ => False).
Proof. intros Hra s a Hin Hs Ho. exact (Hra s a Hin Hs Ho). Qed.

(** ## A local effect

    We now combine these conditions for a single local-effect step of an
    external call. The main theorem of this section is [local_agrees_out],
    which handles a call that may write into borrowed buffers;
    [local_agrees] then follows when no buffers are borrowed. *)

(** This section proves that a single local-effect step of an external call
    preserves all caller-owned memory outside the borrowed buffers. *)
Section Local.

(** The section variables fix the call's readable and writable spans, the
    objects it may free or allocate, and the memory states before and after
    the step. *)
Variables (sources roots : list span) (releases born : list Z) (m m' : mem) (h : gmap piece pval).

(** The step from the initial memory to the updated memory is a valid
    local effect of the external call. *)
Hypothesis Hl : local_effect sources roots releases born m m'.

(** Any object that is live after a local-effect step was already live
    with the exact same bounds before the step. This is because a local
    effect can only free existing objects; it never creates or resizes
    them. *)
Lemma local_live_back : forall b reg, live_at m' b reg -> live_at m b reg.
Proof.
  intros b reg [E L]. destruct Hl as (_ & Hr & _).
  destruct (Hr b reg E) as (reg0 & E0 & [-> | (_ & _ & _ & ->)]); [split; assumption | discriminate L].
Qed.

(** Because a local effect never creates or enlarges regions, live objects
    that were disjoint before the step remain disjoint after it. *)
Lemma local_live_disjoint : live_disjoint m -> live_disjoint m'.
Proof.
  intros Hd b1 r1 b2 r2 H1 H2. exact (Hd b1 r1 b2 r2 (local_live_back _ _ H1) (local_live_back _ _ H2)).
Qed.

(** Consequently, any address that lies in a live caller-owned object
    after the step already lay in that same live object before the step. *)
Lemma local_owned_back : forall a, owned_live h m' a -> owned_live h m a.
Proof.
  intros a (l & v & reg & Hh & Hm & Hlive & Ha). exists l, v, reg. split; [exact Hh|].
  split; [exact Hm|]. split; [exact (local_live_back _ _ Hlive) | exact Ha].
Qed.

(** When a call's writable spans touch caller-owned objects only inside a
    borrowed address range and the call frees no caller-owned objects, a
    local-effect step leaves every caller piece outside the borrowed buffer
    matching physical memory. *)
Lemma local_agrees_out (ks : list piece) (out : Z -> Prop) : live_disjoint m -> agrees_except ks m h ->
  roots_out roots h m out -> pieces_off ks h m out ->
  ids_apart releases h -> ids_apart born h -> agrees_except ks m' h.
Proof.
  intros Hd Ha Hra Hoff Hrel Hb l v Hh Hk. pose proof (Ha l v Hh Hk) as Hp.
  pose proof (Hoff l v Hh Hk) as Hno.
  pose proof (local_effect_kept _ _ _ _ _ _ Hl) as [Hs _].
  pose proof Hl as (Hi & Hr & Hw & _).
  (* Any live address owned in h that does not belong to out keeps both
     its byte value and its aux capability slot across the step. *)
  assert (Hkeep : forall reg o, mem_piece l -> live_at m (piece_id l) reg -> 0 <= o -> piece_id l + o < r_end reg ->
            ~ out (piece_id l + o) ->
            m_bytes m' (piece_id l + o) = m_bytes m (piece_id l + o) /\
            m_aux m' (piece_id l + o) = m_aux m (piece_id l + o)).
  { intros reg o Hm Hlive Ho He Hout. apply Hw.
    assert (Hown : owned_live h m (piece_id l + o)).
    { exists l, v, reg. split; [exact Hh|]. split; [exact Hm|]. split; [exact Hlive|lia]. }
    intros [(s & Hin & _ & Hsp) | Hborn].
    - exact (Hout (Hra s _ Hin Hsp Hown)).
    - exact (owned_not_authority [] born h m _ Hd (fun s a Hin => match Hin with end) Hb Hown
               (or_intror Hborn)). }
  destruct l as [b|b o|b o|k], v as [reg|x|c| |q t|cd|sq sp|ga gi|op]; cbn [agree_piece piece_id] in Hp, Hkeep, Hno |- *;
    try contradiction; try exact I.
  - destruct Hp as [E L]. destruct (Hi b reg E) as [reg' E'].
    destruct (Hr b reg' E') as (reg0 & E0 & [-> | (Hin & _)]); rewrite E in E0; injection E0 as <-.
    + split; assumption.
    + exfalso. apply in_app_or in Hin as [Hin|Hin];
        [exact (Hrel b (PLive b) (VLive reg) Hin Hh I eq_refl) | exact (Hb b (PLive b) (VLive reg) Hin Hh I eq_refl)].
  - unfold registered in *. destruct (object_region b (m_regions m)) as [reg|] eqn:E; [|contradiction].
    destruct (Hi b reg E) as [reg' ->]. discriminate.
  - destruct Hp as [Hreg Hin]. split.
    + unfold registered in *.
      destruct (object_region b (m_regions m)) as [reg|] eqn:E; [|contradiction].
      destruct (Hi b reg E) as [reg' ->]. discriminate.
    + intros reg' E' L'. destruct (local_live_back b reg' (conj E' L')) as [E L].
      destruct (Hin reg' E L) as (Ho & He & Hx).
      split; [exact Ho|]. split; [exact He|]. rewrite (proj1 (Hkeep reg' o I (conj E L) Ho He (Hno reg' (conj E L) Ho He))). exact Hx.
  - destruct Hp as [Hreg Hin]. split.
    + unfold registered in *.
      destruct (object_region b (m_regions m)) as [reg|] eqn:E; [|contradiction].
      destruct (Hi b reg E) as [reg' ->]. discriminate.
    + intros reg' E' L'. destruct (local_live_back b reg' (conj E' L')) as [E L].
      destruct (Hin reg' E L) as (Ho & He & Hx).
      split; [exact Ho|]. split; [exact He|]. unfold aux_holds in *.
      rewrite (proj2 (Hkeep reg' o I (conj E L) Ho He (Hno reg' (conj E L) Ho He))).
      destruct Hx as [Hx | [Hf Ht]]; [left; exact Hx | right].
      split; [exact (freed_in_step m m' _ Hi Hs Hf) | exact (traps_as_freed_step m m' _ Hi Hs Ht)].
Qed.

(** When a local-effect step borrows no buffers and touches no caller-owned
    objects, every piece owned by the caller still matches physical memory
    after the step. *)
Lemma local_agrees : live_disjoint m -> agrees m h -> roots_apart roots h m ->
  ids_apart releases h -> ids_apart born h -> agrees m' h.
Proof.
  intros Hd Ha Hra Hrel Hb l v Hh.
  apply (local_agrees_out [] (fun _ => False) Hd); [| exact (roots_out_apart _ _ _ Hra) | | exact Hrel |
    exact Hb | exact Hh | apply not_elem_of_nil].
  - intros l' v' Hl' _. exact (Ha l' v' Hl').
  - intros l' v' _ _. destruct l'; auto.
Qed.

End Local.

(** ## An allocation

    Besides local-effect steps, an external call can allocate new heap
    objects at [[fresh]] base addresses. Because every object owned by the
    caller is already registered in memory, a newly allocated object at an
    unregistered address cannot collide with any object the caller owns. *)

(** Allocating a new heap object leaves every other live object at the same
    region bounds it had before the allocation. *)
Lemma allocated_live_back : forall m q base b reg,
  base <> b -> live_at (allocated m q base) b reg -> live_at m b reg.
Proof.
  intros m q base b reg Hne [E L]. rewrite object_region_allocated in E.
  destruct (Z.eqb_spec base b) as [<-|_]; [contradiction | split; assumption].
Qed.

(** Because every object tracked by the caller is already registered in
    memory, allocating a new object at an unregistered address does not
    add any new caller-owned addresses. *)
Lemma allocated_owned_back : forall m q base h a,
  object_region base (m_regions m) = None -> agrees m h ->
  owned_live h (allocated m q base) a -> owned_live h m a.
Proof.
  intros m q base h a Hn Ha (l & v & reg & Hh & Hm & Hlive & Hr). exists l, v, reg. split; [exact Hh|].
  split; [exact Hm|]. split; [|exact Hr]. apply (allocated_live_back m q base); [|exact Hlive].
  intros E. apply (agree_piece_registered m l v Hm (Ha l v Hh)). rewrite <- E. exact Hn.
Qed.

(** An unregistered base address cannot belong to any object the caller
    already owns, so recording it among the call's newly allocated objects
    preserves disjointness from the caller's identities. *)
Lemma unregistered_apart : forall m h base bs,
  object_region base (m_regions m) = None -> agrees m h -> ids_apart bs h -> ids_apart (base :: bs) h.
Proof.
  intros m h base bs Hn Ha Hb b l v [<-|Hin] Hh Hm.
  - intros E. apply (agree_piece_registered m l v Hm (Ha l v Hh)). rewrite E. exact Hn.
  - exact (Hb b l v Hin Hh Hm).
Qed.

(** ## Delegated roots

    Some stateful libc calls, such as `c: stdio` operations, update the
    world's writable spans to include buffers they allocated or touched
    during the call. *)

(** When a call derives new writable world spans from its existing spans
    and newly allocated objects, every address in the new spans is one the
    call already had authority to write, so the new spans remain disjoint
    from the caller's live objects. *)
Lemma delegates_apart : forall roots born m w h,
  stdio_delegates roots born m w -> roots_apart roots h m -> ids_apart born h -> live_disjoint m ->
  roots_apart (stdio_roots w) h m.
Proof.
  intros roots born m w h Hdel Hra Hb Hd s a Hin Hs Ho.
  destruct (Hdel s Hin) as [_ Hw].
  exact (owned_not_authority roots born h m a Hd Hra Hb Ho (Hw a Hs)).
Qed.
