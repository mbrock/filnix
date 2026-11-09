(** The resource model both logic spikes share (docs/logic.md): the
    pieces of memory an assertion may own, keyed by [[identity]], and
    the facts about the whole memory that make owning them mean
    something.

    A piece is an object's life ([PLive]), or one byte ([PByte]) or
    [[aux]] slot ([PAux]) at an offset in it. Pieces are keyed by
    identity, not address, because the model's [fresh] lets a new
    object take the addresses of a freed one: an address may belong to
    two identities in turn, an identity never to two objects.

    Two facts about the whole memory are the logics' state
    interpretation. Live objects do not overlap ([live_disjoint]), which
    a run keeps, so a store into one object leaves every other live
    object's bytes alone. And under [keeps_live] (no safepoint frees a
    live object, Buffer.v's premise) a [[poll|safepoint]] changes no
    region and no byte, and changes an aux slot only where the
    capability stored there names a freed object ([safepoint_shape],
    from Runtime.v's [non_moving], [aux_round_trip], [rooting] and
    [safepoint_lifetime]). *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime ExternalCalls.
Import ListNotations.
Open Scope Z_scope.

(** ## Pieces *)

(** A piece of memory an assertion may own: the life of the object of
    identity b, or the byte or aux slot at offset o in it. *)
Inductive piece : Type :=
| PLive (b : Z)
| PByte (b o : Z)
| PAux (b o : Z).

(** The identity a piece belongs to. *)
Definition piece_id (p : piece) : Z :=
  match p with PLive b | PByte b _ | PAux b _ => b end.

(** The null pointer, a constant 0 at class `p`. *)
Definition null : ptr := mkPtr 0 CNone.

(** ## The whole memory *)

(** The object of identity b is live in m, with the region reg. *)
Definition live_at (m : mem) (b : Z) (reg : region) : Prop :=
  object_region b (m_regions m) = Some reg /\ r_life reg = Live.

(** The live objects of m do not overlap. *)
Definition live_disjoint (m : mem) : Prop :=
  forall b1 r1 b2 r2, live_at m b1 r1 -> live_at m b2 r2 -> b1 <> b2 ->
    r_end r1 <= b2 \/ r_end r2 <= b1.

(** m and m' have the same objects, each with the same region. *)
Definition same_regions (m m' : mem) : Prop :=
  forall b, object_region b (m_regions m') = object_region b (m_regions m).

(** From m to m', every aux slot is kept, or held a capability of an
    object freed in m' and now holds one that traps as a freed one
    does: what the collector may do at a safepoint ([aux_round_trip]). *)
Definition aux_moves (m m' : mem) : Prop :=
  forall a, m_aux m' a = m_aux m a \/
            (freed_in (m_regions m') (m_aux m a) /\ traps_as_freed (m_regions m') (m_aux m' a)).

(** The aux slot at a holds the capability c, or c names a freed
    object and the slot holds one that traps as a freed one does: a
    stored capability is known up to the collector's rewriting of dead
    ones ([aux_moves]). For a capability whose object is live, or no
    object's, this is equality ([aux_holds_live]). *)
Definition aux_holds (m : mem) (a : Z) (c : cap) : Prop :=
  m_aux m a = c \/ (freed_in (m_regions m) c /\ traps_as_freed (m_regions m) (m_aux m a)).

(** A freed object's capability stays freed while objects keep their
    regions. *)
Lemma freed_in_same : forall m m' c,
  same_regions m m' -> freed_in (m_regions m) c -> freed_in (m_regions m') c.
Proof.
  intros m m' c Hr (b & reg & Hc & E & L). exists b, reg. rewrite Hr. auto.
Qed.

(** A capability that traps as a freed one keeps doing so while objects
    keep their regions. *)
Lemma traps_as_freed_same : forall m m' c,
  same_regions m m' -> traps_as_freed (m_regions m) c -> traps_as_freed (m_regions m') c.
Proof.
  intros m m' c Hr H a size r align Hs. rewrite <- (H a size r align Hs).
  unfold cap_access_res. destruct c; try reflexivity; rewrite Hr; reflexivity.
Qed.

(** What an aux slot is known to hold survives what a safepoint may do
    to it ([aux_moves]) while objects keep their regions. *)
Lemma aux_holds_moves : forall m m' a c,
  same_regions m m' -> aux_moves m m' -> aux_holds m a c -> aux_holds m' a c.
Proof.
  intros m m' a c Hr Hm [E|(Hf & Ht)]; destruct (Hm a) as [E'|(Hf' & Ht')].
  - left. rewrite E'. exact E.
  - right. subst c. split; [exact Hf'|exact Ht'].
  - right. rewrite E'. split; [exact (freed_in_same _ _ _ Hr Hf)|exact (traps_as_freed_same _ _ _ Hr Ht)].
  - right. split; [exact (freed_in_same _ _ _ Hr Hf)|exact Ht'].
Qed.

(** For no object's capability, or a live object's, [aux_holds] is
    equality. *)
Lemma aux_holds_live : forall m a c,
  aux_holds m a c -> (c = CNone \/ exists b reg, c = Obj b /\ live_at m b reg) -> m_aux m a = c.
Proof.
  intros m a c [E|((b & reg & Hc & E & L) & _)] Hc'; [exact E|].
  destruct Hc' as [->|(b' & reg' & -> & E' & L')]; [destruct Hc as [?|?]; discriminate|].
  destruct Hc as [Hc|Hc]; [|discriminate]. injection Hc as <-. congruence.
Qed.

(** ## Bytes *)

(** A store of size bytes at a leaves every other byte. *)
Lemma store_bytes_other : forall m a size x a',
  ~ (a <= a' < a + size) -> m_bytes (store_bytes m a size x) a' = m_bytes m a'.
Proof.
  intros m a size x a' H. unfold store_bytes; cbn [m_bytes].
  destruct ((a <=? a') && (a' <? a + size)) eqn:E; [|reflexivity].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

(** An 8-byte store of an unsigned 64-bit v reads back as v
    (ExternalCalls.v's [stored_bytes_value]). *)
Lemma load_store_bytes : forall m a v, 0 <= v < 2 ^ 64 ->
  load_bytes (store_bytes m a 8 v) a 8 = v.
Proof.
  intros m a v Hv. rewrite stored_bytes_value by lia.
  change (256 ^ 8) with (2 ^ 64). apply Z.mod_small. exact Hv.
Qed.

(** Neither a byte store nor an aux store changes an object. *)
Lemma store_regions : forall m a size x c,
  m_regions (store_bytes m a size x) = m_regions m /\ m_regions (store_aux m a c) = m_regions m.
Proof. split; reflexivity. Qed.

(** ## Allocation *)

(** After allocating q at base, the object of identity base is the new
    one, and every other identity finds what it found before. *)
Lemma object_region_allocated : forall m q base b,
  object_region b (m_regions (allocated m q base)) =
  if Z.eqb base b then Some (mkRegion base (base + req_extent q) (req_kind q) Live)
  else object_region b (m_regions m).
Proof. intros m q base b. reflexivity. Qed.

(** Allocating at a [fresh] base keeps live objects apart. *)
Lemma live_disjoint_allocated : forall m q base,
  live_disjoint m -> fresh m q base -> 0 <= req_extent q -> live_disjoint (allocated m q base).
Proof.
  intros m q base Hd Hf Hq b1 r1 b2 r2 [E1 L1] [E2 L2] Hne.
  destruct Hf as (_ & _ & _ & _ & Hover & _).
  rewrite object_region_allocated in E1, E2.
  destruct (Z.eqb_spec base b1) as [<-|N1]; destruct (Z.eqb_spec base b2) as [<-|N2].
  - congruence.
  - injection E1 as <-. cbn [r_end].
    specialize (Hover b2 r2 E2). destruct (Z_le_gt_dec (base + req_extent q) b2); [left; lia|].
    destruct (Z_le_gt_dec (r_end r2) base); [right; lia|]. exfalso. apply Hover. lia.
  - injection E2 as <-. cbn [r_end].
    specialize (Hover b1 r1 E1). destruct (Z_le_gt_dec (r_end r1) base); [left; lia|].
    destruct (Z_le_gt_dec (base + req_extent q) b1); [right; lia|]. exfalso. apply Hover. lia.
  - exact (Hd b1 r1 b2 r2 (conj E1 L1) (conj E2 L2) Hne).
Qed.

(** ## Safepoints *)

(** What any runtime R does at a safepoint, under the premise that it
    frees no live object. *)
Module SafepointShape (R : Runtime).

(** No safepoint of R frees a live object: Buffer.v's
    [safepoint_keeps_live]. *)
Definition keeps_live : Prop :=
  forall s m s' m' b reg, R.safepoint s m s' m' ->
    object_region b (m_regions m) = Some reg -> r_life reg = Live ->
    object_region b (m_regions m') = Some reg.

(** Under [keeps_live], a safepoint keeps every object's region and
    every byte, and changes an aux slot only as [aux_moves] allows. *)
Lemma safepoint_shape : keeps_live -> forall s m s' m',
  R.safepoint s m s' m' -> same_regions m m' /\ m_bytes m' = m_bytes m /\ aux_moves m m'.
Proof.
  intros Hk s m s' m' Hsp. split; [|split].
  - intros b. destruct (object_region b (m_regions m')) as [reg'|] eqn:E'.
    + destruct (R.safepoint_lifetime _ _ _ _ Hsp b reg' E') as (reg & E & [<-|(_ & Hl & ->)]);
        [symmetry; exact E|].
      rewrite (Hk _ _ _ _ _ _ Hsp E Hl) in E'. rewrite E. symmetry. exact E'.
    + destruct (object_region b (m_regions m)) as [reg|] eqn:E; [|reflexivity].
      exfalso. apply (R.rooting _ _ _ _ Hsp b); congruence.
  - exact (R.non_moving _ _ _ _ Hsp).
  - exact (R.aux_round_trip _ _ _ _ Hsp).
Qed.

(** A safepoint of R keeps live objects apart, if it frees none. *)
Lemma live_disjoint_safepoint : keeps_live -> forall s m s' m',
  R.safepoint s m s' m' -> live_disjoint m -> live_disjoint m'.
Proof.
  intros Hk s m s' m' Hsp Hd b1 r1 b2 r2 [E1 L1] [E2 L2].
  destruct (safepoint_shape Hk _ _ _ _ Hsp) as (Hr & _).
  rewrite Hr in E1, E2. exact (Hd b1 r1 b2 r2 (conj E1 L1) (conj E2 L2)).
Qed.

End SafepointShape.
