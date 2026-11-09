(** A small separation logic over the model's memory, hand-rolled: the
    first of the two spikes of docs/logic.md. Nothing outside
    nanofil/rocq/spikes depends on it.

    An assertion is a predicate on a footprint and a memory: the
    footprint is the set of pieces of memory the assertion owns, and
    the assertion may speak of the memory only through those pieces and
    through facts that no step can take back. Pieces are keyed by
    [[identity]], not by address: an object's life ([PLive]), one of its
    bytes ([PByte]) and one of its [[aux]] slots ([PAux]), each named by
    the object's base and an offset. Keying by address would not do:
    the model's [fresh] lets a new object take the addresses of a freed
    one, so a byte at an address may belong to two identities in turn.
    A byte piece speaks only while its object is live and the offset is
    in bounds, and then nothing else can write it.

    The separating conjunction [star] splits the footprint in two
    disjoint parts. The frame property is [stable]: an assertion still
    holds after any change that keeps its pieces ([same_on]) and only
    moves objects forward in life ([grows]). Each kind of step that
    changes memory keeps every footprint that does not own what it
    writes ([store_same_on], [pointer_store_same_on], [alloc_same_on]),
    given one fact about the whole memory, that live objects do not
    overlap ([live_disjoint]): that fact is this logic's state
    interpretation.

    A [[poll|safepoint]] is the one step that may change memory nobody
    in the program wrote. Under [keeps_live] (no safepoint frees a live
    object; Buffer.v's premise, here per runtime) it changes nothing an
    assertion owns except an aux slot whose stored capability names a
    freed object, and the list predicate [lst] never stores one
    ([lst_safepoint]). An assertion that survives that is [sp_stable].

    An assertion that owns only pieces of objects ([owns_registered])
    can be dropped into [htrue], the affine assertion of anything
    owned: a walk of the list drops each node it has passed. A write
    is a rule for the owner of what it writes ([writes]: [icell_writes],
    [pcell_writes]) and a fact for everyone else ([keeps]), and the two
    combine under [star] ([writes_star_l], [writes_star_r]); an
    allocation adds a node no one else owned ([alloc_frame]).
    Footprints are predicates compared piece by piece, with no
    extensionality assumed, so [emp] is a unit only up to the same
    pieces ([star_emp_elim]). *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops.
From Spike Require Import Pieces.
Import ListNotations.
Open Scope Z_scope.

(** ## Footprints *)

(** A footprint: a set of pieces. *)
Definition fp : Type := piece -> Prop.

(** An assertion: a predicate on the footprint it owns and the memory. *)
Definition hprop : Type := fp -> mem -> Prop.

(** The footprint S is exactly the pieces ps. *)
Definition only (S : fp) (ps : piece -> Prop) : Prop := forall p, S p <-> ps p.

(** ## How memory may change *)

(** From m to m', every object moved forward in life only: it is still
    there unchanged, or it was live and is now freed and empty. New
    objects may appear. Every step of a run does this. *)
Definition grows (m m' : mem) : Prop :=
  forall b reg, object_region b (m_regions m) = Some reg ->
    object_region b (m_regions m') = Some reg \/
    (r_life reg = Live /\ object_region b (m_regions m') = Some (mkRegion b b (r_kind reg) Freed)).

(** From m to m', the pieces of S are kept: an owned object's region,
    and, while the object is live and the offset in bounds, an owned
    byte or aux slot. *)
Definition same_on (S : fp) (m m' : mem) : Prop :=
  forall p, S p ->
    match p with
    | PLive b => forall reg, object_region b (m_regions m) = Some reg ->
                             object_region b (m_regions m') = Some reg
    | PByte b o => forall reg, live_at m' b reg -> 0 <= o -> b + o < r_end reg ->
                               m_bytes m' (b + o) = m_bytes m (b + o)
    | PAux b o => forall reg, live_at m' b reg -> 0 <= o -> b + o < r_end reg ->
                              m_aux m' (b + o) = m_aux m (b + o)
    end.

(** The assertion P is stable: it survives any change that keeps its
    pieces and moves objects only forward. Every assertion built here
    is. *)
Definition stable (P : hprop) : Prop :=
  forall S m m', P S m -> same_on S m m' -> grows m m' -> P S m'.

(** Every piece of S belongs to an object of m. Every assertion built
    here owns only such pieces, so a [fresh] identity is owned by no
    one. *)
Definition registered (S : fp) (m : mem) : Prop :=
  forall p, S p -> object_region (piece_id p) (m_regions m) <> None.

(** ## Assertions *)

(** Owns nothing. *)
Definition emp : hprop := fun S _ => only S (fun _ => False).

(** Owns nothing, and phi holds. *)
Definition pure (phi : Prop) : hprop := fun S _ => only S (fun _ => False) /\ phi.

(** P and Q hold of disjoint parts of the footprint. *)
Definition star (P Q : hprop) : hprop :=
  fun S m => exists S1 S2,
    (forall p, S p <-> S1 p \/ S2 p) /\ (forall p, ~ (S1 p /\ S2 p)) /\ P S1 m /\ Q S2 m.

(** P x holds for some x. *)
Definition hex {A : Type} (P : A -> hprop) : hprop := fun S m => exists x, P x S m.

Declare Scope hprop_scope.
Delimit Scope hprop_scope with h.
Infix "**" := star (at level 41, right associativity) : hprop_scope.

(** The persistent fact that b is an object of kind k whose bounds, while
    it is live, are n bytes: the [[meta]] of docs/logic.md. Owns nothing,
    and no step takes it back. *)
Definition meta (b n : Z) (k : kind) : hprop :=
  fun S m => only S (fun _ => False) /\
    exists reg, object_region b (m_regions m) = Some reg /\ r_kind reg = k /\
                (r_life reg = Live -> r_end reg = b + n).

(** The object b is live, and only the owner of this may end it: the
    [[live]] token. *)
Definition live (b : Z) : hprop :=
  fun S m => only S (eq (PLive b)) /\ exists reg, live_at m b reg.

(** The eight bytes at offset o of the object b. *)
Definition bytes8 (b o : Z) (p : piece) : Prop :=
  exists i, 0 <= i < 8 /\ p = PByte b (o + i).

(** The eight bytes at offset o of b hold the integer v, while b is
    live; b is an object, and o is in its bounds. *)
Definition icell (b o v : Z) : hprop :=
  fun S m => only S (bytes8 b o) /\ object_region b (m_regions m) <> None /\
    forall reg, live_at m b reg ->
      0 <= o /\ b + o + 8 <= r_end reg /\ load_bytes m (b + o) 8 = v.

(** The pointer slot at offset o of b holds the pointer x, its address
    in the bytes and its capability in the aux ([aux_holds]), while b
    is live. *)
Definition pcell (b o : Z) (x : ptr) : hprop :=
  fun S m => only S (fun p => bytes8 b o p \/ p = PAux b o) /\
    object_region b (m_regions m) <> None /\
    forall reg, live_at m b reg ->
      0 <= o /\ b + o + 8 <= r_end reg /\ load_bytes m (b + o) 8 = ptr_addr x /\
      aux_holds m (b + o) (ptr_cap x).

(** A list node at b: a 16-byte heap object, live, whose first slot
    points to next and whose second holds v (C's `struct node {struct
    node *next; long v;}`). *)
Definition node (b : Z) (next : ptr) (v : Z) : hprop :=
  (meta b 16 Heap ** live b ** pcell b 0 next ** icell b 8 v)%h.

(** The list at p holds the values xs: null for none, else a pointer
    to a node with its own capability, at an 8-aligned address (a
    pointer load checks the alignment of its slot), whose next pointer
    is the rest. *)
Fixpoint lst (p : ptr) (xs : list Z) : hprop :=
  match xs with
  | [] => pure (p = null)
  | v :: xs' => hex (fun next =>
      (pure (p = mkPtr (ptr_addr p) (Obj (ptr_addr p)) /\ 0 < ptr_addr p /\ ptr_addr p mod 8 = 0) **
       node (ptr_addr p) next v ** lst next xs')%h)
  end.

(** One node of a nonempty list at p: its value v, its next pointer
    next and the rest xs, the body of [lst]'s second case. *)
Definition lst_cons (p : ptr) (v : Z) (next : ptr) (xs : list Z) : hprop :=
  (pure (p = mkPtr (ptr_addr p) (Obj (ptr_addr p)) /\ 0 < ptr_addr p /\ ptr_addr p mod 8 = 0) **
   node (ptr_addr p) next v ** lst next xs)%h.

(** ## More ways memory may change *)

(** The assertion P survives what a safepoint may do under
    [keeps_live] ([safepoint_shape]): the same objects, the same bytes,
    and aux slots changed only as [aux_moves] allows. *)
Definition sp_stable (P : hprop) : Prop :=
  forall S m m', P S m -> same_regions m m' -> m_bytes m' = m_bytes m -> aux_moves m m' -> P S m'.

(** The assertion P owns only pieces of objects of the memory. *)
Definition owns_registered (P : hprop) : Prop := forall S m, P S m -> registered S m.

(** Anything owned: the affine assertion into which pieces no longer
    needed are dropped. *)
Definition htrue : hprop := fun S m => registered S m.

(** The pieces a pointer slot at offset o of b owns. *)
Definition pcell_pieces (b o : Z) (p : piece) : Prop := bytes8 b o p \/ p = PAux b o.

(** The pieces a node at b owns. *)
Definition node_pieces (b : Z) (p : piece) : Prop :=
  p = PLive b \/ bytes8 b 0 p \/ p = PAux b 0 \/ bytes8 b 8 p.

(** From m to m', every footprint owning nothing of W is kept: what a
    write of the pieces W does to everyone else. *)
Definition keeps (W : piece -> Prop) (m m' : mem) : Prop :=
  forall S, (forall p, S p -> ~ W p) -> same_on S m m'.

(** From m to m', P becomes P' on the same footprint, which owns the
    written pieces W: the rule of one write for the owner of what it
    writes. *)
Definition writes (W : piece -> Prop) (m m' : mem) (P P' : hprop) : Prop :=
  forall S, P S m -> P' S m' /\ (forall p, W p -> S p).

(** ## Facts about objects and bytes *)

(** The region [object_region] finds for b has b for its base. *)
Lemma object_region_base : forall b rs reg, object_region b rs = Some reg -> r_base reg = b.
Proof.
  intros b rs reg. induction rs as [|r rs IH]; cbn; [discriminate|].
  destruct (Z.eqb_spec (r_base r) b) as [E|_]; [intros H; injection H as <-; exact E | exact IH].
Qed.

(** An object live after a change that moves objects only forward was
    live, with the same region, before it. *)
Lemma grows_live_at : forall m m' b reg, grows m m' -> object_region b (m_regions m) <> None ->
  live_at m' b reg -> live_at m b reg.
Proof.
  intros m m' b reg Hg Hb [E L].
  destruct (object_region b (m_regions m)) as [reg0|] eqn:E0; [|congruence].
  destruct (Hg b reg0 E0) as [E1|(L0 & E1)]; rewrite E1 in E; injection E as <-.
  - split; assumption.
  - discriminate L.
Qed.

(** A footprint of objects stays one when objects move only forward. *)
Lemma grows_registered : forall m m' S, grows m m' -> registered S m -> registered S m'.
Proof.
  intros m m' S Hg Hr p Hp. specialize (Hr p Hp).
  destruct (object_region (piece_id p) (m_regions m)) as [reg|] eqn:E; [|congruence].
  destruct (Hg _ _ E) as [E'|(_ & E')]; rewrite E'; discriminate.
Qed.

(** A footprint of objects stays one while objects keep their regions. *)
Lemma registered_same : forall m m' S, same_regions m m' -> registered S m -> registered S m'.
Proof. intros m m' S Hr H p Hp. rewrite Hr. exact (H p Hp). Qed.

(** A freed object stays freed when objects move only forward. *)
Lemma freed_in_grows : forall m m' c,
  grows m m' -> freed_in (m_regions m) c -> freed_in (m_regions m') c.
Proof.
  intros m m' c Hg (b & reg & Hc & E & L). exists b, reg. split; [exact Hc|].
  destruct (Hg b reg E) as [E'|(L' & _)]; [split; assumption | congruence].
Qed.

(** A capability that traps as a freed one keeps doing so when objects
    move only forward: an object that ends has no bounds left. *)
Lemma traps_as_freed_grows : forall m m' c,
  grows m m' -> traps_as_freed (m_regions m) c -> traps_as_freed (m_regions m') c.
Proof.
  intros m m' c Hg H a size r align Hs. specialize (H a size r align Hs).
  destruct c as [|b|b|f|n]; cbn in H |- *; try exact H;
    destruct (object_region b (m_regions m)) as [reg|] eqn:E; try discriminate H;
    destruct (Hg b reg E) as [E'|(_ & E')]; rewrite E'; try exact H; cbn [r_end];
    (destruct (Z.leb_spec b a); [rewrite (proj2 (Z.leb_gt (a + size) b)) by lia|]; reflexivity).
Qed.

(** The eight bytes at a read the same where each of them is the same. *)
Lemma load_bytes_ext8 : forall m m' a,
  (forall i, 0 <= i < 8 -> m_bytes m' (a + i) = m_bytes m (a + i)) -> load_bytes m' a 8 = load_bytes m a 8.
Proof.
  intros m m' a H. unfold load_bytes. simpl.
  rewrite !H by lia. reflexivity.
Qed.

(** Bytes read the same in a memory with the same bytes. *)
Lemma load_bytes_same : forall m m' a n, m_bytes m' = m_bytes m -> load_bytes m' a n = load_bytes m a n.
Proof. intros m m' a n H. unfold load_bytes. rewrite H. reflexivity. Qed.

(** Eight zero bytes read as zero. *)
Lemma load_bytes_zero : forall m a, (forall i, 0 <= i < 8 -> m_bytes m (a + i) = 0) -> load_bytes m a 8 = 0.
Proof.
  intros m a H. unfold load_bytes. simpl.
  rewrite !H by lia. reflexivity.
Qed.

(** Live objects stay apart while objects keep their regions. *)
Lemma live_disjoint_same : forall m m', m_regions m' = m_regions m -> live_disjoint m -> live_disjoint m'.
Proof. intros m m' E H b1 r1 b2 r2. unfold live_at. rewrite E. apply H. Qed.

(** A memory with the same objects only moves them forward. *)
Lemma grows_same : forall m m', m_regions m' = m_regions m -> grows m m'.
Proof. intros m m' E b reg H. left. rewrite E. exact H. Qed.

(** A footprint's parts are kept where it is. *)
Lemma same_on_sub : forall S S' m m', (forall p, S' p -> S p) -> same_on S m m' -> same_on S' m m'.
Proof. intros S S' m m' H Hs p Hp. exact (Hs p (H p Hp)). Qed.

(** Kept through two changes is kept through both, when the second
    keeps every object's region. *)
Lemma same_on_trans : forall S m1 m2 m3, m_regions m3 = m_regions m2 ->
  same_on S m1 m2 -> same_on S m2 m3 -> same_on S m1 m3.
Proof.
  intros S m1 m2 m3 Hr H12 H23 p Hp. specialize (H12 p Hp). specialize (H23 p Hp).
  destruct p; cbn iota beta in H12, H23 |- *.
  - intros reg E. apply H23, H12, E.
  - intros reg Hl Ho He. rewrite (H23 reg Hl Ho He).
    apply (H12 reg); [|assumption|assumption]. unfold live_at in *. rewrite <- Hr. exact Hl.
  - intros reg Hl Ho He. rewrite (H23 reg Hl Ho He).
    apply (H12 reg); [|assumption|assumption]. unfold live_at in *. rewrite <- Hr. exact Hl.
Qed.

(** ## The algebra of [star] *)

(** [star] commutes. *)
Lemma star_comm : forall P Q S m, (P ** Q)%h S m -> (Q ** P)%h S m.
Proof.
  intros P Q S m (S1 & S2 & HS & Hd & H1 & H2). exists S2, S1.
  split; [intros p; specialize (HS p); tauto|]. split; [intros p; specialize (Hd p); tauto|]. auto.
Qed.

(** [star] associates, to the left. *)
Lemma star_assoc_l : forall P Q R S m, (P ** (Q ** R))%h S m -> ((P ** Q) ** R)%h S m.
Proof.
  intros P Q R S m (S1 & S23 & HS & Hd & H1 & (S2 & S3 & HS23 & Hd23 & H2 & H3)).
  exists (fun p => S1 p \/ S2 p), S3.
  split; [intros p; specialize (HS p); specialize (HS23 p); tauto|].
  split; [intros p; specialize (Hd p); specialize (Hd23 p); specialize (HS23 p); tauto|].
  split; [|exact H3]. exists S1, S2. split; [intros p; tauto|].
  split; [intros p; specialize (Hd p); specialize (HS23 p); tauto|]. auto.
Qed.

(** [star] associates, to the right. *)
Lemma star_assoc_r : forall P Q R S m, ((P ** Q) ** R)%h S m -> (P ** (Q ** R))%h S m.
Proof.
  intros P Q R S m (S12 & S3 & HS & Hd & (S1 & S2 & HS12 & Hd12 & H1 & H2) & H3).
  exists S1, (fun p => S2 p \/ S3 p).
  split; [intros p; specialize (HS p); specialize (HS12 p); tauto|].
  split; [intros p; specialize (Hd p); specialize (Hd12 p); specialize (HS12 p); tauto|].
  split; [exact H1|]. exists S2, S3. split; [intros p; tauto|].
  split; [intros p; specialize (Hd p); specialize (HS12 p); tauto|]. auto.
Qed.

(** The frame rule's monotonicity, on the left. *)
Lemma star_mono_l : forall (P P' Q : hprop) S m, (forall S m, P S m -> P' S m) ->
  (P ** Q)%h S m -> (P' ** Q)%h S m.
Proof. intros P P' Q S m H (S1 & S2 & HS & Hd & H1 & H2). exists S1, S2. auto. Qed.

(** The frame rule's monotonicity, on the right. *)
Lemma star_mono_r : forall (P Q Q' : hprop) S m, (forall S m, Q S m -> Q' S m) ->
  (P ** Q)%h S m -> (P ** Q')%h S m.
Proof. intros P Q Q' S m H (S1 & S2 & HS & Hd & H1 & H2). exists S1, S2. auto. Qed.

(** The first two parts of a [star] trade places. *)
Lemma star_swap : forall P Q R S m, (P ** Q ** R)%h S m -> (Q ** P ** R)%h S m.
Proof.
  intros P Q R S m H. apply star_assoc_r. apply star_assoc_l in H.
  revert H. apply star_mono_l. apply star_comm.
Qed.

(** [emp] is a unit, on the right. *)
Lemma star_emp_r : forall P S m, P S m -> (P ** emp)%h S m.
Proof.
  intros P S m H. exists S, (fun _ => False). split; [intros p; tauto|].
  split; [intros p; tauto|]. split; [exact H | intros p; tauto].
Qed.

(** [emp] is a unit, on the left. *)
Lemma star_emp_l : forall P S m, P S m -> (emp ** P)%h S m.
Proof. intros P S m H. apply star_comm, star_emp_r, H. Qed.

(** And back: without [emp], P holds of a footprint with the same
    pieces. Footprints are predicates, so this is as close as the
    logic gets to equality of footprints without extensionality. *)
Lemma star_emp_elim : forall P S m, (emp ** P)%h S m -> exists S', (forall p, S p <-> S' p) /\ P S' m.
Proof.
  intros P S m (S1 & S2 & HS & _ & H1 & H2). exists S2. split; [|exact H2].
  intros p. specialize (HS p). specialize (H1 p). tauto.
Qed.

(** A pure fact on no footprint may be added. *)
Lemma star_pure_intro : forall (phi : Prop) Q S m, phi -> Q S m -> (pure phi ** Q)%h S m.
Proof. intros phi Q S m Hp H. apply star_comm. destruct (star_emp_r Q S m H) as (S1 & S2 & HS & Hd & H1 & H2). exists S1, S2. split; [exact HS|]. split; [exact Hd|]. split; [exact H1|]. split; [exact H2 | exact Hp]. Qed.

(** The left part of a [star] holds of part of the footprint. *)
Lemma star_elim_l : forall P Q S m, (P ** Q)%h S m -> exists S1, P S1 m.
Proof. intros P Q S m (S1 & S2 & _ & _ & H1 & _). exists S1. exact H1. Qed.

(** The right part of a [star] holds of part of the footprint. *)
Lemma star_elim_r : forall P Q S m, (P ** Q)%h S m -> exists S2, Q S2 m.
Proof. intros P Q S m (S1 & S2 & _ & _ & _ & H2). exists S2. exact H2. Qed.

(** An existential on the left of a [star] comes out. *)
Lemma star_hex_l : forall (A : Type) (P : A -> hprop) Q S m,
  (hex P ** Q)%h S m <-> exists x, (P x ** Q)%h S m.
Proof.
  intros A P Q S m. split.
  - intros (S1 & S2 & HS & Hd & (x & H1) & H2). exists x, S1, S2. auto.
  - intros (x & S1 & S2 & HS & Hd & H1 & H2). exists S1, S2. split; [exact HS|]. split; [exact Hd|]. split; [exists x; exact H1 | exact H2].
Qed.

(** [htrue] holds of no footprint, so it may be added. *)
Lemma htrue_intro : forall Q S m, Q S m -> (htrue ** Q)%h S m.
Proof.
  intros Q S m H. apply star_comm. destruct (star_emp_r Q S m H) as (S1 & S2 & HS & Hd & H1 & H2).
  exists S1, S2. split; [exact HS|]. split; [exact Hd|]. split; [exact H1|]. intros p Hp. destruct (proj1 (H2 p) Hp).
Qed.

(** What owns only pieces of objects can be dropped into [htrue]. *)
Lemma star_drop : forall P Q S m, owns_registered P -> (P ** Q)%h S m -> (htrue ** Q)%h S m.
Proof. intros P Q S m HP. apply star_mono_l. exact HP. Qed.

(** [htrue] absorbs what owns only pieces of objects. *)
Lemma htrue_absorb : forall P R S m, owns_registered P -> (P ** htrue ** R)%h S m -> (htrue ** R)%h S m.
Proof.
  intros P R S m HP H. apply star_assoc_l in H. revert H. apply star_mono_l.
  intros S0 m0 (S1 & S2 & HS & _ & H1 & H2) p Hp. apply HS in Hp as [Hp|Hp]; [exact (HP _ _ H1 p Hp) | exact (H2 p Hp)].
Qed.

(** [htrue] absorbs a part that owns only pieces of objects from in
    front of another. *)
Lemma star_absorb : forall P Q R S m, owns_registered P ->
  (P ** Q ** htrue ** R)%h S m -> (Q ** htrue ** R)%h S m.
Proof.
  intros P Q R S m HP H. apply star_swap in H. revert H. apply star_mono_r.
  intros S0 m0. apply htrue_absorb, HP.
Qed.

(** ## Stability of each assertion *)

(** A [star] is stable if its parts are. *)
Lemma star_stable : forall P Q, stable P -> stable Q -> stable (P ** Q)%h.
Proof.
  intros P Q HP HQ S m m' (S1 & S2 & HS & Hd & H1 & H2) Hs Hg. exists S1, S2.
  split; [exact HS|]. split; [exact Hd|]. split.
  - apply (HP S1 m m' H1); [|exact Hg]. apply (same_on_sub S); [intros p Hp; apply HS; left; exact Hp | exact Hs].
  - apply (HQ S2 m m' H2); [|exact Hg]. apply (same_on_sub S); [intros p Hp; apply HS; right; exact Hp | exact Hs].
Qed.

(** A [star] survives a safepoint if its parts do. *)
Lemma star_sp_stable : forall P Q, sp_stable P -> sp_stable Q -> sp_stable (P ** Q)%h.
Proof.
  intros P Q HP HQ S m m' (S1 & S2 & HS & Hd & H1 & H2) Hr Hb Ha. exists S1, S2.
  split; [exact HS|]. split; [exact Hd|]. split; [exact (HP _ _ _ H1 Hr Hb Ha) | exact (HQ _ _ _ H2 Hr Hb Ha)].
Qed.

(** A [star] owns pieces of objects if its parts do. *)
Lemma star_registered : forall P Q, owns_registered P -> owns_registered Q -> owns_registered (P ** Q)%h.
Proof.
  intros P Q HP HQ S m (S1 & S2 & HS & Hd & H1 & H2) p Hp.
  apply HS in Hp as [Hp|Hp]; [exact (HP _ _ H1 p Hp) | exact (HQ _ _ H2 p Hp)].
Qed.

(** [hex] is stable if each instance is. *)
Lemma hex_stable : forall (A : Type) (P : A -> hprop), (forall x, stable (P x)) -> stable (hex P).
Proof. intros A P HP S m m' (x & H) Hs Hg. exists x. exact (HP x _ _ _ H Hs Hg). Qed.

(** [hex] survives a safepoint if each instance does. *)
Lemma hex_sp_stable : forall (A : Type) (P : A -> hprop), (forall x, sp_stable (P x)) -> sp_stable (hex P).
Proof. intros A P HP S m m' (x & H) Hr Hb Ha. exists x. exact (HP x _ _ _ H Hr Hb Ha). Qed.

(** [hex] owns pieces of objects if each instance does. *)
Lemma hex_registered : forall (A : Type) (P : A -> hprop), (forall x, owns_registered (P x)) -> owns_registered (hex P).
Proof. intros A P HP S m (x & H). exact (HP x _ _ H). Qed.

(** [emp] is stable. *)
Lemma emp_stable : stable emp.
Proof. intros S m m' H _ _. exact H. Qed.

(** [emp] survives a safepoint. *)
Lemma emp_sp_stable : sp_stable emp.
Proof. intros S m m' H _ _ _. exact H. Qed.

(** [emp] owns nothing. *)
Lemma emp_registered : owns_registered emp.
Proof. intros S m H p Hp. destruct (proj1 (H p) Hp). Qed.

(** [pure] is stable. *)
Lemma pure_stable : forall phi, stable (pure phi).
Proof. intros phi S m m' H _ _. exact H. Qed.

(** [pure] survives a safepoint. *)
Lemma pure_sp_stable : forall phi, sp_stable (pure phi).
Proof. intros phi S m m' H _ _ _. exact H. Qed.

(** [pure] owns nothing. *)
Lemma pure_registered : forall phi, owns_registered (pure phi).
Proof. intros phi S m [H _] p Hp. destruct (proj1 (H p) Hp). Qed.

(** [htrue] is stable. *)
Lemma htrue_stable : stable htrue.
Proof. intros S m m' H _ Hg. exact (grows_registered _ _ _ Hg H). Qed.

(** [htrue] survives a safepoint. *)
Lemma htrue_sp_stable : sp_stable htrue.
Proof. intros S m m' H Hr _ _. exact (registered_same _ _ _ Hr H). Qed.

(** [htrue] owns pieces of objects. *)
Lemma htrue_registered : owns_registered htrue.
Proof. intros S m H. exact H. Qed.

(** [meta] is stable: an object that ends keeps its kind, and has no
    bounds to speak of. *)
Lemma meta_stable : forall b n k, stable (meta b n k).
Proof.
  intros b n k S m m' (HS & reg & E & Hk & Hl) _ Hg. split; [exact HS|].
  destruct (Hg b reg E) as [E'|(L & E')].
  - exists reg. auto.
  - eexists. split; [exact E'|]. split; [exact Hk | discriminate].
Qed.

(** [meta] survives a safepoint. *)
Lemma meta_sp_stable : forall b n k, sp_stable (meta b n k).
Proof. intros b n k S m m' (HS & reg & E & Hk & Hl) Hr _ _. split; [exact HS|]. exists reg. rewrite Hr. auto. Qed.

(** [meta] owns nothing. *)
Lemma meta_registered : forall b n k, owns_registered (meta b n k).
Proof. intros b n k S m [H _] p Hp. destruct (proj1 (H p) Hp). Qed.

(** [live] is stable: its owner keeps the object's region. *)
Lemma live_stable : forall b, stable (live b).
Proof.
  intros b S m m' (HS & reg & E & L) Hs _. split; [exact HS|]. exists reg. split; [|exact L].
  exact (Hs (PLive b) (proj2 (HS _) eq_refl) reg E).
Qed.

(** [live] survives a safepoint. *)
Lemma live_sp_stable : forall b, sp_stable (live b).
Proof. intros b S m m' (HS & reg & E & L) Hr _ _. split; [exact HS|]. exists reg. unfold live_at. rewrite Hr. auto. Qed.

(** [live] owns a piece of its object. *)
Lemma live_registered : forall b, owns_registered (live b).
Proof. intros b S m (HS & reg & E & L) p Hp. apply HS in Hp. subst p. cbn. congruence. Qed.

(** [icell] is stable: while the object is live it is the same object,
    and its owned bytes are kept. *)
Lemma icell_stable : forall b o v, stable (icell b o v).
Proof.
  intros b o v S m m' (HS & Hb & H) Hs Hg. split; [exact HS|]. split.
  - destruct (object_region b (m_regions m)) as [reg|] eqn:E0; [|congruence].
    destruct (Hg _ _ E0) as [E1|(_ & E1)]; congruence.
  - intros reg Hl. destruct (H reg (grows_live_at _ _ _ _ Hg Hb Hl)) as (Ho & He & Hv).
    split; [exact Ho|]. split; [exact He|]. rewrite <- Hv. apply load_bytes_ext8. intros i Hi.
    assert (Hp : S (PByte b (o + i))) by (apply HS; exists i; split; [exact Hi | reflexivity]).
    pose proof (Hs _ Hp) as Hs'. cbn iota beta in Hs'. rewrite <- Z.add_assoc. apply (Hs' reg); [exact Hl|lia|lia].
Qed.

(** [icell] survives a safepoint. *)
Lemma icell_sp_stable : forall b o v, sp_stable (icell b o v).
Proof.
  intros b o v S m m' (HS & Hb & H) Hr Hbytes _. split; [exact HS|]. split; [rewrite Hr; exact Hb|].
  intros reg Hl. unfold live_at in Hl. rewrite Hr in Hl. destruct (H reg Hl) as (Ho & He & Hv).
  split; [exact Ho|]. split; [exact He|]. rewrite (load_bytes_same m m' _ _ Hbytes). exact Hv.
Qed.

(** [icell] owns pieces of its object. *)
Lemma icell_registered : forall b o v, owns_registered (icell b o v).
Proof. intros b o v S m (HS & Hb & _) p Hp. apply HS in Hp as (i & _ & ->). exact Hb. Qed.

(** [pcell] is stable: as [icell], and its aux slot is kept, or what it
    is known to hold names a freed object, which stays freed. *)
Lemma pcell_stable : forall b o x, stable (pcell b o x).
Proof.
  intros b o x S m m' (HS & Hb & H) Hs Hg. split; [exact HS|]. split.
  - destruct (object_region b (m_regions m)) as [reg|] eqn:E0; [|congruence].
    destruct (Hg _ _ E0) as [E1|(_ & E1)]; congruence.
  - intros reg Hl. destruct (H reg (grows_live_at _ _ _ _ Hg Hb Hl)) as (Ho & He & Hv & Ha).
    split; [exact Ho|]. split; [exact He|]. split.
    + rewrite <- Hv. apply load_bytes_ext8. intros i Hi.
      assert (Hp : S (PByte b (o + i))) by (apply HS; left; exists i; split; [exact Hi | reflexivity]).
      pose proof (Hs _ Hp) as Hs'. cbn iota beta in Hs'. rewrite <- Z.add_assoc. apply (Hs' reg); [exact Hl|lia|lia].
    + assert (Hp : S (PAux b o)) by (apply HS; right; reflexivity).
      pose proof (Hs _ Hp) as Hs'. cbn iota beta in Hs'. unfold aux_holds. rewrite (Hs' reg Hl Ho ltac:(lia)).
      destruct Ha as [E|(Hf & Ht)]; [left; exact E|].
      right. split; [exact (freed_in_grows _ _ _ Hg Hf) | exact (traps_as_freed_grows _ _ _ Hg Ht)].
Qed.

(** [pcell] survives a safepoint ([aux_holds_moves]). *)
Lemma pcell_sp_stable : forall b o x, sp_stable (pcell b o x).
Proof.
  intros b o x S m m' (HS & Hb & H) Hr Hbytes Ha. split; [exact HS|]. split; [rewrite Hr; exact Hb|].
  intros reg Hl. unfold live_at in Hl. rewrite Hr in Hl. destruct (H reg Hl) as (Ho & He & Hv & Hx).
  split; [exact Ho|]. split; [exact He|]. split; [rewrite (load_bytes_same m m' _ _ Hbytes); exact Hv|].
  exact (aux_holds_moves _ _ _ _ Hr Ha Hx).
Qed.

(** [pcell] owns pieces of its object. *)
Lemma pcell_registered : forall b o x, owns_registered (pcell b o x).
Proof. intros b o x S m (HS & Hb & _) p Hp. apply HS in Hp as [(i & _ & ->)| ->]; exact Hb. Qed.

(** [node] is stable. *)
Lemma node_stable : forall b next v, stable (node b next v).
Proof.
  intros. unfold node. repeat apply star_stable;
    auto using meta_stable, live_stable, pcell_stable, icell_stable.
Qed.

(** [node] survives a safepoint. *)
Lemma node_sp_stable : forall b next v, sp_stable (node b next v).
Proof.
  intros. unfold node. repeat apply star_sp_stable;
    auto using meta_sp_stable, live_sp_stable, pcell_sp_stable, icell_sp_stable.
Qed.

(** [node] owns pieces of its object. *)
Lemma node_registered : forall b next v, owns_registered (node b next v).
Proof.
  intros. unfold node. repeat apply star_registered;
    auto using meta_registered, live_registered, pcell_registered, icell_registered.
Qed.

(** [lst] is stable. *)
Lemma lst_stable : forall xs p, stable (lst p xs).
Proof.
  induction xs as [|v xs IH]; intros p; cbn [lst]; [apply pure_stable|].
  apply hex_stable. intros next.
  apply star_stable; [apply pure_stable|]. apply star_stable; [apply node_stable | apply IH].
Qed.

(** [lst] survives a safepoint: the list never stores the capability
    of a freed object, and what it stores is known up to the
    collector's rewriting anyway. *)
Lemma lst_safepoint : forall xs p, sp_stable (lst p xs).
Proof.
  induction xs as [|v xs IH]; intros p; cbn [lst]; [apply pure_sp_stable|].
  apply hex_sp_stable. intros next.
  apply star_sp_stable; [apply pure_sp_stable|]. apply star_sp_stable; [apply node_sp_stable | apply IH].
Qed.

(** [lst] owns pieces of objects. *)
Lemma lst_registered : forall xs p, owns_registered (lst p xs).
Proof.
  induction xs as [|v xs IH]; intros p; cbn [lst]; [apply pure_registered|].
  apply hex_registered. intros next.
  apply star_registered; [apply pure_registered|]. apply star_registered; [apply node_registered | apply IH].
Qed.

(** ## The steps that change memory *)

(** An 8-byte store at offset o of the live object b, in bounds, keeps
    every footprint that owns none of those bytes: other live objects
    do not overlap b. *)
Lemma store_same_on : forall m b o reg x, live_disjoint m -> live_at m b reg -> 0 <= o ->
  b + o + 8 <= r_end reg -> keeps (bytes8 b o) m (store_bytes m (b + o) 8 x).
Proof.
  intros m b o reg x Hd Hl Ho He S HS p Hp. specialize (HS p Hp).
  destruct p as [b'|b' o'|b' o']; cbn iota beta.
  - intros reg' E. exact E.
  - intros reg' Hl' Ho' He'. apply store_bytes_other. intros Ha. change (live_at m b' reg') in Hl'.
    destruct (Z.eq_dec b' b) as [->|Hne].
    + assert (reg' = reg) as -> by (destruct Hl, Hl'; congruence).
      apply HS. exists (o' - o). split; [lia|]. f_equal. lia.
    + destruct (Hd b' reg' b reg Hl' Hl Hne); lia.
  - intros. reflexivity.
Qed.

(** An aux store at offset o of the live object b, in bounds, keeps
    every footprint that does not own that slot. *)
Lemma aux_store_same_on : forall m b o reg c, live_disjoint m -> live_at m b reg -> 0 <= o ->
  b + o + 8 <= r_end reg -> keeps (eq (PAux b o)) m (store_aux m (b + o) c).
Proof.
  intros m b o reg c Hd Hl Ho He S HS p Hp. specialize (HS p Hp).
  destruct p as [b'|b' o'|b' o']; cbn iota beta.
  - intros reg' E. exact E.
  - intros. reflexivity.
  - intros reg' Hl' Ho' He'. change (live_at m b' reg') in Hl'. cbn [m_aux store_aux].
    destruct (Z.eqb_spec (b' + o') (b + o)) as [Ha|_]; [exfalso|reflexivity].
    destruct (Z.eq_dec b' b) as [->|Hne].
    + apply HS. f_equal. lia.
    + destruct (Hd b' reg' b reg Hl' Hl Hne); lia.
Qed.

(** The pointer store's protocol in listsum.c (ensure, barrier, reload,
    then the capability and the address) is an aux store and then an
    8-byte store. *)
Lemma pointer_store_protocol : forall a x m,
  pointer_store_effects a x m [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite] =
  Some (store_bytes (store_aux m a (ptr_cap x)) a 8 (ptr_addr x)).
Proof. reflexivity. Qed.

(** That pointer store at offset o of the live object b, in bounds,
    keeps every footprint that owns none of the slot's pieces. *)
Lemma pointer_store_same_on : forall m b o reg c v, live_disjoint m -> live_at m b reg -> 0 <= o ->
  b + o + 8 <= r_end reg -> keeps (pcell_pieces b o) m (store_bytes (store_aux m (b + o) c) (b + o) 8 v).
Proof.
  intros m b o reg c v Hd Hl Ho He S HS. apply same_on_trans with (store_aux m (b + o) c); [reflexivity| |].
  - apply (aux_store_same_on m b o reg c Hd Hl Ho He). intros p Hp E. apply (HS p Hp). right. symmetry. exact E.
  - apply (store_same_on (store_aux m (b + o) c) b o reg v); [|exact Hl|exact Ho|exact He|].
    + exact (live_disjoint_same m _ eq_refl Hd).
    + intros p Hp E. apply (HS p Hp). left. exact E.
Qed.

(** Allocating at a [fresh] base keeps every footprint: no one owns
    the new identity, and no byte changes. *)
Lemma alloc_same_on : forall S m q base, fresh m q base -> same_on S m (allocated m q base).
Proof.
  intros S m q base (_ & _ & _ & Hn & _) p _. destruct p as [b|b o|b o]; cbn iota beta.
  - intros reg E. rewrite object_region_allocated. destruct (Z.eqb_spec base b) as [<-|_]; [congruence | exact E].
  - intros. reflexivity.
  - intros. reflexivity.
Qed.

(** Allocating at a [fresh] base moves no object. *)
Lemma alloc_grows : forall m q base, fresh m q base -> grows m (allocated m q base).
Proof.
  intros m q base (_ & _ & _ & Hn & _) b reg E. left. rewrite object_region_allocated.
  destruct (Z.eqb_spec base b) as [<-|_]; [congruence | exact E].
Qed.

(** A footprint of objects of m owns nothing of a [fresh] base. *)
Lemma registered_fresh : forall S m q base p, registered S m -> fresh m q base -> S p -> piece_id p <> base.
Proof. intros S m q base p Hr (_ & _ & _ & Hn & _) Hp E. apply (Hr p Hp). rewrite E. exact Hn. Qed.

(** ## Updating the owned cell *)

(** A write rule carries over a frame on the right that does not own
    what is written. *)
Lemma writes_star_l : forall W m m' P P' Q, keeps W m m' -> grows m m' -> stable Q ->
  writes W m m' P P' -> writes W m m' (P ** Q)%h (P' ** Q)%h.
Proof.
  intros W m m' P P' Q Hk Hg HQ HP S (S1 & S2 & HS & Hd & H1 & H2).
  destruct (HP S1 H1) as [H1' HW]. split.
  - exists S1, S2. split; [exact HS|]. split; [exact Hd|]. split; [exact H1'|].
    apply (HQ S2 m m' H2); [|exact Hg]. apply Hk. intros p Hp Hw. apply (Hd p). split; [apply HW, Hw | exact Hp].
  - intros p Hw. apply HS. left. apply HW, Hw.
Qed.

(** A write rule carries over a frame on the left. *)
Lemma writes_star_r : forall W m m' P P' Q, keeps W m m' -> grows m m' -> stable Q ->
  writes W m m' P P' -> writes W m m' (Q ** P)%h (Q ** P')%h.
Proof.
  intros W m m' P P' Q Hk Hg HQ HP S (S1 & S2 & HS & Hd & H1 & H2).
  destruct (HP S2 H2) as [H2' HW]. split.
  - exists S1, S2. split; [exact HS|]. split; [exact Hd|]. split; [|exact H2'].
    apply (HQ S1 m m' H1); [|exact Hg]. apply Hk. intros p Hp Hw. apply (Hd p). split; [exact Hp | apply HW, Hw].
  - intros p Hw. apply HS. right. apply HW, Hw.
Qed.

(** After an 8-byte store of an unsigned x at offset o of b, the owned
    cell there holds x. *)
Lemma icell_writes : forall m b o v x, 0 <= x < 2 ^ 64 ->
  writes (bytes8 b o) m (store_bytes m (b + o) 8 x) (icell b o v) (icell b o x).
Proof.
  intros m b o v x Hx S (HS & Hb & H). split; [|intros p Hp; apply HS, Hp].
  split; [exact HS|]. split; [exact Hb|]. intros reg Hl. destruct (H reg Hl) as (Ho & He & _).
  split; [exact Ho|]. split; [exact He|]. apply load_store_bytes, Hx.
Qed.

(** After the pointer store of x' at offset o of b, the owned slot there
    holds x'. *)
Lemma pcell_writes : forall m b o x x', 0 <= ptr_addr x' < 2 ^ 64 ->
  writes (pcell_pieces b o) m (store_bytes (store_aux m (b + o) (ptr_cap x')) (b + o) 8 (ptr_addr x'))
    (pcell b o x) (pcell b o x').
Proof.
  intros m b o x x' Hx S (HS & Hb & H). split; [|intros p Hp; apply HS, Hp].
  split; [exact HS|]. split; [exact Hb|]. intros reg Hl. destruct (H reg Hl) as (Ho & He & _).
  split; [exact Ho|]. split; [exact He|]. split; [apply load_store_bytes, Hx|].
  left. cbn [m_aux store_bytes store_aux]. rewrite Z.eqb_refl. reflexivity.
Qed.

(** A node's object is live, a heap object of 16 bytes. *)
Lemma node_region : forall b x v S m, node b x v S m ->
  object_region b (m_regions m) = Some (mkRegion b (b + 16) Heap Live).
Proof.
  intros b x v S m (S1 & S2 & _ & _ & (_ & reg & E & Hk & Hl) & (S3 & S4 & _ & _ & (_ & reg' & E' & L') & _)).
  rewrite E in E'. injection E' as <-. specialize (Hl L'). pose proof (object_region_base _ _ _ E) as Hb.
  rewrite E. destruct reg as [rb re rk rl]; cbn in *; subst. reflexivity.
Qed.

(** A node's next slot reads as its next pointer. *)
Lemma node_next : forall b x v S m, node b x v S m ->
  load_bytes m b 8 = ptr_addr x /\ aux_holds m b (ptr_cap x).
Proof.
  intros b x v S m H. pose proof (node_region _ _ _ _ _ H) as Hr.
  destruct H as (S1 & S2 & _ & _ & _ & (S3 & S4 & _ & _ & _ & (S5 & S6 & _ & _ & (_ & _ & Hp) & _))).
  destruct (Hp _ (conj Hr eq_refl)) as (_ & _ & Hv & Ha). rewrite Z.add_0_r in Hv, Ha. auto.
Qed.

(** The pointer store of x' into the next slot of the node at b, which
    the assertion owns, makes x' its next pointer, and keeps the
    frame Q. *)
Lemma node_store_next : forall m b x x' v Q S, live_disjoint m -> stable Q -> 0 <= ptr_addr x' < 2 ^ 64 ->
  (node b x v ** Q)%h S m ->
  (node b x' v ** Q)%h S (store_bytes (store_aux m b (ptr_cap x')) b 8 (ptr_addr x')).
Proof.
  intros m b x x' v Q S Hd HQ Hx H.
  destruct (star_elim_l _ _ _ _ H) as (S0 & H0). pose proof (node_region _ _ _ _ _ H0) as Hr.
  set (m' := store_bytes (store_aux m b (ptr_cap x')) b 8 (ptr_addr x')).
  assert (Hk : keeps (pcell_pieces b 0) m m').
  { pose proof (pointer_store_same_on m b 0 _ (ptr_cap x') (ptr_addr x') Hd (conj Hr eq_refl)) as K.
    rewrite Z.add_0_r in K. apply K; cbn; lia. }
  assert (Hg : grows m m') by (apply grows_same; reflexivity).
  refine (proj1 (writes_star_l _ _ _ _ _ Q Hk Hg HQ _ S H)).
  unfold node. apply writes_star_r; [exact Hk | exact Hg | apply meta_stable|].
  apply writes_star_r; [exact Hk | exact Hg | apply live_stable|].
  apply writes_star_l; [exact Hk | exact Hg | apply icell_stable|].
  pose proof (pcell_writes m b 0 x x' Hx) as W. rewrite Z.add_0_r in W. exact W.
Qed.

(** The 8-byte store of an unsigned x into the value slot of the node
    at b, which the assertion owns, makes x its value, and keeps the
    frame Q. *)
Lemma node_store_value : forall m b next v x Q S, live_disjoint m -> stable Q -> 0 <= x < 2 ^ 64 ->
  (node b next v ** Q)%h S m -> (node b next x ** Q)%h S (store_bytes m (b + 8) 8 x).
Proof.
  intros m b next v x Q S Hd HQ Hx H.
  destruct (star_elim_l _ _ _ _ H) as (S0 & H0). pose proof (node_region _ _ _ _ _ H0) as Hr.
  assert (Hk : keeps (bytes8 b 8) m (store_bytes m (b + 8) 8 x))
    by (apply (store_same_on m b 8 _ x Hd (conj Hr eq_refl)); cbn; lia).
  assert (Hg : grows m (store_bytes m (b + 8) 8 x)) by (apply grows_same; reflexivity).
  refine (proj1 (writes_star_l _ _ _ _ _ Q Hk Hg HQ _ S H)).
  unfold node. apply writes_star_r; [exact Hk | exact Hg | apply meta_stable|].
  apply writes_star_r; [exact Hk | exact Hg | apply live_stable|].
  apply writes_star_r; [exact Hk | exact Hg | apply pcell_stable|].
  apply icell_writes, Hx.
Qed.

(** After allocating a 16-byte heap object at a [fresh] base b, the
    pieces [node_pieces] of b make a node with a null next pointer and
    the value 0: Fil-C's allocation reads as zero, with no stored
    capability. *)
Lemma alloc_node : forall m b, fresh m (heap_req 16 16) b ->
  node b null 0 (node_pieces b) (allocated m (heap_req 16 16) b).
Proof.
  intros m b Hf. pose proof Hf as (_ & _ & _ & _ & _ & Hz). cbn [req_extent heap_req] in Hz.
  change ((16 + 15) / 16 * 16) with 16 in Hz.
  set (m' := allocated m (heap_req 16 16) b).
  assert (Hr : object_region b (m_regions m') = Some (mkRegion b (b + 16) Heap Live))
    by (cbn; rewrite Z.eqb_refl; reflexivity).
  assert (Hl : forall reg, live_at m' b reg -> reg = mkRegion b (b + 16) Heap Live)
    by (intros reg [E _]; rewrite Hr in E; injection E as <-; reflexivity).
  assert (Hn : object_region b (m_regions m') <> None) by (rewrite Hr; discriminate).
  exists (fun _ => False), (node_pieces b). split; [intros p; tauto|]. split; [intros p; tauto|].
  split.
  { split; [intros p; tauto|]. exists (mkRegion b (b + 16) Heap Live). split; [exact Hr|]. split; reflexivity. }
  exists (eq (PLive b)), (fun p => pcell_pieces b 0 p \/ bytes8 b 8 p).
  split; [intros p; unfold node_pieces, pcell_pieces; split; intros H; [destruct H as [<-|[H|[H|H]]]|destruct H as [<-|[[H|H]|H]]]; tauto|].
  split; [intros p [<- [[(i & _ & E)|E]|(i & _ & E)]]; discriminate|].
  split; [split; [intros p; tauto | exists (mkRegion b (b + 16) Heap Live); split; [exact Hr|reflexivity]]|].
  exists (pcell_pieces b 0), (bytes8 b 8). split; [intros p; tauto|].
  split; [intros p [[(i & Hi & ->)| ->] (j & Hj & E')]; [assert (0 + i = 8 + j) by congruence; lia | discriminate]|].
  split.
  - split; [intros p; apply iff_refl|]. split; [exact Hn|]. intros reg Hreg. apply Hl in Hreg as ->.
    split; [lia|]. split; [cbn; lia|]. rewrite Z.add_0_r. split.
    + apply load_bytes_zero. intros i Hi. apply (Hz (b + i)). lia.
    + left. exact (proj2 (Hz b ltac:(lia))).
  - split; [intros p; tauto|]. split; [exact Hn|]. intros reg Hreg. apply Hl in Hreg as ->.
    split; [lia|]. split; [cbn; lia|].
    apply load_bytes_zero. intros i Hi. rewrite <- Z.add_assoc. apply (Hz (b + (8 + i))). lia.
Qed.

(** Allocating a node at a [fresh] base adds it to any stable
    assertion P of pieces of objects: the new pieces are disjoint from
    P's, since no one owned the new identity. *)
Lemma alloc_frame : forall m b P S, fresh m (heap_req 16 16) b -> stable P -> owns_registered P -> P S m ->
  (node b null 0 ** P)%h (fun p => node_pieces b p \/ S p) (allocated m (heap_req 16 16) b).
Proof.
  intros m b P S Hf HP Hreg H. exists (node_pieces b), S. split; [intros p; tauto|]. split.
  - intros p [Hn Hs]. apply (registered_fresh S m _ b p (Hreg _ _ H) Hf Hs).
    destruct Hn as [->|[(i & _ & ->)|[->|(i & _ & ->)]]]; reflexivity.
  - split; [exact (alloc_node m b Hf)|]. exact (HP S m _ H (alloc_same_on S m _ b Hf) (alloc_grows m _ b Hf)).
Qed.

(** ## The list *)

(** The empty list at null owns nothing. *)
Lemma lst_nil : forall m, lst null [] (fun _ => False) m.
Proof. intros m. split; [intros p; tauto | reflexivity]. Qed.

(** A nonempty list is a [lst_cons] for some next pointer. *)
Lemma lst_cons_iff : forall p v xs S m, lst p (v :: xs) S m <-> exists next, lst_cons p v next xs S m.
Proof. intros. reflexivity. Qed.

(** A list's pointer is null, or a live object's capability. *)
Lemma lst_cap : forall xs p S m, lst p xs S m ->
  ptr_cap p = CNone \/ exists b reg, ptr_cap p = Obj b /\ live_at m b reg.
Proof.
  intros [|v xs] p S m H; cbn [lst] in H.
  - destruct H as [_ ->]. left. reflexivity.
  - destruct H as (next & S1 & S2 & _ & _ & (_ & Hp & _) & H2). right.
    destruct (star_elim_l _ _ _ _ H2) as (S3 & H3). exists (ptr_addr p), (mkRegion (ptr_addr p) (ptr_addr p + 16) Heap Live).
    rewrite Hp at 1. split; [reflexivity|]. split; [exact (node_region _ _ _ _ _ H3) | reflexivity].
Qed.

(** A list's address is 0 or a node's, inside the address space when
    every object is ([objects_fit]). *)
Lemma lst_range : forall xs p S m, objects_fit (m_regions m) -> lst p xs S m -> 0 <= ptr_addr p < 2 ^ 48.
Proof.
  intros [|v xs] p S m Hfit H; cbn [lst] in H.
  - destruct H as [_ ->]. cbn. lia.
  - destruct H as (next & S1 & S2 & _ & _ & (_ & _ & Hpos & _) & H2).
    destruct (star_elim_l _ _ _ _ H2) as (S3 & H3). destruct (Hfit _ _ (node_region _ _ _ _ _ H3)). cbn in *. lia.
Qed.

(** A list at a nonzero address is a node and the rest. *)
Lemma lst_nonnull : forall xs p R S m, ptr_addr p <> 0 -> (lst p xs ** R)%h S m ->
  exists v next xs', (lst_cons p v next xs' ** R)%h S m.
Proof.
  intros [|v xs] p R S m Hp H.
  - destruct (star_elim_l _ _ _ _ H) as (S1 & _ & ->). cbn in Hp. lia.
  - cbn [lst] in H. apply star_hex_l in H as (next & H). exists v, next, xs. exact H.
Qed.

(** What a node of a list gives a step that reads it: its address a,
    aligned, inside the address space, a live 16-byte heap object
    whose next slot holds next, address in the bytes and capability,
    exactly, in the aux. *)
Lemma lst_cons_facts : forall p v next xs R S m, objects_fit (m_regions m) -> (lst_cons p v next xs ** R)%h S m ->
  exists a, p = mkPtr a (Obj a) /\ 0 < a /\ a mod 8 = 0 /\ a + 16 <= 2 ^ 48 /\
    object_region a (m_regions m) = Some (mkRegion a (a + 16) Heap Live) /\
    load_bytes m a 8 = ptr_addr next /\ m_aux m a = ptr_cap next.
Proof.
  intros p v next xs R S m Hfit H. destruct (star_elim_l _ _ _ _ H) as (S0 & S1 & S2 & _ & _ & (_ & Hp & Hpos & Hal) & H2).
  destruct (star_elim_l _ _ _ _ H2) as (S3 & H3). destruct (star_elim_r _ _ _ _ H2) as (S4 & H4).
  pose proof (node_region _ _ _ _ _ H3) as Hr. destruct (node_next _ _ _ _ _ H3) as [Hv Ha].
  exists (ptr_addr p). split; [exact Hp|]. split; [exact Hpos|]. split; [exact Hal|].
  split; [destruct (Hfit _ _ Hr); cbn in *; lia|]. split; [exact Hr|]. split; [exact Hv|].
  apply (aux_holds_live _ _ _ Ha). exact (lst_cap _ _ _ _ H4).
Qed.

(** A node and the rest of a list make a list one longer. *)
Lemma lst_cons_intro : forall b h v xs S m, 0 < b -> b mod 8 = 0 ->
  (node b h v ** lst h xs)%h S m -> lst (mkPtr b (Obj b)) (v :: xs) S m.
Proof.
  intros b h v xs S m Hb Hal H. cbn [lst]. exists h. apply star_pure_intro; [|exact H].
  cbn. auto.
Qed.

(** Walking past a node drops it, and its pure facts, into [htrue]. *)
Lemma lst_cons_drop : forall p v next xs F S m,
  (lst_cons p v next xs ** htrue ** F)%h S m -> (lst next xs ** htrue ** F)%h S m.
Proof.
  intros p v next xs F S m H. unfold lst_cons in H. apply star_assoc_r in H.
  apply (star_mono_r _ _ _ _ _ (star_assoc_r _ _ _)) in H.
  apply (star_mono_r _ _ _ _ _ (star_swap _ _ _)) in H. apply star_swap in H. revert H. apply star_mono_r.
  intros S0 m0 H. apply (star_mono_r _ _ _ _ _ (fun S1 m1 => htrue_absorb _ _ S1 m1 (node_registered _ _ _))) in H.
  exact (htrue_absorb _ _ _ _ (pure_registered _) H).
Qed.
