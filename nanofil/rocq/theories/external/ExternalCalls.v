(** External calls describe permitted memory effects and observable events.
    This framework preserves runtime readiness and object identities across
    each call. The glibc campaign also uses its byte-fill and copy contracts;
    the older libc specifications live in
    [LibcCalls](../hello_contracts/LibcCalls.v). *)

From Stdlib Require Import String ZArith List Bool Lia Relations.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Machine Identity.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Authority and footprints *)

(** A span: a pointer span_ptr, whose [[capability]] is the authority,
    and the number of bytes span_size from its address. Contracts name
    the memory a call may read capabilities from or write as spans. *)
Record span : Type := mkSpan { span_ptr : ptr; span_size : Z }.

(** Address a lies in span s: from the span's address up to, but not
    including, that address plus its size. *)
Definition span_contains (s : span) (a : Z) : Prop :=
  ptr_addr (span_ptr s) <= a < ptr_addr (span_ptr s) + span_size s.

(** Span s is writable in memory m: its size is nonnegative, and its
    pointer carries an explicit [Obj] [[capability]] for a live
    [[region|object]] that permits writing all its bytes ([access_res]
    with [Write]), even when the size is zero. The life test matters for
    zero-length spans of freed objects, which the access check alone
    would pass. *)
Definition writable_span (m : mem) (s : span) : Prop :=
  0 <= span_size s /\
  exists base reg,
    ptr_cap (span_ptr s) = Obj base /\
    object_region base (m_regions m) = Some reg /\ r_life reg = Live /\
    access_res m (ptr_addr (span_ptr s)) (Obj base) (span_size s) Write 1 = Some ok.

(** A call may write address a of memory m if a lies in one of the
    contract's writable roots (each a [writable_span]), or inside a live
    heap object whose base is in born, the objects this call allocated.
    Born objects belong to this call; old objects require an explicit
    root supplied by the contract. Writes to the [[aux]] use the same
    roots but need not have the same byte footprint (a partial memset,
    for instance). *)
Definition write_authority (roots : list span) (born : list Z) (m : mem) (a : Z) : Prop :=
  (exists s, In s roots /\ writable_span m s /\ span_contains s a) \/
  (exists base reg, In base born /\ object_region base (m_regions m) = Some reg /\
    r_kind reg = Heap /\ r_life reg = Live /\ base <= a < r_end reg).

(** Capability c is one a call with readable spans sources and born
    objects born may store in memory m: no capability ([CNone]); a
    source pointer's own capability, copied; one loaded from a complete
    eight-byte pointer slot inside a source, read through that source's
    capability (the [[aux]] entry [m_aux] at the slot); or [Obj] or [Ro]
    of an object this call allocated. In particular, [Ro] never becomes
    [Obj] merely because their address bits coincide. Contracts copying
    parts of pointers (the runtime's smidgens) must extend this
    complete-slot rule first. *)
Definition available_cap (sources : list span) (born : list Z) (m : mem) (c : cap) : Prop :=
  c = CNone \/
  (exists s, In s sources /\ c = ptr_cap (span_ptr s)) \/
  (exists s a, In s sources /\ span_contains s a /\
    a + 8 <= ptr_addr (span_ptr s) + span_size s /\
    access_res m a (ptr_cap (span_ptr s)) 8 Read 8 = Some ok /\ c = m_aux m a) \/
  (exists base, In base born /\ (c = Obj base \/ c = Ro base)).

(** Every address a call has [write_authority] over lies inside some
    object of the memory ([in_object]); [local_effect_kept] needs this. *)
Lemma write_authority_in : forall roots born m a,
  write_authority roots born m a -> in_object m a.
Proof.
  intros roots born m a [(s & _ & (_ & base & reg & Hcap & Hr & _ & Ha) & Hin) |
                        (base & reg & _ & Hr & _ & _ & Hin)].
  - eapply access_in; [exact Ha | exact Hin].
  - exists base, reg. auto.
Qed.

(** One allocation-free segment of a call's memory effect, from m to m':
    - every object of m is still an object of m' ([ids]);
    - each object of m' is as it was in m or, if its base is in releases
      or born and it was a live heap object, freed with empty bounds;
    - bytes and [[aux]] entries outside [write_authority] are unchanged;
    - every changed stored capability is [available_cap] from sources.

    Byte and [[shadow]] footprints are independent, but every changed
    cell needs write authority, and a changed stored capability needs a
    source. Release permissions are separate from write permissions. *)
Definition local_effect (sources roots : list span) (releases born : list Z) (m m' : mem) : Prop :=
  ids m m' /\
  (forall b reg', object_region b (m_regions m') = Some reg' ->
    exists reg, object_region b (m_regions m) = Some reg /\
      (reg' = reg \/ (In b (releases ++ born) /\ r_kind reg = Heap /\
        r_life reg = Live /\ reg' = mkRegion b b Heap Freed))) /\
  (forall a, ~ write_authority roots born m a ->
    m_bytes m' a = m_bytes m a /\ m_aux m' a = m_aux m a) /\
  (forall a, m_aux m' a = m_aux m a \/ available_cap sources born m (m_aux m' a)).

(** A [local_effect] is a change the program itself may make to memory
    ([kept]), so the [[runtime]] stays [[ready]] across it by the
    runtime axiom [ready_kept]. *)
Lemma local_effect_kept : forall sources roots releases born m m',
  local_effect sources roots releases born m m' -> kept m m'.
Proof.
  intros sources roots releases born m m' (_ & Hr & Hw & _). split.
  - intros b reg' H. destruct (Hr _ _ H) as (reg & E & [-> | (_ & Hk & Hl & ->)]).
    + exists reg. auto.
    + exists reg. split; auto. right. rewrite Hk. auto.
  - intros a Hout. apply Hw. intros Ha. apply Hout. eapply write_authority_in; eauto.
Qed.

(** Changing nothing is a [local_effect]. *)
Lemma local_effect_refl : forall sources roots releases born m,
  local_effect sources roots releases born m m.
Proof.
  intros. split; [apply ids_refl|]. split; [intros b reg E; exists reg; auto |]. auto.
Qed.

(** Storing the n bytes of x at address a is a [local_effect], if the
    call has [write_authority] over each of those n addresses. *)
Lemma local_store_bytes : forall sources roots releases born m a n x,
  (forall b, a <= b < a + n -> write_authority roots born m b) ->
  local_effect sources roots releases born m (store_bytes m a n x).
Proof.
  intros sources roots releases born m a n x Ha.
  split; [apply ids_same; reflexivity|]. split.
  - intros b reg E. exists reg. auto.
  - split; [|intros b; left; reflexivity]. intros b Hn. simpl. split; [|reflexivity].
    destruct ((a <=? b) && (b <? a + n)) eqn:E; [|reflexivity].
    exfalso. apply Hn, Ha. apply andb_true_iff in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

(** Construction facts shared by native buffer setup and entry vectors.
    Writing a pointer requires a capability source as well as writable
    bytes. These are ordinary model stores, not additional axioms. *)
Lemma local_store_pointer : forall sources roots releases born m a p,
  (forall b, a <= b < a + 8 -> write_authority roots born m b) ->
  available_cap sources born m (ptr_cap p) ->
  local_effect sources roots releases born m
    (store_aux (store_bytes m a 8 (ptr_addr p)) a (ptr_cap p)).
Proof.
  intros sources roots releases born m a p Ha Hcap.
  split; [apply ids_same; reflexivity|]. split.
  - intros b reg E. exists reg. auto.
  - split.
    + intros b Hn. simpl. split.
      * destruct ((a <=? b) && (b <? a + 8)) eqn:E; [|reflexivity].
        exfalso. apply Hn, Ha. apply andb_true_iff in E as [E1 E2].
        apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
      * destruct (b =? a) eqn:E; [|reflexivity].
        apply Z.eqb_eq in E. subst. exfalso. apply Hn, Ha. lia.
    + intros b. simpl. destruct (b =? a); [right; exact Hcap|left; reflexivity].
Qed.

Lemma load_bytes_agree : forall m m' a size,
  0 <= size ->
  (forall i, 0 <= i < size -> m_bytes m (a + i) = m_bytes m' (a + i)) ->
  load_bytes m a size = load_bytes m' a size.
Proof.
  intros m m' a size Hsize Hbytes. unfold load_bytes.
  remember (Z.to_nat size) as n eqn:En.
  assert (Hn : Z.of_nat n <= size) by (rewrite En, Z2Nat.id; lia).
  clear En. revert Hn. generalize 0 as acc.
  induction n as [|n IH]; intros acc Hn; [reflexivity|].
  cbn -[Z.of_nat Z.add Z.mul].
  rewrite Hbytes by (rewrite Nat2Z.inj_succ in Hn; lia).
  apply IH. rewrite Nat2Z.inj_succ in Hn. lia.
Qed.

Lemma stored_byte : forall m a size x i,
  0 <= i < size -> m_bytes (store_bytes m a size x) (a + i) = byte_of x i.
Proof.
  intros m a size x i Hi. unfold store_bytes. simpl.
  assert ((a <=? a + i) = true) as Hlo by (apply Z.leb_le; lia).
  assert ((a + i <? a + size) = true) as Hhi by (apply Z.ltb_lt; lia).
  rewrite Hlo, Hhi. simpl. replace (a + i - a) with i by lia. reflexivity.
Qed.

Lemma stored_bytes_value : forall m a size x,
  0 <= size -> load_bytes (store_bytes m a size x) a size = x mod 256 ^ size.
Proof.
  intros m a size x Hsize. unfold load_bytes.
  remember (Z.to_nat size) as n eqn:En.
  assert (Hn : Z.of_nat n <= size) by (rewrite En, Z2Nat.id; lia).
  replace (x mod 256 ^ size) with
    (0 * 256 ^ Z.of_nat n + x mod 256 ^ Z.of_nat n)
    by (rewrite En, Z2Nat.id by lia; ring).
  clear En. revert Hn. generalize 0 as acc.
  induction n as [|n IH]; intros acc Hn.
  - cbn -[Z.add Z.mul Z.modulo]. rewrite Z.mod_1_r. ring.
  - cbn -[store_bytes Z.of_nat Z.add Z.mul Z.pow].
    rewrite stored_byte by (rewrite Nat2Z.inj_succ in Hn; lia).
    rewrite IH by (rewrite Nat2Z.inj_succ in Hn; lia).
    unfold byte_of. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite Z.pow_mul_r by lia. change (2 ^ 8) with 256.
    pose proof (Z.pow_pos_nonneg 256 (Z.of_nat n) ltac:(lia) ltac:(lia)) as Hpow.
    rewrite (Z.mul_comm 256 (256 ^ Z.of_nat n)), Z.rem_mul_r by lia.
    ring.
Qed.

(** A fresh allocation cannot shadow an already registered identity or
    invalidate a capability-backed root of the caller. *)
Lemma allocated_old_region : forall m q base old reg,
  object_region base (m_regions m) = None ->
  object_region old (m_regions m) = Some reg ->
  object_region old (m_regions (allocated m q base)) = Some reg.
Proof.
  intros m q base old reg Hnew Hold. simpl.
  assert ((base =? old) = false) as E.
  { apply Z.eqb_neq. intros ->. rewrite Hnew in Hold. discriminate. }
  rewrite E. exact Hold.
Qed.

Lemma allocated_old_access : forall m q base a c size rights align,
  object_region base (m_regions m) = None ->
  access_res m a c size rights align = Some ok ->
  access_res (allocated m q base) a c size rights align = Some ok.
Proof.
  intros m q base a c size rights align Hnew Ha.
  unfold access_res, cap_access_res in Ha. destruct c as [|old|old|f|f]; try discriminate.
  all: destruct (object_region old (m_regions m)) as [reg|] eqn:E; try discriminate.
  all: unfold access_res, cap_access_res;
    rewrite (allocated_old_region m q base old reg Hnew E); exact Ha.
Qed.

Lemma allocated_old_span : forall m q base s,
  object_region base (m_regions m) = None -> writable_span m s ->
  writable_span (allocated m q base) s.
Proof.
  intros m q base s Hnew [Hsize [old [reg [Hcap [Hr [Hl Ha]]]]]].
  split; [exact Hsize|]. exists old, reg. split; [exact Hcap|].
  split; [eapply allocated_old_region; eauto|]. split; [exact Hl|].
  eapply allocated_old_access; eauto.
Qed.

(** ## Events and contract results *)

(** An observation an [[external call]] makes: [StreamBytes] stream
    bytes, bytes that stdio accepted for the stream with descriptor
    number stream (possibly only into its buffer, not a kernel write),
    or [ProcessExit] status, the end of the process. *)
Inductive event : Type :=
| StreamBytes (stream : Z) (bytes : list Z)
| ProcessExit (status : Z).

(** How a completed call ends: returning the [[word|words]] values,
    exiting the process with status, or a resource ending with the
    [[trap]] reason why. *)
Inductive call_end : Type :=
| CallReturn (values : list word)
| CallExit (status : Z)
| CallResource (why : reason).

(** A resource reason: out of memory, or a request too big. These are
    the only [[trap]] reasons a call within its contract may end with,
    and they are not capability panics; [puts_contract] allows both. *)
Definition resource_reason (why : reason) : Prop :=
  why = OutOfMemory \/ why = TooBig.

(** The words values fit the declared return type ty: none for void,
    one word already at its [[class]] for a scalar, one per class for a
    tuple. Keep the declared return shape: an empty or singleton tuple
    is not a void or scalar return. The machine adapter must use this
    signature, not [words_outcome]'s list-length convention. *)
Definition return_shape (ty : ret_type) (values : list word) : Prop :=
  match ty with
  | RVoid => values = []
  | RClass k => exists x, values = [x] /\ word_at_class k x = Some x
  | RTuple ks => Forall2 (fun k x => word_at_class k x = Some x) ks values
  end.

(** A returned [[word]] x carries only authority the call had: the
    capability of a pointer, or of a [[limit]] word, is [available_cap]
    from the sources and born objects in the final memory m; an integer
    needs none. *)
Definition word_authority (sources : list span) (born : list Z) (m : mem) (x : word) : Prop :=
  match x with
  | WPtr p => available_cap sources born m (ptr_cap p)
  | WLimit c _ => available_cap sources born m c
  | WInt _ => True
  end.

(** The [[external call|contract]] of one libc function, over a logical
    world of libc state. It separates, in order: the declared return
    type; the ABI premise on the call's result and argument syntax; the
    caller's precondition on the argument words, memory and world; the
    readable capability sources, writable roots and heap bases it may
    release; the allocation requests (alignment, size) it may make; its
    finite observable prefixes; its postcondition for normal endings;
    the reasons it may end for lack of resources; and its panic set.
    The panic set documents checks reachable outside the premises; it
    does not grant a transition when a premise fails. *)
Record contract (world : Type) : Type := mkContract {
  contract_returns : ret_type;
  contract_abi : call_result -> list arg -> Prop;
  contract_pre : list word -> mem -> world -> Prop;
  contract_sources : list word -> mem -> world -> list span;
  contract_writes : list word -> mem -> world -> list span;
  contract_releases : list word -> mem -> world -> list Z;
  contract_requests : list word -> mem -> world -> Z -> Z -> Prop;
  contract_prefix : list word -> mem -> world -> list Z -> list event -> mem -> world -> Prop;
  contract_post : list word -> mem -> world -> list Z -> list event -> call_end -> mem -> world -> Prop;
  contract_resource : reason -> Prop;
  contract_panics : reason -> Prop
}.

Arguments contract_returns {world}.
Arguments contract_abi {world}.
Arguments contract_pre {world}.
Arguments contract_sources {world}.
Arguments contract_writes {world}.
Arguments contract_releases {world}.
Arguments contract_requests {world}.
Arguments contract_prefix {world}.
Arguments contract_post {world}.
Arguments contract_resource {world}.
Arguments contract_panics {world}.

(** ## Bounded string scans *)

(** The first NUL is at offset k before the bound n, or all n bytes
    are nonzero and k=n. Only the consumed interval is readable; an
    early NUL does not require n readable bytes or address+n to fit.
    Even a zero-length scan requires a live object capability, allowing
    one-past but not null, expired or forged pointers. *)
Definition bounded_length (m : mem) (p : ptr) (n k : Z) : Prop :=
  0 <= n < 2 ^ 64 /\ 0 <= k <= n /\
  (exists base reg, (ptr_cap p = Obj base \/ ptr_cap p = Ro base) /\
    object_region base (m_regions m) = Some reg /\ r_life reg = Live) /\
  access_res m (ptr_addr p) (ptr_cap p) (k + (if k <? n then 1 else 0)) Read 1 = Some ok /\
  (forall i, 0 <= i < k -> 0 < m_bytes m (ptr_addr p + i) < 256) /\
  (k < n -> m_bytes m (ptr_addr p + k) = 0).

(** The first NUL, or the exhausted bound, uniquely fixes the result. *)
Lemma bounded_length_unique : forall m p n left right,
  bounded_length m p n left -> bounded_length m p n right -> left = right.
Proof.
  intros m p n left right (_ & Hl & _ & _ & Hbytesl & Hnull) (_ & Hr & _ & _ & Hbytesr & Hnulr).
  destruct (Z.lt_trichotomy left right) as [Hlt | [Heq | Hgt]]; [|exact Heq|].
  - specialize (Hbytesr left ltac:(lia)). rewrite Hnull in Hbytesr by lia. lia.
  - specialize (Hbytesl right ltac:(lia)). rewrite Hnulr in Hbytesl by lia. lia.
Qed.

(** An unbounded string terminates strictly before SIZE_MAX. The sentinel
    is a logical bound, not permission to read SIZE_MAX bytes: only the
    first k nonzero bytes and their NUL are required through p's live
    object capability. An exhausted nonterminated span is not a string. *)
Definition terminated_length (m : mem) (p : ptr) (k : Z) : Prop :=
  bounded_length m p (2 ^ 64 - 1) k /\ k < 2 ^ 64 - 1.

(** The first NUL uniquely fixes strlen's integer result, not just its sign. *)
Lemma terminated_length_unique : forall m p left right,
  terminated_length m p left -> terminated_length m p right -> left = right.
Proof. intros m p left right [Hl _] [Hr _]. eapply bounded_length_unique; eauto. Qed.

(** The read footprint is one identity's region (including life) and
    bytes at offsets 0 through k. Agreement on those pieces suffices;
    unrelated objects, bytes and every auxiliary slot may change. *)
Lemma terminated_length_agree : forall m m' p k,
  (forall base, ptr_cap p = Obj base \/ ptr_cap p = Ro base ->
    object_region base (m_regions m') = object_region base (m_regions m)) ->
  (forall i, 0 <= i <= k -> m_bytes m' (ptr_addr p + i) = m_bytes m (ptr_addr p + i)) ->
  terminated_length m p k -> terminated_length m' p k.
Proof.
  intros m m' p k Hregions Hbytes [(Hn & Hk & Hlife & Ha & Hbefore & Hnul) Hmax].
  destruct Hlife as (base & reg & Hcap & Hreg & Hlive).
  split; [|exact Hmax]. split; [exact Hn|]. split; [exact Hk|]. split.
  - exists base, reg. split; [exact Hcap|]. rewrite Hregions by exact Hcap. auto.
  - split.
    + unfold access_res, cap_access_res in Ha |- *.
      destruct Hcap as [Hcap|Hcap]; rewrite Hcap in Ha |- *;
        rewrite Hregions by auto; exact Ha.
    + split.
      * intros i Hi. rewrite Hbytes by lia. apply Hbefore. exact Hi.
      * intros Hlt. rewrite Hbytes by lia. apply Hnul. exact Hlt.
Qed.

(** A canonical size_t count of well-formed bytes is readable through
    one live object capability. Zero count still needs live authority,
    possibly one-past. This is a full-span premise, not an early-stop scan. *)
Definition readable_bytes (m : mem) (p : ptr) (n : Z) : Prop :=
  0 <= n < 2 ^ 64 /\
  (exists base reg, (ptr_cap p = Obj base \/ ptr_cap p = Ro base) /\
    object_region base (m_regions m) = Some reg /\ r_life reg = Live) /\
  access_res m (ptr_addr p) (ptr_cap p) n Read 1 = Some ok /\
  (forall i, 0 <= i < n -> 0 <= m_bytes m (ptr_addr p + i) < 256).

(** A shorter prefix retains the same live capability and byte domain. *)
Lemma readable_bytes_prefix : forall m p n k,
  readable_bytes m p n -> 0 <= k <= n -> readable_bytes m p k.
Proof.
  intros m p n k (Hn & Hlife & Ha & Hbytes) Hk.
  split; [lia|]. split; [exact Hlife|]. split; [|intros i Hi; apply Hbytes; lia].
  destruct Hlife as (base & reg & [Hcap|Hcap] & Hreg & Hlive);
    unfold access_res, cap_access_res in Ha |- *; rewrite Hcap, Hreg in Ha |- *.
  all: destruct ((base <=? ptr_addr p) && (ptr_addr p + n <=? r_end reg)) eqn:Hbounds;
    [|discriminate Ha].
  all: apply andb_true_iff in Hbounds as [Hlo Hhi]; apply Z.leb_le in Hhi.
  all: rewrite Hlo, (proj2 (Z.leb_le (ptr_addr p + k) (r_end reg)) ltac:(lia)); exact Ha.
Qed.

(** Every smaller consumed prefix is a readable byte span, including
    its witnessed NUL when present. No byte after that NUL is needed. *)
Lemma bounded_prefix_readable : forall m p n k count,
  bounded_length m p n k ->
  0 <= count <= k + (if k <? n then 1 else 0) -> readable_bytes m p count.
Proof.
  intros m p n k count (Hn & Hk & Hlive & Ha & Hbytes & Hnul) Hcount.
  assert (Hsmall : count <= n).
  { destruct (k <? n) eqn:E; [apply Z.ltb_lt in E|apply Z.ltb_ge in E]; lia. }
  split; [lia|]. split; [exact Hlive|]. split.
  - destruct Hlive as (base & reg & [Hcap | Hcap] & Hreg & _);
      unfold access_res in *; rewrite Hcap in *; cbn in *; rewrite Hreg in *.
    all: destruct ((base <=? ptr_addr p) &&
      (ptr_addr p + (k + (if k <? n then 1 else 0)) <=? r_end reg)) eqn:E;
      [|discriminate].
    all: apply andb_true_iff in E; destruct E as [Hlo Hhi];
      apply Z.leb_le in Hlo; apply Z.leb_le in Hhi.
    all: assert (E : (base <=? ptr_addr p) && (ptr_addr p + count <=? r_end reg) = true)
      by (apply andb_true_iff; split; apply Z.leb_le; lia).
    all: rewrite E; exact Ha.
  - intros i Hi. destruct (Z_lt_dec i k).
    + specialize (Hbytes i ltac:(lia)). lia.
    + assert (Hiend : i = k /\ k < n).
      { destruct (k <? n) eqn:E; [apply Z.ltb_lt in E|apply Z.ltb_ge in E]; lia. }
      destruct Hiend as [-> Hkn]. rewrite Hnul by exact Hkn. lia.
Qed.

(** The complete string including its NUL is a readable byte span.
    Only the consumed extent is required, without runtime readiness. *)
Lemma terminated_length_readable : forall m p k,
  terminated_length m p k -> readable_bytes m p (k + 1).
Proof.
  intros m p k [Hlength Hmax]. eapply bounded_prefix_readable; [exact Hlength|].
  assert (Hlt : (k <? 2 ^ 64 - 1) = true) by (apply Z.ltb_lt; exact Hmax).
  rewrite Hlt. destruct Hlength as (_ & Hk & _). lia.
Qed.

(** The aligned pointer slot at a intersects a nonempty byte fill.
    Its start can precede p; a slot starting at the exclusive endpoint
    is not touched. The positive-count guard makes empty fills empty. *)
Definition memset_touched (p : ptr) (n a : Z) : bool :=
  (0 <? n) && (a mod 8 =? 0) && (a <? ptr_addr p + n) && (ptr_addr p <? a + 8).

(** The boolean footprint states precisely positive count, slot
    alignment and overlap of the two half-open intervals. *)
Lemma memset_touched_spec : forall p n a,
  memset_touched p n a = true <->
  0 < n /\ a mod 8 = 0 /\ a < ptr_addr p + n /\ ptr_addr p < a + 8.
Proof.
  intros. unfold memset_touched. repeat rewrite andb_true_iff.
  rewrite Z.eqb_eq. repeat rewrite Z.ltb_lt. tauto.
Qed.

(** Permission hull, not the byte footprint: round the start down
    to include a partially touched auxiliary slot, but do not round
    the end up. Empty fills retain the original zero-size pointer. *)
Definition memset_root (p : ptr) (n : Z) : span :=
  if n =? 0 then mkSpan p 0 else
  mkSpan (mkPtr (ptr_addr p - ptr_addr p mod 8) (ptr_cap p)) (n + ptr_addr p mod 8).

(** Independent admission: canonical int and size_t, live writable
    destination bytes, and an eight-aligned object base for positive
    counts. The base restriction matches native object-relative aux
    rounding to the model's absolute slots; it is not a runtime axiom.
    Zero-count live Obj admission is conservative: native returns
    before checking even null, Ro or expired pointers at zero count. *)
Definition memset_domain (m : mem) (p : ptr) (c n : Z) : Prop :=
  0 <= c < 2 ^ 32 /\ 0 <= n < 2 ^ 64 /\ writable_span m (mkSpan p n) /\
  (n = 0 \/ exists base, ptr_cap p = Obj base /\ base mod 8 = 0).

(** Ordinary writable bytes and the explicit base alignment derive
    the hull's authority; callers need not assume a second span. *)
Lemma memset_root_writable : forall m p c n,
  memset_domain m p c n -> writable_span m (memset_root p n).
Proof.
  intros m p c n (_ & Hn & Hw & Halign).
  unfold memset_root. destruct (n =? 0) eqn:E.
  - apply Z.eqb_eq in E. subst. exact Hw.
  - apply Z.eqb_neq in E.
    destruct Hw as (Hsize & base & reg & Hcap & Hr & Hl & Ha).
    cbn in Hcap.
    change (access_res m (ptr_addr p) (Obj base) n Write 1 = Some ok) in Ha.
    destruct Halign as [Hz | (other & Hother & Hmod)]; [contradiction|].
    rewrite Hcap in Hother. injection Hother as <-.
    unfold access_res, cap_access_res in Ha. rewrite Hr in Ha.
    destruct ((base <=? ptr_addr p) && (ptr_addr p + n <=? r_end reg)) eqn:Hbounds;
      [|discriminate].
    apply andb_true_iff in Hbounds as [Hlo Hhi].
    apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
    pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)) as Hrem.
    pose proof (Z.div_mod (ptr_addr p) 8 ltac:(lia)) as Hp.
    pose proof (Z.div_mod base 8 ltac:(lia)) as Hb.
    split; [simpl; lia|]. exists base, reg. split; [exact Hcap|].
    split; [exact Hr|]. split; [exact Hl|].
    unfold access_res, cap_access_res. simpl. rewrite Hr.
    assert ((base <=? ptr_addr p - ptr_addr p mod 8) = true) as Hstart by (apply Z.leb_le; lia).
    assert ((ptr_addr p - ptr_addr p mod 8 + (n + ptr_addr p mod 8) <=? r_end reg) = true)
      as Hend by (apply Z.leb_le; lia).
    rewrite Hstart, Hend. unfold aligned_res. rewrite Z.mod_1_r. reflexivity.
Qed.

(** Every written byte lies in the permission hull, including for
    unaligned destinations; an empty byte interval has no members. *)
Lemma memset_byte_in_root : forall p n a,
  span_contains (mkSpan p n) a -> span_contains (memset_root p n) a.
Proof.
  intros p n a H. unfold span_contains in *. simpl in H.
  unfold memset_root. destruct (n =? 0) eqn:E; simpl.
  - apply Z.eqb_eq in E. subst. lia.
  - pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)). lia.
Qed.

(** Each touched auxiliary slot start also lies in the hull, even
    when it precedes the first written byte. *)
Lemma memset_aux_in_root : forall p n a,
  memset_touched p n a = true -> span_contains (memset_root p n) a.
Proof.
  intros p n a H. apply memset_touched_spec in H as (Hn & Halign & Hhi & Hlo).
  unfold memset_root, span_contains. destruct (n =? 0) eqn:E; simpl.
  - apply Z.eqb_eq in E. lia.
  - pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)).
    pose proof (Z.div_mod (ptr_addr p) 8 ltac:(lia)).
    pose proof (Z.div_mod a 8 ltac:(lia)). lia.
Qed.

(** Exact frame for every accepted prefix: retain all regions,
    all bytes outside the requested interval and all auxiliary entries
    outside touched slots. The hull grants no extra byte writes. *)
Definition memset_frame (m : mem) (p : ptr) (n : Z) (m' : mem) : Prop :=
  m_regions m' = m_regions m /\
  (forall a, ~ span_contains (mkSpan p n) a -> m_bytes m' a = m_bytes m a) /\
  (forall a, memset_touched p n a = false -> m_aux m' a = m_aux m a).

(** Completion fills every requested byte with the same low byte and
    clears every touched slot, preserving the independent exact frame. *)
Definition memset_result (m : mem) (p : ptr) (c n : Z) (m' : mem) : Prop :=
  memset_frame m p n m' /\
  (forall a, span_contains (mkSpan p n) a -> m_bytes m' a = c mod 256) /\
  (forall a, memset_touched p n a = true -> m_aux m' a = CNone).

(** A logical result witness, not an implementation of native libc.
    Return m directly at zero count, avoiding extensionality assumptions.
    At positive counts byte repetition is not a little-endian store. *)
Definition memset_memory (m : mem) (p : ptr) (c n : Z) : mem :=
  if n =? 0 then m else
  mkMem (fun a => if (ptr_addr p <=? a) && (a <? ptr_addr p + n)
                 then c mod 256 else m_bytes m a)
    (m_regions m) (fun a => if memset_touched p n a then CNone else m_aux m a).

(** The witness meets the exact byte and auxiliary result without
    assuming coverage, readiness or an eventual native return. *)
Lemma memset_memory_result : forall m p c n,
  memset_result m p c n (memset_memory m p c n).
Proof.
  intros m p c n. unfold memset_memory. destruct (n =? 0) eqn:E.
  - apply Z.eqb_eq in E. subst. split; [repeat split; reflexivity|]. split.
    + intros a H. unfold span_contains in H. simpl in H. lia.
    + intros a H. apply memset_touched_spec in H. lia.
  - split.
    + split; [reflexivity|]. split.
      * intros a H. simpl. destruct ((ptr_addr p <=? a) && (a <? ptr_addr p + n)) eqn:Hrange;
          [|reflexivity]. exfalso. apply H. apply andb_true_iff in Hrange as [Hlo Hhi].
        unfold span_contains. simpl. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi. lia.
      * intros a H. simpl. rewrite H. reflexivity.
    + split.
      * intros a H. unfold span_contains in H. simpl in H. simpl.
        assert ((ptr_addr p <=? a) && (a <? ptr_addr p + n) = true) as Hr.
        { apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
        rewrite Hr. reflexivity.
      * intros a H. simpl. rewrite H. reflexivity.
Qed.

(** Every exact framed effect is a legal allocation-free segment:
    changed cells lie in the writable hull and changed capabilities
    are only CNone. This proves authority, not native satisfaction. *)
Lemma memset_result_local : forall m p c n m',
  memset_domain m p c n -> memset_result m p c n m' ->
  local_effect [mkSpan p 0] [memset_root p n] [] [] m m'.
Proof.
  intros m p c n m' Hdomain ((Hregions & Hbytes & Haux) & Hfill & Hclear).
  pose proof (memset_root_writable _ _ _ _ Hdomain) as Hroot.
  assert (Hauthority : forall a, span_contains (memset_root p n) a ->
    write_authority [memset_root p n] [] m a).
  { intros a Ha. left. exists (memset_root p n).
    split; [left; reflexivity|]. split; assumption. }
  split; [apply ids_same; exact Hregions|]. split.
  - intros b reg Hr. rewrite Hregions in Hr. exists reg. auto.
  - split.
    + intros a Hout. split.
      * apply Hbytes. intros Ha. apply Hout, Hauthority. apply memset_byte_in_root. exact Ha.
      * apply Haux. destruct (memset_touched p n a) eqn:Ha; [|reflexivity].
        exfalso. apply Hout, Hauthority. apply memset_aux_in_root. exact Ha.
    + intros a. destruct (memset_touched p n a) eqn:Ha.
      * right. rewrite (Hclear a Ha). left. reflexivity.
      * left. apply Haux. exact Ha.
Qed.

(** Memset's ABI is P/W/L to P, with a discarded result permitted.
    It is distinct from searches' P/W and copies' P/P/L signatures. *)
Definition memset_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d P) /\
  exists p c n, args = [Arg P p; Arg W c; Arg L n].

(** Trusted nonallocating memset with an exact byte/aux frame. The
    zero-size source permits returning the original pointer capability,
    not importing slots. The widened root is permission only. No events,
    ownership transfer, release, resource ending or exit are admitted.
    Native coverage across internal collector safepoints is uninstantiated;
    unrelated freed-capability rewrites are not hidden in this frame. *)
Definition memset_contract (world : Type) : contract world :=
  mkContract world (RClass P) memset_abi
    (fun xs m _ => exists p c n, xs = [WPtr p; WInt c; WInt n] /\ memset_domain m p c n)
    (fun xs _ _ => match xs with [WPtr p; WInt _; WInt _] => [mkSpan p 0] | _ => [] end)
    (fun xs _ _ => match xs with [WPtr p; WInt _; WInt n] => [memset_root p n] | _ => [] end)
    (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (fun xs m w born trace m' w' => born = [] /\ trace = [] /\ w' = w /\
      exists p c n, xs = [WPtr p; WInt c; WInt n] /\ memset_frame m p n m')
    (fun xs m w born trace ending m' w' => born = [] /\ trace = [] /\ w' = w /\
      exists p c n, xs = [WPtr p; WInt c; WInt n] /\ memset_result m p c n m' /\
        ending = CallReturn [WPtr p])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; Readonly; ArgumentSize; ReturnSize]).

(** ## Snapshot copies and partial pointer words *)

(** A complete destination word maps to a complete aligned source
    word. Partial smidgens and out-of-phase transfers do not compose
    pointer authority. Slot alignment itself comes from the touched set. *)
Definition copy_full_slot (d s : ptr) (n a : Z) : bool :=
  (ptr_addr d <=? a) && (a + 8 <=? ptr_addr d + n) &&
  ((ptr_addr s + (a - ptr_addr d)) mod 8 =? 0).

(** The exact capability for a touched destination slot, from the
    original memory snapshot. A partial or out-of-phase word is cleared.
    Native lower/box correspondence remains a representation obligation. *)
Definition copy_slot (m : mem) (d s : ptr) (n a : Z) : cap :=
  if copy_full_slot d s n a then m_aux m (ptr_addr s + (a - ptr_addr d)) else CNone.

(** Both operands have independent live authority; positive counts
    require aligned object bases, not aligned operand addresses. memcpy
    and mempcpy require disjoint byte ranges; memmove permits overlap.
    Adjacent byte intervals may share a partial auxiliary word. *)
Definition copy_domain (overlap : bool) (m : mem) (d s : ptr) (n : Z) : Prop :=
  memset_domain m d 0 n /\ readable_bytes m s n /\
  (n = 0 \/ exists base, (ptr_cap s = Obj base \/ ptr_cap s = Ro base) /\ base mod 8 = 0) /\
  (overlap = true \/ n = 0 \/ ptr_addr d + n <= ptr_addr s \/ ptr_addr s + n <= ptr_addr d).

(** Read authority for each complete aligned source word follows
    from full-span input readability, not from an auxiliary-cell lookup. *)
Lemma readable_bytes_slot : forall m p n a,
  readable_bytes m p n -> ptr_addr p <= a -> a + 8 <= ptr_addr p + n -> a mod 8 = 0 ->
  access_res m a (ptr_cap p) 8 Read 8 = Some ok.
Proof.
  intros m p n a (_ & (base & reg & Hcap & Hr & Hl) & Ha & _) Hlo Hhi Halign.
  unfold access_res, cap_access_res in Ha |- *.
  destruct Hcap as [Hcap|Hcap]; rewrite Hcap in Ha |- *; rewrite Hr in Ha |- *.
  all: destruct ((base <=? ptr_addr p) && (ptr_addr p + n <=? r_end reg)) eqn:Hbounds;
    try discriminate.
  all: apply andb_true_iff in Hbounds as [Hb He]; apply Z.leb_le in Hb; apply Z.leb_le in He.
  all: assert ((base <=? a) = true) as Hstart by (apply Z.leb_le; lia).
  all: assert ((a + 8 <=? r_end reg) = true) as Hend by (apply Z.leb_le; lia).
  all: rewrite Hstart, Hend; simpl; unfold aligned_res; rewrite Halign; reflexivity.
Qed.

(** A specified copied capability is available through a complete
    original source slot, or is CNone. Destination authority is separate. *)
Lemma copy_slot_authority : forall m d s n a,
  readable_bytes m s n ->
  available_cap [mkSpan s n; mkSpan d 0] [] m (copy_slot m d s n a).
Proof.
  intros m d s n a Hread. unfold copy_slot. destruct (copy_full_slot d s n a) eqn:Hfull.
  - unfold copy_full_slot in Hfull. repeat rewrite andb_true_iff in Hfull.
    destruct Hfull as [[Hlo Hhi] Halign]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
    apply Z.eqb_eq in Halign. right. right. left.
    exists (mkSpan s n), (ptr_addr s + (a - ptr_addr d)).
    split; [left; reflexivity|]. split.
    + unfold span_contains. simpl. lia.
    + split; [simpl; lia|]. split; [|reflexivity].
      apply (readable_bytes_slot m s n); try assumption; lia.
  - left. reflexivity.
Qed.

(** Snapshot bytes and exact touched-slot capabilities, with the
    independent destination-only frame shared with byte fills. *)
Definition copy_result (m : mem) (d s : ptr) (n : Z) (m' : mem) : Prop :=
  memset_frame m d n m' /\
  (forall a, span_contains (mkSpan d n) a ->
    m_bytes m' a = m_bytes m (ptr_addr s + (a - ptr_addr d))) /\
  (forall a, memset_touched d n a = true -> m_aux m' a = copy_slot m d s n a).

(** Observable cells of any completed snapshot, not only its chosen
    witness. Outside-range byte and auxiliary frames are independent. *)
Lemma copy_result_cells : forall m d s n m' a,
  copy_result m d s n m' ->
  m_bytes m' a = (if (ptr_addr d <=? a) && (a <? ptr_addr d + n)
    then m_bytes m (ptr_addr s + (a - ptr_addr d)) else m_bytes m a) /\
  m_aux m' a = (if memset_touched d n a then copy_slot m d s n a else m_aux m a).
Proof.
  intros m d s n m' a ((Hr & Hb & Ha) & Hbytes & Hslots). split.
  - destruct ((ptr_addr d <=? a) && (a <? ptr_addr d + n)) eqn:H.
    + apply Hbytes. apply andb_true_iff in H as [Hlo Hhi].
      apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi. unfold span_contains. simpl. lia.
    + apply Hb. intros Hrange. unfold span_contains in Hrange. simpl in Hrange.
      apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H|apply Z.ltb_ge in H]; lia.
  - destruct (memset_touched d n a) eqn:H; [apply Hslots|apply Ha]; exact H.
Qed.

(** One logical snapshot witness, including for overlapping moves.
    Empty copies return the original memory; self-copies of partial
    words still clear metadata and are not a blanket no-op. *)
Definition copy_memory (m : mem) (d s : ptr) (n : Z) : mem :=
  if n =? 0 then m else
  mkMem (fun a => if (ptr_addr d <=? a) && (a <? ptr_addr d + n)
    then m_bytes m (ptr_addr s + (a - ptr_addr d)) else m_bytes m a)
    (m_regions m) (fun a => if memset_touched d n a then copy_slot m d s n a else m_aux m a).

(** The snapshot witness satisfies the exact copy relation, without
    any claim that native libc terminates or realizes every prefix. *)
Lemma copy_memory_result : forall m d s n, copy_result m d s n (copy_memory m d s n).
Proof.
  intros m d s n. unfold copy_memory. destruct (n =? 0) eqn:E.
  - apply Z.eqb_eq in E. subst. split; [repeat split; reflexivity|]. split.
    + intros a H. unfold span_contains in H. simpl in H. lia.
    + intros a H. apply memset_touched_spec in H. lia.
  - split.
    + split; [reflexivity|]. split.
      * intros a H. simpl. destruct ((ptr_addr d <=? a) && (a <? ptr_addr d + n)) eqn:Ha;
          [|reflexivity]. exfalso. apply H. unfold span_contains. simpl.
        apply andb_true_iff in Ha as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi. lia.
      * intros a H. simpl. rewrite H. reflexivity.
    + split.
      * intros a H. unfold span_contains in H. simpl in H. simpl.
        assert ((ptr_addr d <=? a) && (a <? ptr_addr d + n) = true) as Ha.
        { apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
        rewrite Ha. reflexivity.
      * intros a H. simpl. rewrite H. reflexivity.
Qed.

(** Every specified snapshot result is an authorized local effect.
    Only destination cells change; imported caps come from original
    complete source words, never from fragments or the result memory. *)
Lemma copy_result_local : forall overlap m d s n m',
  copy_domain overlap m d s n -> copy_result m d s n m' ->
  local_effect [mkSpan s n; mkSpan d 0] [memset_root d n] [] [] m m'.
Proof.
  intros overlap m d s n m' (Hd & Hs & _) ((Hr & Hb & Ha) & Hbytes & Hslots).
  pose proof (memset_root_writable _ _ _ _ Hd) as Hroot.
  assert (Hwrite : forall a, span_contains (memset_root d n) a ->
    write_authority [memset_root d n] [] m a).
  { intros a H. left. exists (memset_root d n). split; [left; reflexivity|]. auto. }
  split; [apply ids_same; exact Hr|]. split.
  - intros b reg Hreg. rewrite Hr in Hreg. exists reg. auto.
  - split.
    + intros a Hout. split.
      * apply Hb. intros H. apply Hout, Hwrite. apply memset_byte_in_root. exact H.
      * apply Ha. destruct (memset_touched d n a) eqn:H; [|reflexivity].
        exfalso. apply Hout, Hwrite. apply memset_aux_in_root. exact H.
    + intros a. destruct (memset_touched d n a) eqn:H.
      * right. rewrite (Hslots a H). apply copy_slot_authority. exact Hs.
      * left. apply Ha. exact H.
Qed.

(** The shared byte-copy ABI: destination, source, count, with a
    discarded result or a pointer result. *)
Definition copy_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d P) /\
  exists d s n, args = [Arg P d; Arg P s; Arg L n].

(** Copy APIs differ only in overlap admission and destination/end
    return. The end retains the destination's exact capability. *)
Definition copy_return (end_return : bool) (d : ptr) (n : Z) : ptr :=
  if end_return then mkPtr (ptr_addr d + n) (ptr_cap d) else d.

(** Conditional logical byte-copy contract. Metadata allocation can
    fail or exit/re-enter even for small native copies: resource and
    collector prefix coverage, and lower/box correspondence, remain
    uninstantiated. No application-visible allocation is invented for
    that internal storage. The shared relation includes partial words. *)
Definition copy_contract (overlap end_return : bool) (world : Type) : contract world :=
  mkContract world (RClass P) copy_abi
    (fun xs m _ => exists d s n, xs = [WPtr d; WPtr s; WInt n] /\ copy_domain overlap m d s n)
    (fun xs _ _ => match xs with [WPtr d; WPtr s; WInt n] => [mkSpan s n; mkSpan d 0] | _ => [] end)
    (fun xs _ _ => match xs with [WPtr d; WPtr _; WInt n] => [memset_root d n] | _ => [] end)
    (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (fun xs m w born trace m' w' => born = [] /\ trace = [] /\ w' = w /\
      exists d s n, xs = [WPtr d; WPtr s; WInt n] /\ memset_frame m d n m')
    (fun xs m w born trace ending m' w' => born = [] /\ trace = [] /\ w' = w /\
      exists d s n, xs = [WPtr d; WPtr s; WInt n] /\ copy_result m d s n m' /\
        ending = CallReturn [WPtr (copy_return end_return d n)])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; Readonly; ArgumentSize; ReturnSize]).

(** memcpy returns its destination and requires nonoverlapping bytes. *)
Definition memcpy_contract := copy_contract false false.
(** mempcpy has the same effect but returns the destination endpoint. *)
Definition mempcpy_contract := copy_contract false true.
(** memmove uses the same original snapshot with overlapping ranges. *)
Definition memmove_contract := copy_contract true false.

(** The represented thread supplies a live, nonnull writable int cell.
    Alignment is of its address, not merely of its containing object. *)
Definition errno_cell (m : mem) (p : ptr) : Prop :=
  ptr_addr p <> 0 /\ writable_span m (mkSpan p 4) /\ ptr_addr p mod 4 = 0.

(** ## Memory paths over any runtime

    A call changes memory through a finite sequence of authorized effects.
    Each step preserves readiness and the identities of existing objects. *)

(** The call relations over any [[runtime]] R, whose allocator answers
    each request the contract makes. *)
Module ExternalCalls (R : Runtime).

(** A finite path of a call's memory effects, from runtime state s,
    memory m and born list born (the bases this call allocated) to s',
    m' and born': [local_effect] segments, and successful allocations
    of requests the contract allows, of at most [max_allocation_size]
    bytes, each adding the new base to born. Each allocation extends
    the call's private authority. It cannot claim an existing object's
    identity: [fresh_allocation] proves that from readiness. The list
    is historical, so freed identities never become available for
    reuse. *)
Inductive effects (sources roots : list span) (releases : list Z) (requests : Z -> Z -> Prop)
    : R.state -> mem -> list Z -> R.state -> mem -> list Z -> Prop :=
| effects_refl : forall s m born, effects sources roots releases requests s m born s m born
| effects_local : forall s m born m1 s' m' born',
    local_effect sources roots releases born m m1 ->
    effects sources roots releases requests s m1 born s' m' born' ->
    effects sources roots releases requests s m born s' m' born'
| effects_alloc : forall s m born align size base s1 s' m' born',
    requests align size -> 0 <= size <= max_allocation_size ->
    R.alloc s (heap_req align size) = Some (base, s1) ->
    effects sources roots releases requests s1 (allocated m (heap_req align size) base) (base :: born) s' m' born' ->
    effects sources roots releases requests s m born s' m' born'.

(** If the [[runtime]] is [[ready]] in state s and memory m, it is ready
    at the end of an [effects] path, and every object of m
    [[identity|persists]] into m'. This is a prefix theorem as well as
    an endpoint theorem: every finite prefix is itself an effects
    derivation. *)
Theorem effects_preserve : forall sources roots releases requests s m born s' m' born',
  effects sources roots releases requests s m born s' m' born' -> R.ready s m ->
  R.ready s' m' /\ persists m m'.
Proof.
  intros sources roots releases requests s m born s' m' born' H. induction H; intros Hr.
  - split; auto using persists_refl.
  - pose proof (local_effect_kept _ _ _ _ _ _ H) as Hk.
    destruct (IHeffects (R.ready_kept _ _ _ Hr Hk)) as [Hr' Hp]. split; auto.
    eapply persists_trans; [apply kept_ids_persists; [exact Hk | exact (proj1 H)] | exact Hp].
  - assert (Ha : 0 < req_align (heap_req align size)) by (simpl; lia).
    assert (He : 0 <= req_extent (heap_req align size)).
    { simpl. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia | lia]. }
    destruct (R.fresh_allocation _ _ _ _ _ Hr Ha He H1) as [Hf Hr1].
    destruct (IHeffects Hr1) as [Hr' Hp]. split; auto.
    eapply persists_trans; [apply allocated_persists; exact (proj1 (proj2 (proj2 (proj2 Hf)))) | exact Hp].
Qed.

(** A finite observed prefix of a call of the contract spec on argument
    words xs: an [effects] path from s and m, with the contract's
    sources, roots, releases and requests and no born objects yet, to
    s', m' and born, where the contract's prefix relation accepts the
    observations trace and the new world w'. Prefixes do not require an
    eventual return: a blocking call may have these finite
    observations. Concrete prefix coverage is trusted, not established
    by the structural preservation theorem. *)
Definition prefix {world : Type} (spec : contract world) xs s m w born trace s' m' w' : Prop :=
  effects (contract_sources spec xs m w) (contract_writes spec xs m w)
    (contract_releases spec xs m w) (contract_requests spec xs m w) s m [] s' m' born /\
  contract_prefix spec xs m w born trace m' w'.

(** A call [prefix] from a [[ready]] state keeps the runtime ready and
    every object [[identity|persisting]]. *)
Theorem prefix_preserve : forall world (spec : contract world) xs s m w born trace s' m' w',
  prefix spec xs s m w born trace s' m' w' -> R.ready s m ->
  R.ready s' m' /\ persists m m'.
Proof. intros world spec xs s m w born trace s' m' w' [He _] Hr. eapply effects_preserve; eauto. Qed.

(** Why an allocation the contract requests may fail in runtime state
    s: [OutOfMemory] when the runtime refuses a request of legal size,
    [TooBig] when the size exceeds [max_allocation_size]
    (`max_allocation_size/1`). Compare the original requested size,
    BEFORE [heap_req] rounds it up, exactly as Ops.v does. A legal size
    2^48-1 has extent 2^48, and may be refused by a runtime, but is not
    TooBig. *)
Inductive resource_failure (requests : Z -> Z -> Prop) (s : R.state) : reason -> Prop :=
| failure_oom : forall align size,
    requests align size -> 0 <= size <= max_allocation_size ->
    R.alloc s (heap_req align size) = None -> resource_failure requests s OutOfMemory
| failure_big : forall align size,
    requests align size -> max_allocation_size < size ->
    resource_failure requests s TooBig.

(** A completed call of the contract spec, with call result r, argument
    syntax args and argument words xs, from runtime state s, memory m
    and world w, observing trace and ending as ending. In both rules the
    ABI and the precondition hold and a [prefix] reaches the end state.
    - Normal: the postcondition holds and the ending is not a resource
      ending; returned values have the declared [return_shape] and only
      the call's authority ([word_authority]); an exit ends the trace
      with its [ProcessExit].
    - Resource: a requested allocation fails ([resource_failure]) for a
      reason the contract allows.

    No rule turns a failed precondition into success or a native trap.
    The future machine wrapper must check admissibility even when no
    invoke derivation exists; absence of behavior is not adequacy. *)
Inductive invoke {world : Type} (spec : contract world) (r : call_result) (args : list arg)
    (xs : list word) (s : R.state) (m : mem) (w : world)
    : list event -> call_end -> R.state -> mem -> world -> Prop :=
| invoke_normal : forall trace ending s' m' w' born,
    contract_abi spec r args -> contract_pre spec xs m w ->
    prefix spec xs s m w born trace s' m' w' ->
    contract_post spec xs m w born trace ending m' w' ->
    (forall why, ending <> CallResource why) ->
    (forall values, ending = CallReturn values ->
      return_shape (contract_returns spec) values /\
      Forall (word_authority (contract_sources spec xs m w) born m') values) ->
    (forall status, ending = CallExit status -> exists before, trace = before ++ [ProcessExit status]) ->
    invoke spec r args xs s m w trace ending s' m' w'
| invoke_resource : forall why trace s' m' w' born,
    contract_abi spec r args -> contract_pre spec xs m w ->
    prefix spec xs s m w born trace s' m' w' ->
    resource_failure (contract_requests spec xs m w) s' why -> contract_resource spec why ->
    invoke spec r args xs s m w trace (CallResource why) s' m' w'.

(** Every completed call, normal or resource, is a [prefix] ending in
    the same state, for some list of born objects. *)
Theorem invoke_prefix : forall world (spec : contract world) r args xs s m w trace ending s' m' w',
  invoke spec r args xs s m w trace ending s' m' w' ->
  exists born, prefix spec xs s m w born trace s' m' w'.
Proof. intros. destruct H; eauto. Qed.

(** A completed call from a [[ready]] state keeps the runtime ready and
    every object [[identity|persisting]]; the labelled machine's
    [step_ready] and [step_persists] rest on this. *)
Theorem invoke_preserve : forall world (spec : contract world) r args xs s m w trace ending s' m' w',
  invoke spec r args xs s m w trace ending s' m' w' -> R.ready s m ->
  R.ready s' m' /\ persists m m'.
Proof.
  intros world spec r args xs s m w trace ending s' m' w' H Hr.
  destruct (invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ H) as (born & He & _).
  eapply effects_preserve; eauto.
Qed.

(** The largest legal size, rounded by [heap_req], reserves 2^48
    bytes. Boundary checks use the caller's size, not the rounded
    extent. *)
Example rounded_maximum_extent :
  req_extent (heap_req 16 max_allocation_size) = 2 ^ 48.
Proof. reflexivity. Qed.

(** An allocation of the largest legal size is an [effects] step when
    the runtime grants it. Successful allocation remains conditional on
    the runtime's answer. *)
Example rounded_maximum_allocation : forall s m base s',
  R.alloc s (heap_req 16 max_allocation_size) = Some (base, s') ->
  effects [] [] [] (fun align size => align = 16 /\ size = max_allocation_size)
    s m [] s' (allocated m (heap_req 16 max_allocation_size) base) [base].
Proof.
  intros s m base s' Ha. eapply effects_alloc;
    [split; reflexivity | unfold max_allocation_size; lia | exact Ha | constructor].
Qed.

(** A request of the largest legal size never fails as [TooBig], even
    though its rounded extent is 2^48. *)
Example rounded_maximum_not_too_big : forall s,
  ~ resource_failure (fun align size => align = 16 /\ size = max_allocation_size) s TooBig.
Proof.
  intros s H. inversion H as [align size Hreq Hbound Ha | align size Hreq Hbig].
  destruct Hreq as [_ ->]. lia.
Qed.

(** A request of 2^48 bytes fails as [TooBig] in any runtime state. *)
Example oversized_request : forall s,
  resource_failure (fun align size => align = 16 /\ size = 2 ^ 48) s TooBig.
Proof.
  intros s. eapply failure_big with (align := 16) (size := 2 ^ 48);
    [split; reflexivity | unfold max_allocation_size; lia].
Qed.

(** Any exact memset result gives an actual returning invocation from
    independent admission. Its finite path has one authorized segment,
    no allocation and no state change in the runtime. *)
Theorem memset_return : forall world r args p c n s m m' (w : world),
  memset_abi r args -> memset_domain m p c n -> memset_result m p c n m' ->
  invoke (memset_contract world) r args [WPtr p; WInt c; WInt n] s m w
    [] (CallReturn [WPtr p]) s m' w.
Proof.
  intros world r args p c n s m m' w Habi Hdomain Hresult.
  eapply invoke_normal with (born := []).
  - exact Habi.
  - exists p, c, n. auto.
  - split.
    + eapply effects_local; [eapply memset_result_local; eauto|constructor].
    + split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists p, c, n. split; [reflexivity|exact (proj1 Hresult)].
  - split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exists p, c, n. auto.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WPtr p). split; reflexivity.
    + constructor; [|constructor]. right. left. exists (mkSpan p 0).
      split; [left; reflexivity|reflexivity].
  - intros status Hbad. discriminate.
Qed.

(** Input-only premises construct a completed effect, not merely a
    postcondition witness. This is logical nonvacuity, not a native
    coverage or termination theorem. *)
Theorem memset_admitted : forall world r args p c n s m (w : world),
  memset_abi r args -> memset_domain m p c n ->
  invoke (memset_contract world) r args [WPtr p; WInt c; WInt n] s m w
    [] (CallReturn [WPtr p]) s (memset_memory m p c n) w.
Proof.
  intros. apply memset_return; [assumption|assumption|apply memset_memory_result].
Qed.

(** Every completion extracts the original admitted arguments, exact
    destination pointer, byte/aux effect, empty trace and unchanged
    world. Resource and exit completions are excluded. *)
Theorem memset_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (memset_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ w' = w /\
  exists p c n, xs = [WPtr p; WInt c; WInt n] /\ memset_domain m p c n /\
    memset_result m p c n m' /\ ending = CallReturn [WPtr p].
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with
    | Hpost : contract_post _ _ _ _ _ _ _ _ _, Hpre : contract_pre _ _ _ _ |- _ =>
      destruct Hpost as (_ & Htrace & Hworld & p & c & n & Hxs & Hresult & Hending);
      destruct Hpre as (q & v & size & Hxs' & Hdomain)
    end.
    rewrite Hxs in Hxs'. injection Hxs' as <- <- <-.
    split; [exact Htrace|]. split; [exact Hworld|]. exists p, c, n. auto.
  - contradiction.
Qed.

(** Zero-count completions preserve all bytes, regions and auxiliary
    entries, not just the constructed witness. No extensionality axiom
    is needed for this pointwise public-call result. *)
Theorem memset_zero_invocation : forall world r args p c s m (w : world) trace ending s' m' w',
  invoke (memset_contract world) r args [WPtr p; WInt c; WInt 0] s m w
    trace ending s' m' w' ->
  ending = CallReturn [WPtr p] /\ m_regions m' = m_regions m /\
  forall a, m_bytes m' a = m_bytes m a /\ m_aux m' a = m_aux m a.
Proof.
  intros world r args p c s m w trace ending s' m' w' Hcall.
  destruct (memset_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & q & v & n & Hargs & Hdomain & ((Hr & Hb & Ha) & _) & Hend).
  injection Hargs as <- <- <-. split; [exact Hend|]. split; [exact Hr|].
  intros a. split.
  - apply Hb. unfold span_contains. simpl. lia.
  - apply Ha. reflexivity.
Qed.

(** Any permitted snapshot result constructs a real returning call,
    using original source authority even when byte ranges overlap. *)
Theorem copy_completed : forall overlap end_return world r args d src n s m m' (w : world),
  copy_abi r args -> copy_domain overlap m d src n -> copy_result m d src n m' ->
  invoke (copy_contract overlap end_return world) r args [WPtr d; WPtr src; WInt n] s m w
    [] (CallReturn [WPtr (copy_return end_return d n)]) s m' w.
Proof.
  intros overlap end_return world r args d src n s m m' w Habi Hdomain Hresult.
  eapply invoke_normal with (born := []).
  - exact Habi.
  - exists d, src, n. auto.
  - split.
    + eapply effects_local; [eapply copy_result_local; eauto|constructor].
    + split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists d, src, n. split; [reflexivity|exact (proj1 Hresult)].
  - split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exists d, src, n. auto.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WPtr (copy_return end_return d n)). split; reflexivity.
    + constructor; [|constructor]. unfold copy_return. destruct end_return; simpl.
      all: right; left; exists (mkSpan d 0); split; [right; left; reflexivity|reflexivity].
  - intros status Hbad. discriminate.
Qed.

(** Independent inputs construct a snapshot invocation. This proves
    nonvacuity, not native success, resource coverage or termination. *)
Theorem copy_admitted : forall overlap end_return world r args d src n s m (w : world),
  copy_abi r args -> copy_domain overlap m d src n ->
  invoke (copy_contract overlap end_return world) r args [WPtr d; WPtr src; WInt n] s m w
    [] (CallReturn [WPtr (copy_return end_return d n)]) s (copy_memory m d src n) w.
Proof. intros. apply copy_completed; [assumption|assumption|apply copy_memory_result]. Qed.

(** Every completion retains the admitted operands and exact snapshot
    result, including the API's chosen destination/end provenance. *)
Theorem copy_invocation : forall overlap end_return world r args xs s m (w : world)
    trace ending s' m' w',
  invoke (copy_contract overlap end_return world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ w' = w /\ exists d src n, xs = [WPtr d; WPtr src; WInt n] /\
    copy_domain overlap m d src n /\ copy_result m d src n m' /\
    ending = CallReturn [WPtr (copy_return end_return d n)].
Proof.
  intros overlap end_return world r args xs s m w trace ending s' m' w' Hcall.
  inversion Hcall; subst.
  - match goal with
    | Hpost : contract_post _ _ _ _ _ _ _ _ _, Hpre : contract_pre _ _ _ _ |- _ =>
      destruct Hpost as (_ & Htrace & Hworld & d & src & n & Hxs & Hresult & Hending);
      destruct Hpre as (q & v & size & Hxs' & Hdomain)
    end.
    rewrite Hxs in Hxs'. injection Hxs' as <- <- <-.
    split; [exact Htrace|]. split; [exact Hworld|]. exists d, src, n. auto.
  - contradiction.
Qed.

(** In a ready memory the mathematical destination endpoint stays in
    its object or one-past, below 2^64. No modular wrap or extra bound
    axiom is needed for mempcpy's result. *)
Theorem copy_endpoint : forall overlap s m d src n,
  R.ready s m -> copy_domain overlap m d src n ->
  exists base reg, ptr_cap d = Obj base /\ object_region base (m_regions m) = Some reg /\
    base <= ptr_addr d /\ ptr_addr d + n <= r_end reg /\ 0 <= ptr_addr d + n < 2 ^ 64.
Proof.
  intros overlap s m d src n Hready ((Hc & Hn & Hw & _) & _).
  destruct Hw as (_ & base & reg & Hcap & Hr & Hl & Ha). cbn in Hcap.
  change (access_res m (ptr_addr d) (Obj base) n Write 1 = Some ok) in Ha.
  unfold access_res, cap_access_res in Ha. rewrite Hr in Ha.
  destruct ((base <=? ptr_addr d) && (ptr_addr d + n <=? r_end reg)) eqn:E;
    [|discriminate].
  apply andb_true_iff in E as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  destruct (R.address_space _ _ Hready base reg Hr) as (Hb & He).
  exists base, reg. split; [exact Hcap|]. split; [exact Hr|]. repeat split; try assumption; lia.
Qed.

(** Readiness bounds only the consumed interval. A huge unused maximum
    need not fit in the address space, and is not part of this bound. *)
Lemma bounded_length_extent : forall s m p n k,
  R.ready s m -> bounded_length m p n k ->
  0 <= ptr_addr p /\ ptr_addr p + k + (if k <? n then 1 else 0) <= 2 ^ 48.
Proof.
  intros s m p n k Hr (_ & _ & (base & reg & Hcap & Hreg & _) & Ha & _).
  pose proof (R.address_space s m Hr base reg Hreg) as [Hb Hend].
  unfold access_res in Ha. destruct Hcap as [Hcap | Hcap]; rewrite Hcap in Ha;
    cbn in Ha; rewrite Hreg in Ha.
  all: destruct ((base <=? ptr_addr p) &&
      (ptr_addr p + (k + (if k <? n then 1 else 0)) <=? r_end reg)) eqn:E;
    [|discriminate].
  all: apply andb_true_iff in E; destruct E as [Hlo Hhi];
    apply Z.leb_le in Hlo; apply Z.leb_le in Hhi; lia.
Qed.

(** The consumed extent includes the terminating byte and fits in the
    address space whenever the runtime starts ready. *)
Lemma terminated_length_extent : forall s m p k,
  R.ready s m -> terminated_length m p k ->
  0 <= ptr_addr p /\ ptr_addr p + k + 1 <= 2 ^ 48.
Proof.
  intros s m p k Hr [Hlength Hmax].
  pose proof (bounded_length_extent _ _ _ _ _ Hr Hlength) as Hextent.
  assert (Hlt : (k <? 2 ^ 64 - 1) = true) by (apply Z.ltb_lt; exact Hmax).
  rewrite Hlt in Hextent. exact Hextent.
Qed.

(** A ready readable byte span's entire interval fits in the address space;
    unlike [bounded_length_extent], this includes the full maximum. *)
Lemma readable_bytes_extent : forall s m p n,
  R.ready s m -> readable_bytes m p n ->
  0 <= ptr_addr p /\ ptr_addr p + n <= 2 ^ 48.
Proof.
  intros s m p n Hr (_ & (base & reg & Hcap & Hreg & _) & Ha & _).
  pose proof (R.address_space s m Hr base reg Hreg) as [Hb Hend].
  unfold access_res in Ha. destruct Hcap as [Hcap | Hcap]; rewrite Hcap in Ha;
    cbn in Ha; rewrite Hreg in Ha.
  all: destruct ((base <=? ptr_addr p) && (ptr_addr p + n <=? r_end reg)) eqn:E;
    [|discriminate].
  all: apply andb_true_iff in E; destruct E as [Hlo Hhi];
    apply Z.leb_le in Hlo; apply Z.leb_le in Hhi; lia.
Qed.

End ExternalCalls.

(** ## C-string contents

    A C string contains nonzero bytes followed by a NUL within readable memory.
    These predicates connect its byte list to the position of that terminator. *)

(** The memory m holds the nonzero bytes bytes from address a on,
    followed by a NUL byte. *)
Fixpoint string_at (m : mem) (a : Z) (bytes : list Z) : Prop :=
  match bytes with
  | [] => m_bytes m a = 0
  | b :: rest => 0 < b < 256 /\ m_bytes m a = b /\ string_at m (a + 1) rest
  end.

(** Pointer p points at a C string with contents bytes in memory m:
    its capability permits reading the bytes and the terminating NUL
    ([access_res] with [Read]), and [string_at] holds there, so the
    first NUL is within a readable capability. There is no bound on the
    length in the contract; examples' short strings are fixtures. *)
Definition c_string (m : mem) (p : ptr) (bytes : list Z) : Prop :=
  access_res m (ptr_addr p) (ptr_cap p) (Z.of_nat (length bytes) + 1) Read 1 = Some ok /\
  string_at m (ptr_addr p) bytes.

(** A list string has nonzero byte contents before its length and a NUL
    exactly at that length. No authority is inferred from total memory. *)
Lemma string_at_length : forall bytes m a,
  string_at m a bytes ->
  (forall i, 0 <= i < Z.of_nat (length bytes) -> 0 < m_bytes m (a + i) < 256) /\
  m_bytes m (a + Z.of_nat (length bytes)) = 0.
Proof.
  induction bytes as [|b rest IH]; intros m a Hstring.
  - simpl in *. split; [intros i Hi; lia|]. replace (a + 0) with a by lia. exact Hstring.
  - destruct Hstring as (Hb & Hhead & Hrest).
    destruct (IH m (a + 1) Hrest) as [Hbytes Hnul].
    change ((forall i, 0 <= i < Z.of_nat (S (length rest)) ->
      0 < m_bytes m (a + i) < 256) /\ m_bytes m (a + Z.of_nat (S (length rest))) = 0).
    rewrite Nat2Z.inj_succ. split.
    + intros i Hi. destruct (Z.eq_dec i 0) as [->|Hnonzero].
      * replace (a + 0) with a by lia. rewrite Hhead. exact Hb.
      * replace (a + i) with (a + 1 + (i - 1)) by lia. apply Hbytes. lia.
    + replace (a + Z.succ (Z.of_nat (length rest))) with
        (a + 1 + Z.of_nat (length rest)) by lia. exact Hnul.
Qed.

(** Finite nonzero bytes ending in NUL construct their list representation.
    This constructive enumeration is a proof, not a native scan algorithm. *)
Lemma string_at_exists : forall count m a,
  (forall i, 0 <= i < Z.of_nat count -> 0 < m_bytes m (a + i) < 256) ->
  m_bytes m (a + Z.of_nat count) = 0 ->
  exists bytes, length bytes = count /\ string_at m a bytes.
Proof.
  induction count as [|count IH]; intros m a Hbytes Hnul.
  - exists []. split; [reflexivity|]. simpl in Hnul. replace (a + 0) with a in Hnul by lia.
    exact Hnul.
  - rewrite Nat2Z.inj_succ in Hbytes, Hnul.
    destruct (IH m (a + 1)) as (bytes & Hlen & Hstring).
    + intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. apply Hbytes. lia.
    + replace (a + 1 + Z.of_nat count) with (a + Z.succ (Z.of_nat count)) by lia. exact Hnul.
    + exists (m_bytes m a :: bytes). split; [simpl; congruence|]. simpl.
      split; [|auto]. replace a with (a + 0) by lia. apply Hbytes. lia.
Qed.

(** Terminated-length authority constructs a checked list string without
    readiness; the reverse direction below needs ready-memory facts. *)
Lemma terminated_length_string : forall m p k,
  terminated_length m p k ->
  exists bytes, c_string m p bytes /\ k = Z.of_nat (length bytes).
Proof.
  intros m p k [(_ & Hk & _ & Ha & Hbytes & Hnul) Hmax].
  assert (Hlt : (k <? 2 ^ 64 - 1) = true) by (apply Z.ltb_lt; exact Hmax).
  rewrite Hlt in Ha.
  destruct (string_at_exists (Z.to_nat k) m (ptr_addr p)) as (bytes & Hlen & Hstring).
  - rewrite Z2Nat.id by lia. exact Hbytes.
  - rewrite Z2Nat.id by lia. apply Hnul. exact Hmax.
  - exists bytes. assert (Hlength : Z.of_nat (length bytes) = k) by
      (rewrite Hlen, Z2Nat.id by lia; reflexivity).
    split; [split; [rewrite Hlength; exact Ha|exact Hstring]|lia].
Qed.

(** Ready-memory facts connect strlen's explicit lifetime and canonical
    result to the unchanged list-string domain used by puts. *)
Module StringLengths (R : Runtime).

(** A checked list string is live under readiness: freed objects have
    empty bounds. Its positive extent fits in 2^48, so the first NUL is
    strictly before SIZE_MAX, not an extra practical length restriction. *)
Lemma c_string_length : forall s m p bytes,
  R.ready s m -> c_string m p bytes ->
  terminated_length m p (Z.of_nat (length bytes)).
Proof.
  intros s m p bytes Hr [Ha Hstring].
  pose proof (string_at_length bytes m (ptr_addr p) Hstring) as [Hbytes Hnul].
  assert (Hnonneg : 0 <= Z.of_nat (length bytes)) by lia.
  unfold access_res, cap_access_res in Ha.
  destruct (ptr_cap p) as [|base|base|f|f] eqn:Hcap; try discriminate.
  all: destruct (object_region base (m_regions m)) as [reg|] eqn:Hreg; try discriminate.
  all: destruct ((base <=? ptr_addr p) &&
      (ptr_addr p + (Z.of_nat (length bytes) + 1) <=? r_end reg)) eqn:Hbounds;
    [|discriminate].
  all: apply andb_true_iff in Hbounds as [Hlo Hhi];
    apply Z.leb_le in Hlo; apply Z.leb_le in Hhi.
  all: pose proof (R.address_space s m Hr base reg Hreg) as [Hb Hend].
  all: assert (Hmax : Z.of_nat (length bytes) < 2 ^ 64 - 1) by lia.
  all: assert (Hlive : r_life reg = Live) by
    (destruct (r_life reg) eqn:Hlife; [reflexivity|];
      pose proof (R.freed_bounds s m Hr base reg Hreg Hlife); lia).
  all: split; [|exact Hmax]; split; [vm_compute; split; congruence|];
    split; [lia|]; split.
  - exists base, reg. auto.
  - split.
    + assert (Hlt : (Z.of_nat (length bytes) <? 2 ^ 64 - 1) = true) by (apply Z.ltb_lt; exact Hmax).
      rewrite Hlt. unfold access_res, cap_access_res. rewrite Hcap, Hreg.
      rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.leb_le _ _) Hhi). exact Ha.
    + auto.
  - exists base, reg. auto.
  - split.
    + assert (Hlt : (Z.of_nat (length bytes) <? 2 ^ 64 - 1) = true) by (apply Z.ltb_lt; exact Hmax).
      rewrite Hlt. unfold access_res, cap_access_res. rewrite Hcap, Hreg.
      rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.leb_le _ _) Hhi). exact Ha.
    + auto.
Qed.

(** Under readiness, terminated lengths and checked list strings are
    equivalent. This does not strengthen puts on arbitrary model memories. *)
Theorem terminated_length_c_string : forall s m p k,
  R.ready s m ->
  (terminated_length m p k <->
   exists bytes, c_string m p bytes /\ k = Z.of_nat (length bytes)).
Proof.
  intros s m p k Hr. split; [apply terminated_length_string|].
  intros (bytes & Hstring & ->). eapply c_string_length; eauto.
Qed.

End StringLengths.
