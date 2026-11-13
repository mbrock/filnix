(** When a compiled C module calls across an [[external call]] boundary,
    such as libpizlo's `zsys_*` system calls, `c: zmemset`, or
    `c: zmemmove` in `rocq/glibc/zsys/`, execution does not step through
    intermediate-representation instructions inside the callee. Instead,
    each external function is specified by a [contract] that states its
    calling-convention ABI, its entry precondition, the byte spans it may
    read or overwrite, the heap objects it may release or allocate, and
    the postcondition that links its return value and observable events
    to the updated memory state.

    To reason about external calls without changing the core [Runtime] or
    [Machine] semantics, the functor [ExternalCalls] bounds what a call
    can do to memory through three relations. An [effects] path chains
    authorized byte and [[aux]] capability writes with fresh heap
    allocations, a [prefix] pairs an effects path with intermediate
    observable events, and [invoke] completes a call either normally or
    with an allocation failure while preserving runtime [[ready|readiness]]
    and existing object [[identity|identities]].

    In addition to the general contract framework, this module defines
    the bounded string scan predicates, the thread-local [errno_cell]
    predicate, and the memory-fill and memory-copy contracts
    [memset_contract], [memcpy_contract], [mempcpy_contract], and
    [memmove_contract] shared with the glibc verification campaign. The
    older C standard library specifications for the standalone hello
    proofs live in [LibcCalls](../hello_contracts/LibcCalls.v). *)

From Stdlib Require Import String ZArith List Bool Lia Relations.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Machine Identity.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Authority and footprints

    When an external function runs, it may read pointer capabilities from
    caller buffers, overwrite byte ranges and their shadow [[aux]] slots,
    or free heap objects passed to it. Before defining a full call
    contract, this section defines memory spans, write authority,
    available capabilities, and single allocation-free memory segments in
    [local_effect]. These definitions ensure that every memory change
    authorized by a contract obeys the same invariants as ordinary
    program instructions. *)

(** An external call contract names each buffer range it may read or
    overwrite as a [span], which pairs a base pointer [span_ptr] carrying
    the caller's [[capability]] with a byte length [span_size]. *)
Record span : Type := mkSpan { span_ptr : ptr; span_size : Z }.

(** The predicate [span_contains] holds when address a falls within the
    half-open byte interval starting at the address of s and extending
    for [span_size] bytes. *)
Definition span_contains (s : span) (a : Z) : Prop :=
  ptr_addr (span_ptr s) <= a < ptr_addr (span_ptr s) + span_size s.

(** For a call to overwrite a caller buffer, [writable_span] requires a
    nonnegative byte length and a pointer whose [Obj] [[capability]]
    names a live [[region|object]] and passes [access_res] with [Write]
    permission across the entire span. Checking that the target object is
    live rules out zero-length spans into freed objects, which a bounds
    check alone would otherwise accept. *)
Definition writable_span (m : mem) (s : span) : Prop :=
  0 <= span_size s /\
  exists base reg,
    ptr_cap (span_ptr s) = Obj base /\
    object_region base (m_regions m) = Some reg /\ r_life reg = Live /\
    access_res m (ptr_addr (span_ptr s)) (Obj base) (span_size s) Write 1 = Some ok.

(** During an external call, [write_authority] permits modifying address
    a in memory m when a lies either inside one of the contract's
    writable root spans or inside a live heap object allocated by the
    call itself and recorded in born. Newly allocated objects belong to
    the call automatically, whereas existing caller objects can only be
    modified through a [writable_span] listed in the contract's roots.
    Both data byte stores and [[aux]] capability updates draw their write
    permission from this same set of addresses. *)
Definition write_authority (roots : list span) (born : list Z) (m : mem) (a : Z) : Prop :=
  (exists s, In s roots /\ writable_span m s /\ span_contains s a) \/
  (exists base reg, In base born /\ object_region base (m_regions m) = Some reg /\
    r_kind reg = Heap /\ r_life reg = Live /\ base <= a < r_end reg).

(** An external call cannot forge a pointer [[capability]] out of raw
    integer bits or upgrade a read-only [Ro] capability into a writable
    [Obj] capability. The predicate [available_cap] restricts any
    capability c that a call stores into memory m or returns to the
    caller to four sources: the empty capability [CNone], the capability
    carried by one of the contract's readable source pointers, a
    capability loaded from an aligned eight-byte slot inside a readable
    source span via [m_aux], or an [Obj] or [Ro] capability for a heap
    object in born that the call allocated itself. *)
Definition available_cap (sources : list span) (born : list Z) (m : mem) (c : cap) : Prop :=
  c = CNone \/
  (exists s, In s sources /\ c = ptr_cap (span_ptr s)) \/
  (exists s a, In s sources /\ span_contains s a /\
    a + 8 <= ptr_addr (span_ptr s) + span_size s /\
    access_res m a (ptr_cap (span_ptr s)) 8 Read 8 = Some ok /\ c = m_aux m a) \/
  (exists base, In base born /\ (c = Obj base \/ c = Ro base)).

(** Every address that a call has [write_authority] to modify belongs
    either to a checked writable span or to a live heap allocation, so
    it always lies inside a registered object in memory. This ensures
    that an external call never writes to unallocated addresses outside
    all objects. *)
Lemma write_authority_in : forall roots born m a,
  write_authority roots born m a -> in_object m a.
Proof.
  intros roots born m a [(s & _ & (_ & base & reg & Hcap & Hr & _ & Ha) & Hin) |
                        (base & reg & _ & Hr & _ & _ & Hin)].
  - eapply access_in; [exact Ha | exact Hin].
  - exists base, reg. auto.
Qed.

(** Between heap allocations, an external call changes memory in
    single steps described by [local_effect]. Such a step keeps all
    registered objects registered, frees only live heap objects that
    the call has permission to release, leaves all bytes and capability
    slots outside the call's writable addresses untouched, and writes
    only capabilities that the call already holds. *)
Definition local_effect (sources roots : list span) (releases born : list Z) (m m' : mem) : Prop :=
  ids m m' /\
  (forall b reg', object_region b (m_regions m') = Some reg' ->
    exists reg, object_region b (m_regions m) = Some reg /\
      (reg' = reg \/ (In b (releases ++ born) /\ r_kind reg = Heap /\
        r_life reg = Live /\ reg' = mkRegion b b Heap Freed))) /\
  (forall a, ~ write_authority roots born m a ->
    m_bytes m' a = m_bytes m a /\ m_aux m' a = m_aux m a) /\
  (forall a, m_aux m' a = m_aux m a \/ available_cap sources born m (m_aux m' a)).

(** The core runtime invariant requires every memory transition to leave
    existing object identities intact and to modify bytes only inside
    registered objects, as captured by [kept]. Lemma [local_effect_kept]
    proves that any [local_effect] satisfies [kept], which allows
    [effects_preserve] to maintain [[runtime]] [[ready|readiness]] across
    each segment via [ready_kept]. *)
Lemma local_effect_kept : forall sources roots releases born m m',
  local_effect sources roots releases born m m' -> kept m m'.
Proof.
  intros sources roots releases born m m' (_ & Hr & Hw & _). split.
  - intros b reg' H. destruct (Hr _ _ H) as (reg & E & [-> | (_ & Hk & Hl & ->)]).
    + exists reg. auto.
    + exists reg. split; auto. right. rewrite Hk. auto.
  - intros a Hout. apply Hw. intros Ha. apply Hout. eapply write_authority_in; eauto.
Qed.

(** A step that leaves memory completely unchanged is always a valid
    [local_effect] because it frees no objects and modifies no bytes or
    capabilities. *)
Lemma local_effect_refl : forall sources roots releases born m,
  local_effect sources roots releases born m m.
Proof.
  intros. split; [apply ids_refl|]. split; [intros b reg E; exists reg; auto |]. auto.
Qed.

(** When a call has [write_authority] over every byte from address a
    through a + n - 1, [local_store_bytes] shows that storing the n-byte
    integer value x at address a with [store_bytes] forms a valid
    [local_effect]. *)
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

(** When an external call writes a full pointer p to an eight-byte slot
    at address a, it stores both the address bytes and the pointer's
    capability. Lemma [local_store_pointer] proves that this combined
    update is a [local_effect] whenever the eight bytes have
    [write_authority] and the pointer's capability satisfies
    [available_cap], while the helper lemmas immediately below establish
    that [load_bytes] reads back the stored bytes. *)
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

(** When an external call allocates a fresh heap object at an
    unregistered base address, existing caller objects and their
    capabilities must remain valid. Lemma [allocated_old_region] and the
    two lemmas following it show that [allocated] preserves every
    previously registered region, every passing [access_res] check, and
    every [writable_span] from the pre-allocation memory. *)
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

(** ## Events and contract results

    Besides modifying memory, an external call can emit observable stream
    output, terminate the process, return result words to its caller, or
    stop when an allocation request fails. This section defines those
    observable events and call endings, checks that returned pointer
    words carry only capabilities available to the call, and packages the
    complete specification of an external function in the [contract]
    record. *)

(** An [event] records a single externally observable action performed
    during a call. The constructor [StreamBytes] records a list of bytes
    accepted for an output stream descriptor, while [ProcessExit] records
    that the call terminated the process with a given exit status. *)
Inductive event : Type :=
| StreamBytes (stream : Z) (bytes : list Z)
| ProcessExit (status : Z).

(** When an external call finishes, [call_end] classifies how it
    terminates. A call either returns a list of result [[word|words]] to
    its caller with [CallReturn], exits the process with [CallExit], or
    halts on an allocation failure with [CallResource]. *)
Inductive call_end : Type :=
| CallReturn (values : list word)
| CallExit (status : Z)
| CallResource (why : reason).

(** Even when a caller satisfies a function's entry precondition, an
    external call that allocates memory can still fail if the allocator
    cannot satisfy its request. The predicate [resource_reason] restricts
    those legitimate resource [[trap]] reasons to [OutOfMemory] and
    [TooBig], distinguishing them from capability safety panics. *)
Definition resource_reason (why : reason) : Prop :=
  why = OutOfMemory \/ why = TooBig.

(** When an external call returns, the returned word list must match the
    callee's declared [ret_type]. The predicate [return_shape] requires
    an empty list for [RVoid], a single word matching its register
    [[class]] for [RClass], and a word list matching each element class
    in order for [RTuple], keeping void and scalar returns distinct from
    empty or singleton tuples. *)
Definition return_shape (ty : ret_type) (values : list word) : Prop :=
  match ty with
  | RVoid => values = []
  | RClass k => exists x, values = [x] /\ word_at_class k x = Some x
  | RTuple ks => Forall2 (fun k x => word_at_class k x = Some x) ks values
  end.

(** Just as a call may only store capabilities permitted by
    [available_cap] into memory, any pointer or [[limit]] [[word]] it
    returns in a register must also carry a capability from the call's
    sources or newly allocated objects. The predicate [word_authority]
    enforces that check on pointer and limit words while placing no
    restriction on plain integer words. *)
Definition word_authority (sources : list span) (born : list Z) (m : mem) (x : word) : Prop :=
  match x with
  | WPtr p => available_cap sources born m (ptr_cap p)
  | WLimit c _ => available_cap sources born m c
  | WInt _ => True
  end.

(** A [contract] specifies the complete boundary behavior of one external
    function over an abstract state type world. Its fields record the
    declared return type [contract_returns], the call-site syntax check
    [contract_abi], the entry precondition [contract_pre], the readable
    spans [contract_sources], the writable spans [contract_writes], the
    releasable heap bases [contract_releases], and the permitted
    allocation requests [contract_requests]. The remaining fields specify
    valid intermediate states in [contract_prefix], completed outcomes in
    [contract_post], allowed allocator failure reasons in
    [contract_resource], and documented safety trap reasons outside the
    precondition in [contract_panics]. *)
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

(** ## Bounded string scans

    Many external functions either scan a byte buffer up to a terminating
    NUL byte or overwrite a contiguous byte range while clearing any
    pointer capabilities stored in its [[aux]] slots. This section
    defines bounded and NUL-terminated string scan lengths alongside
    full-span byte readability, and then builds the memory-fill
    specification [memset_contract] used by `c: memset` and libpizlo's
    `c: zmemset`. Because overwriting even one byte of a pointer
    invalidates the whole eight-byte pointer slot in Fil-C,
    [memset_contract] widens its write permission hull to include any
    partially touched capability slot while keeping byte writes inside
    the caller's exact range. *)

(** When a bounded string scan such as `c: strnlen` inspects at most n
    bytes starting at pointer p, it stops either at the first NUL byte at
    offset k < n or after reading n nonzero bytes with k = n. The
    predicate [bounded_length] requires p to carry a live object
    [[capability]] and demands read permission only across the consumed
    prefix of length k (plus the terminating NUL byte when k < n), so
    an early NUL byte makes the call valid even if the full bound n
    extends past the end of the object. *)
Definition bounded_length (m : mem) (p : ptr) (n k : Z) : Prop :=
  0 <= n < 2 ^ 64 /\ 0 <= k <= n /\
  (exists base reg, (ptr_cap p = Obj base \/ ptr_cap p = Ro base) /\
    object_region base (m_regions m) = Some reg /\ r_life reg = Live) /\
  access_res m (ptr_addr p) (ptr_cap p) (k + (if k <? n then 1 else 0)) Read 1 = Some ok /\
  (forall i, 0 <= i < k -> 0 < m_bytes m (ptr_addr p + i) < 256) /\
  (k < n -> m_bytes m (ptr_addr p + k) = 0).

(** Because every byte before offset k is nonzero and any byte at offset
    k < n is NUL, [bounded_length_unique] shows that [bounded_length]
    determines a unique scan length k for any memory m, pointer p, and
    bound n. *)
Lemma bounded_length_unique : forall m p n left right,
  bounded_length m p n left -> bounded_length m p n right -> left = right.
Proof.
  intros m p n left right (_ & Hl & _ & _ & Hbytesl & Hnull) (_ & Hr & _ & _ & Hbytesr & Hnulr).
  destruct (Z.lt_trichotomy left right) as [Hlt | [Heq | Hgt]]; [|exact Heq|].
  - specialize (Hbytesr left ltac:(lia)). rewrite Hnull in Hbytesr by lia. lia.
  - specialize (Hbytesl right ltac:(lia)). rewrite Hnulr in Hbytesl by lia. lia.
Qed.

(** An unbounded string scan such as `c: strlen` requires a terminating
    NUL byte to appear at some offset k strictly below `SIZE_MAX`
    (2^64 - 1). The predicate [terminated_length] defines that scan as a
    [bounded_length] up to 2^64 - 1 with k < 2^64 - 1, requiring read
    authority only through the first NUL byte at offset k rather than
    across `SIZE_MAX` bytes. *)
Definition terminated_length (m : mem) (p : ptr) (k : Z) : Prop :=
  bounded_length m p (2 ^ 64 - 1) k /\ k < 2 ^ 64 - 1.

(** Because a C string stops at its first NUL byte, any pointer p has
    at most one NUL-terminated length k in memory m under
    [terminated_length]. *)
Lemma terminated_length_unique : forall m p left right,
  terminated_length m p left -> terminated_length m p right -> left = right.
Proof. intros m p left right [Hl _] [Hr _]. eapply bounded_length_unique; eauto. Qed.

(** Whether [terminated_length] holds at pointer p with length k depends
    only on the region of p's target object and the data bytes at offsets
    0 through k. Lemma [terminated_length_agree] shows that if two
    memories agree on that object region and those k + 1 bytes, any
    [terminated_length] in the first memory holds with the same length in
    the second. *)
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

(** Unlike a NUL-terminated scan that stops early, a memory copy or
    fixed-length write reads all n bytes starting at pointer p. The
    predicate [readable_bytes] requires a canonical 64-bit length n, a
    live [Obj] or [Ro] capability on p, passing [access_res] read
    permission across all n bytes, and well-formed byte values in `0..255`
    at every offset, including when n is zero. *)
Definition readable_bytes (m : mem) (p : ptr) (n : Z) : Prop :=
  0 <= n < 2 ^ 64 /\
  (exists base reg, (ptr_cap p = Obj base \/ ptr_cap p = Ro base) /\
    object_region base (m_regions m) = Some reg /\ r_life reg = Live) /\
  access_res m (ptr_addr p) (ptr_cap p) n Read 1 = Some ok /\
  (forall i, 0 <= i < n -> 0 <= m_bytes m (ptr_addr p + i) < 256).

(** Because capability bounds checks are downward closed on nonnegative
    lengths, [readable_bytes_prefix] shows that if n bytes are readable
    at pointer p under [readable_bytes], any shorter prefix of k <= n
    bytes is also readable. *)
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

(** A bounded string scan checks read permission up through its consumed
    prefix, including the terminating NUL byte when k < n. Lemma
    [bounded_prefix_readable] shows that any byte count up to that
    consumed extent satisfies [readable_bytes], without requiring any
    bytes after the NUL terminator to be readable. *)
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

(** Since a NUL-terminated string of length k always has k < 2^64 - 1,
    [terminated_length_readable] specializes [bounded_prefix_readable] to
    show that the k + 1 bytes of the string and its NUL terminator
    satisfy [readable_bytes]. *)
Lemma terminated_length_readable : forall m p k,
  terminated_length m p k -> readable_bytes m p (k + 1).
Proof.
  intros m p k [Hlength Hmax]. eapply bounded_prefix_readable; [exact Hlength|].
  assert (Hlt : (k <? 2 ^ 64 - 1) = true) by (apply Z.ltb_lt; exact Hmax).
  rewrite Hlt. destruct Hlength as (_ & Hk & _). lia.
Qed.

(** In Fil-C, pointer capabilities live in eight-byte-aligned [[aux]]
    slots, so overwriting even a single byte inside an eight-byte word
    must clear the capability stored for that slot. The boolean test
    [memset_touched] returns `true` when a positive byte count n causes
    the filled byte range at p to overlap the eight-byte-aligned slot
    starting at address a. *)
Definition memset_touched (p : ptr) (n a : Z) : bool :=
  (0 <? n) && (a mod 8 =? 0) && (a <? ptr_addr p + n) && (ptr_addr p <? a + 8).

(** Lemma [memset_touched_spec] rewrites the boolean test
    [memset_touched] into the equivalent arithmetic conjunction: the fill
    count n is positive, the slot address a is eight-byte aligned, and the
    filled byte range overlaps the eight-byte slot at a. *)
Lemma memset_touched_spec : forall p n a,
  memset_touched p n a = true <->
  0 < n /\ a mod 8 = 0 /\ a < ptr_addr p + n /\ ptr_addr p < a + 8.
Proof.
  intros. unfold memset_touched. repeat rewrite andb_true_iff.
  rewrite Z.eqb_eq. repeat rewrite Z.ltb_lt. tauto.
Qed.

(** When `c: memset` starts at an address that is not a multiple of
    eight, the first eight-byte [[aux]] capability slot it overlaps
    begins at the preceding eight-byte boundary. To give the call
    permission to clear that slot's capability, [memset_root] rounds a
    nonempty span's start address down to an eight-byte boundary while
    keeping the original end address. *)
Definition memset_root (p : ptr) (n : Z) : span :=
  if n =? 0 then mkSpan p 0 else
  mkSpan (mkPtr (ptr_addr p - ptr_addr p mod 8) (ptr_cap p)) (n + ptr_addr p mod 8).

(** A call to `c: memset` is admissible under [memset_domain] when the
    fill value c fits in 32 bits, the byte count n fits in 64 bits, the
    n destination bytes at p form a [writable_span], and for positive n
    the target object's base address is a multiple of eight. Because
    every Fil-C object starts at an eight-byte-aligned base, rounding
    an in-bounds destination address down to an eight-byte boundary
    never steps before the start of the object. *)
Definition memset_domain (m : mem) (p : ptr) (c n : Z) : Prop :=
  0 <= c < 2 ^ 32 /\ 0 <= n < 2 ^ 64 /\ writable_span m (mkSpan p n) /\
  (n = 0 \/ exists base, ptr_cap p = Obj base /\ base mod 8 = 0).

(** When `c: memset` fills a positive number of bytes inside an
    eight-byte-aligned object, rounding the destination address down
    to an eight-byte boundary never steps before the start of that
    object. The widened span [memset_root] is therefore writable
    whenever the caller's destination buffer is writable. *)
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

(** Rounding the start of a nonempty destination range down to an
    eight-byte boundary only enlarges the interval on the left, so
    every byte address in the caller's destination range also lies
    inside [memset_root]. *)
Lemma memset_byte_in_root : forall p n a,
  span_contains (mkSpan p n) a -> span_contains (memset_root p n) a.
Proof.
  intros p n a H. unfold span_contains in *. simpl in H.
  unfold memset_root. destruct (n =? 0) eqn:E; simpl.
  - apply Z.eqb_eq in E. subst. lia.
  - pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)). lia.
Qed.

(** When an eight-byte capability slot overlaps a nonempty `c: memset`
    range, that slot begins at or after the preceding eight-byte
    boundary and before the end of the fill range. Its aligned start
    address therefore lies inside [memset_root], giving the call
    permission to clear the slot's capability. *)
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

(** Even though [memset_root] widens the contract's write permission down
    to the nearest eight-byte boundary so it can clear a partially
    overwritten capability slot, the call must not alter data bytes
    before `ptr_addr p`. The frame relation [memset_frame] states that a
    memory step preserves all object regions, leaves every data byte
    outside `mkSpan p n` unchanged, and leaves every [[aux]] slot where
    [memset_touched] is `false` unchanged. *)
Definition memset_frame (m : mem) (p : ptr) (n : Z) (m' : mem) : Prop :=
  m_regions m' = m_regions m /\
  (forall a, ~ span_contains (mkSpan p n) a -> m_bytes m' a = m_bytes m a) /\
  (forall a, memset_touched p n a = false -> m_aux m' a = m_aux m a).

(** When a `c: memset` call finishes, [memset_result] states that every
    byte in the destination buffer holds the low byte of c, every
    overlapped capability slot is cleared, and all other bytes,
    capability slots, and object regions remain unchanged. *)
Definition memset_result (m : mem) (p : ptr) (c n : Z) (m' : mem) : Prop :=
  memset_frame m p n m' /\
  (forall a, span_contains (mkSpan p n) a -> m_bytes m' a = c mod 256) /\
  (forall a, memset_touched p n a = true -> m_aux m' a = CNone).

(** To show that [memset_result] is satisfiable for any valid input,
    [memset_memory] constructs the exact post-call memory state directly,
    returning the original memory m unchanged when n is zero and updating
    the filled byte range and touched [[aux]] slots when n is positive. *)
Definition memset_memory (m : mem) (p : ptr) (c n : Z) : mem :=
  if n =? 0 then m else
  mkMem (fun a => if (ptr_addr p <=? a) && (a <? ptr_addr p + n)
                 then c mod 256 else m_bytes m a)
    (m_regions m) (fun a => if memset_touched p n a then CNone else m_aux m a).

(** Lemma [memset_memory_result] proves that the witness memory
    [memset_memory] satisfies all three clauses of [memset_result] for
    any memory m, pointer p, fill value c, and byte count n. *)
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

(** A `c: memset` call overwrites bytes and capability slots only
    within its widened writable span and clears each touched
    capability slot rather than storing a new pointer. Filling memory
    according to [memset_result] is therefore a valid [local_effect]. *)
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

(** A call instruction matches [memset_abi] when it passes a
    destination pointer, a 32-bit fill value, and a 64-bit byte count,
    and either discards the return value or binds the returned pointer. *)
Definition memset_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d P) /\
  exists p c n, args = [Arg P p; Arg W c; Arg L n].

(** The specification [memset_contract] packages the calling
    convention, precondition, writable span, and postcondition for
    `c: memset` and libpizlo's `c: zmemset`. It records a zero-length
    readable span on the destination pointer so the call may return
    that pointer's capability, uses [memset_root] as its writable
    span, performs no allocations or frees, and emits no events. *)
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

(** ## Snapshot copies and partial pointer words

    When `c: memcpy` or `c: memmove` copies bytes between buffers in
    Fil-C, an eight-byte destination slot preserves a pointer
    [[capability]] only when it receives all eight bytes from a single
    eight-byte-aligned slot in the source buffer. Any destination slot
    that is only partially overwritten or receives bytes from an
    unaligned source offset has its capability cleared. This section
    models byte copies from a snapshot of the initial memory so that
    disjoint and overlapping copies share one specification. *)

(** When a byte copy of length n from source s to destination d touches
    an eight-byte destination slot at address a, that slot preserves a
    pointer [[capability]] only if all eight of its bytes come from a
    single eight-byte-aligned slot in the source buffer. The boolean test
    [copy_full_slot] checks that the eight-byte slot at a lies completely
    inside the destination range and that the corresponding source
    address `ptr_addr s + (a - ptr_addr d)` is a multiple of eight. *)
Definition copy_full_slot (d s : ptr) (n a : Z) : bool :=
  (ptr_addr d <=? a) && (a + 8 <=? ptr_addr d + n) &&
  ((ptr_addr s + (a - ptr_addr d)) mod 8 =? 0).

(** For each eight-byte destination slot at address a touched by a copy,
    [copy_slot] computes the [[capability]] that must appear in [m_aux]
    after the call. When [copy_full_slot] holds, the slot receives the
    capability stored in the initial memory m at the corresponding source
    slot `ptr_addr s + (a - ptr_addr d)`, and otherwise it is cleared to
    [CNone] because partial or misaligned pointer copies never preserve
    capabilities in Fil-C. *)
Definition copy_slot (m : mem) (d s : ptr) (n a : Z) : cap :=
  if copy_full_slot d s n a then m_aux m (ptr_addr s + (a - ptr_addr d)) else CNone.

(** A byte copy of n bytes from source s to destination d is admissible
    under [copy_domain] when the destination satisfies [memset_domain],
    the source satisfies [readable_bytes] with an eight-byte-aligned
    object base for positive n, and the byte intervals either are
    disjoint or have `overlap = true` as in `c: memmove`. Even when the
    byte ranges are disjoint, adjacent source and destination buffers may
    still share an eight-byte [[aux]] slot if their boundary is not
    eight-byte aligned. *)
Definition copy_domain (overlap : bool) (m : mem) (d s : ptr) (n : Z) : Prop :=
  memset_domain m d 0 n /\ readable_bytes m s n /\
  (n = 0 \/ exists base, (ptr_cap s = Obj base \/ ptr_cap s = Ro base) /\ base mod 8 = 0) /\
  (overlap = true \/ n = 0 \/ ptr_addr d + n <= ptr_addr s \/ ptr_addr s + n <= ptr_addr d).

(** When n bytes starting at pointer p are readable under
    [readable_bytes], any eight-byte-aligned word completely inside that
    range lies in the same live object and has eight-byte read
    permission. This gives a copy call authority to read the
    capability stored in that source slot. *)
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

(** When a copy reads from a valid source buffer, the capability
    selected by [copy_slot] for any destination slot is either copied
    from a complete aligned pointer slot in the source buffer or
    cleared, so the call always has permission to store it. *)
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

(** When a byte copy of n bytes from s to d finishes, [copy_result]
    states that memory outside the destination range satisfies
    [memset_frame], each byte in the destination range equals the
    corresponding byte from the initial source buffer, and each
    touched destination capability slot equals [copy_slot]. *)
Definition copy_result (m : mem) (d s : ptr) (n : Z) (m' : mem) : Prop :=
  memset_frame m d n m' /\
  (forall a, span_contains (mkSpan d n) a ->
    m_bytes m' a = m_bytes m (ptr_addr s + (a - ptr_addr d))) /\
  (forall a, memset_touched d n a = true -> m_aux m' a = copy_slot m d s n a).

(** Combining the inside-range updates and outside-range frame of
    [copy_result] determines the exact byte value and capability slot
    at every address in the post-call memory. *)
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

(** Just as [memset_memory] witnesses the post-state of a byte fill,
    [copy_memory] constructs the post-state memory of a byte copy directly
    from the pre-state snapshot m, returning m unchanged when n is zero
    even if a positive self-copy would have cleared a partially touched
    capability slot. *)
Definition copy_memory (m : mem) (d s : ptr) (n : Z) : mem :=
  if n =? 0 then m else
  mkMem (fun a => if (ptr_addr d <=? a) && (a <? ptr_addr d + n)
    then m_bytes m (ptr_addr s + (a - ptr_addr d)) else m_bytes m a)
    (m_regions m) (fun a => if memset_touched d n a then copy_slot m d s n a else m_aux m a).

(** Lemma [copy_memory_result] proves that the explicit snapshot memory
    [copy_memory] satisfies [copy_result] for any initial memory m,
    destination d, source s, and count n. *)
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

(** A byte copy overwrites bytes and capability slots only inside the
    destination buffer's writable span and copies capabilities only
    from complete aligned words in the source buffer. Copying memory
    according to [copy_result] is therefore a valid [local_effect]. *)
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

(** A call instruction matches [copy_abi] when it passes a destination
    pointer, a source pointer, and a 64-bit byte count, and either
    discards the return value or binds the returned pointer. *)
Definition copy_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d P) /\
  exists d s n, args = [Arg P d; Arg P s; Arg L n].

(** While `c: memcpy` and `c: memmove` return the original destination
    pointer d, `c: mempcpy` returns a pointer to the byte immediately
    following the copied range. The helper [copy_return] selects between
    `mkPtr (ptr_addr d + n) (ptr_cap d)` and d according to the boolean
    flag `end_return`, keeping the destination's capability in both cases. *)
Definition copy_return (end_return : bool) (d : ptr) (n : Z) : ptr :=
  if end_return then mkPtr (ptr_addr d + n) (ptr_cap d) else d.

(** The specification [copy_contract] defines the external call
    contract for the byte-copy family, parameterized by whether the
    source and destination ranges may overlap and whether the call
    returns the start or the end of the destination range. Its readable
    spans cover the n-byte source buffer and a zero-length span on the
    destination pointer so the call can both copy source capabilities
    and return the destination capability. *)
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

(** Specializing [copy_contract] with `overlap = false` and
    `end_return = false` gives [memcpy_contract], which requires disjoint
    source and destination ranges and returns the destination pointer d. *)
Definition memcpy_contract := copy_contract false false.
(** Specializing [copy_contract] with `overlap = false` and
    `end_return = true` gives [mempcpy_contract], which requires disjoint
    ranges and returns `ptr_addr d + n` with the destination's capability. *)
Definition mempcpy_contract := copy_contract false true.
(** Specializing [copy_contract] with `overlap = true` and
    `end_return = false` gives [memmove_contract], which permits
    overlapping buffers and is used with `void_only` in `OsRegistry.v` to
    specify libpizlo's `c: zmemmove`. *)
Definition memmove_contract := copy_contract true false.

(** When a system call fails, libpizlo writes a 32-bit error code into
    the calling thread's `c: errno` variable. The predicate [errno_cell]
    requires the `c: errno` pointer p to have a nonzero, four-byte-aligned
    address and to form a four-byte [writable_span] in memory m. *)
Definition errno_cell (m : mem) (p : ptr) : Prop :=
  ptr_addr p <> 0 /\ writable_span m (mkSpan p 4) /\ ptr_addr p mod 4 = 0.

(** ## Memory paths over any runtime

    While an external call is running, it can alternate between local
    memory writes and fresh heap allocations answered by the
    [[runtime]] allocator. This section chains those steps into finite
    paths over any [Runtime] implementation and proves that every
    in-flight prefix and completed call preserves runtime
    [[ready|readiness]] and existing object [[identity|identities]]. *)

(** The functor [ExternalCalls] parameterizes the multi-step effect,
    prefix, and invocation relations over any [Runtime] implementation R
    whose allocator answers the call's heap allocation requests. *)
Module ExternalCalls (R : Runtime).

(** While an external call is running, it can alternate between
    modifying existing buffers and allocating new heap objects. The
    inductive relation [effects] chains those steps from an initial
    runtime and memory state to a final state, recording each newly
    allocated heap base in born so later steps of the call can
    initialize or free that object without touching caller memory. *)
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

(** Every local memory write and every fresh heap allocation along an
    [effects] path preserves the invariants of a [[ready]] runtime and
    keeps existing objects registered. By induction on the path, any
    sequence of authorized call effects starting from a ready state
    ends in a ready state where every initial object [[identity|persists]]. *)
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

(** Before an external call returns, or while a blocking call is still
    in flight, [prefix] describes any finite intermediate stage of its
    execution. A valid prefix consists of an [effects] path starting from
    an empty born list together with an event trace and updated world w'
    accepted by the contract's [contract_prefix] relation. *)
Definition prefix {world : Type} (spec : contract world) xs s m w born trace s' m' w' : Prop :=
  effects (contract_sources spec xs m w) (contract_writes spec xs m w)
    (contract_releases spec xs m w) (contract_requests spec xs m w) s m [] s' m' born /\
  contract_prefix spec xs m w born trace m' w'.

(** Any in-flight call [prefix] starting from a [[ready]] runtime and
    memory state keeps the runtime ready and preserves all existing
    object [[identity|identities]]. *)
Theorem prefix_preserve : forall world (spec : contract world) xs s m w born trace s' m' w',
  prefix spec xs s m w born trace s' m' w' -> R.ready s m ->
  R.ready s' m' /\ persists m m'.
Proof. intros world spec xs s m w born trace s' m' w' [He _] Hr. eapply effects_preserve; eauto. Qed.

(** When an external call requests a heap allocation permitted by its
    contract, [resource_failure] explains how that request can fail in
    runtime state s. Either the requested byte size is at most
    [max_allocation_size] and `R.alloc` returns `None`, producing
    [OutOfMemory] via [failure_oom], or the requested size before
    [heap_req] rounding exceeds [max_allocation_size], producing [TooBig]
    via [failure_big]. *)
Inductive resource_failure (requests : Z -> Z -> Prop) (s : R.state) : reason -> Prop :=
| failure_oom : forall align size,
    requests align size -> 0 <= size <= max_allocation_size ->
    R.alloc s (heap_req align size) = None -> resource_failure requests s OutOfMemory
| failure_big : forall align size,
    requests align size -> max_allocation_size < size ->
    resource_failure requests s TooBig.

(** The inductive relation [invoke] defines when a completed external
    call transitions from an initial runtime state, memory, and world
    to a final state with an event trace and a [call_end] outcome. In
    both cases, the call site must match the contract's ABI, the entry
    state must satisfy the precondition, and the memory transition must
    form a valid [prefix].

    A normal completion satisfies the contract's postcondition, returns
    words that match the declared return type and carry only
    capabilities available to the call, and records a trailing exit
    event whenever the call exits the process. A resource completion
    stops when a permitted allocation request fails in the allocator
    with a [resource_failure] reason that the contract allows. *)
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

(** Every completed external call, whether it finishes normally or
    stops on an allocation failure, reaches its final state through a
    valid [prefix] for some list of newly allocated objects. *)
Theorem invoke_prefix : forall world (spec : contract world) r args xs s m w trace ending s' m' w',
  invoke spec r args xs s m w trace ending s' m' w' ->
  exists born, prefix spec xs s m w born trace s' m' w'.
Proof. intros. destruct H; eauto. Qed.

(** Combining [invoke_prefix] with [effects_preserve], [invoke_preserve]
    proves that every completed external call from a [[ready]] state
    keeps the runtime ready and preserves every pre-existing object
    [[identity]]. The labelled machine in `ExternalMachine.v` relies on
    this theorem to prove its step-level readiness and persistence
    invariants. *)
Theorem invoke_preserve : forall world (spec : contract world) r args xs s m w trace ending s' m' w',
  invoke spec r args xs s m w trace ending s' m' w' -> R.ready s m ->
  R.ready s' m' /\ persists m m'.
Proof.
  intros world spec r args xs s m w trace ending s' m' w' H Hr.
  destruct (invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ H) as (born & He & _).
  eapply effects_preserve; eauto.
Qed.

(** The largest legal allocation request asks for one byte less than
    2^48 bytes, and rounding that request up to a 16-byte boundary
    with [heap_req] reserves an extent of 2^48 bytes. *)
Example rounded_maximum_extent :
  req_extent (heap_req 16 max_allocation_size) = 2 ^ 48.
Proof. reflexivity. Qed.

(** Because [effects_alloc] checks the caller's unrounded size against
    [max_allocation_size] before passing the rounded request to `R.alloc`,
    [rounded_maximum_allocation] shows that an allocation of
    [max_allocation_size] bytes forms a valid [effects] step whenever the
    runtime grants it. *)
Example rounded_maximum_allocation : forall s m base s',
  R.alloc s (heap_req 16 max_allocation_size) = Some (base, s') ->
  effects [] [] [] (fun align size => align = 16 /\ size = max_allocation_size)
    s m [] s' (allocated m (heap_req 16 max_allocation_size) base) [base].
Proof.
  intros s m base s' Ha. eapply effects_alloc;
    [split; reflexivity | unfold max_allocation_size; lia | exact Ha | constructor].
Qed.

(** Even though a request for [max_allocation_size] bytes rounds up to an
    extent of 2^48 bytes, [rounded_maximum_not_too_big] shows that it can
    never fail with [TooBig] under [resource_failure]. *)
Example rounded_maximum_not_too_big : forall s,
  ~ resource_failure (fun align size => align = 16 /\ size = max_allocation_size) s TooBig.
Proof.
  intros s H. inversion H as [align size Hreq Hbound Ha | align size Hreq Hbig].
  destruct Hreq as [_ ->]. lia.
Qed.

(** Once a contract requests 2^48 bytes, the unrounded size exceeds
    [max_allocation_size], and [oversized_request] shows that the request
    fails with [TooBig] in every runtime state s. *)
Example oversized_request : forall s,
  resource_failure (fun align size => align = 16 /\ size = 2 ^ 48) s TooBig.
Proof.
  intros s. eapply failure_big with (align := 16) (size := 2 ^ 48);
    [split; reflexivity | unfold max_allocation_size; lia].
Qed.

(** Whenever a `c: memset` call site and its arguments are valid and
    the updated memory satisfies [memset_result], the call completes
    under [memset_contract] and returns the destination pointer without
    allocating memory or emitting events. *)
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

(** Whenever a `c: memset` call passes a valid destination buffer, fill
    byte, and length, the call can finish in the updated memory
    [memset_memory] and return the destination pointer. *)
Theorem memset_admitted : forall world r args p c n s m (w : world),
  memset_abi r args -> memset_domain m p c n ->
  invoke (memset_contract world) r args [WPtr p; WInt c; WInt n] s m w
    [] (CallReturn [WPtr p]) s (memset_memory m p c n) w.
Proof.
  intros. apply memset_return; [assumption|assumption|apply memset_memory_result].
Qed.

(** When a call governed by [memset_contract] finishes, it emits no
    events, leaves the external world unchanged, returns the
    destination pointer, and updates memory according to
    [memset_result]. *)
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

(** When `c: memset` or `c: zmemset` is called with a byte count of zero,
    no byte lies inside `mkSpan p 0` and no [[aux]] slot is touched under
    [memset_touched]. Theorem [memset_zero_invocation] uses
    [memset_invocation] to show that any completed zero-length call
    returns p and leaves every region, data byte, and capability slot in
    m' equal to its value in m. *)
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

(** Whenever a byte-copy call site and its operands are valid and the
    updated memory satisfies [copy_result], the call completes under
    [copy_contract] in a single local-effect step and returns the
    specified destination pointer. *)
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

(** Every valid byte-copy call site and input state can complete in the
    explicit snapshot memory [copy_memory], showing that
    [copy_contract] is satisfiable for all admissible operands. *)
Theorem copy_admitted : forall overlap end_return world r args d src n s m (w : world),
  copy_abi r args -> copy_domain overlap m d src n ->
  invoke (copy_contract overlap end_return world) r args [WPtr d; WPtr src; WInt n] s m w
    [] (CallReturn [WPtr (copy_return end_return d n)]) s (copy_memory m d src n) w.
Proof. intros. apply copy_completed; [assumption|assumption|apply copy_memory_result]. Qed.

(** When a call governed by [copy_contract] finishes, it emits no
    events, leaves the external world unchanged, updates the
    destination buffer according to [copy_result], and returns the
    destination or end pointer. *)
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

(** In a [[ready]] memory state, every registered object lies inside the
    48-bit [[address-space|address space]] below 2^48. Theorem
    [copy_endpoint] uses `R.address_space` to show that when [copy_domain]
    holds, the endpoint `ptr_addr d + n` returned by `c: mempcpy` stays
    within the destination object's bounds (including one-past-the-end)
    and fits in a canonical 64-bit address without modular wraparound. *)
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

(** In a [[ready]] memory state, every registered object lies inside the
    48-bit address space. Because [bounded_length] checks read
    permission across the consumed prefix of a string scan, both the
    start address and the end of that consumed prefix fit below 2^48,
    even when the caller's maximum bound n is much larger. *)
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

(** Since a NUL-terminated string of length k always consumes k + 1 bytes
    including its terminating NUL, [terminated_length_extent] specializes
    [bounded_length_extent] to show that `ptr_addr p + k + 1 <= 2 ^ 48`
    in any [[ready]] memory state. *)
Lemma terminated_length_extent : forall s m p k,
  R.ready s m -> terminated_length m p k ->
  0 <= ptr_addr p /\ ptr_addr p + k + 1 <= 2 ^ 48.
Proof.
  intros s m p k Hr [Hlength Hmax].
  pose proof (bounded_length_extent _ _ _ _ _ Hr Hlength) as Hextent.
  assert (Hlt : (k <? 2 ^ 64 - 1) = true) by (apply Z.ltb_lt; exact Hmax).
  rewrite Hlt in Hextent. exact Hextent.
Qed.

(** Unlike a bounded string scan that may stop before its maximum bound,
    [readable_bytes] checks read permission across all n bytes, so
    [readable_bytes_extent] proves that the entire n-byte interval
    starting at `ptr_addr p` fits within `0..2^48` in any [[ready]]
    memory state. *)
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

    Higher-level contracts and separation-logic proofs often describe a C
    string by the mathematical list of its nonzero character bytes rather
    than by the numeric offset of its terminating NUL byte. This final
    section defines the list-based predicates [string_at] and [c_string]
    and proves in [StringLengths] that, in any [[ready]] memory state, a
    readable list string is equivalent to a [terminated_length] scan
    whose NUL byte lies strictly below `SIZE_MAX`. *)

(** Given a memory m, a start address a, and a list of character codes
    bytes, the recursive predicate [string_at] holds when memory stores
    each byte of the list at consecutive addresses starting at a, with
    every byte in `1..255`, followed immediately by a terminating NUL
    byte `0`. *)
Fixpoint string_at (m : mem) (a : Z) (bytes : list Z) : Prop :=
  match bytes with
  | [] => m_bytes m a = 0
  | b :: rest => 0 < b < 256 /\ m_bytes m a = b /\ string_at m (a + 1) rest
  end.

(** A pointer p points to a valid C string with character list bytes
    under [c_string] when its [[capability]] grants read permission
    across the characters and their terminating NUL byte and
    [string_at] holds at p's address. *)
Definition c_string (m : mem) (p : ptr) (bytes : list Z) : Prop :=
  access_res m (ptr_addr p) (ptr_cap p) (Z.of_nat (length bytes) + 1) Read 1 = Some ok /\
  string_at m (ptr_addr p) bytes.

(** By induction on the byte list, [string_at_length] translates the
    recursive predicate [string_at] into indexed byte lookups: every
    offset i before `length bytes` holds a nonzero byte in `1..255`, and
    the offset `length bytes` holds the terminating NUL byte `0`. *)
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

(** Conversely, if every offset before count holds a nonzero byte in
    `1..255` and offset count holds `0`, [string_at_exists] constructs the
    unique list of bytes of length count that satisfies [string_at] at
    address a. *)
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

(** Any pointer whose NUL-terminated scan length is k under
    [terminated_length] points to a valid [c_string] whose character
    list has length k. *)
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

(** While converting [terminated_length] into a [c_string] in
    [terminated_length_string] needs no runtime assumptions, the reverse
    direction must show that the target object is live and that the
    string length k is strictly less than `SIZE_MAX`. The functor
    [StringLengths] proves that reverse direction over any [Runtime] R
    using the [[ready]] memory invariants. *)
Module StringLengths (R : Runtime).

(** In Fil-C, freed objects have zero-length bounds and every object
    fits inside the 48-bit address space. Because a valid C string
    under [c_string] has at least one readable byte for its NUL
    terminator, its object must still be live and its length is always
    less than `SIZE_MAX`. *)
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

(** In any [[ready]] memory state, a pointer has NUL-terminated scan
    length k under [terminated_length] if and only if it points to a
    valid [c_string] of length k. *)
Theorem terminated_length_c_string : forall s m p k,
  R.ready s m ->
  (terminated_length m p k <->
   exists bytes, c_string m p bytes /\ k = Z.of_nat (length bytes)).
Proof.
  intros s m p k Hr. split; [apply terminated_length_string|].
  intros (bytes & Hstring & ->). eapply c_string_length; eauto.
Qed.

End StringLengths.
