(** [[campaign|Campaign]] 4's trusted [[external call]] boundary
    ([libc-contracts.md](../../docs/libc-contracts.md),
    [milestone 1](../../docs/formal.md#campaign-4-milestone-1-a-standalone-contract-boundary)).

    Contracts describe libc; they do not implement or prove it. A call
    must establish its ABI and semantic premises. A missing premise is
    an unmet [[obligation]], not a proof that native libc necessarily traps.
    In-contract calls may return, terminate, or exhaust resources, but
    cannot produce [Unchecked] or a capability panic.

    Memory effects are finite paths: bounded writes and authorized heap
    releases alternate with allocations by an arbitrary [[runtime]]. Each
    prefix preserves [[ready|readiness]] and [[identity|object identities]].
    No new assumption is added to Runtime, and the existing
    [[machine]] is unchanged.

    [StreamBytes] records bytes accepted by stdio, possibly buffered; it
    is deliberately NOT a kernel write. Flush and exit handlers still
    need their own contracts before a whole-program trace is closed. *)

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

(** strlen returns a size_t (class L) and takes exactly one pointer. *)
Definition strlen_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d L) /\ exists p, args = [Arg P p].

(** Pure trusted strlen. Its input names the object life and the byte
    span through the first NUL; no auxiliary slots are read to compute
    the result. Empty sources prohibit capability propagation, not reads.
    All memory, including regions and auxiliary slots, is preserved;
    no allocation, release, observation or resource ending is permitted. *)
Definition strlen_contract (world : Type) : contract world :=
  mkContract world (RClass L) strlen_abi
    (fun xs m _ => exists p k, xs = [WPtr p] /\ terminated_length m p k)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun xs m w born trace ending m' w' =>
      born = [] /\ trace = [] /\ m' = m /\ w' = w /\
      exists p k, xs = [WPtr p] /\ terminated_length m p k /\ ending = CallReturn [WInt k])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize]).

(** strnlen returns a size_t (class L) and takes a pointer and size_t.
    Discarding the result does not change the callee's return shape. *)
Definition strnlen_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d L) /\ exists p n, args = [Arg P p; Arg L n].

(** A pure, read-only trusted API contract over any logical world.
    Empty sources govern capability propagation, not all byte reads:
    those are justified by [bounded_length]. No writes, releases,
    allocations, events or resource outcomes are authorized. Empty
    prefixes allow no visible progress without promising termination.
    Panic annotations describe violated premises, not native behavior
    for every invalid input (notably zero-count null pointers). *)
Definition strnlen_contract (world : Type) : contract world :=
  mkContract world (RClass L) strnlen_abi
    (fun xs m _ => exists p n k, xs = [WPtr p; WInt n] /\ bounded_length m p n k)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun xs m w born trace ending m' w' =>
      born = [] /\ trace = [] /\ m' = m /\ w' = w /\
      exists p n k, xs = [WPtr p; WInt n] /\ bounded_length m p n k /\ ending = CallReturn [WInt k])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize]).

(** A canonical size_t count of well-formed bytes is readable through
    one live object capability. Zero count still needs live authority,
    possibly one-past. This is a full-span premise, not an early-stop scan. *)
Definition readable_bytes (m : mem) (p : ptr) (n : Z) : Prop :=
  0 <= n < 2 ^ 64 /\
  (exists base reg, (ptr_cap p = Obj base \/ ptr_cap p = Ro base) /\
    object_region base (m_regions m) = Some reg /\ r_life reg = Live) /\
  access_res m (ptr_addr p) (ptr_cap p) n Read 1 = Some ok /\
  (forall i, 0 <= i < n -> 0 <= m_bytes m (ptr_addr p + i) < 256).

(** memchr reads sequentially through its first matching byte, or the
    whole bound on a miss. The memory-only stop witness does not assume
    an invocation or its returned pointer. Zero count retains the live
    capability requirement of [readable_bytes]. *)
Definition memchr_input (m : mem) (p : ptr) (c n : Z) : Prop :=
  0 <= c < 2 ^ 32 /\ 0 <= n < 2 ^ 64 /\
  exists k, 0 <= k <= n /\
    readable_bytes m p (k + (if k <? n then 1 else 0)) /\
    (forall i, 0 <= i < k -> m_bytes m (ptr_addr p + i) <> c mod 256) /\
    (k < n -> m_bytes m (ptr_addr p + k) = c mod 256).

(** A hit is the first matching byte, with exactly the input capability;
    a miss is null. The int's low byte implements unsigned-char
    conversion, including negative C ints already normalized at class W. *)
Definition memchr_result (m : mem) (p : ptr) (c n : Z) (q : ptr) : Prop :=
  (exists k, 0 <= k < n /\ m_bytes m (ptr_addr p + k) = c mod 256 /\
    (forall i, 0 <= i < k -> m_bytes m (ptr_addr p + i) <> c mod 256) /\
    q = mkPtr (ptr_addr p + k) (ptr_cap p)) \/
  ((forall i, 0 <= i < n -> m_bytes m (ptr_addr p + i) <> c mod 256) /\
    q = mkPtr 0 CNone).

(** Finite first-match existence is constructive and independent of
    invocation existence or memory authority. It is not a libc executor
    or a native termination theorem. Extend the interval on the right. *)
Lemma memchr_result_total : forall m p c n,
  0 <= n -> exists q, memchr_result m p c n q.
Proof.
  intros m p c n Hn.
  assert (Hfinite : forall count : nat, exists q, memchr_result m p c (Z.of_nat count) q).
  { induction count as [|count [q Hq]].
    - exists (mkPtr 0 CNone). right. split; [intros i Hi; lia|reflexivity].
    - destruct Hq as [(k & Hk & Hbyte & Hbefore & ->) | (Hmiss & ->)].
      + exists (mkPtr (ptr_addr p + k) (ptr_cap p)). left. exists k.
        rewrite Nat2Z.inj_succ. repeat split; auto; lia.
      + destruct (Z.eq_dec (m_bytes m (ptr_addr p + Z.of_nat count)) (c mod 256)) as [Heq | Hneq].
        * exists (mkPtr (ptr_addr p + Z.of_nat count) (ptr_cap p)). left.
          exists (Z.of_nat count). rewrite Nat2Z.inj_succ. repeat split; auto; lia.
        * exists (mkPtr 0 CNone). right. split; [|reflexivity].
          intros i Hi. rewrite Nat2Z.inj_succ in Hi.
          destruct (Z_lt_dec i (Z.of_nat count)); [apply Hmiss; lia|].
          replace i with (Z.of_nat count) by lia. exact Hneq. }
  replace n with (Z.of_nat (Z.to_nat n)) by (rewrite Z2Nat.id; lia). apply Hfinite.
Qed.

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

(** Existing full-span callers remain admitted. Early hits no longer
    require their unused suffix to be inside the object. *)
Lemma memchr_input_full : forall m p c n,
  0 <= c < 2 ^ 32 -> readable_bytes m p n -> memchr_input m p c n.
Proof.
  intros m p c n Hc Hread.
  pose proof (proj1 Hread) as Hn.
  split; [exact Hc|]. split; [exact Hn|].
  destruct (memchr_result_total m p c n ltac:(lia)) as [q [(k & Hk & Hbyte & Hbefore & _) | (Hmiss & _)]].
  - exists k. split; [lia|]. split.
    + rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hk)). eapply readable_bytes_prefix; [exact Hread|lia].
    + auto.
  - exists n. rewrite Z.ltb_irrefl. simpl. rewrite Z.add_0_r.
    split; [lia|]. split; [exact Hread|]. split; [exact Hmiss|intros; lia].
Qed.

(** The admitted stop witness constructs a result without searching an
    inaccessible suffix, even when the maximum is SIZE_MAX. *)
Lemma memchr_input_result : forall m p c n,
  memchr_input m p c n -> exists q, memchr_result m p c n q.
Proof.
  intros m p c n (_ & _ & k & Hk & _ & Hbefore & Hmatch).
  destruct (Z_lt_dec k n) as [Hlt|Hlast].
  - exists (mkPtr (ptr_addr p + k) (ptr_cap p)). left. exists k.
    split; [lia|]. split; [apply Hmatch; exact Hlt|]. auto.
  - exists (mkPtr 0 CNone). right. split; [|reflexivity].
    intros i Hi. apply Hbefore. lia.
Qed.

(** First-match order fixes the entire returned pointer, not only its
    numeric address or an available capability. *)
Lemma memchr_result_unique : forall m p c n left right,
  memchr_result m p c n left -> memchr_result m p c n right -> left = right.
Proof.
  intros m p c n left right Hl Hr.
  destruct Hl as [(l & Hl & Hbl & Hbeforel & ->) | (Hmissl & ->)];
    destruct Hr as [(r & Hr & Hbr & Hbeforer & ->) | (Hmissr & ->)].
  - assert (l = r).
    { destruct (Z.lt_trichotomy l r) as [Hlt | [Heq | Hgt]]; [|exact Heq|].
      - exfalso. apply (Hbeforer l ltac:(lia)). exact Hbl.
      - exfalso. apply (Hbeforel r ltac:(lia)). exact Hbr. }
    subst. reflexivity.
  - exfalso. apply (Hmissr l Hl). exact Hbl.
  - exfalso. apply (Hmissl r Hr). exact Hbr.
  - reflexivity.
Qed.

(** A memchr result has only source-pointer authority, or none for a
    miss. The exact provenance requirement remains [memchr_result]. *)
Lemma memchr_result_authority : forall m p c n q,
  memchr_result m p c n q -> available_cap [mkSpan p n] [] m (ptr_cap q).
Proof.
  intros m p c n q [(k & _ & _ & _ & ->) | (_ & ->)].
  - right. left. exists (mkSpan p n). split; [left; reflexivity|reflexivity].
  - left. reflexivity.
Qed.

(** memchr returns a pointer and takes a pointer, int and size_t. *)
Definition memchr_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d P) /\
  exists p c n, args = [Arg P p; Arg W c; Arg L n].

(** Pure trusted search with one capability source and no mutation,
    allocation or resource permission. Admission requires only the
    input domain and first-match prefix, not a supplied result or invocation.
    Its source span is a capability propagation envelope, not the consumed
    byte-read footprint; [memchr_result] allows only the input cap or null. *)
Definition memchr_contract (world : Type) : contract world :=
  mkContract world (RClass P) memchr_abi
    (fun xs m _ => exists p c n, xs = [WPtr p; WInt c; WInt n] /\ memchr_input m p c n)
    (fun xs _ _ => match xs with [WPtr p; WInt _; WInt n] => [mkSpan p n] | _ => [] end)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun xs m w born trace ending m' w' =>
      born = [] /\ trace = [] /\ m' = m /\ w' = w /\
      exists p c n q, xs = [WPtr p; WInt c; WInt n] /\ memchr_result m p c n q /\
        ending = CallReturn [WPtr q])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize]).

(** ## Bounded binary comparisons *)

(** Lexicographic byte order: either every pair is equal, or the first
    differing pair fixes the order. Both pointers refer to the same
    memory; overlap and identical spans are permitted. Readability and
    unsigned-byte domains are separate admission obligations. *)
Definition memcmp_order (m : mem) (p q : ptr) (n : Z) (ordering : comparison) : Prop :=
  (ordering = Datatypes.Eq /\
    forall i, 0 <= i < n -> m_bytes m (ptr_addr p + i) = m_bytes m (ptr_addr q + i)) \/
  (exists k, 0 <= k < n /\
    (forall i, 0 <= i < k -> m_bytes m (ptr_addr p + i) = m_bytes m (ptr_addr q + i)) /\
    m_bytes m (ptr_addr p + k) <> m_bytes m (ptr_addr q + k) /\
    ordering = Z.compare (m_bytes m (ptr_addr p + k)) (m_bytes m (ptr_addr q + k))).

(** A finite interval has a first difference or is equal throughout.
    This constructive existence does not assume invocation coverage. *)
Lemma memcmp_order_total : forall m p q n,
  0 <= n -> exists ordering, memcmp_order m p q n ordering.
Proof.
  intros m p q n Hn.
  assert (Hfinite : forall count : nat, exists ordering, memcmp_order m p q (Z.of_nat count) ordering).
  { induction count as [|count [ordering Horder]].
    - exists Datatypes.Eq. left. split; [reflexivity|intros i Hi; lia].
    - destruct Horder as [(-> & Hsame) | (k & Hk & Hbefore & Hdifferent & ->)].
      + destruct (Z.eq_dec (m_bytes m (ptr_addr p + Z.of_nat count))
          (m_bytes m (ptr_addr q + Z.of_nat count))) as [Heq | Hneq].
        * exists Datatypes.Eq. left. split; [reflexivity|]. intros i Hi.
          rewrite Nat2Z.inj_succ in Hi. destruct (Z_lt_dec i (Z.of_nat count)).
          -- apply Hsame. lia.
          -- replace i with (Z.of_nat count) by lia. exact Heq.
        * eexists. right. exists (Z.of_nat count). rewrite Nat2Z.inj_succ.
          repeat split; auto; lia.
      + eexists. right. exists k. rewrite Nat2Z.inj_succ. repeat split; auto; lia. }
  replace n with (Z.of_nat (Z.to_nat n)) by (rewrite Z2Nat.id; lia). apply Hfinite.
Qed.

(** The first differing pair fixes the order uniquely, not the returned
    int's magnitude. An equal prefix rules out a competing earlier pair. *)
Lemma memcmp_order_unique : forall m p q n left right,
  memcmp_order m p q n left -> memcmp_order m p q n right -> left = right.
Proof.
  intros m p q n left right Hl Hr.
  destruct Hl as [(-> & Hsamel) | (l & Hl & Hbeforel & Hdiffl & ->)];
    destruct Hr as [(-> & Hsamer) | (r & Hr & Hbeforer & Hdiffr & ->)].
  - reflexivity.
  - exfalso. apply Hdiffr. apply Hsamel. exact Hr.
  - exfalso. apply Hdiffl. apply Hsamer. exact Hl.
  - assert (l = r).
    { destruct (Z.lt_trichotomy l r) as [Hlt | [Heq | Hgt]]; [|exact Heq|].
      - exfalso. apply Hdiffl. apply Hbeforer. lia.
      - exfalso. apply Hdiffr. apply Hbeforel. lia. }
    subst. reflexivity.
Qed.

(** A canonical class-W bit pattern whose signed reading has the byte
    order's sign. All representable correct magnitudes are permitted,
    not merely minus/plus one or the first byte difference. *)
Definition memcmp_result (m : mem) (p q : ptr) (n bits : Z) : Prop :=
  0 <= bits < 2 ^ 32 /\ exists ordering, memcmp_order m p q n ordering /\
    Z.compare (sign_extension (2 ^ 32) (2 ^ 31) bits) 0 = ordering.

(** Every finite comparison permits a canonical zero, negative or
    positive witness. Other magnitudes remain permitted by the contract. *)
Lemma memcmp_result_total : forall m p q n,
  0 <= n -> exists bits, memcmp_result m p q n bits.
Proof.
  intros m p q n Hn. destruct (memcmp_order_total m p q n Hn) as [ordering Horder].
  destruct ordering; [exists 0|exists (2 ^ 32 - 1)|exists 1].
  all: split; [vm_compute; split; congruence|]; eexists; split; [exact Horder|reflexivity].
Qed.

(** Permitted result words may differ, but their signed signs agree. *)
Lemma memcmp_result_sign_unique : forall m p q n left right,
  memcmp_result m p q n left -> memcmp_result m p q n right ->
  Z.compare (sign_extension (2 ^ 32) (2 ^ 31) left) 0 =
    Z.compare (sign_extension (2 ^ 32) (2 ^ 31) right) 0.
Proof.
  intros m p q n left right (_ & ol & Hl & El) (_ & or & Hr & Er).
  rewrite El, Er. eapply memcmp_order_unique; eauto.
Qed.

(** memcmp returns an int and takes two pointers and a size_t. *)
Definition memcmp_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d W) /\
  exists p q n, args = [Arg P p; Arg P q; Arg L n].

(** Pure trusted binary comparison. Both full spans must be readable,
    even at zero count or an early difference. There is no capability
    propagation, mutation, allocation or resource outcome. *)
Definition memcmp_contract (world : Type) : contract world :=
  mkContract world (RClass W) memcmp_abi
    (fun xs m _ => exists p q n, xs = [WPtr p; WPtr q; WInt n] /\
      readable_bytes m p n /\ readable_bytes m q n)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun xs m w born trace ending m' w' =>
      born = [] /\ trace = [] /\ m' = m /\ w' = w /\
      exists p q n bits, xs = [WPtr p; WPtr q; WInt n] /\ memcmp_result m p q n bits /\
        ending = CallReturn [WInt bits])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize]).

(** ## Bounded string comparisons *)

(** A logical comparison window includes an earlier terminator, but
    never byte n. These are mathematical integers: adding one before
    taking the minimum must not wrap at SIZE_MAX. A first difference
    can decide the result earlier than the end of this window. *)
Definition strncmp_window (n left right : Z) : Z :=
  Z.min n (Z.min (left + 1) (right + 1)).

(** The window fits both independently justified consumed intervals. *)
Lemma strncmp_window_bounds : forall n left right,
  0 <= left <= n -> 0 <= right <= n ->
  0 <= strncmp_window n left right /\ strncmp_window n left right <= n /\
  strncmp_window n left right <= left + (if left <? n then 1 else 0) /\
  strncmp_window n left right <= right + (if right <? n then 1 else 0).
Proof.
  intros n left right Hl Hr.
  assert (Hzero : 0 <= strncmp_window n left right).
  { unfold strncmp_window. apply Z.min_glb; [lia|]. apply Z.min_glb; lia. }
  assert (Hn : strncmp_window n left right <= n) by apply Z.le_min_l.
  assert (Hleft : strncmp_window n left right <= left + 1).
  { eapply Z.le_trans; [apply Z.le_min_r|apply Z.le_min_l]. }
  assert (Hright : strncmp_window n left right <= right + 1).
  { eapply Z.le_trans; [apply Z.le_min_r|apply Z.le_min_r]. }
  repeat split; try assumption.
  - destruct (left <? n) eqn:E; [lia|]. apply Z.ltb_ge in E. lia.
  - destruct (right <? n) eqn:E; [lia|]. apply Z.ltb_ge in E. lia.
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

(** Both sides can read every byte on which the comparison depends.
    Total model memory alone would not establish this authority fact. *)
Lemma strncmp_window_readable : forall m p q n left right,
  bounded_length m p n left -> bounded_length m q n right ->
  readable_bytes m p (strncmp_window n left right) /\
  readable_bytes m q (strncmp_window n left right).
Proof.
  intros m p q n left right Hl Hr.
  destruct (strncmp_window_bounds n left right (proj1 (proj2 Hl)) (proj1 (proj2 Hr)))
    as (Hzero & _ & Hleft & Hright).
  split; eapply bounded_prefix_readable; eauto; lia.
Qed.

(** The sign comes from the logical window, using the original memory
    and independently witnessed bounded strings. Magnitudes stay free. *)
Definition strncmp_result (m : mem) (p q : ptr) (n bits : Z) : Prop :=
  exists left right, bounded_length m p n left /\ bounded_length m q n right /\
    memcmp_result m p q (strncmp_window n left right) bits.

(** Result existence follows from input obligations, not call coverage. *)
Lemma strncmp_result_total : forall m p q n left right,
  bounded_length m p n left -> bounded_length m q n right ->
  exists bits, strncmp_result m p q n bits.
Proof.
  intros m p q n left right Hl Hr.
  destruct (strncmp_window_readable m p q n left right Hl Hr) as [Hread _].
  destruct (memcmp_result_total m p q (strncmp_window n left right)
    ltac:(destruct Hread as [Hn _]; lia)) as [bits Hbits].
  exists bits, left, right. auto.
Qed.

(** First-NUL uniqueness fixes the window; only the signed sign of
    permitted return words is unique, not their integer magnitude. *)
Lemma strncmp_result_sign_unique : forall m p q n left right,
  strncmp_result m p q n left -> strncmp_result m p q n right ->
  Z.compare (sign_extension (2 ^ 32) (2 ^ 31) left) 0 =
    Z.compare (sign_extension (2 ^ 32) (2 ^ 31) right) 0.
Proof.
  intros m p q n left right (ll & lr & Hll & Hlr & Hl) (rl & rr & Hrl & Hrr & Hr).
  pose proof (bounded_length_unique _ _ _ _ _ Hll Hrl) as <-.
  pose proof (bounded_length_unique _ _ _ _ _ Hlr Hrr) as <-.
  eapply memcmp_result_sign_unique; eauto.
Qed.

(** Pure trusted strncmp, with memcmp's unchanged P/P/L-to-W ABI.
    The table's independent bounded-string premises are conservative:
    an early difference does not waive an invalid suffix on either side.
    Empty sources mean no capability propagation, not an absence of reads. *)
Definition strncmp_contract (world : Type) : contract world :=
  mkContract world (RClass W) memcmp_abi
    (fun xs m _ => exists p q n left right, xs = [WPtr p; WPtr q; WInt n] /\
      bounded_length m p n left /\ bounded_length m q n right)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun xs m w born trace ending m' w' =>
      born = [] /\ trace = [] /\ m' = m /\ w' = w /\
      exists p q n bits, xs = [WPtr p; WPtr q; WInt n] /\ strncmp_result m p q n bits /\
        ending = CallReturn [WInt bits])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize]).

(** ## Unbounded string comparisons *)

(** Both terminated strings authorize the comparison window through the
    earlier NUL. Admission still depends on each complete string through
    its own NUL, including the longer string's tail outside this window. *)
Lemma strcmp_window_readable : forall m p q left right,
  terminated_length m p left -> terminated_length m q right ->
  readable_bytes m p (Z.min (left + 1) (right + 1)) /\
  readable_bytes m q (Z.min (left + 1) (right + 1)).
Proof.
  intros m p q left right [Hl Hleft] [Hr Hright].
  pose proof (strncmp_window_readable m p q (2 ^ 64 - 1) left right Hl Hr) as Hread.
  unfold strncmp_window in Hread. rewrite Z.min_r in Hread; [exact Hread|].
  eapply Z.le_trans; [apply Z.le_min_l|lia].
Qed.

(** strcmp compares unsigned bytes through the earlier terminator.
    Independent complete-string witnesses govern admission; only the
    signed sign of the canonical int result is specified, not magnitude. *)
Definition strcmp_result (m : mem) (p q : ptr) (bits : Z) : Prop :=
  exists left right, terminated_length m p left /\ terminated_length m q right /\
    memcmp_result m p q (Z.min (left + 1) (right + 1)) bits.

(** Terminated inputs construct a result independently of invocation
    existence; window readability is proved before using total memory. *)
Lemma strcmp_result_total : forall m p q left right,
  terminated_length m p left -> terminated_length m q right ->
  exists bits, strcmp_result m p q bits.
Proof.
  intros m p q left right Hl Hr.
  destruct (strcmp_window_readable m p q left right Hl Hr) as [Hread _].
  destruct (memcmp_result_total m p q (Z.min (left + 1) (right + 1))
    ltac:(destruct Hread as [Hn _]; lia)) as [bits Hbits].
  exists bits, left, right. auto.
Qed.

(** Unique first-NUL lengths fix the window, hence the result's signed
    sign. Distinct representable magnitudes of that sign remain legal. *)
Lemma strcmp_result_sign_unique : forall m p q left right,
  strcmp_result m p q left -> strcmp_result m p q right ->
  Z.compare (sign_extension (2 ^ 32) (2 ^ 31) left) 0 =
    Z.compare (sign_extension (2 ^ 32) (2 ^ 31) right) 0.
Proof.
  intros m p q left right (ll & lr & Hll & Hlr & Hl) (rl & rr & Hrl & Hrr & Hr).
  pose proof (terminated_length_unique _ _ _ _ Hll Hrl) as <-.
  pose proof (terminated_length_unique _ _ _ _ Hlr Hrr) as <-.
  eapply memcmp_result_sign_unique; eauto.
Qed.

(** strcmp returns an int and takes exactly two pointer arguments, no count. *)
Definition strcmp_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d W) /\ exists p q, args = [Arg P p; Arg P q].

(** Pure trusted strcmp over two independent live terminated strings.
    The input footprint is both referenced identities' regions and each
    string's bytes through its NUL; no auxiliary slots are read. The
    result compares only the minimum window. All memory and world are
    preserved, with no writes, propagation, allocation or release. *)
Definition strcmp_contract (world : Type) : contract world :=
  mkContract world (RClass W) strcmp_abi
    (fun xs m _ => exists p q left right, xs = [WPtr p; WPtr q] /\
      terminated_length m p left /\ terminated_length m q right)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun xs m w born trace ending m' w' =>
      born = [] /\ trace = [] /\ m' = m /\ w' = w /\
      exists p q bits, xs = [WPtr p; WPtr q] /\ strcmp_result m p q bits /\
        ending = CallReturn [WInt bits])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize]).

(** ## Unbounded character search *)

(** The complete string including its NUL is a readable byte span.
    Only the consumed extent is required, without runtime readiness. *)
Lemma terminated_length_readable : forall m p k,
  terminated_length m p k -> readable_bytes m p (k + 1).
Proof.
  intros m p k [Hlength Hmax]. eapply bounded_prefix_readable; [exact Hlength|].
  assert (Hlt : (k <? 2 ^ 64 - 1) = true) by (apply Z.ltb_lt; exact Hmax).
  rewrite Hlt. destruct Hlength as (_ & Hk & _). lia.
Qed.

(** strchr selects the first low-byte match through the first NUL,
    including that NUL when searched for, with exactly the source's
    capability; a miss is null. Full string admission is independent
    of an early match. The int's canonical domain is checked separately. *)
Definition strchr_result (m : mem) (p : ptr) (c : Z) (q : ptr) : Prop :=
  exists k, terminated_length m p k /\ memchr_result m p c (k + 1) q.

(** Input string authority constructs a first match or miss, after
    proving readability. This is nonvacuity, not native termination. *)
Lemma strchr_result_total : forall m p c k,
  terminated_length m p k -> exists q, strchr_result m p c q.
Proof.
  intros m p c k Hlength.
  pose proof (terminated_length_readable m p k Hlength) as [Hspan _].
  destruct (memchr_result_total m p c (k + 1) ltac:(lia)) as [q Hq].
  exists q, k. auto.
Qed.

(** First-NUL and first-match uniqueness fix the full returned pointer,
    including its capability rather than just its numeric address. *)
Lemma strchr_result_unique : forall m p c left right,
  strchr_result m p c left -> strchr_result m p c right -> left = right.
Proof.
  intros m p c left right (kl & Hl & Hleft) (kr & Hr & Hright).
  pose proof (terminated_length_unique _ _ _ _ Hl Hr) as <-.
  eapply memchr_result_unique; eauto.
Qed.

(** A zero-size source permits p's own capability, not any auxiliary
    slot. This is capability provenance, not the string's read footprint. *)
Lemma strchr_result_authority : forall m p c q,
  strchr_result m p c q -> available_cap [mkSpan p 0] [] m (ptr_cap q).
Proof.
  intros m p c q (k & _ & [(i & _ & _ & _ & ->) | (_ & ->)]).
  - right. left. exists (mkSpan p 0). split; [left; reflexivity|reflexivity].
  - left. reflexivity.
Qed.

(** A low-byte-zero search necessarily returns the readable terminator
    with the source capability; null or a later pointer cannot qualify. *)
Lemma strchr_result_nul : forall m p c q k,
  terminated_length m p k -> strchr_result m p c q -> c mod 256 = 0 ->
  q = mkPtr (ptr_addr p + k) (ptr_cap p).
Proof.
  intros m p c q k Hlength Hresult Hzero.
  eapply strchr_result_unique; [exact Hresult|]. exists k. split; [exact Hlength|].
  destruct Hlength as [(_ & Hk & _ & _ & Hbytes & Hnul) Hmax].
  left. exists k. split; [lia|]. split.
  - rewrite Hzero. apply Hnul. exact Hmax.
  - split; [|reflexivity]. intros i Hi. specialize (Hbytes i Hi). rewrite Hzero. lia.
Qed.

(** strchr returns a pointer and takes exactly a pointer and an int. *)
Definition strchr_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d P) /\ exists p c, args = [Arg P p; Arg W c].

(** Pure trusted strchr. Read dependencies are the source identity's
    region/life and bytes through its own NUL; auxiliary slots are not
    dependencies. The zero-size capability source permits returning p's
    own authority only, not zero byte reads or pointer-slot imports.
    No ownership transfers: a hit retains the source capability and is
    invalidated when that object's lifetime ends. No memory is changed. *)
Definition strchr_contract (world : Type) : contract world :=
  mkContract world (RClass P) strchr_abi
    (fun xs m _ => exists p c k, xs = [WPtr p; WInt c] /\
      0 <= c < 2 ^ 32 /\ terminated_length m p k)
    (fun xs _ _ => match xs with [WPtr p; WInt _] => [mkSpan p 0] | _ => [] end)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun xs m w born trace ending m' w' =>
      born = [] /\ trace = [] /\ m' = m /\ w' = w /\
      exists p c q, xs = [WPtr p; WInt c] /\ 0 <= c < 2 ^ 32 /\ strchr_result m p c q /\
        ending = CallReturn [WPtr q])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize]).

(** strrchr selects the last low-byte match through the first NUL,
    retaining the exact source capability, or returns canonical null.
    Earlier matches are permitted; later matches in the string are not. *)
Definition strrchr_result (m : mem) (p : ptr) (c : Z) (q : ptr) : Prop :=
  exists k, terminated_length m p k /\
    ((exists i, 0 <= i <= k /\ m_bytes m (ptr_addr p + i) = c mod 256 /\
      (forall j, i < j <= k -> m_bytes m (ptr_addr p + j) <> c mod 256) /\
      q = mkPtr (ptr_addr p + i) (ptr_cap p)) \/
     ((forall i, 0 <= i <= k -> m_bytes m (ptr_addr p + i) <> c mod 256) /\
      q = mkPtr 0 CNone)).

(** Constructive last-match existence uses a local finite-interval
    induction, not an assumption that a shorter prefix is terminated.
    Independent string authority justifies the complete readable span. *)
Lemma strrchr_result_total : forall m p c k,
  terminated_length m p k -> exists q, strrchr_result m p c q.
Proof.
  intros m p c k Hlength.
  pose proof (terminated_length_readable m p k Hlength) as [Hspan _].
  assert (Hfinite : forall count : nat, exists q,
    (exists i, 0 <= i < Z.of_nat count /\ m_bytes m (ptr_addr p + i) = c mod 256 /\
      (forall j, i < j < Z.of_nat count -> m_bytes m (ptr_addr p + j) <> c mod 256) /\
      q = mkPtr (ptr_addr p + i) (ptr_cap p)) \/
    ((forall i, 0 <= i < Z.of_nat count -> m_bytes m (ptr_addr p + i) <> c mod 256) /\
      q = mkPtr 0 CNone)).
  { induction count as [|count [q Hq]].
    - exists (mkPtr 0 CNone). right. split; [intros i Hi; lia|reflexivity].
    - destruct (Z.eq_dec (m_bytes m (ptr_addr p + Z.of_nat count)) (c mod 256)) as [Heq | Hneq].
      + exists (mkPtr (ptr_addr p + Z.of_nat count) (ptr_cap p)). left.
        exists (Z.of_nat count). rewrite Nat2Z.inj_succ.
        split; [lia|]. split; [exact Heq|]. split; [intros j Hj; lia|reflexivity].
      + exists q. destruct Hq as [(i & Hi & Hbyte & Hlater & ->) | (Hmiss & ->)].
        * left. exists i. rewrite Nat2Z.inj_succ. split; [lia|].
          split; [exact Hbyte|]. split; [|reflexivity]. intros j Hj.
          destruct (Z_lt_dec j (Z.of_nat count)); [apply Hlater; lia|].
          replace j with (Z.of_nat count) by lia. exact Hneq.
        * right. split; [|reflexivity]. intros i Hi. rewrite Nat2Z.inj_succ in Hi.
          destruct (Z_lt_dec i (Z.of_nat count)); [apply Hmiss; lia|].
          replace i with (Z.of_nat count) by lia. exact Hneq. }
  destruct (Hfinite (Z.to_nat (k + 1))) as [q Hq].
  rewrite Z2Nat.id in Hq by lia. exists q, k. split; [exact Hlength|].
  destruct Hq as [(i & Hi & Hbyte & Hlater & ->) | (Hmiss & ->)].
  - left. exists i. split; [lia|]. split; [exact Hbyte|].
    split; [intros j Hj; apply Hlater; lia|reflexivity].
  - right. split; [intros i Hi; apply Hmiss; lia|reflexivity].
Qed.

(** The shared first-NUL boundary and last-match exclusion fix the
    full returned pointer, not just its address. *)
Lemma strrchr_result_unique : forall m p c left right,
  strrchr_result m p c left -> strrchr_result m p c right -> left = right.
Proof.
  intros m p c left right (kl & Hl & Hleft) (kr & Hr & Hright).
  pose proof (terminated_length_unique _ _ _ _ Hl Hr) as <-.
  destruct Hleft as [(i & Hi & Hbyte & Hlater & ->) | (Hmiss & ->)];
    destruct Hright as [(j & Hj & Hother & Hafter & ->) | (Hnone & ->)].
  - destruct (Z.lt_trichotomy i j) as [Hij | [-> | Hji]]; [|reflexivity|].
    + exfalso. apply (Hlater j ltac:(lia)). exact Hother.
    + exfalso. apply (Hafter i ltac:(lia)). exact Hbyte.
  - exfalso. apply (Hnone i Hi). exact Hbyte.
  - exfalso. apply (Hmiss j Hj). exact Hother.
  - reflexivity.
Qed.

(** Last-match returns need only the source pointer's capability, not
    any auxiliary slot or capability from a different object. *)
Lemma strrchr_result_authority : forall m p c q,
  strrchr_result m p c q -> available_cap [mkSpan p 0] [] m (ptr_cap q).
Proof.
  intros m p c q (k & _ & [(i & _ & _ & _ & ->) | (_ & ->)]).
  - right. left. exists (mkSpan p 0). split; [left; reflexivity|reflexivity].
  - left. reflexivity.
Qed.

(** The readable NUL is a last match for every low-byte-zero argument,
    since the logical search interval has no later index. *)
Lemma strrchr_result_nul : forall m p c q k,
  terminated_length m p k -> strrchr_result m p c q -> c mod 256 = 0 ->
  q = mkPtr (ptr_addr p + k) (ptr_cap p).
Proof.
  intros m p c q k Hlength Hresult Hzero.
  eapply strrchr_result_unique; [exact Hresult|]. exists k. split; [exact Hlength|].
  destruct Hlength as [(_ & Hk & _ & _ & _ & Hnul) Hmax].
  left. exists k. split; [lia|]. split.
  - rewrite Hzero. apply Hnul. exact Hmax.
  - split; [intros j Hj; lia|reflexivity].
Qed.

(** Pure trusted strrchr shares strchr's ABI and propagation source,
    but selects the last match. Its full read dependencies are the
    referenced identity's region/life and bytes through NUL, not aux.
    The zero-size source is not a read footprint. A hit retains Obj or
    Ro with no ownership transfer or lifetime extension, becoming invalid
    when the source object dies. Memory/world remain exactly unchanged. *)
Definition strrchr_contract (world : Type) : contract world :=
  mkContract world (RClass P) strchr_abi
    (fun xs m _ => exists p c k, xs = [WPtr p; WInt c] /\
      0 <= c < 2 ^ 32 /\ terminated_length m p k)
    (fun xs _ _ => match xs with [WPtr p; WInt _] => [mkSpan p 0] | _ => [] end)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun xs m w born trace ending m' w' =>
      born = [] /\ trace = [] /\ m' = m /\ w' = w /\
      exists p c q, xs = [WPtr p; WInt c] /\ 0 <= c < 2 ^ 32 /\ strrchr_result m p c q /\
        ending = CallReturn [WPtr q])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize]).

(** ## Byte fills and auxiliary footprints *)

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

(** ## Thread-local errno lookup *)

(** The represented thread supplies a live, nonnull writable int cell.
    Alignment is of its address, not merely of its containing object. *)
Definition errno_cell (m : mem) (p : ptr) : Prop :=
  ptr_addr p <> 0 /\ writable_span m (mkSpan p 4) /\ ptr_addr p mod 4 = 0.

(** Plain __errno_location takes no arguments and returns P, including
    when the caller discards that result. Tuples are not scalar returns. *)
Definition errno_location_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d P) /\ args = [].

(** The representation independently ties the selected cell to the
    current thread. Its zero-length source exports that exact capability,
    not arbitrary stored pointers. Looking it up neither writes errno
    nor changes the world, allocates, releases, emits events or fails for
    resources. No cross-thread lifetime/stability theorem is implied. *)
Definition errno_location_contract (world : Type) (cell : world -> ptr)
    (rep : mem -> world -> Prop) : contract world :=
  mkContract world (RClass P) errno_location_abi
    (fun xs m w => xs = [] /\ rep m w /\ errno_cell m (cell w))
    (fun _ _ w => [mkSpan (cell w) 0])
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun _ m w born trace ending m' w' =>
      born = [] /\ trace = [] /\ m' = m /\ w' = w /\
      ending = CallReturn [WPtr (cell w)])
    (fun _ => False)
    (fun why => In why [ArgumentSize; ReturnSize]).

(** ## Fresh allocation *)

(** malloc takes one size_t and returns a pointer, or its result is
    discarded. Width coincidence does not admit a W argument. *)
Definition malloc_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d P) /\ exists n, args = [Arg L n].

(** The one permitted request shape; this does not count attempts. *)
Definition malloc_request (xs : list word) (align size : Z) : Prop :=
  exists n, xs = [WInt n] /\ align = 16 /\ size = n.

(** One successful allocation, including its independent freshness
    and legal original size. No old byte or auxiliary cell changes. *)
Definition malloc_result (m : mem) (n base : Z) (m' : mem) : Prop :=
  0 <= n <= max_allocation_size /\ fresh m (heap_req 16 n) base /\
  m' = allocated m (heap_req 16 n) base.

(** A logical allocation prefix is either unchanged or one-born.
    The generic resource rule can refuse a further permitted request
    after the one-born prefix. This terminal overapproximation is
    explicit: it is not a native two-request claim, nor a guarantee
    that every failure leaves the region list unchanged. *)
Definition malloc_prefix (m : mem) (n : Z) (born : list Z) (m' : mem) : Prop :=
  (born = [] /\ m' = m) \/
  exists base, born = [base] /\ malloc_result m n base m'.

(** The selected Fil-C malloc calls zgc_alloc, which does not return
    NULL on refusal. Refusal is a resource ending, never a panic.
    Exact endpoint framing is logical; native collector prefixes at
    allocation safepoints remain a correspondence obligation. *)
Definition malloc_contract (world : Type) : contract world :=
  mkContract world (RClass P) malloc_abi
    (fun xs _ _ => exists n, xs = [WInt n] /\ 0 <= n < 2 ^ 64)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ => [])
    (fun xs _ _ => malloc_request xs)
    (fun xs m w born trace m' w' => trace = [] /\ w' = w /\
      exists n, xs = [WInt n] /\ malloc_prefix m n born m')
    (fun xs m w born trace ending m' w' => trace = [] /\ w' = w /\
      exists n base, xs = [WInt n] /\ born = [base] /\ malloc_result m n base m' /\
        ending = CallReturn [WPtr (mkPtr base (Obj base))])
    resource_reason (fun why => In why [ArgumentSize; ReturnSize]).

(** Rounded capacity covers n, with strictly less than 16 extra
    bytes. Zero has zero modeled extent and grants no byte access. *)
Lemma malloc_extent : forall n, 0 <= n ->
  n <= req_extent (heap_req 16 n) < n + 16.
Proof.
  intros n Hn. change (n <= (n + 15) / 16 * 16 < n + 16).
  pose proof (Z.div_mod (n + 15) 16 ltac:(lia)).
  pose proof (Z.mod_pos_bound (n + 15) 16 ltac:(lia)). lia.
Qed.

(** The exact endpoint frames old objects as well as both cell maps. *)
Lemma malloc_old_cells : forall m n base m', malloc_result m n base m' ->
  (forall a, m_bytes m' a = m_bytes m a /\ m_aux m' a = m_aux m a) /\
  (forall b reg, object_region b (m_regions m) = Some reg ->
    object_region b (m_regions m') = Some reg).
Proof.
  intros m n base m' (_ & (_ & _ & _ & Hnew & _) & ->).
  split; [intros; split; reflexivity|]. intros. eapply allocated_old_region; eauto.
Qed.

(** ## Computing exact string footprints *)

(** A total bounded logical scan, not an implementation of libc.
    Exhaustion returns the bound; admission still requires a NUL. *)
Fixpoint nul_count (bytes : Z -> Z) (a : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' => if bytes a =? 0 then 0 else 1 + nul_count bytes (a + 1) fuel'
  end.

(** Remaining bytes of the object named by p's own capability.
    Missing/nonobject authority yields no scan capacity. *)
Definition string_capacity (m : mem) (p : ptr) : Z :=
  match ptr_cap p with
  | Obj base | Ro base => match object_region base (m_regions m) with
    | Some reg => Z.max 0 (r_end reg - ptr_addr p)
    | None => 0
    end
  | _ => 0
  end.

(** A concrete length lets a single fixed registry name the exact
    source span for strings of different lengths, without choice or a
    ghost length index. The precondition, not this scan, grants reads. *)
Definition string_length (m : mem) (p : ptr) : Z :=
  nul_count (m_bytes m) (ptr_addr p) (Z.to_nat (string_capacity m p)).

Lemma nul_count_first : forall fuel bytes a k,
  0 <= k < Z.of_nat fuel ->
  (forall i, 0 <= i < k -> bytes (a + i) <> 0) -> bytes (a + k) = 0 ->
  nul_count bytes a fuel = k.
Proof.
  induction fuel as [|fuel IH]; intros bytes a k Hk Hbefore Hnul; [simpl in Hk; lia|].
  cbn -[Z.add]. destruct (Z.eq_dec k 0) as [->|Hpos].
  - rewrite Z.add_0_r in Hnul. rewrite Hnul. reflexivity.
  - assert ((bytes a =? 0) = false) as E.
    { apply Z.eqb_neq. replace a with (a + 0) by lia. apply Hbefore. lia. }
    rewrite E. rewrite (IH bytes (a + 1) (k - 1)).
    + lia.
    + rewrite Nat2Z.inj_succ in Hk. lia.
    + intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply Hbefore. lia.
    + replace (a + 1 + (k - 1)) with (a + k) by lia. exact Hnul.
Qed.

(** An independently established first NUL determines the computed
    footprint. Invalid inputs need not compute a meaningful length. *)
Lemma terminated_string_length : forall m p k,
  terminated_length m p k -> string_length m p = k.
Proof.
  intros m p k Hlength.
  pose proof (terminated_length_readable _ _ _ Hlength) as
    (Hsize & (base & reg & Hcap & Hr & Hl) & Ha & _).
  destruct Hlength as ((_ & Hk & _ & _ & Hbytes & Hnul) & Hmax).
  assert (Hcapacity : k < string_capacity m p).
  { unfold string_capacity. unfold access_res, cap_access_res in Ha.
    destruct Hcap as [Hcap|Hcap]; rewrite Hcap in Ha |- *; rewrite Hr in Ha |- *.
    all: destruct ((base <=? ptr_addr p) && (ptr_addr p + (k + 1) <=? r_end reg)) eqn:E;
      try discriminate.
    all: apply andb_true_iff in E as [_ He]; apply Z.leb_le in He;
      rewrite Z.max_r by lia; lia. }
  unfold string_length. apply nul_count_first.
  - rewrite Z2Nat.id by lia. lia.
  - intros i Hi. specialize (Hbytes i Hi). lia.
  - apply Hnul. exact Hmax.
Qed.

(** ## Scalar string copies *)

(** Ordinary scalar stores retain destination auxiliary entries; they
    neither clear them nor import source capabilities. No rounded
    shadow footprint or base-alignment premise is needed here. *)
Definition string_copy_frame (m : mem) (d : ptr) (n : Z) (m' : mem) : Prop :=
  m_regions m' = m_regions m /\
  (forall a, m_aux m' a = m_aux m a) /\
  (forall a, ~ span_contains (mkSpan d n) a -> m_bytes m' a = m_bytes m a).

(** Snapshot bytes through NUL with the scalar-store frame. *)
Definition string_copy_result (m : mem) (d src : ptr) (n : Z) (m' : mem) : Prop :=
  string_copy_frame m d n m' /\
  forall a, span_contains (mkSpan d n) a ->
    m_bytes m' a = m_bytes m (ptr_addr src + (a - ptr_addr d)).

(** Admission is independent of the computed footprint: a terminated
    source, writable destination through NUL, and byte nonoverlap. *)
Definition string_copy_domain (m : mem) (d src : ptr) (k : Z) : Prop :=
  terminated_length m src k /\ writable_span m (mkSpan d (k + 1)) /\
  (ptr_addr d + (k + 1) <= ptr_addr src \/ ptr_addr src + (k + 1) <= ptr_addr d).

(** A logical witness, not an implementation or native termination proof. *)
Definition string_copy_memory (m : mem) (d src : ptr) (n : Z) : mem :=
  mkMem (fun a => if (ptr_addr d <=? a) && (a <? ptr_addr d + n)
    then m_bytes m (ptr_addr src + (a - ptr_addr d)) else m_bytes m a)
    (m_regions m) (m_aux m).

Lemma string_copy_memory_result : forall m d src n,
  string_copy_result m d src n (string_copy_memory m d src n).
Proof.
  intros m d src n. split.
  - split; [reflexivity|]. split; [intros; reflexivity|]. intros a Hout.
    change ((if (ptr_addr d <=? a) && (a <? ptr_addr d + n)
      then m_bytes m (ptr_addr src + (a - ptr_addr d)) else m_bytes m a) = m_bytes m a).
    destruct ((ptr_addr d <=? a) && (a <? ptr_addr d + n)) eqn:E; [|reflexivity].
    exfalso. apply Hout. apply andb_true_iff in E as [Hlo Hhi].
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi. exact (conj Hlo Hhi).
  - intros a [Hlo Hhi]. simpl in Hlo, Hhi. unfold string_copy_memory. simpl.
    assert ((ptr_addr d <=? a) && (a <? ptr_addr d + n) = true) as E.
    { apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; assumption. }
    rewrite E. reflexivity.
Qed.

(** Any specified completion has these cells, not only the witness. *)
Lemma string_copy_cells : forall m d src n m' a,
  string_copy_result m d src n m' ->
  m_bytes m' a = (if (ptr_addr d <=? a) && (a <? ptr_addr d + n)
    then m_bytes m (ptr_addr src + (a - ptr_addr d)) else m_bytes m a) /\
  m_aux m' a = m_aux m a.
Proof.
  intros m d src n m' a ((Hr & Ha & Hb) & Hcopy). split; [|apply Ha].
  destruct ((ptr_addr d <=? a) && (a <? ptr_addr d + n)) eqn:E.
  - apply Hcopy. apply andb_true_iff in E as [Hlo Hhi].
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi. exact (conj Hlo Hhi).
  - apply Hb. intros [Hlo Hhi]. simpl in Hlo, Hhi.
    apply andb_false_iff in E as [E|E]; [apply Z.leb_gt in E|apply Z.ltb_ge in E]; lia.
Qed.

(** Only ordinary destination bytes need write permission; every aux
    entry retains its old authority regardless of new numeric bits. *)
Lemma string_copy_local : forall m d src k m',
  string_copy_domain m d src k -> string_copy_result m d src (k + 1) m' ->
  local_effect [mkSpan src (k + 1); mkSpan d 0] [mkSpan d (k + 1)] [] [] m m'.
Proof.
  intros m d src k m' (_ & Hw & _) ((Hr & Ha & Hb) & Hcopy).
  split; [apply ids_same; exact Hr|]. split.
  - intros b reg Hreg. rewrite Hr in Hreg. exists reg. auto.
  - split.
    + intros a Hout. split; [|apply Ha]. apply Hb. intros Hin.
      apply Hout. left. exists (mkSpan d (k + 1)). split; [left; reflexivity|]. auto.
    + intros a. left. apply Ha.
Qed.

(** P/P to P/discarded. The length is neither a native nor a ghost argument. *)
Definition string_copy_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d P) /\ exists d src, args = [Arg P d; Arg P src].

(** Conditional contract for the selected scalar strcpy/stpcpy paths.
    Their archive and shared bodies use ordinary stores, not memcpy.
    Internal polls may rewrite freed capabilities: this exact logical
    aux frame does not establish native collector-prefix correspondence,
    wider-load adequacy, universal satisfaction or termination. *)
Definition string_copy_contract (end_return : bool) (world : Type) : contract world :=
  mkContract world (RClass P) string_copy_abi
    (fun xs m _ => exists d src k, xs = [WPtr d; WPtr src] /\ string_copy_domain m d src k)
    (fun xs m _ => match xs with [WPtr d; WPtr src] =>
      [mkSpan src (string_length m src + 1); mkSpan d 0] | _ => [] end)
    (fun xs m _ => match xs with [WPtr d; WPtr src] =>
      [mkSpan d (string_length m src + 1)] | _ => [] end)
    (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (fun xs m w born trace m' w' => born = [] /\ trace = [] /\ w' = w /\
      exists d src, xs = [WPtr d; WPtr src] /\ string_copy_frame m d (string_length m src + 1) m')
    (fun xs m w born trace ending m' w' => born = [] /\ trace = [] /\ w' = w /\
      exists d src, xs = [WPtr d; WPtr src] /\
        string_copy_result m d src (string_length m src + 1) m' /\
        ending = CallReturn [WPtr (copy_return end_return d (string_length m src))])
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; Readonly; ArgumentSize; ReturnSize]).

(** strcpy returns its original destination capability. *)
Definition strcpy_contract := string_copy_contract false.
(** stpcpy returns the destination's NUL position, not one byte after it. *)
Definition stpcpy_contract := string_copy_contract true.

(** ## Fresh string duplication *)

(** P to P/discarded: the length is not a native or ghost argument. *)
Definition strdup_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d P) /\ exists p, args = [Arg P p].

(** Conservative source-base domain for the reviewed memcpy metadata
    relation. The source address itself need not be aligned. *)
Definition strdup_domain (m : mem) (p : ptr) (k : Z) : Prop :=
  terminated_length m p k /\
  exists base, (ptr_cap p = Obj base \/ ptr_cap p = Ro base) /\ base mod 8 = 0.

(** strlen plus the NUL, computed from the original memory. *)
Definition strdup_request (xs : list word) (m : mem) (align size : Z) : Prop :=
  exists p, xs = [WPtr p] /\ align = 16 /\ size = string_length m p + 1.

(** Fresh storage first, then the reviewed snapshot copy. The malloc
    endpoint is the intermediate memory, NOT the filled result. *)
Definition strdup_result (m : mem) (p : ptr) (n base : Z) (m' : mem) : Prop :=
  malloc_result m n base (allocated m (heap_req 16 n) base) /\
  copy_result (allocated m (heap_req 16 n) base) (mkPtr base (Obj base)) p n m'.

(** Prefixes preserve old objects and restrict writes to the fresh
    destination. As for malloc, terminal OOM can abandon one allocation. *)
Definition strdup_prefix (m : mem) (p : ptr) (n : Z) (born : list Z) (m' : mem) : Prop :=
  (born = [] /\ m' = m) \/ exists base, born = [base] /\
    malloc_result m n base (allocated m (heap_req 16 n) base) /\
    memset_frame (allocated m (heap_req 16 n) base) (mkPtr base (Obj base)) n m'.

(** Trusted strdup for the selected strlen/malloc/memcpy path. No old
    write root or release, no NULL or exit, and exact source metadata
    only for full in-phase words. Auxiliary allocation, native boxing
    and collector-prefix coverage retain the copying qualifications. *)
Definition strdup_contract (world : Type) : contract world :=
  mkContract world (RClass P) strdup_abi
    (fun xs m _ => exists p k, xs = [WPtr p] /\ strdup_domain m p k)
    (fun xs m _ => match xs with [WPtr p] => [mkSpan p (string_length m p + 1)] | _ => [] end)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun xs m _ => strdup_request xs m)
    (fun xs m w born trace m' w' => trace = [] /\ w' = w /\ exists p,
      xs = [WPtr p] /\ strdup_prefix m p (string_length m p + 1) born m')
    (fun xs m w born trace ending m' w' => trace = [] /\ w' = w /\ exists p base,
      xs = [WPtr p] /\ born = [base] /\ strdup_result m p (string_length m p + 1) base m' /\
      ending = CallReturn [WPtr (mkPtr base (Obj base))])
    resource_reason (fun why => In why [NullCapability; OutOfBounds; ArgumentSize; ReturnSize]).

(** Fresh allocation preserves every previously readable byte span. *)
Lemma readable_bytes_allocated : forall m q base p n,
  object_region base (m_regions m) = None -> readable_bytes m p n ->
  readable_bytes (allocated m q base) p n.
Proof.
  intros m q base p n Hnew (Hn & (b & reg & Hcap & Hr & Hl) & Ha & Hbytes).
  split; [exact Hn|]. split.
  - exists b, reg. split; [exact Hcap|]. split; [eapply allocated_old_region; eauto|exact Hl].
  - split; [eapply allocated_old_access; eauto|exact Hbytes].
Qed.

(** A 16-aligned fresh base is also a globally aligned aux-slot start. *)
Lemma fresh_heap_aligned8 : forall m n base,
  fresh m (heap_req 16 n) base -> base mod 8 = 0.
Proof.
  intros m n base (_ & Ha & _). change (base mod 16 = 0) in Ha.
  apply Z.mod_divide in Ha; [|lia]. destruct Ha as [k ->].
  replace (k * 16) with ((k * 2) * 8) by ring. apply Z.mod_mul. lia.
Qed.

(** All changed cells, including shadow slot starts, are within the
    fresh object; no caller write root is needed. Imported capabilities
    still require complete readable original-source slots. *)
Lemma strdup_result_local : forall m p n base m',
  0 < n -> readable_bytes m p n -> strdup_result m p n base m' ->
  local_effect [mkSpan p n] [] [] [base] (allocated m (heap_req 16 n) base) m'.
Proof.
  intros m p n base m' Hpos Hread ((Hlegal & Hfresh & _) & ((Hr & Hb & Ha) & Hbytes & Hslots)).
  pose proof (fresh_heap_aligned8 _ _ _ Hfresh) as Halign.
  destruct Hfresh as (Hbase & Hmod & Hbound & Hnew & Hsep & Hzero).
  pose proof (malloc_extent n ltac:(lia)) as Hextent.
  pose proof (readable_bytes_allocated m (heap_req 16 n) base p n Hnew Hread) as Hread'.
  assert (Hwrite : forall a, base <= a < base + n ->
    write_authority [] [base] (allocated m (heap_req 16 n) base) a).
  { intros a Hin. right. exists base, (mkRegion base (base + req_extent (heap_req 16 n)) Heap Live).
    split; [left; reflexivity|]. split; [simpl; rewrite Z.eqb_refl; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    change (base <= a < base + req_extent (heap_req 16 n)). lia. }
  assert (Htouched : forall a, memset_touched (mkPtr base (Obj base)) n a = true -> base <= a < base + n).
  { intros a H. apply memset_aux_in_root in H. unfold memset_root, span_contains in H.
    assert ((n =? 0) = false) as E by (apply Z.eqb_neq; lia).
    rewrite E in H. simpl in H. rewrite Halign in H. lia. }
  split; [apply ids_same; exact Hr|]. split.
  - intros b reg Hreg. rewrite Hr in Hreg. exists reg. auto.
  - split.
    + intros a Hout. split.
      * apply Hb. intros Hin. apply Hout, Hwrite. exact Hin.
      * apply Ha. destruct (memset_touched (mkPtr base (Obj base)) n a) eqn:E; [|reflexivity].
        exfalso. apply Hout, Hwrite, Htouched. exact E.
    + intros a. destruct (memset_touched (mkPtr base (Obj base)) n a) eqn:E.
      * right. rewrite (Hslots a E). unfold copy_slot.
        destruct (copy_full_slot (mkPtr base (Obj base)) p n a) eqn:Hfull; [|left; reflexivity].
        unfold copy_full_slot in Hfull. repeat rewrite andb_true_iff in Hfull.
        destruct Hfull as [[Hlo Hhi] Hphase]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
        apply Z.eqb_eq in Hphase. right; right; left.
        exists (mkSpan p n), (ptr_addr p + (a - base)).
        split; [left; reflexivity|]. split; [unfold span_contains; simpl in *; lia|].
        split; [simpl in *; lia|]. split; [|reflexivity].
        apply (readable_bytes_slot _ _ n); simpl in *; try assumption; lia.
      * left. apply Ha. exact E.
Qed.

(** Every accepted duplication prefix frames the caller's objects,
    including source bytes and stored capabilities, even on refusal. *)
Lemma strdup_prefix_old : forall m p n born m',
  0 < n -> strdup_prefix m p n born m' ->
  (forall b reg, object_region b (m_regions m) = Some reg ->
    object_region b (m_regions m') = Some reg) /\
  (forall a, in_object m a -> m_bytes m' a = m_bytes m a /\ m_aux m' a = m_aux m a).
Proof.
  intros m p n born m' Hpos [(_ & ->)|(base & _ & (Hlegal & Hfresh & _) & Hr & Hb & Ha)].
  - auto.
  - pose proof (fresh_heap_aligned8 _ _ _ Hfresh) as Halign.
    destruct Hfresh as (_ & _ & _ & Hnew & Hsep & _).
    pose proof (malloc_extent n ltac:(lia)) as Hextent. split.
    + intros b reg Hreg. rewrite Hr. eapply allocated_old_region; eauto.
    + intros a (b & reg & Hreg & Hin).
      assert (Hout : ~ (base <= a < base + n)).
      { intros Hboth. apply (Hsep b reg Hreg). split; lia. }
      split.
      * apply Hb. exact Hout.
      * apply Ha. destruct (memset_touched (mkPtr base (Obj base)) n a) eqn:E; [|reflexivity].
        exfalso. apply Hout. apply memset_aux_in_root in E.
        unfold memset_root, span_contains in E.
        assert ((n =? 0) = false) as En by (apply Z.eqb_neq; lia).
        rewrite En in E. simpl in E. rewrite Halign in E. lia.
Qed.

(** ## Memory paths over any runtime *)

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

(** Independent representation and cell admission construct a real call
    in the logical relation; this is not a native termination theorem. *)
Theorem errno_location_return : forall world cell rep r args s m (w : world),
  errno_location_abi r args -> rep m w -> errno_cell m (cell w) ->
  invoke (errno_location_contract world cell rep) r args [] s m w
    [] (CallReturn [WPtr (cell w)]) s m w.
Proof.
  intros world cell rep r args s m w Habi Hrep Hcell.
  eapply invoke_normal with (born := []).
  - exact Habi.
  - split; [reflexivity|]. auto.
  - split; [constructor|]. repeat split; reflexivity.
  - repeat split; reflexivity.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WPtr (cell w)). split; reflexivity.
    + constructor; [|constructor]. right. left.
      exists (mkSpan (cell w) 0). split; [left; reflexivity|reflexivity].
  - intros status Hbad. discriminate.
Qed.

(** Every endpoint returns the exact represented cell with its original
    capability. All memory, runtime and world state remain unchanged. *)
Theorem errno_location_invocation : forall world cell rep r args xs s m (w : world)
    trace ending s' m' w',
  invoke (errno_location_contract world cell rep) r args xs s m w
    trace ending s' m' w' ->
  errno_location_abi r args /\ xs = [] /\ rep m w /\ errno_cell m (cell w) /\
  trace = [] /\ s' = s /\ m' = m /\ w' = w /\ ending = CallReturn [WPtr (cell w)].
Proof.
  intros world cell rep r args xs s m w trace ending s' m' w' Hcall.
  inversion Hcall; subst.
  - match goal with
    | Habi : contract_abi _ _ _, Hpre : contract_pre _ _ _ _,
      Hp : prefix _ _ _ _ _ _ _ _ _ _, Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpre as (Hxs & Hrep & Hcell);
      destruct Hpost as (Hb & Htrace & Hmem & Hworld & Hend);
      destruct Hp as [He _];
      assert (Hs : s' = s) by (clear -He; induction He; [reflexivity|exact IHHe|contradiction]);
      exact (conj Habi (conj Hxs (conj Hrep (conj Hcell
        (conj Htrace (conj Hs (conj Hmem (conj Hworld Hend))))))))
    end.
  - contradiction.
Qed.

(** Every admitted scan has a permitted normal invocation via the
    reflexive effect path. This proves nonvacuity, not native termination. *)
Theorem strnlen_return : forall world r args p n k s m (w : world),
  strnlen_abi r args -> bounded_length m p n k ->
  invoke (strnlen_contract world) r args [WPtr p; WInt n] s m w
    [] (CallReturn [WInt k]) s m w.
Proof.
  intros world r args p n k s m w Habi Hlength.
  eapply invoke_normal with (born := []).
  - exact Habi.
  - exists p, n, k. auto.
  - split; [constructor|]. repeat split; reflexivity.
  - repeat split; try reflexivity. exists p, n, k. auto.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WInt k). split; [reflexivity|]. simpl.
      rewrite Z.mod_small; [reflexivity|destruct Hlength as [Hn [Hk _]]; lia].
    + constructor; [exact I|constructor].
  - intros status Hbad. discriminate.
Qed.

(** Every represented completion is the pure bounded result. There is
    no resource or exit ending; malformed arguments get no invocation. *)
Theorem strnlen_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (strnlen_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ m' = m /\ w' = w /\
  exists p n k, xs = [WPtr p; WInt n] /\ bounded_length m p n k /\ ending = CallReturn [WInt k].
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpost as (_ & Htrace & Hmem & Hworld & Hresult); auto end.
  - contradiction.
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

(** Input-only string authority constructs an actual pure invocation.
    This is specification nonvacuity, not native execution or termination. *)
Theorem strlen_return : forall world r args p k s m (w : world),
  strlen_abi r args -> terminated_length m p k ->
  invoke (strlen_contract world) r args [WPtr p] s m w
    [] (CallReturn [WInt k]) s m w.
Proof.
  intros world r args p k s m w Habi Hlength.
  eapply invoke_normal with (born := []).
  - exact Habi.
  - exists p, k. auto.
  - split; [constructor|]. repeat split; reflexivity.
  - repeat split; try reflexivity. exists p, k. auto.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WInt k). split; [reflexivity|]. simpl.
      rewrite Z.mod_small; [reflexivity|destruct Hlength as [(_ & Hk & _) Hmax]; lia].
    + constructor; [exact I|constructor].
  - intros status Hbad. discriminate.
Qed.

(** Every represented completion returns the original string's exact
    length, with empty observations and unchanged memory and world.
    There is no resource or process-exit alternative. *)
Theorem strlen_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (strlen_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ m' = m /\ w' = w /\
  exists p k, xs = [WPtr p] /\ terminated_length m p k /\ ending = CallReturn [WInt k].
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpost as (_ & Htrace & Hmem & Hworld & Hresult); auto end.
  - contradiction.
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

(** Any specified first match or miss has a permitted pure invocation. *)
Theorem memchr_return : forall world r args p c n q s m (w : world),
  memchr_abi r args -> memchr_input m p c n -> memchr_result m p c n q ->
  invoke (memchr_contract world) r args [WPtr p; WInt c; WInt n] s m w
    [] (CallReturn [WPtr q]) s m w.
Proof.
  intros world r args p c n q s m w Habi Hinput Hresult.
  eapply invoke_normal with (born := []).
  - exact Habi.
  - exists p, c, n. auto.
  - split; [constructor|]. repeat split; reflexivity.
  - repeat split; try reflexivity. exists p, c, n, q. auto.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WPtr q). split; reflexivity.
    + constructor; [apply memchr_result_authority with (c := c); exact Hresult|constructor].
  - intros status Hbad. discriminate.
Qed.

(** Every admitted input has some permitted result, without requiring
    a returned-pointer witness in its precondition. Not native termination. *)
Theorem memchr_admitted : forall world r args p c n s m (w : world),
  memchr_abi r args -> memchr_input m p c n ->
  exists q, invoke (memchr_contract world) r args [WPtr p; WInt c; WInt n] s m w
    [] (CallReturn [WPtr q]) s m w.
Proof.
  intros world r args p c n s m w Habi Hinput.
  destruct (memchr_input_result _ _ _ _ Hinput) as [q Hq].
  exists q. apply memchr_return; assumption.
Qed.

(** Every represented completion is pure and returns exactly the first
    matching pointer with its source capability, or null on a miss. *)
Theorem memchr_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (memchr_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ m' = m /\ w' = w /\
  exists p c n q, xs = [WPtr p; WInt c; WInt n] /\ memchr_result m p c n q /\
    ending = CallReturn [WPtr q].
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpost as (_ & Htrace & Hmem & Hworld & Hresult); auto end.
  - contradiction.
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

(** Runtime readiness bounds the consumed prefix, NOT the maximum count.
    A first-byte hit with SIZE_MAX need not authorize p + SIZE_MAX. *)
Lemma memchr_input_extent : forall s m p c n,
  R.ready s m -> memchr_input m p c n ->
  exists k, 0 <= k <= n /\
    0 <= ptr_addr p /\ ptr_addr p + k + (if k <? n then 1 else 0) <= 2 ^ 48.
Proof.
  intros s m p c n Hr (_ & _ & k & Hk & Hread & _).
  exists k. split; [exact Hk|].
  pose proof (readable_bytes_extent _ _ _ _ Hr Hread). lia.
Qed.

(** Every legal signed magnitude has a permitted pure invocation, not
    only the three witnesses used in [memcmp_result_total]. *)
Theorem memcmp_return : forall world r args p q n bits s m (w : world),
  memcmp_abi r args -> readable_bytes m p n -> readable_bytes m q n ->
  memcmp_result m p q n bits ->
  invoke (memcmp_contract world) r args [WPtr p; WPtr q; WInt n] s m w
    [] (CallReturn [WInt bits]) s m w.
Proof.
  intros world r args p q n bits s m w Habi Hp Hq Hresult.
  eapply invoke_normal with (born := []).
  - exact Habi.
  - exists p, q, n. auto.
  - split; [constructor|]. repeat split; reflexivity.
  - repeat split; try reflexivity. exists p, q, n, bits. auto.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WInt bits). split; [reflexivity|]. simpl.
      rewrite Z.mod_small; [reflexivity|exact (proj1 Hresult)].
    + constructor; [exact I|constructor].
  - intros status Hbad. discriminate.
Qed.

(** Independently readable arguments admit some permitted result;
    invocation existence is a conclusion, not an admission premise. *)
Theorem memcmp_admitted : forall world r args p q n s m (w : world),
  memcmp_abi r args -> readable_bytes m p n -> readable_bytes m q n ->
  exists bits, invoke (memcmp_contract world) r args [WPtr p; WPtr q; WInt n] s m w
    [] (CallReturn [WInt bits]) s m w.
Proof.
  intros world r args p q n s m w Habi Hp Hq.
  destruct (memcmp_result_total m p q n ltac:(destruct Hp as [Hn _]; lia)) as [bits Hbits].
  exists bits. apply memcmp_return; assumption.
Qed.

(** Every represented completion is pure with the specified signed
    byte-order result. Resource and process-exit endings are excluded. *)
Theorem memcmp_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (memcmp_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ m' = m /\ w' = w /\
  exists p q n bits, xs = [WPtr p; WPtr q; WInt n] /\ memcmp_result m p q n bits /\
    ending = CallReturn [WInt bits].
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpost as (_ & Htrace & Hmem & Hworld & Hresult); auto end.
  - contradiction.
Qed.

(** Any legal strncmp result admits a pure invocation. Its result
    predicate already includes the two independent input witnesses. *)
Theorem strncmp_return : forall world r args p q n bits s m (w : world),
  memcmp_abi r args -> strncmp_result m p q n bits ->
  invoke (strncmp_contract world) r args [WPtr p; WPtr q; WInt n] s m w
    [] (CallReturn [WInt bits]) s m w.
Proof.
  intros world r args p q n bits s m w Habi Hresult.
  destruct Hresult as (left & right & Hl & Hr & Hbits).
  eapply invoke_normal with (born := []).
  - exact Habi.
  - exists p, q, n, left, right. auto.
  - split; [constructor|]. repeat split; reflexivity.
  - repeat split; try reflexivity. exists p, q, n, bits. split; [reflexivity|].
    split; [exists left, right; auto|reflexivity].
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WInt bits). split; [reflexivity|]. simpl.
      rewrite Z.mod_small; [reflexivity|exact (proj1 Hbits)].
    + constructor; [exact I|constructor].
  - intros status Hbad. discriminate.
Qed.

(** Input-only premises construct a permitted return; this is trusted
    specification nonvacuity, not a native termination theorem. *)
Theorem strncmp_admitted : forall world r args p q n left right s m (w : world),
  memcmp_abi r args -> bounded_length m p n left -> bounded_length m q n right ->
  exists bits, invoke (strncmp_contract world) r args [WPtr p; WPtr q; WInt n] s m w
    [] (CallReturn [WInt bits]) s m w.
Proof.
  intros world r args p q n left right s m w Habi Hl Hr.
  destruct (strncmp_result_total m p q n left right Hl Hr) as [bits Hbits].
  exists bits. apply strncmp_return; assumption.
Qed.

(** Every represented completion has the signed string-order result
    and exact unchanged endpoint, with no resource or exit alternative. *)
Theorem strncmp_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (strncmp_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ m' = m /\ w' = w /\
  exists p q n bits, xs = [WPtr p; WPtr q; WInt n] /\ strncmp_result m p q n bits /\
    ending = CallReturn [WInt bits].
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpost as (_ & Htrace & Hmem & Hworld & Hresult); auto end.
  - contradiction.
Qed.

(** Every legal sign and magnitude constructs a pure strcmp invocation.
    The result predicate already contains independent input authority. *)
Theorem strcmp_return : forall world r args p q bits s m (w : world),
  strcmp_abi r args -> strcmp_result m p q bits ->
  invoke (strcmp_contract world) r args [WPtr p; WPtr q] s m w
    [] (CallReturn [WInt bits]) s m w.
Proof.
  intros world r args p q bits s m w Habi (left & right & Hl & Hr & Hbits).
  eapply invoke_normal with (born := []).
  - exact Habi.
  - exists p, q, left, right. auto.
  - split; [constructor|]. repeat split; reflexivity.
  - repeat split; try reflexivity. exists p, q, bits. split; [reflexivity|].
    split; [exists left, right; auto|reflexivity].
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WInt bits). split; [reflexivity|]. simpl.
      rewrite Z.mod_small; [reflexivity|exact (proj1 Hbits)].
    + constructor; [exact I|constructor].
  - intros status Hbad. discriminate.
Qed.

(** Independent terminated inputs suffice for some permitted return.
    This is logical nonvacuity, not a native termination theorem. *)
Theorem strcmp_admitted : forall world r args p q left right s m (w : world),
  strcmp_abi r args -> terminated_length m p left -> terminated_length m q right ->
  exists bits, invoke (strcmp_contract world) r args [WPtr p; WPtr q] s m w
    [] (CallReturn [WInt bits]) s m w.
Proof.
  intros world r args p q left right s m w Habi Hl Hr.
  destruct (strcmp_result_total m p q left right Hl Hr) as [bits Hbits].
  exists bits. apply strcmp_return; assumption.
Qed.

(** Every represented strcmp completion returns its original-memory
    string-order result, with empty observations and unchanged memory/world.
    No resource or process-exit completion is admitted. *)
Theorem strcmp_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (strcmp_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ m' = m /\ w' = w /\
  exists p q bits, xs = [WPtr p; WPtr q] /\ strcmp_result m p q bits /\
    ending = CallReturn [WInt bits].
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpost as (_ & Htrace & Hmem & Hworld & Hresult); auto end.
  - contradiction.
Qed.

(** A specified first match or miss constructs a pure pointer return
    from the independent ABI and canonical-int admission obligations. *)
Theorem strchr_return : forall world r args p c q s m (w : world),
  strchr_abi r args -> 0 <= c < 2 ^ 32 -> strchr_result m p c q ->
  invoke (strchr_contract world) r args [WPtr p; WInt c] s m w
    [] (CallReturn [WPtr q]) s m w.
Proof.
  intros world r args p c q s m w Habi Hc Hresult.
  destruct Hresult as (k & Hlength & Hq).
  eapply invoke_normal with (born := []).
  - exact Habi.
  - exists p, c, k. auto.
  - split; [constructor|]. repeat split; reflexivity.
  - repeat split; try reflexivity. exists p, c, q. split; [reflexivity|].
    split; [exact Hc|]. split; [exists k; auto|reflexivity].
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WPtr q). split; reflexivity.
    + constructor.
      * apply (strchr_result_authority m p c q). exists k. auto.
      * constructor.
  - intros status Hbad. discriminate.
Qed.

(** Canonical int and terminated-string inputs suffice for some actual
    permitted invocation; native coverage and termination remain trusted. *)
Theorem strchr_admitted : forall world r args p c k s m (w : world),
  strchr_abi r args -> 0 <= c < 2 ^ 32 -> terminated_length m p k ->
  exists q, invoke (strchr_contract world) r args [WPtr p; WInt c] s m w
    [] (CallReturn [WPtr q]) s m w.
Proof.
  intros world r args p c k s m w Habi Hc Hlength.
  destruct (strchr_result_total m p c k Hlength) as [q Hq].
  exists q. apply strchr_return; assumption.
Qed.

(** Every represented completion is a first-match pointer or null in
    the original memory, with canonical int admission, empty observations,
    unchanged memory/world, and no resource or process-exit ending. *)
Theorem strchr_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (strchr_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ m' = m /\ w' = w /\
  exists p c q, xs = [WPtr p; WInt c] /\ 0 <= c < 2 ^ 32 /\ strchr_result m p c q /\
    ending = CallReturn [WPtr q].
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpost as (_ & Htrace & Hmem & Hworld & Hresult); auto end.
  - contradiction.
Qed.

(** ABI, canonical int and a specified last match or miss suffice for
    an actual pure invocation, with no borrowed auxiliary authority. *)
Theorem strrchr_return : forall world r args p c q s m (w : world),
  strchr_abi r args -> 0 <= c < 2 ^ 32 -> strrchr_result m p c q ->
  invoke (strrchr_contract world) r args [WPtr p; WInt c] s m w
    [] (CallReturn [WPtr q]) s m w.
Proof.
  intros world r args p c q s m w Habi Hc Hresult.
  destruct Hresult as (k & Hlength & Hq).
  eapply invoke_normal with (born := []).
  - exact Habi.
  - exists p, c, k. auto.
  - split; [constructor|]. repeat split; reflexivity.
  - repeat split; try reflexivity. exists p, c, q. split; [reflexivity|].
    split; [exact Hc|]. split; [exists k; auto|reflexivity].
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WPtr q). split; reflexivity.
    + constructor.
      * apply (strrchr_result_authority m p c q). exists k. auto.
      * constructor.
  - intros status Hbad. discriminate.
Qed.

(** Independent input authority constructs some last-match invocation,
    without a native executor, coverage or termination assumption. *)
Theorem strrchr_admitted : forall world r args p c k s m (w : world),
  strchr_abi r args -> 0 <= c < 2 ^ 32 -> terminated_length m p k ->
  exists q, invoke (strrchr_contract world) r args [WPtr p; WInt c] s m w
    [] (CallReturn [WPtr q]) s m w.
Proof.
  intros world r args p c k s m w Habi Hc Hlength.
  destruct (strrchr_result_total m p c k Hlength) as [q Hq].
  exists q. apply strrchr_return; assumption.
Qed.

(** Every completion returns a last match or canonical null from the
    original memory, retaining canonical int admission, exact memory/world
    preservation, empty observations and no resource or exit ending. *)
Theorem strrchr_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (strrchr_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ m' = m /\ w' = w /\
  exists p c q, xs = [WPtr p; WInt c] /\ 0 <= c < 2 ^ 32 /\ strrchr_result m p c q /\
    ending = CallReturn [WPtr q].
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpost as (_ & Htrace & Hmem & Hworld & Hresult); auto end.
  - contradiction.
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

(** A successful runtime answer constructs an actual malloc call;
    readiness supplies freshness, rather than assuming it of callers. *)
Theorem malloc_return : forall world r args n s m (w : world) base s',
  malloc_abi r args -> 0 <= n < 2 ^ 64 -> n <= max_allocation_size ->
  R.ready s m -> R.alloc s (heap_req 16 n) = Some (base, s') ->
  invoke (malloc_contract world) r args [WInt n] s m w []
    (CallReturn [WPtr (mkPtr base (Obj base))]) s' (allocated m (heap_req 16 n) base) w.
Proof.
  intros world r args n s m w base s' Habi Hn Hsize Hr Ha.
  destruct (R.fresh_allocation s m (heap_req 16 n) base s' Hr ltac:(simpl; lia)
    ltac:(pose proof (malloc_extent n ltac:(lia)); lia) Ha) as [Hfresh _].
  assert (Hresult : malloc_result m n base (allocated m (heap_req 16 n) base))
    by (split; [lia|]; auto).
  eapply invoke_normal with (born := [base]).
  - exact Habi.
  - exists n. auto.
  - split.
    + eapply effects_alloc; [exists n; auto|lia|exact Ha|constructor].
    + split; [reflexivity|]. split; [reflexivity|]. exists n. split; [reflexivity|].
      right. exists base. auto.
  - split; [reflexivity|]. split; [reflexivity|]. exists n, base. auto.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + eexists. split; reflexivity.
    + constructor; [|constructor]. right; right; right. exists base. simpl. auto.
  - intros status Hbad. discriminate.
Qed.

(** Refusal can be observed with no successful allocation at all. *)
Theorem malloc_refused : forall world r args n s m (w : world) why,
  malloc_abi r args -> 0 <= n < 2 ^ 64 ->
  resource_failure (malloc_request [WInt n]) s why ->
  invoke (malloc_contract world) r args [WInt n] s m w [] (CallResource why) s m w.
Proof.
  intros world r args n s m w why Habi Hn Hfail.
  eapply invoke_resource with (born := []).
  - exact Habi.
  - exists n. auto.
  - split; [constructor|]. split; [reflexivity|]. split; [reflexivity|].
    exists n. split; [reflexivity|]. left. auto.
  - exact Hfail.
  - change (resource_reason why). destruct Hfail; unfold resource_reason; auto.
Qed.

(** Input-only nonvacuity: a ready runtime either grants the sole
    request shape, refuses it, or rejects the original size as TooBig. *)
Theorem malloc_admitted : forall world r args n s m (w : world),
  malloc_abi r args -> 0 <= n < 2 ^ 64 -> R.ready s m ->
  exists ending s' m', invoke (malloc_contract world) r args [WInt n] s m w
    [] ending s' m' w.
Proof.
  intros world r args n s m w Habi Hn Hr.
  destruct (Z_le_dec n max_allocation_size) as [Hsize|Hbig].
  - destruct (R.alloc s (heap_req 16 n)) as [[base s']|] eqn:Ha.
    + do 3 eexists. eapply malloc_return; eauto.
    + exists (CallResource OutOfMemory), s, m. apply malloc_refused; auto.
      eapply failure_oom; [exists n; auto|lia|exact Ha].
  - exists (CallResource TooBig), s, m. apply malloc_refused; auto.
    eapply failure_big; [exists n; auto|lia].
Qed.

(** Public inversion retains the exact success endpoint or the
    documented terminal-resource prefix, with refusal in its final
    runtime state. There is no NULL return and no exit outcome. *)
Theorem malloc_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (malloc_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ w' = w /\ exists n, xs = [WInt n] /\ 0 <= n < 2 ^ 64 /\
    ((exists base, malloc_result m n base m' /\
       ending = CallReturn [WPtr (mkPtr base (Obj base))]) \/
     (exists why born, ending = CallResource why /\ malloc_prefix m n born m' /\
       resource_failure (malloc_request [WInt n]) s' why)).
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with
    | Hpre : contract_pre _ _ _ _, Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpre as (n & Hxs & Hn);
      destruct Hpost as (Ht & Hw & size & base & Hxs' & Hb & Hresult & Hend)
    end.
    rewrite Hxs in Hxs'. injection Hxs' as <-.
    split; [exact Ht|]. split; [exact Hw|]. exists n. split; [exact Hxs|].
    split; [exact Hn|]. left. exists base. auto.
  - match goal with
    | Hpre : contract_pre _ _ _ _, Hp : prefix _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpre as (n & Hxs & Hn);
      destruct Hp as (_ & Ht & Hw & size & Hxs' & Hprefix)
    end.
    rewrite Hxs in Hxs'. injection Hxs' as <-.
    split; [exact Ht|]. split; [exact Hw|]. exists n. split; [exact Hxs|].
    split; [exact Hn|]. right. do 2 eexists. split; [reflexivity|].
    split; [exact Hprefix|]. subst xs. assumption.
Qed.

(** Oversize refusal cannot follow the successful prefix: legal-size
    admission of that prefix makes this distinction provable. *)
Theorem malloc_too_big_unchanged : forall world r args n s m (w : world) trace s' m' w',
  invoke (malloc_contract world) r args [WInt n] s m w trace (CallResource TooBig) s' m' w' ->
  max_allocation_size < n /\ m' = m.
Proof.
  intros world r args n s m w trace s' m' w' Hcall.
  destruct (malloc_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & size & Hargs & _ & [(base & _ & Hend)|(why & born & Hend & Hp & Hf)]).
  - discriminate Hend.
  - injection Hargs as <-. injection Hend as <-. inversion Hf; subst.
    match goal with Hreq : malloc_request _ _ _ |- _ =>
      destruct Hreq as (k & Hargs & _ & Hsize); injection Hargs as <-; subst
    end.
    split; [assumption|]. destruct Hp as [(_ & ->)|(base & _ & (Hlegal & _))]; [reflexivity|lia].
Qed.

(** Successful allocation followed by any specified snapshot produces
    an actual strdup invocation. Source length is proved from inputs. *)
Theorem strdup_return : forall world r args p k s m (w : world) base s' m',
  strdup_abi r args -> strdup_domain m p k -> k + 1 <= max_allocation_size ->
  R.ready s m -> R.alloc s (heap_req 16 (k + 1)) = Some (base, s') ->
  copy_result (allocated m (heap_req 16 (k + 1)) base)
    (mkPtr base (Obj base)) p (k + 1) m' ->
  invoke (strdup_contract world) r args [WPtr p] s m w []
    (CallReturn [WPtr (mkPtr base (Obj base))]) s' m' w.
Proof.
  intros world r args p k s m w base s' m' Habi Hdomain Hsize Hr Ha Hcopy.
  pose proof (terminated_string_length _ _ _ (proj1 Hdomain)) as Hlen.
  pose proof (terminated_length_readable _ _ _ (proj1 Hdomain)) as Hread.
  destruct (proj1 Hdomain) as ((_ & Hk & _) & Hmax).
  destruct (R.fresh_allocation s m (heap_req 16 (k + 1)) base s' Hr ltac:(simpl; lia)
    ltac:(pose proof (malloc_extent (k + 1) ltac:(lia)); lia) Ha) as [Hfresh _].
  assert (Hresult : strdup_result m p (k + 1) base m').
  { split; [split; [lia|]; auto|exact Hcopy]. }
  eapply invoke_normal with (born := [base]).
  - exact Habi.
  - exists p, k. auto.
  - split.
    + change (effects [mkSpan p (string_length m p + 1)] [] [] (strdup_request [WPtr p] m)
        s m [] s' m' [base]). rewrite Hlen.
      eapply effects_alloc with (align := 16) (size := k + 1).
      * exists p. split; [reflexivity|]. split; [reflexivity|]. rewrite Hlen. reflexivity.
      * lia.
      * exact Ha.
      * eapply effects_local; [eapply strdup_result_local; eauto; lia|constructor].
    + split; [reflexivity|]. split; [reflexivity|]. exists p. split; [reflexivity|].
      rewrite Hlen. right. exists base. split; [reflexivity|].
      split; [exact (proj1 Hresult)|exact (proj1 Hcopy)].
  - split; [reflexivity|]. split; [reflexivity|]. exists p, base.
    split; [reflexivity|]. split; [reflexivity|]. rewrite Hlen. auto.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + eexists. split; reflexivity.
    + constructor; [|constructor]. right; right; right. exists base. simpl. auto.
  - intros status Hbad. discriminate.
Qed.

(** Allocation refusal is an actual unchanged prefix, not NULL. *)
Theorem strdup_refused : forall world r args p k s m (w : world) why,
  strdup_abi r args -> strdup_domain m p k ->
  resource_failure (strdup_request [WPtr p] m) s why ->
  invoke (strdup_contract world) r args [WPtr p] s m w [] (CallResource why) s m w.
Proof.
  intros world r args p k s m w why Habi Hdomain Hfail.
  eapply invoke_resource with (born := []).
  - exact Habi.
  - exists p, k. auto.
  - split; [constructor|]. split; [reflexivity|]. split; [reflexivity|].
    exists p. split; [reflexivity|]. left. auto.
  - exact Hfail.
  - change (resource_reason why). destruct Hfail; unfold resource_reason; auto.
Qed.

(** Every independently admitted string has a modeled success or
    resource invocation, even when the runtime refuses to allocate. *)
Theorem strdup_admitted : forall world r args p k s m (w : world),
  strdup_abi r args -> strdup_domain m p k -> R.ready s m ->
  exists ending s' m', invoke (strdup_contract world) r args [WPtr p] s m w
    [] ending s' m' w.
Proof.
  intros world r args p k s m w Habi Hdomain Hr.
  pose proof (terminated_string_length _ _ _ (proj1 Hdomain)) as Hlen.
  destruct (proj1 Hdomain) as ((_ & Hk & _) & Hmax).
  destruct (Z_le_dec (k + 1) max_allocation_size) as [Hsize|Hbig].
  - destruct (R.alloc s (heap_req 16 (k + 1))) as [[base s']|] eqn:Ha.
    + do 3 eexists. eapply strdup_return; eauto. apply copy_memory_result.
    + exists (CallResource OutOfMemory), s, m. eapply strdup_refused; eauto.
      eapply failure_oom with (align := 16) (size := k + 1).
      * exists p. split; [reflexivity|]. split; [reflexivity|]. rewrite Hlen. reflexivity.
      * lia.
      * exact Ha.
  - exists (CallResource TooBig), s, m. eapply strdup_refused; eauto.
    eapply failure_big with (align := 16) (size := k + 1).
    + exists p. split; [reflexivity|]. split; [reflexivity|]. rewrite Hlen. reflexivity.
    + lia.
Qed.

(** Extract the independent string witness, exact fresh result, or
    terminal-resource prefix. The computed span equals k+1 for this
    witness, so one fixed contract handles different lengths. *)
Theorem strdup_invocation : forall world r args xs s m (w : world) trace ending s' m' w',
  invoke (strdup_contract world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ w' = w /\ exists p k, xs = [WPtr p] /\ strdup_domain m p k /\
    ((exists base, strdup_result m p (k + 1) base m' /\
       ending = CallReturn [WPtr (mkPtr base (Obj base))]) \/
     (exists why born, ending = CallResource why /\ strdup_prefix m p (k + 1) born m' /\
       resource_failure (strdup_request [WPtr p] m) s' why)).
Proof.
  intros world r args xs s m w trace ending s' m' w' Hcall. inversion Hcall; subst.
  - match goal with
    | Hpre : contract_pre _ _ _ _, Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpre as (p & k & Hxs & Hd);
      destruct Hpost as (Ht & Hw & q & base & Hxs' & Hb & Hr & Hend)
    end.
    rewrite Hxs in Hxs'. injection Hxs' as <-.
    pose proof (terminated_string_length _ _ _ (proj1 Hd)) as Hlen. rewrite Hlen in Hr.
    split; [exact Ht|]. split; [exact Hw|]. exists p, k.
    split; [exact Hxs|]. split; [exact Hd|]. left. exists base. auto.
  - match goal with
    | Hpre : contract_pre _ _ _ _, Hp : prefix _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct Hpre as (p & k & Hxs & Hd);
      destruct Hp as (_ & Ht & Hw & q & Hxs' & Hprefix)
    end.
    rewrite Hxs in Hxs'. injection Hxs' as <-.
    pose proof (terminated_string_length _ _ _ (proj1 Hd)) as Hlen. rewrite Hlen in Hprefix.
    split; [exact Ht|]. split; [exact Hw|]. exists p, k.
    split; [exact Hxs|]. split; [exact Hd|]. right. do 2 eexists.
    split; [reflexivity|]. split; [exact Hprefix|]. subst xs. assumption.
Qed.

(** Any specified scalar copy constructs an actual invocation from
    independently admitted inputs. The computed footprint equals k+1. *)
Theorem string_copy_completed : forall end_return world r args d src k s m m' (w : world),
  string_copy_abi r args -> string_copy_domain m d src k ->
  string_copy_result m d src (k + 1) m' ->
  invoke (string_copy_contract end_return world) r args [WPtr d; WPtr src] s m w
    [] (CallReturn [WPtr (copy_return end_return d k)]) s m' w.
Proof.
  intros end_return world r args d src k s m m' w Habi Hdomain Hresult.
  pose proof (terminated_string_length _ _ _ (proj1 Hdomain)) as Hlen.
  eapply invoke_normal with (born := []).
  - exact Habi.
  - exists d, src, k. auto.
  - split.
    + change (effects [mkSpan src (string_length m src + 1); mkSpan d 0]
        [mkSpan d (string_length m src + 1)] [] (fun _ _ => False) s m [] s m' []).
      rewrite Hlen. eapply effects_local; [eapply string_copy_local; eauto|constructor].
    + split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists d, src. split; [reflexivity|]. rewrite Hlen. exact (proj1 Hresult).
  - split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exists d, src. split; [reflexivity|]. rewrite Hlen. auto.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WPtr (copy_return end_return d k)). split; reflexivity.
    + constructor; [|constructor]. unfold copy_return. destruct end_return; simpl.
      all: right; left; exists (mkSpan d 0); split; [right; left; reflexivity|reflexivity].
  - intros status Hbad. discriminate.
Qed.

(** Input-only nonvacuity, without a native progress or termination claim. *)
Theorem string_copy_admitted : forall end_return world r args d src k s m (w : world),
  string_copy_abi r args -> string_copy_domain m d src k ->
  invoke (string_copy_contract end_return world) r args [WPtr d; WPtr src] s m w
    [] (CallReturn [WPtr (copy_return end_return d k)]) s (string_copy_memory m d src (k + 1)) w.
Proof. intros. apply string_copy_completed; [assumption|assumption|apply string_copy_memory_result]. Qed.

(** Arbitrary completions retain all destination aux, exact bytes/NUL,
    and destination or NUL-position provenance. No resource/exit branch. *)
Theorem string_copy_invocation : forall end_return world r args xs s m (w : world)
    trace ending s' m' w',
  invoke (string_copy_contract end_return world) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ w' = w /\ exists d src k, xs = [WPtr d; WPtr src] /\
    string_copy_domain m d src k /\ string_copy_result m d src (k + 1) m' /\
    ending = CallReturn [WPtr (copy_return end_return d k)].
Proof.
  intros end_return world r args xs s m w trace ending s' m' w' Hcall.
  inversion Hcall; subst.
  - match goal with
    | Hpost : contract_post _ _ _ _ _ _ _ _ _, Hpre : contract_pre _ _ _ _ |- _ =>
      destruct Hpost as (_ & Htrace & Hworld & d & src & Hxs & Hresult & Hending);
      destruct Hpre as (q & v & k & Hxs' & Hdomain)
    end.
    rewrite Hxs in Hxs'. injection Hxs' as <- <-.
    pose proof (terminated_string_length _ _ _ (proj1 Hdomain)) as Hlen.
    rewrite Hlen in Hresult, Hending. split; [exact Htrace|]. split; [exact Hworld|].
    exists d, src, k. auto.
  - contradiction.
Qed.

(** stpcpy's returned NUL is inside the destination, not one-past.
    Readiness bounds its mathematical address without a new runtime axiom. *)
Theorem string_copy_endpoint : forall s m d src k,
  R.ready s m -> string_copy_domain m d src k ->
  exists base reg, ptr_cap d = Obj base /\ object_region base (m_regions m) = Some reg /\
    base <= ptr_addr d + k < r_end reg /\ 0 <= ptr_addr d + k < 2 ^ 64.
Proof.
  intros s m d src k Hready (Hlength & (_ & base & reg & Hcap & Hr & Hl & Ha) & _).
  destruct Hlength as ((_ & Hk & _) & _). simpl in Hcap, Ha.
  unfold access_res, cap_access_res in Ha. rewrite Hr in Ha.
  destruct ((base <=? ptr_addr d) && (ptr_addr d + (k + 1) <=? r_end reg)) eqn:E;
    [|discriminate].
  apply andb_true_iff in E as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  destruct (R.address_space _ _ Hready base reg Hr) as (Hb & He).
  exists base, reg. split; [exact Hcap|]. split; [exact Hr|]. split; lia.
Qed.

End ExternalCalls.

(** ## The first contract: puts *)

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

(** The logical libc world of [puts_contract]. This small world records
    only the currently modeled stream's usability (stdout_usable) and
    reachable writable libc roots, stdio_roots (stdout, errno, buffer).
    Establishing those roots at startup remains an entry obligation.
    It does not claim that an arbitrary writable object is a FILE. *)
Record stdio_world : Type := mkStdioWorld {
  stdout_usable : bool;
  stdio_roots : list span
}.

(** In memory m, the world w's stdout is usable and every libc root it
    names is a [writable_span]. *)
Definition stdio_ready (m : mem) (w : stdio_world) : Prop :=
  stdout_usable w = true /\ Forall (writable_span m) (stdio_roots w).

(** The ABI of puts: the result is discarded or read as one word of
    [[class]] [W], and the one argument is passed as a pointer ([P]). *)
Definition puts_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d W) /\ exists v, args = [Arg P v].

(** The precondition of puts: the world w is represented in memory m
    (rep), it is [stdio_ready], and the one argument word is a pointer
    to a [c_string]. rep is the trusted relation between the abstract
    stream state and its memory representation, including ownership and
    pointer sources. No concrete FILE representation or startup instance
    is claimed here. *)
Definition puts_pre (rep : mem -> stdio_world -> Prop)
    (xs : list word) (m : mem) (w : stdio_world) : Prop :=
  rep m w /\ stdio_ready m w /\ exists p bytes, xs = [WPtr p] /\ c_string m p bytes.

(** Every libc root of the new world w is backed by the call's own
    authority: its capability is [available_cap] from the old roots and
    the born objects, and the call has [write_authority] over all of its
    bytes. A call may retain newly allocated buffers, but cannot acquire
    write authority to an unrelated old object by changing the logical
    world. *)
Definition stdio_delegates (roots : list span) (born : list Z) (m : mem) (w : stdio_world) : Prop :=
  forall s, In s (stdio_roots w) ->
    available_cap roots born m (ptr_cap (span_ptr s)) /\
    forall a, span_contains s a -> write_authority roots born m a.

(** A world whose roots are exactly the old roots, all writable, is
    delegated: keeping the same roots needs no new authority. *)
Lemma stdio_delegates_refl : forall roots born m w,
  stdio_roots w = roots -> Forall (writable_span m) roots -> stdio_delegates roots born m w.
Proof.
  intros roots born m w <- Hroots s Hin. split.
  - right. left. exists s. auto.
  - intros a Ha. left. exists s. split; auto. split; auto.
    rewrite Forall_forall in Hroots. apply Hroots. exact Hin.
Qed.

(** What any finite prefix of a puts call may observe: the new world w'
    is represented in m', [stdio_ready] and [stdio_delegates] from the
    old roots; and the trace is empty, or one [StreamBytes] event on
    stream 1 (stdout) accepting a prefix of the string followed by its
    newline (byte 10). *)
Definition puts_prefix (rep : mem -> stdio_world -> Prop)
    (xs : list word) (m : mem) (w : stdio_world) (born : list Z)
    (trace : list event) (m' : mem) (w' : stdio_world) : Prop :=
  rep m' w' /\ stdio_ready m' w' /\ stdio_delegates (stdio_roots w) born m' w' /\
  (trace = [] \/ exists p bytes accepted tail,
    xs = [WPtr p] /\ c_string m p bytes /\ bytes ++ [10] = accepted ++ tail /\
    trace = [StreamBytes 1 accepted]).

(** The postcondition of puts: the call accepted a prefix of the string
    and its newline, observed as one [StreamBytes] event on stdout, and
    returned one integer, with the world still [stdio_ready]. Successful
    acceptance is the whole string plus newline, with a nonnegative int
    result. On an I/O error, any prefix may have been accepted
    (including all of it), and the result is EOF: -1 at this glibc pin,
    represented as unsigned bits of [[class]] w, 2^32 - 1. Neither event
    says that the bytes have reached a file descriptor. *)
Definition puts_post (xs : list word) (m : mem) (w : stdio_world) (born : list Z)
    (trace : list event) (ending : call_end) (m' : mem) (w' : stdio_world) : Prop :=
  exists p bytes accepted tail result,
    xs = [WPtr p] /\ c_string m p bytes /\
    bytes ++ [10] = accepted ++ tail /\
    ((tail = [] /\ 0 <= result < 2 ^ 31) \/ result = 2 ^ 32 - 1) /\
    trace = [StreamBytes 1 accepted] /\ ending = CallReturn [WInt result] /\
    stdio_ready m' w'.

(** The capability checks a puts call outside its contract can reach
    (codes R, W and V of [libc-contracts.md](../../docs/libc-contracts.md)):
    null capability, out of bounds, misaligned, read-only store, and
    argument or return size mismatch. *)
Definition puts_panic (why : reason) : Prop :=
  In why [NullCapability; OutOfBounds; Misaligned; Readonly; ArgumentSize; ReturnSize].

(** The [[external call|contract]] of puts, given the trusted stream
    representation rep and the allocation requests it may make: a word
    result, [puts_abi], [puts_pre], the world's roots as both sources
    and writable roots, no releases, [puts_prefix], [puts_post], the
    [resource_reason] endings and the [puts_panic] set. *)
Definition puts_contract (rep : mem -> stdio_world -> Prop)
    (requests : list word -> mem -> stdio_world -> Z -> Z -> Prop) : contract stdio_world :=
  mkContract stdio_world (RClass W) puts_abi (puts_pre rep)
    (fun _ _ w => stdio_roots w)
    (fun _ _ w => stdio_roots w) (fun _ _ _ => [])
    requests (puts_prefix rep) puts_post resource_reason puts_panic.

(** ## Contract boundary checks *)

(** No resource ending puts may have is in its panic set: running out of
    memory is not a capability panic. *)
Lemma puts_no_capability_panic : forall rep requests why,
  contract_resource (puts_contract rep requests) why -> ~ puts_panic why.
Proof.
  intros rep requests why [-> | ->]; unfold puts_panic; simpl; intuition discriminate.
Qed.

(** A null pointer is never a [c_string], so puts of null fails the
    precondition rather than having a modeled behavior. *)
Lemma puts_null_not_admissible : forall m bytes,
  ~ c_string m (mkPtr 0 CNone) bytes.
Proof. intros m bytes [H _]. discriminate H. Qed.

(** A puts call that returns anything but EOF accepted exactly its
    whole string followed by a newline on stdout. *)
Lemma puts_success_bytes : forall xs m w born trace m' w' result,
  puts_post xs m w born trace (CallReturn [WInt result]) m' w' ->
  result <> 2 ^ 32 - 1 ->
  exists p bytes, xs = [WPtr p] /\ c_string m p bytes /\ trace = [StreamBytes 1 (bytes ++ [10])].
Proof.
  intros xs m w born trace m' w' result (p & bytes & accepted & tail & n & Hx & Hs & Hb & Hr & Ht & He & _) Hn.
  injection He as <-. destruct Hr as [[-> _] | Hr]; [|contradiction].
  rewrite app_nil_r in Hb. exists p, bytes. split; auto. split; auto. rewrite Hb. exact Ht.
Qed.

(** ## Inhabited behaviors and regression boundaries *)

(** The call relations over the interpreter's runtime, for the
    examples below. *)
Module InterpExternal := ExternalCalls InterpRuntime.

(** The list-string bridge instantiated with the interpreter's ready memory. *)
Module InterpStrings := StringLengths InterpRuntime.

(** The bytes of hello. *)
Definition hello_bytes : list Z := [104; 101; 108; 108; 111].
(** A read-only pointer to the string, at address 1024. *)
Definition hello_ptr : ptr := mkPtr 1024 (Ro 1024).
(** The fixture's one libc root: 16 writable bytes at 2048 standing for
    stdout's state. *)
Definition stdout_span : span := mkSpan (mkPtr 2048 (Obj 2048)) 16.
(** A usable stdout whose only root is [stdout_span]. *)
Definition hello_world : stdio_world := mkStdioWorld true [stdout_span].
(** An abstract stream-state fixture, not a native FILE implementation:
    hello and its NUL in a global object at 1024, the libc state at
    2048, and an unrelated caller heap object at 3072. String, libc
    state and caller object are asymmetric. *)
Definition hello_mem : mem :=
  mkMem (fun a => if a =? 1024 then 104 else if a =? 1025 then 101 else
                   if a =? 1026 then 108 else if a =? 1027 then 108 else
                   if a =? 1028 then 111 else 0)
    [mkRegion 1024 1030 GlobalData Live; mkRegion 2048 2064 Heap Live;
     mkRegion 3072 3080 Heap Live] (fun _ => CNone).

(** Use the fixture's libc object as represented errno storage. Both P
    and discarded calls construct an exact, unchanged-state endpoint. *)
Example errno_location_fixture : Forall (fun r =>
  InterpExternal.invoke (errno_location_contract ptr (fun p => p) (fun _ _ => True))
    r [] [] (2 ^ 32) hello_mem (mkPtr 2048 (Obj 2048))
    [] (CallReturn [WPtr (mkPtr 2048 (Obj 2048))])
    (2 ^ 32) hello_mem (mkPtr 2048 (Obj 2048))) [CResult (TAtom "errno") P; CVoid].
Proof.
  apply Forall_forall. intros r [<-|[<-|[]]];
    apply InterpExternal.errno_location_return;
    [split; [right; eexists; reflexivity|reflexivity]|exact I|
     |split; [left; reflexivity|reflexivity]|exact I|].
  all: (split; [discriminate|]; split; [|reflexivity];
    split; [simpl; lia|]; exists 2048, (mkRegion 2048 2064 Heap Live);
    repeat split; reflexivity).
Qed.

(** Invalid cells never invoke: null, read-only, misaligned, too short,
    missing, and freed. The freed case keeps a former object's bytes. *)
Example errno_location_invalid_cells :
  Forall (fun p => forall r args s trace ending s' m' w',
    ~ InterpExternal.invoke (errno_location_contract ptr (fun q => q) (fun _ _ => True))
      r args [] s hello_mem p trace ending s' m' w')
    [mkPtr 0 (Obj 2048); mkPtr 2048 (Ro 2048); mkPtr 2049 (Obj 2048);
     mkPtr 2064 (Obj 2048); mkPtr 4096 (Obj 4096)] /\
  (forall r args s trace ending s' m' w',
    ~ InterpExternal.invoke (errno_location_contract ptr (fun q => q) (fun _ _ => True))
      r args [] s (mkMem (m_bytes hello_mem) [mkRegion 2048 2048 Heap Freed] (m_aux hello_mem))
      (mkPtr 2048 (Obj 2048)) trace ending s' m' w').
Proof.
  assert (Hreject : forall m p, ~ errno_cell m p -> forall r args s trace ending s' m' w',
    ~ InterpExternal.invoke (errno_location_contract ptr (fun q => q) (fun _ _ => True))
      r args [] s m p trace ending s' m' w').
  { intros m p Hbad r args s trace ending s' m' w' Hcall.
    destruct (InterpExternal.errno_location_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
      as (_ & _ & _ & Hcell & _). exact (Hbad Hcell). }
  split.
  - repeat constructor; apply Hreject;
      intros (Hnz & (_ & base & reg & Hcap & Hr & Hl & Ha) & Halign);
      simpl in Hcap; try discriminate Hcap; injection Hcap as <-;
      try solve [vm_compute in Hr, Halign, Hnz; intuition congruence];
      vm_compute in Hr; injection Hr as <-; vm_compute in Ha; discriminate Ha.
  - apply Hreject. intros (_ & (_ & base & reg & Hcap & Hr & Hl & Ha) & _).
    injection Hcap as <-. vm_compute in Hr. injection Hr as <-. discriminate Hl.
Qed.

(** A writable live cell is not itself evidence of initialized TLS. *)
Example errno_location_unrepresented : forall r args s trace ending s' m' w',
  ~ InterpExternal.invoke (errno_location_contract ptr (fun p => p) (fun _ _ => False))
    r args [] s hello_mem (mkPtr 2048 (Obj 2048)) trace ending s' m' w'.
Proof.
  intros r args s trace ending s' m' w' Hcall.
  destruct (InterpExternal.errno_location_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & Hrep & _). exact Hrep.
Qed.

(** The abstract model allows writable storage at zero. Reject it for
    being NULL independently of bounds, lifetime, alignment or TLS. *)
Example errno_location_live_null :
  let m := mkMem (fun _ => 0) [mkRegion 0 4 GlobalData Live] (fun _ => CNone) in
  let p := mkPtr 0 (Obj 0) in
  writable_span m (mkSpan p 4) /\ ptr_addr p mod 4 = 0 /\
  forall r args s trace ending s' m' w',
  ~ InterpExternal.invoke (errno_location_contract ptr (fun q => q) (fun _ _ => True))
    r args [] s m p trace ending s' m' w'.
Proof.
  split.
  - split; [simpl; lia|]. exists 0, (mkRegion 0 4 GlobalData Live).
    repeat split; reflexivity.
  - split; [reflexivity|]. intros r args s trace ending s' m' w' Hcall.
    destruct (InterpExternal.errno_location_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
      as (_ & _ & _ & (Hnonnull & _) & _). apply Hnonnull. reflexivity.
Qed.

(** Even a readable same-address replacement cannot substitute a Ro
    capability for the exact Obj capability supplied by the thread. *)
Example errno_location_no_cap_substitution : forall r args s trace s' m' w',
  ~ InterpExternal.invoke (errno_location_contract ptr (fun p => p) (fun _ _ => True))
    r args [] s hello_mem (mkPtr 2048 (Obj 2048))
    trace (CallReturn [WPtr (mkPtr 2048 (Ro 2048))]) s' m' w'.
Proof.
  intros r args s trace s' m' w' Hcall.
  destruct (InterpExternal.errno_location_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & _ & _ & _ & _ & _ & Hend). discriminate Hend.
Qed.

(** Width coincidence, extra native arguments and extra argument words
    are rejected through the public invocation, not just ABI inspection. *)
Example errno_location_invalid_abi :
  Forall (fun call => let '(r, args, xs) := call in
    forall s trace ending s' m' w',
    ~ InterpExternal.invoke (errno_location_contract ptr (fun p => p) (fun _ _ => True))
      r args xs s hello_mem (mkPtr 2048 (Obj 2048)) trace ending s' m' w')
    [(CResult (TAtom "n") L, [], []); (CVoid, [Arg W (Const 0)], []); (CVoid, [], [WInt 0])].
Proof.
  repeat constructor; intros s trace ending s' m' w' Hcall;
    destruct (InterpExternal.errno_location_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
      as (([Hvoid|(d & Hr)] & Hargs) & Hxs & _); discriminate.
Qed.

(** The fixture's stream representation: the world is [hello_world]
    and the libc object at 2048 is a live heap object. *)
Definition fixture_rep (m : mem) (w : stdio_world) : Prop :=
  w = hello_world /\ object_region 2048 (m_regions m) = Some (mkRegion 2048 2064 Heap Live).

(** The fixture's one allowed allocation: 32 bytes, 16-aligned. *)
Definition fixture_requests (_ : list word) (_ : mem) (_ : stdio_world) (align size : Z) : Prop :=
  align = 16 /\ size = 32.

(** [hello_ptr] points at the C string hello in [hello_mem]. *)
Lemma hello_string : c_string hello_mem hello_ptr hello_bytes.
Proof. vm_compute. repeat split; lia. Qed.

(** The fixture's stdout is [stdio_ready] in [hello_mem]. *)
Lemma hello_stdio : stdio_ready hello_mem hello_world.
Proof.
  split; [reflexivity|]. constructor; [|constructor].
  split; [simpl; lia|]. exists 2048, (mkRegion 2048 2064 Heap Live).
  repeat split; reflexivity.
Qed.

(** puts of [hello_ptr] meets its precondition in the fixture. *)
Lemma hello_pre : puts_pre fixture_rep [WPtr hello_ptr] hello_mem hello_world.
Proof.
  split; [split; reflexivity|]. split; [exact hello_stdio|].
  exists hello_ptr, hello_bytes. split; [reflexivity|exact hello_string].
Qed.

(** puts of hello may complete having accepted any prefix, accepted, of
    hello and its newline: it returns 0 if that is all of them, and may
    return EOF (2^32 - 1) whatever the prefix. Success and both empty
    and nonempty partial EOF results use the same public call relation,
    [invoke]. No allocation or kernel write is required. *)
Lemma hello_return : forall accepted tail n,
  hello_bytes ++ [10] = accepted ++ tail ->
  ((tail = [] /\ n = 0) \/ n = 2 ^ 32 - 1) ->
  InterpExternal.invoke (puts_contract fixture_rep fixture_requests)
    CVoid [Arg P (Const 0)] [WPtr hello_ptr]
    InterpRuntime.start hello_mem hello_world
    [StreamBytes 1 accepted] (CallReturn [WInt n])
    InterpRuntime.start hello_mem hello_world.
Proof.
  intros accepted tail n Hb Hn.
  eapply InterpExternal.invoke_normal with (born := []).
  - split; [left; reflexivity|]. exists (Const 0). reflexivity.
  - exact hello_pre.
  - split; [constructor|]. split; [split; reflexivity|]. split; [exact hello_stdio|]. split.
    + apply stdio_delegates_refl; [reflexivity|exact (proj2 hello_stdio)].
    + right. exists hello_ptr, hello_bytes, accepted, tail. repeat split; auto using hello_string.
  - exists hello_ptr, hello_bytes, accepted, tail, n.
    split; [reflexivity|]. split; [exact hello_string|]. split; [exact Hb|]. split.
    + destruct Hn as [[Ht ->] | ->];
        [left; split; [exact Ht|change (0 <= 0 < 2147483648); lia] | right; reflexivity].
    + split; [reflexivity|]. split; [reflexivity|exact hello_stdio].
  - intros why H. discriminate H.
  - intros values H. injection H as <-. split.
    + exists (WInt n). split; [reflexivity|]. simpl.
      destruct Hn as [[_ ->] | ->]; reflexivity.
    + constructor; [exact I | constructor].
  - intros status H. discriminate H.
Qed.

(** puts of hello succeeds, accepting hello and a newline and
    returning 0. *)
Example hello_success :
  InterpExternal.invoke (puts_contract fixture_rep fixture_requests)
    CVoid [Arg P (Const 0)] [WPtr hello_ptr]
    InterpRuntime.start hello_mem hello_world
    [StreamBytes 1 [104; 101; 108; 108; 111; 10]] (CallReturn [WInt 0])
    InterpRuntime.start hello_mem hello_world.
Proof. apply (hello_return _ []); [reflexivity | left; auto]. Qed.

(** puts of hello may return EOF having accepted nothing. *)
Example hello_eof_empty :
  InterpExternal.invoke (puts_contract fixture_rep fixture_requests)
    CVoid [Arg P (Const 0)] [WPtr hello_ptr]
    InterpRuntime.start hello_mem hello_world
    [StreamBytes 1 []] (CallReturn [WInt (2 ^ 32 - 1)])
    InterpRuntime.start hello_mem hello_world.
Proof. apply (hello_return _ (hello_bytes ++ [10])); [reflexivity | right; reflexivity]. Qed.

(** puts of hello may return EOF having accepted only he. *)
Example hello_eof_partial :
  InterpExternal.invoke (puts_contract fixture_rep fixture_requests)
    CVoid [Arg P (Const 0)] [WPtr hello_ptr]
    InterpRuntime.start hello_mem hello_world
    [StreamBytes 1 [104; 101]] (CallReturn [WInt (2 ^ 32 - 1)])
    InterpRuntime.start hello_mem hello_world.
Proof. apply (hello_return _ [108; 108; 111; 10]); [reflexivity | right; reflexivity]. Qed.

(** puts of hello may return EOF even having accepted all of it and
    the newline. *)
Example hello_eof_full :
  InterpExternal.invoke (puts_contract fixture_rep fixture_requests)
    CVoid [Arg P (Const 0)] [WPtr hello_ptr]
    InterpRuntime.start hello_mem hello_world
    [StreamBytes 1 (hello_bytes ++ [10])] (CallReturn [WInt (2 ^ 32 - 1)])
    InterpRuntime.start hello_mem hello_world.
Proof. apply (hello_return _ []); [reflexivity | right; reflexivity]. Qed.

(** An allocation the contract requests is an [effects] step: the
    interpreter's runtime places it at 2^32 and adds it to born. *)
Example internal_allocation :
  InterpExternal.effects [stdout_span] [stdout_span] []
    (fixture_requests [] hello_mem hello_world)
    InterpRuntime.start hello_mem [] (2 ^ 32 + 48)
    (allocated hello_mem (heap_req 16 32) (2 ^ 32)) [2 ^ 32].
Proof.
  eapply InterpExternal.effects_alloc; [split; reflexivity |
    unfold max_allocation_size; simpl; lia | reflexivity | constructor].
Qed.

(** A call that writes libc state and accepts h, and whose allocation
    the runtime then refuses (its address space is used up), ends as
    [OutOfMemory] keeping that write and that observation. *)
Example refusal_keeps_prefix :
  InterpExternal.invoke (puts_contract fixture_rep fixture_requests)
    CVoid [Arg P (Const 0)] [WPtr hello_ptr]
    InterpRuntime.address_end hello_mem hello_world
    [StreamBytes 1 [104]] (CallResource OutOfMemory)
    InterpRuntime.address_end (store_bytes hello_mem 2048 1 1) hello_world.
Proof.
  eapply InterpExternal.invoke_resource with (born := []).
  - split; [left; reflexivity|]. exists (Const 0). reflexivity.
  - exact hello_pre.
  - split.
    + eapply InterpExternal.effects_local; [apply local_store_bytes|constructor].
      intros b Hb. left. exists stdout_span. split; [left; reflexivity|].
      split; [exact (Forall_inv (proj2 hello_stdio))|]. unfold span_contains. simpl. lia.
    + split; [split; reflexivity|]. split; [exact hello_stdio|]. split.
      * apply stdio_delegates_refl; [reflexivity|exact (proj2 hello_stdio)].
      * right. exists hello_ptr, hello_bytes, ([104]), ([101; 108; 108; 111; 10]).
        split; [reflexivity|]. split; [exact hello_string|]. split; reflexivity.
  - eapply InterpExternal.failure_oom with (align := 16) (size := 32);
      [split; reflexivity | unfold max_allocation_size; simpl; lia | reflexivity].
  - left. reflexivity.
Qed.

(** The interpreter's runtime is [[ready]] in [hello_mem] with any next
    allocation address next from 4096 up to the end of the address
    space. *)
Lemma hello_ready : forall next,
  4096 <= next <= InterpRuntime.address_end -> InterpRuntime.ready next hello_mem.
Proof.
  intros next Hnext. split; [lia|]. split.
  - intros b reg E. cbn -[Z.eqb] in E.
    destruct (1024 =? b) eqn:E1.
    + apply Z.eqb_eq in E1. injection E as <-. simpl. split; [lia|]. split; [lia | discriminate].
    + destruct (2048 =? b) eqn:E2.
      * apply Z.eqb_eq in E2. injection E as <-. simpl. split; [lia|]. split; [lia | discriminate].
      * destruct (3072 =? b) eqn:E3; [|discriminate E].
        apply Z.eqb_eq in E3. injection E as <-. simpl. split; [lia|]. split; [lia | discriminate].
  - intros a Ha. simpl. split; [|reflexivity].
    destruct (a =? 1024) eqn:E1; [apply Z.eqb_eq in E1; lia|].
    destruct (a =? 1025) eqn:E2; [apply Z.eqb_eq in E2; lia|].
    destruct (a =? 1026) eqn:E3; [apply Z.eqb_eq in E3; lia|].
    destruct (a =? 1027) eqn:E4; [apply Z.eqb_eq in E4; lia|].
    destruct (a =? 1028) eqn:E5; [apply Z.eqb_eq in E5; lia|]. reflexivity.
Qed.

(** hello followed by an A is not the string at [hello_ptr], since the
    NUL comes first. This and the examples below are negative contract
    obligations, not invented native traps. *)
Example missing_nul : ~ c_string hello_mem hello_ptr (hello_bytes ++ [65]).
Proof. intros [H _]. discriminate H. Qed.

(** [hello_mem] with every byte A: all six bytes of the string object
    are readable, but the sixth is not a terminator. *)
Definition nonzero_mem : mem :=
  mkMem (fun _ => 65) (m_regions hello_mem) (m_aux hello_mem).

(** In [nonzero_mem], the six bytes at 1024 are readable. *)
Example nonzero_readable : access_res nonzero_mem 1024 (Ro 1024) 6 Read 1 = Some ok.
Proof. reflexivity. Qed.

(** Yet five As are not a C string there: readable bytes without a NUL
    do not satisfy [c_string]. *)
Example missing_nul_in_bounds : ~ c_string nonzero_mem hello_ptr [65; 65; 65; 65; 65].
Proof. intros [_ H]. vm_compute in H. intuition discriminate. Qed.

(** A call cannot add a zero-length root on the string's object to the
    world: its [Obj] capability is not available from stdout's root,
    even though the span has no bytes. *)
Example no_zero_span_root_injection :
  ~ stdio_delegates [stdout_span] [] hello_mem
    (mkStdioWorld true [stdout_span; mkSpan (mkPtr 1024 (Obj 1024)) 0]).
Proof.
  intros H. destruct (H (mkSpan (mkPtr 1024 (Obj 1024)) 0) (or_intror (or_introl eq_refl))) as [Ha _].
  destruct Ha as [Hc | [(s & [<- | []] & Hc) |
    [(s & a & [<- | []] & _ & _ & _ & Hc) | (b & [] & _)]]]; discriminate Hc.
Qed.

(** A call cannot widen stdout's root to cover the unrelated caller
    object at 3072, even with stdout's own capability. *)
Example no_unrelated_root_coverage :
  ~ stdio_delegates [stdout_span] [] hello_mem
    (mkStdioWorld true [mkSpan (mkPtr 2048 (Obj 2048)) 2048]).
Proof.
  intros H. destruct (H (mkSpan (mkPtr 2048 (Obj 2048)) 2048) (or_introl eq_refl)) as [_ Hw].
  assert (Hin : span_contains (mkSpan (mkPtr 2048 (Obj 2048)) 2048) 3072) by (unfold span_contains; simpl; lia).
  destruct (Hw 3072 Hin) as [(s & [<- | []] & _ & Ha) | (b & reg & [] & _)].
  unfold span_contains in Ha. simpl in Ha. lia.
Qed.

(** Writing a byte of the unrelated caller object is not a
    [local_effect] of a call whose only root is stdout's. *)
Example no_unrelated_write :
  ~ local_effect [stdout_span] [stdout_span] [] [] hello_mem (store_bytes hello_mem 3072 1 7).
Proof.
  intros (_ & _ & Hw & _).
  assert (Hn : ~ write_authority [stdout_span] [] hello_mem 3072).
  { intros [(s & [<- | []] & _ & Hin) | (b & reg & [] & _)]; unfold span_contains in Hin; simpl in Hin; lia. }
  destruct (Hw _ Hn) as [Hb _]. discriminate Hb.
Qed.

(** Storing a forged capability to the caller object into stdout's
    state is not a [local_effect]: it has no source. *)
Example no_forged_capability :
  ~ local_effect [stdout_span] [stdout_span] [] [] hello_mem (store_aux hello_mem 2048 (Obj 3072)).
Proof.
  intros (_ & _ & _ & Haux). destruct (Haux 2048) as [H | H]; [discriminate H|].
  destruct H as [H | [(s & [<- | []] & H) | [(s & a & [<- | []] & _ & _ & _ & H) | (b & [] & _)]]];
    discriminate H.
Qed.

(** A read-only source does not make [Obj] of the same address
    available. *)
Example no_readonly_upgrade :
  ~ available_cap [mkSpan hello_ptr 6] [] hello_mem (Obj 1024).
Proof.
  intros [H | [(s & [<- | []] & H) | [(s & a & [<- | []] & _ & _ & _ & H) | (b & [] & _)]]];
    discriminate H.
Qed.

(** Freeing the caller object is not a [local_effect] of a call that
    may release nothing. *)
Example no_unauthorized_release :
  ~ local_effect [stdout_span] [stdout_span] [] [] hello_mem
    (mkMem (m_bytes hello_mem)
      [mkRegion 1024 1030 GlobalData Live; mkRegion 2048 2064 Heap Live;
       mkRegion 3072 3072 Heap Freed] (m_aux hello_mem)).
Proof.
  intros (_ & Hr & _). destruct (Hr 3072 (mkRegion 3072 3072 Heap Freed) eq_refl)
    as (reg & Hreg & [H | ([] & _)]).
  change (Some (mkRegion 3072 3080 Heap Live) = Some reg) in Hreg.
  injection Hreg as <-. discriminate H.
Qed.

(** Once an object is freed, neither a root on it nor its having been
    born in this call gives [write_authority] over it. *)
Example no_write_after_release :
  ~ write_authority [mkSpan (mkPtr 3072 (Obj 3072)) 8] [3072]
    (mkMem (fun _ => 0) [mkRegion 3072 3072 Heap Freed] (fun _ => CNone)) 3072.
Proof.
  intros [(s & [<- | []] & (_ & b & reg & Hcap & Hr & Hl & _) & _) |
          (b & reg & [<- | []] & Hr & _ & Hl & _)]; simpl in *.
  - injection Hcap as <-. injection Hr as <-. discriminate Hl.
  - injection Hr as <-. discriminate Hl.
Qed.

(** High bytes are nonzero bytes, and the exact six-byte object has no
    required seventh byte or terminator for a bound of six. *)
Definition high_byte_mem : mem :=
  mkMem (fun a => if (1024 <=? a) && (a <? 1030)
    then if a =? 1024 then 128 else 255 else m_bytes hello_mem a)
    (m_regions hello_mem) (m_aux hello_mem).

(** High bytes are confined to the represented object, retaining the
    runtime's zeroed unused address space. *)
Example high_byte_ready : InterpRuntime.ready InterpRuntime.start high_byte_mem.
Proof.
  destruct (hello_ready InterpRuntime.start ltac:(unfold InterpRuntime.start, InterpRuntime.address_end; lia))
    as (Hnext & Hregions & Hunused).
  split; [exact Hnext|]. split; [exact Hregions|]. intros a Ha.
  specialize (Hunused a Ha). cbn -[Z.leb Z.ltb Z.eqb].
  assert (Hout : (1024 <=? a) && (a <? 1030) = false).
  { apply andb_false_iff. right. apply Z.ltb_ge. unfold InterpRuntime.start in Ha. lia. }
  rewrite Hout. exact Hunused.
Qed.

(** An actual permitted invocation returns the exhausted bound without
    modifying memory/world or producing observations. *)
Example strnlen_exact_bound :
  InterpExternal.invoke (strnlen_contract unit) CVoid [Arg P (Const 0); Arg L (Const 6)]
    [WPtr hello_ptr; WInt 6] InterpRuntime.start high_byte_mem tt
    [] (CallReturn [WInt 6]) InterpRuntime.start high_byte_mem tt.
Proof.
  apply InterpExternal.strnlen_return.
  - split; [left; reflexivity|]. exists (Const 0), (Const 6). reflexivity.
  - split; [vm_compute; split; congruence|]. split; [lia|]. split.
    + exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
    + split; [reflexivity|]. split; [|lia]. intros i Hi.
      assert (Hinside : (1024 <=? 1024 + i) && (1024 + i <? 1030) = true).
      { apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
      change (0 < (if (1024 <=? 1024 + i) && (1024 + i <? 1030)
        then if 1024 + i =? 1024 then 128 else 255 else m_bytes hello_mem (1024 + i)) < 256).
      rewrite Hinside.
      change (0 < (if 1024 + i =? 1024 then 128 else 255) < 256).
      destruct (1024 + i =? 1024); lia.
Qed.

(** A readable first NUL permits the largest size_t maximum, even
    though address+maximum would wrap; the sixth byte is the NUL. *)
Example strnlen_early_nul_huge : bounded_length hello_mem hello_ptr (2 ^ 64 - 1) 5.
Proof.
  split; [vm_compute; split; congruence|]. split; [vm_compute; split; congruence|]. split.
  - exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
  - split; [reflexivity|]. split; [|intros; reflexivity]. intros i Hi.
    assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
    destruct H as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; split; congruence.
Qed.

(** A returning invocation cannot pass the earlier NUL and return six,
    even with the largest bound and arbitrary proposed endpoints. *)
Example strnlen_wrong_result_rejected : forall s' m' w',
  ~ InterpExternal.invoke (strnlen_contract unit) CVoid [Arg P (Const 0); Arg L (Const 0)]
    [WPtr hello_ptr; WInt (2 ^ 64 - 1)] InterpRuntime.start hello_mem tt
    [] (CallReturn [WInt 6]) s' m' w'.
Proof.
  intros s' m' w' Hcall.
  destruct (InterpExternal.strnlen_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & p & n & k & Hargs & Hlength & Hending).
  injection Hargs as <- <-. injection Hending as <-.
  pose proof (bounded_length_unique _ _ _ _ _ Hlength strnlen_early_nul_huge). lia.
Qed.

(** Zero count accepts a live read-only one-past pointer without a load. *)
Example strnlen_zero_one_past : bounded_length hello_mem (mkPtr 1030 (Ro 1024)) 0 0.
Proof.
  split; [vm_compute; split; congruence|]. split; [lia|]. split.
  - exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
  - split; [reflexivity|]. split; intros; lia.
Qed.

(** The same one-past pointer does not admit even one byte of scanning. *)
Example strnlen_positive_one_past_rejected : forall k,
  ~ bounded_length hello_mem (mkPtr 1030 (Ro 1024)) 1 k.
Proof.
  intros k (_ & Hk & _ & Ha & _). assert (k = 0 \/ k = 1) by lia.
  destruct H as [-> | ->]; discriminate Ha.
Qed.

(** Null and non-object capabilities remain failed obligations even
    for zero count, without claiming native zero-count calls trap. *)
Example strnlen_zero_null_rejected : forall m k,
  ~ bounded_length m (mkPtr 0 CNone) 0 k.
Proof. intros m k (_ & _ & (base & reg & [Hcap | Hcap] & _) & _); discriminate Hcap. Qed.

(** A freed empty object passes the raw zero-size access check but not
    the live-object requirement of the bounded scan contract. *)
Example strnlen_zero_freed_rejected : forall k,
  ~ bounded_length (mkMem (fun _ => 0) [mkRegion 1024 1024 Heap Freed] (fun _ => CNone))
    (mkPtr 1024 (Obj 1024)) 0 k.
Proof.
  intros k (_ & _ & (base & reg & [Hcap | Hcap] & Hreg & Hlife) & _);
    [injection Hcap as <-; injection Hreg as <-; discriminate Hlife|discriminate Hcap].
Qed.

(** A malformed byte 256 is not a nonzero character merely because
    memory uses Z-valued cells. The contract does not normalize it. *)
Example strnlen_malformed_byte_rejected :
  ~ bounded_length (mkMem (fun _ => 256) (m_regions hello_mem) (m_aux hello_mem)) hello_ptr 1 1.
Proof.
  intros (_ & _ & _ & _ & Hbytes & _). specialize (Hbytes 0 ltac:(lia)). simpl in Hbytes. lia.
Qed.

(** Both the return channel and count argument must have size_t width;
    same-word-count but class-W calls fail independently of behavior. *)
Example strnlen_wrong_abi_rejected :
  ~ strnlen_abi (CResult (TAtom "result") W) [Arg P (Const 0); Arg L (Const 0)] /\
  ~ strnlen_abi CVoid [Arg P (Const 0); Arg W (Const 0)].
Proof.
  split.
  - intros [[Hbad | (d & Hbad)] _]; discriminate Hbad.
  - intros [_ (p & n & Hbad)]. discriminate Hbad.
Qed.

(** An evaluated pointer is not an integer count, even with the right ABI. *)
Example strnlen_pointer_count_rejected :
  ~ contract_pre (strnlen_contract unit) [WPtr hello_ptr; WPtr hello_ptr] hello_mem tt.
Proof. intros (p & n & k & Hargs & _). discriminate Hargs. Qed.

(** The established puts string also meets strlen's explicit live domain. *)
Example strlen_hello_bridge : terminated_length hello_mem hello_ptr 5.
Proof.
  apply (InterpStrings.c_string_length InterpRuntime.start hello_mem hello_ptr hello_bytes).
  - apply hello_ready. unfold InterpRuntime.start, InterpRuntime.address_end. lia.
  - exact hello_string.
Qed.

(** An unaligned high-byte string whose NUL is the object's last byte. *)
Definition strlen_high_mem : mem := store_bytes high_byte_mem 1029 1 0.

(** Offsets zero and one consume high bytes, while offset five is a
    readable empty string. Each reaches the same final in-object NUL. *)
Lemma strlen_boundary_length : forall offset count,
  In (offset, count) [(0, 5); (1, 4); (5, 0)] ->
  terminated_length strlen_high_mem (mkPtr (1024 + offset) (Ro 1024)) count.
Proof.
  intros offset count Hcase. destruct Hcase as [Hcase|[Hcase|[Hcase|[]]]];
    injection Hcase as <- <-.
  all: split; [|vm_compute; congruence]; split; [vm_compute; split; congruence|];
    split; [lia|]; split.
  all: try (exists 1024, (mkRegion 1024 1030 GlobalData Live); split; [right; reflexivity|]; auto).
  all: split; [reflexivity|]; split; [|intros; reflexivity].
  - intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
    destruct H as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; split; congruence.
  - intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct H as [-> | [-> | [-> | ->]]]; vm_compute; split; congruence.
  - intros i Hi. lia.
Qed.

(** The boundary inputs really admit pure size_t returns through the
    public call relation, including the empty and interior strings. *)
Example strlen_boundary_calls : forall offset count,
  In (offset, count) [(0, 5); (1, 4); (5, 0)] ->
  InterpExternal.invoke (strlen_contract unit) (CResult (TAtom "length") L) [Arg P (Const 0)]
    [WPtr (mkPtr (1024 + offset) (Ro 1024))] InterpRuntime.start strlen_high_mem tt
    [] (CallReturn [WInt count]) InterpRuntime.start strlen_high_mem tt.
Proof.
  intros offset count Hcase. apply InterpExternal.strlen_return.
  - split; [right; exists (TAtom "length"); reflexivity|]. exists (Const 0). reflexivity.
  - apply strlen_boundary_length. exact Hcase.
Qed.

(** Incorrect lengths fail at an otherwise admitted public call,
    independently of the proposed return memory, runtime state or world. *)
Example strlen_wrong_result_rejected : forall bits s' m' w',
  bits <> 4 ->
  ~ InterpExternal.invoke (strlen_contract unit) CVoid [Arg P (Const 0)]
    [WPtr (mkPtr 1025 (Ro 1024))] InterpRuntime.start strlen_high_mem tt
    [] (CallReturn [WInt bits]) s' m' w'.
Proof.
  intros bits s' m' w' Hwrong Hcall.
  destruct (InterpExternal.strlen_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & p & k & Hargs & Hlength & Hending).
  injection Hargs as <-. injection Hending as <-.
  apply Hwrong. eapply terminated_length_unique; [exact Hlength|].
  apply (strlen_boundary_length 1 4). simpl. auto.
Qed.

(** Numeric zeroes outside the high-byte object's bounds cannot satisfy
    strlen's existential admission premise: no in-object NUL exists. *)
Example strlen_missing_nul_rejected :
  ~ contract_pre (strlen_contract unit) [WPtr hello_ptr] high_byte_mem tt.
Proof.
  intros (p & k & Hargs & [(Hn & Hk & _ & Ha & Hbytes & Hnul) Hmax]).
  injection Hargs as <-.
  assert (Hlt : (k <? 2 ^ 64 - 1) = true) by (apply Z.ltb_lt; exact Hmax).
  rewrite Hlt in Ha.
  change (Some (if 1024 + (k + 1) <=? 1030 then ok else RTrap OutOfBounds) = Some ok) in Ha.
  destruct (1024 + (k + 1) <=? 1030) eqn:Hend; [|discriminate Ha].
  apply Z.leb_le in Hend.
  specialize (Hnul Hmax).
  assert (Hinside : (1024 <=? 1024 + k) && (1024 + k <? 1030) = true).
  { apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
  change ((if (1024 <=? 1024 + k) && (1024 + k <? 1030)
    then if 1024 + k =? 1024 then 128 else 255 else m_bytes hello_mem (1024 + k)) = 0) in Hnul.
  rewrite Hinside in Hnul. destruct (1024 + k =? 1024); discriminate Hnul.
Qed.

(** Unlike zero-count strnlen, strlen needs a readable byte even for an
    empty result. One-past, null and freed pointers are not admitted. *)
Example strlen_bad_authority_rejected :
  ~ contract_pre (strlen_contract unit) [WPtr (mkPtr 1030 (Ro 1024))] hello_mem tt /\
  ~ contract_pre (strlen_contract unit) [WPtr (mkPtr 0 CNone)] hello_mem tt /\
  ~ contract_pre (strlen_contract unit) [WPtr (mkPtr 1024 (Obj 1024))]
    (mkMem (fun _ => 0) [mkRegion 1024 1024 Heap Freed] (fun _ => CNone)) tt.
Proof.
  split.
  - intros (p & k & Hargs & [(Hn & Hk & _ & Ha & _) Hmax]). injection Hargs as <-.
    assert (Hlt : (k <? 2 ^ 64 - 1) = true) by (apply Z.ltb_lt; exact Hmax).
    rewrite Hlt in Ha.
    change (Some (if 1030 + (k + 1) <=? 1030 then ok else RTrap OutOfBounds) = Some ok) in Ha.
    destruct (1030 + (k + 1) <=? 1030) eqn:Hend; [|discriminate Ha].
    apply Z.leb_le in Hend. lia.
  - split; intros (p & k & Hargs & [(_ & _ & (base & reg & [Hcap|Hcap] & Hreg & Hlife) & _) _]);
      injection Hargs as <-; try discriminate Hcap.
    injection Hcap as <-. injection Hreg as <-. discriminate Hlife.
Qed.

(** The ready high-byte fixture admits any canonical int argument,
    including values whose unsigned-char conversion changes them. *)
Lemma memchr_high_input : forall c, 0 <= c < 2 ^ 32 ->
  memchr_input high_byte_mem hello_ptr c 6.
Proof.
  intros c Hc. apply memchr_input_full; [exact Hc|]. split; [vm_compute; split; congruence|]. split.
  - exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
  - split; [reflexivity|]. intros i Hi.
    assert (Hinside : (1024 <=? 1024 + i) && (1024 + i <? 1030) = true).
    { apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
    change (0 <= (if (1024 <=? 1024 + i) && (1024 + i <? 1030)
      then if 1024 + i =? 1024 then 128 else 255 else m_bytes hello_mem (1024 + i)) < 256).
    rewrite Hinside. destruct (1024 + i =? 1024); lia.
Qed.

(** 511 converts to byte 255, whose first match is at offset one even
    though four later bytes also match. Read-only authority is retained. *)
Lemma memchr_high_first :
  memchr_result high_byte_mem hello_ptr 511 6 (mkPtr 1025 (Ro 1024)).
Proof.
  left. exists 1. repeat split; try reflexivity; try lia.
  intros i Hi. assert (i = 0) by lia. subst. vm_compute. discriminate.
Qed.

(** The contract really admits a returning pointer invocation. *)
Example memchr_first_call :
  InterpExternal.invoke (memchr_contract unit) (CResult (TAtom "found") P)
    [Arg P (Const 0); Arg W (Const 511); Arg L (Const 6)]
    [WPtr hello_ptr; WInt 511; WInt 6] InterpRuntime.start high_byte_mem tt
    [] (CallReturn [WPtr (mkPtr 1025 (Ro 1024))]) InterpRuntime.start high_byte_mem tt.
Proof.
  apply InterpExternal.memchr_return.
  - split; [right; eexists; reflexivity|]. eexists _, _, _. reflexivity.
  - apply memchr_high_input. vm_compute; split; congruence.
  - exact memchr_high_first.
Qed.

(** Later matches, fabricated null and correct-address capability
    amplification/loss all fail through the public invocation relation. *)
Example memchr_wrong_pointer_rejected : forall q s' m' w',
  In q [mkPtr 1026 (Ro 1024); mkPtr 0 CNone; mkPtr 1025 (Obj 1024); mkPtr 1025 CNone] ->
  ~ InterpExternal.invoke (memchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 511); Arg L (Const 6)]
    [WPtr hello_ptr; WInt 511; WInt 6] InterpRuntime.start high_byte_mem tt
    [] (CallReturn [WPtr q]) s' m' w'.
Proof.
  intros q s' m' w' Hbad Hcall.
  destruct (InterpExternal.memchr_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & p & c & n & result & Hargs & Hresult & Hending).
  injection Hargs as <- <- <-. injection Hending as <-.
  pose proof (memchr_result_unique _ _ _ _ _ _ Hresult memchr_high_first) as Heq.
  destruct Hbad as [<- | [<- | [<- | [<- | []]]]]; discriminate Heq.
Qed.

(** No byte is zero in the same bounded binary region. *)
Example memchr_miss : memchr_result high_byte_mem hello_ptr 0 6 (mkPtr 0 CNone).
Proof.
  right. split; [|reflexivity]. intros i Hi.
  assert (Hinside : (1024 <=? 1024 + i) && (1024 + i <? 1030) = true).
  { apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
  change ((if (1024 <=? 1024 + i) && (1024 + i <? 1030)
    then if 1024 + i =? 1024 then 128 else 255 else m_bytes hello_mem (1024 + i)) <> 0).
  rewrite Hinside. destruct (1024 + i =? 1024); discriminate.
Qed.

(** Zero is searchable binary data, not an implicit stopping condition. *)
Example memchr_zero_byte : memchr_result hello_mem hello_ptr 0 6 (mkPtr 1029 (Ro 1024)).
Proof.
  left. exists 5. repeat split; try reflexivity; try lia.
  intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
  destruct H as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; discriminate.
Qed.

(** Read-only live one-past is admitted at zero count and returns null. *)
Example memchr_zero_one_past :
  memchr_input hello_mem (mkPtr 1030 (Ro 1024)) (2 ^ 32 - 1) 0 /\
  memchr_result hello_mem (mkPtr 1030 (Ro 1024)) (2 ^ 32 - 1) 0 (mkPtr 0 CNone).
Proof.
  split.
  - apply memchr_input_full; [vm_compute; split; congruence|]. split; [vm_compute; split; congruence|]. split.
    + exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
    + split; [reflexivity|]. intros; lia.
  - right. split; [intros; lia|reflexivity].
Qed.

(** An immediate match waives the unreadable suffix, not the hit byte. *)
Example memchr_early_hit :
  memchr_input high_byte_mem hello_ptr 128 (2 ^ 64 - 1).
Proof.
  split; [vm_compute; split; congruence|]. split; [vm_compute; split; congruence|].
  exists 0. split; [lia|]. split.
  - change (readable_bytes high_byte_mem hello_ptr 1).
    split; [vm_compute; split; congruence|]. split.
    + exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
    + split; [reflexivity|]. intros i Hi. assert (i = 0) by lia. subst. vm_compute; split; congruence.
  - split; [intros; lia|intros; reflexivity].
Qed.

(** An immediate hit admits a real call even with an unreadable suffix. *)
Example memchr_early_call :
  InterpExternal.invoke (memchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 128); Arg L (Const (2 ^ 64 - 1))]
    [WPtr hello_ptr; WInt 128; WInt (2 ^ 64 - 1)] InterpRuntime.start high_byte_mem tt
    [] (CallReturn [WPtr hello_ptr]) InterpRuntime.start high_byte_mem tt.
Proof.
  apply InterpExternal.memchr_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - exact memchr_early_hit.
  - left. exists 0. split; [vm_compute; split; congruence|]. split; [reflexivity|].
    split; [intros; lia|reflexivity].
Qed.

(** The object's final NUL permits an oversized count without granting
    authority after the matching byte. The same proof covers SIZE_MAX. *)
Lemma memchr_final_nul_input : forall n,
  6 <= n < 2 ^ 64 -> memchr_input hello_mem hello_ptr 0 n.
Proof.
  intros n Hn. split; [vm_compute; split; congruence|]. split; [lia|].
  exists 5. split; [lia|]. split.
  - rewrite (proj2 (Z.ltb_lt 5 n) ltac:(lia)).
    split; [vm_compute; split; congruence|]. split.
    + exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
    + split; [reflexivity|]. intros i Hi.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
      destruct H as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; split; congruence.
  - split.
    + intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
      destruct H as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; discriminate.
    + intros. reflexivity.
Qed.

(** Exact-bound, oversized and SIZE_MAX calls return the same final byte. *)
Example memchr_final_nul_calls : forall n,
  In n [6; 12; 2 ^ 64 - 1] ->
  InterpExternal.invoke (memchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 0); Arg L (Const n)]
    [WPtr hello_ptr; WInt 0; WInt n] InterpRuntime.start hello_mem tt
    [] (CallReturn [WPtr (mkPtr 1029 (Ro 1024))]) InterpRuntime.start hello_mem tt.
Proof.
  intros n Hn. assert (Hbound : 6 <= n < 2 ^ 64).
  { destruct Hn as [<- | [<- | [<- | []]]]; vm_compute; split; congruence. }
  apply InterpExternal.memchr_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - apply memchr_final_nul_input. exact Hbound.
  - left. exists 5. split; [lia|]. split; [reflexivity|]. split; [|reflexivity].
    intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
    destruct H as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; discriminate.
Qed.

(** A null, a later matching byte in total memory, and same-address
    capability substitutions are rejected on an admitted early-stop call. *)
Example memchr_early_wrong_result : forall q s' m' w',
  In q [mkPtr 0 CNone; mkPtr 1030 (Ro 1024); mkPtr 1029 (Obj 1024); mkPtr 1029 CNone] ->
  ~ InterpExternal.invoke (memchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 0); Arg L (Const 12)]
    [WPtr hello_ptr; WInt 0; WInt 12] InterpRuntime.start hello_mem tt
    [] (CallReturn [WPtr q]) s' m' w'.
Proof.
  intros q s' m' w' Hbad Hcall.
  destruct (InterpExternal.memchr_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & p & c & n & result & Hargs & Hresult & Hending).
  injection Hargs as <- <- <-. injection Hending as <-.
  destruct (InterpExternal.memchr_invocation _ _ _ _ _ _ _ _ _ _ _ _
    (memchr_final_nul_calls 12 ltac:(simpl; auto)))
    as (_ & _ & _ & p & c & n & result & Hargs & Hright & Hending).
  injection Hargs as <- <- <-. injection Hending as <-.
  pose proof (memchr_result_unique _ _ _ _ _ _ Hresult Hright) as Heq.
  destruct Hbad as [<- | [<- | [<- | [<- | []]]]]; discriminate Heq.
Qed.

(** A match at offset n is ignored; the immediately larger bound above
    includes it. This five-byte miss still has full readable authority. *)
Example memchr_match_at_count_ignored :
  InterpExternal.invoke (memchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 0); Arg L (Const 5)]
    [WPtr hello_ptr; WInt 0; WInt 5] InterpRuntime.start hello_mem tt
    [] (CallReturn [WPtr (mkPtr 0 CNone)]) InterpRuntime.start hello_mem tt.
Proof.
  apply InterpExternal.memchr_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - apply memchr_input_full; [vm_compute; split; congruence|].
    split; [vm_compute; split; congruence|]. split.
    + exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
    + split; [reflexivity|]. intros i Hi.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
      destruct H as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; split; congruence.
  - right. split; [|reflexivity]. intros i Hi.
    assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
    destruct H as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; discriminate.
Qed.

(** Binary search crosses an earlier NUL to find a nonzero byte. *)
Example memchr_crosses_nul :
  InterpExternal.invoke (memchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 111); Arg L (Const 12)]
    [WPtr hello_ptr; WInt 111; WInt 12] InterpRuntime.start (store_bytes hello_mem 1025 1 0) tt
    [] (CallReturn [WPtr (mkPtr 1028 (Ro 1024))])
    InterpRuntime.start (store_bytes hello_mem 1025 1 0) tt.
Proof.
  apply InterpExternal.memchr_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - split; [vm_compute; split; congruence|]. split; [vm_compute; split; congruence|].
    exists 4. split; [lia|]. split.
    + change (readable_bytes (store_bytes hello_mem 1025 1 0) hello_ptr 5).
      split; [vm_compute; split; congruence|]. split.
      * exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
      * split; [reflexivity|]. intros i Hi.
        assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
        destruct H as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; split; congruence.
    + split; [|intros; reflexivity]. intros i Hi.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
      destruct H as [-> | [-> | [-> | ->]]]; vm_compute; discriminate.
  - left. exists 4. split; [lia|]. split; [reflexivity|]. split; [|reflexivity].
    intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct H as [-> | [-> | [-> | ->]]]; vm_compute; discriminate.
Qed.

(** A zero in total memory just beyond the object cannot authorize a
    miss or a matching read there. All in-object bytes are nonzero. *)
Example memchr_unreadable_match_rejected : ~ memchr_input high_byte_mem hello_ptr 0 7.
Proof.
  intros (_ & _ & k & Hk & (_ & _ & Ha & _) & _ & Hmatch).
  change (Some (if 1024 + (k + (if k <? 7 then 1 else 0)) <=? 1030
    then ok else RTrap OutOfBounds) = Some ok) in Ha.
  destruct (1024 + (k + (if k <? 7 then 1 else 0)) <=? 1030) eqn:Hend; [|discriminate Ha].
  apply Z.leb_le in Hend.
  assert (Hlt : k < 7) by (destruct (k <? 7) eqn:E; [apply Z.ltb_lt; exact E|lia]).
  rewrite (proj2 (Z.ltb_lt _ _) Hlt) in Hend.
  specialize (Hmatch Hlt).
  destruct memchr_miss as [Hbad|[Hmiss _]].
  - destruct Hbad as (i & _ & _ & _ & Hptr). discriminate Hptr.
  - apply (Hmiss k ltac:(lia)). exact Hmatch.
Qed.

(** Null and freed authority are not admitted even at zero count. *)
Example memchr_zero_invalid_rejected :
  (forall m, ~ memchr_input m (mkPtr 0 CNone) 0 0) /\
  ~ memchr_input (mkMem (fun _ => 0) [mkRegion 1024 1024 Heap Freed] (fun _ => CNone))
    (mkPtr 1024 (Obj 1024)) 0 0.
Proof.
  split.
  - intros m (_ & _ & k & _ & (_ & (base & reg & [Hcap | Hcap] & _) & _) & _); discriminate Hcap.
  - intros (_ & _ & k & _ & (_ & (base & reg & [Hcap | Hcap] & Hreg & Hlife) & _) & _);
      [injection Hcap as <-; injection Hreg as <-; discriminate Hlife|discriminate Hcap].
Qed.

(** Wrong ABI classes and unnormalized scalar words fail independently
    of whether a finite search result can be described. *)
Example memchr_bad_domain_rejected :
  ~ memchr_abi (CResult (TAtom "found") L) [Arg P (Const 0); Arg W (Const 0); Arg L (Const 0)] /\
  ~ memchr_abi CVoid [Arg P (Const 0); Arg L (Const 0); Arg L (Const 0)] /\
  ~ memchr_input high_byte_mem hello_ptr (-1) 6 /\
  ~ memchr_input high_byte_mem hello_ptr 128 (2 ^ 64).
Proof.
  split; [intros [[H | (d & H)] _]; discriminate H|]. split.
  - intros [_ (p & c & n & H)]. discriminate H.
  - split.
    + intros (Hc & _). lia.
    + intros (_ & Hn & _). lia.
Qed.

(** Two overlapping five-byte spans of the ready high-byte fixture. *)
Lemma high_five_readable : forall offset, 0 <= offset <= 1 ->
  readable_bytes high_byte_mem (mkPtr (1024 + offset) (Ro 1024)) 5.
Proof.
  intros offset Hoffset. split; [vm_compute; split; congruence|]. split.
  - exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
  - split.
    + assert (Hlo : (1024 <=? 1024 + offset) = true) by (apply Z.leb_le; lia).
      assert (Hhi : (1024 + offset + 5 <=? 1030) = true) by (apply Z.leb_le; lia).
      unfold access_res, cap_access_res. cbn -[Z.add Z.leb Z.modulo].
      rewrite Hlo, Hhi. simpl. unfold aligned_res. rewrite Z.mod_1_r. reflexivity.
    + intros i Hi.
      assert (Hinside : (1024 <=? 1024 + offset + i) && (1024 + offset + i <? 1030) = true).
      { apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
      change (0 <= (if (1024 <=? 1024 + offset + i) && (1024 + offset + i <? 1030)
        then if 1024 + offset + i =? 1024 then 128 else 255 else m_bytes hello_mem (1024 + offset + i)) < 256).
      rewrite Hinside. destruct (1024 + offset + i =? 1024); lia.
Qed.

(** The first unsigned-byte pair is 128 versus 255. *)
Lemma memcmp_high_less :
  memcmp_order high_byte_mem hello_ptr (mkPtr 1025 (Ro 1024)) 5 Datatypes.Lt.
Proof.
  right. exists 0. split; [lia|]. split; [intros; lia|]. split; [discriminate|reflexivity].
Qed.

(** Reversing the two overlapping spans reverses their order. *)
Lemma memcmp_high_greater :
  memcmp_order high_byte_mem (mkPtr 1025 (Ro 1024)) hello_ptr 5 Datatypes.Gt.
Proof.
  right. exists 0. split; [lia|]. split; [intros; lia|]. split; [discriminate|reflexivity].
Qed.

(** Distinct nonunit negative magnitudes, including one greater than
    255, are permitted; the byte difference itself need not be returned. *)
Example memcmp_negative_magnitudes : forall bits, In bits [2 ^ 32 - 2; 2 ^ 32 - 7; 2 ^ 32 - 512] ->
  InterpExternal.invoke (memcmp_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 1); Arg L (Const 5)]
    [WPtr hello_ptr; WPtr (mkPtr 1025 (Ro 1024)); WInt 5] InterpRuntime.start high_byte_mem tt
    [] (CallReturn [WInt bits]) InterpRuntime.start high_byte_mem tt.
Proof.
  intros bits Hbits. apply InterpExternal.memcmp_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - apply (high_five_readable 0). lia.
  - apply (high_five_readable 1). lia.
  - split.
    + destruct Hbits as [<- | [<- | [<- | []]]]; vm_compute; split; congruence.
    + exists Datatypes.Lt. split; [exact memcmp_high_less|].
      destruct Hbits as [<- | [<- | [<- | []]]]; reflexivity.
Qed.

(** Positive 2, 7 and 512 are also permitted through the public invocation. *)
Example memcmp_positive_magnitudes : forall bits, In bits [2; 7; 512] ->
  InterpExternal.invoke (memcmp_contract unit) CVoid
    [Arg P (Const 1); Arg P (Const 0); Arg L (Const 5)]
    [WPtr (mkPtr 1025 (Ro 1024)); WPtr hello_ptr; WInt 5] InterpRuntime.start high_byte_mem tt
    [] (CallReturn [WInt bits]) InterpRuntime.start high_byte_mem tt.
Proof.
  intros bits Hbits. apply InterpExternal.memcmp_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - apply (high_five_readable 1). lia.
  - apply (high_five_readable 0). lia.
  - split.
    + destruct Hbits as [<- | [<- | [<- | []]]]; vm_compute; split; congruence.
    + exists Datatypes.Gt. split; [exact memcmp_high_greater|].
      destruct Hbits as [<- | [<- | [<- | []]]]; reflexivity.
Qed.

(** Wrong zero/positive signs are rejected at otherwise admitted calls. *)
Example memcmp_wrong_sign_rejected : forall bits s' m' w', In bits [0; 2; 7] ->
  ~ InterpExternal.invoke (memcmp_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 1); Arg L (Const 5)]
    [WPtr hello_ptr; WPtr (mkPtr 1025 (Ro 1024)); WInt 5] InterpRuntime.start high_byte_mem tt
    [] (CallReturn [WInt bits]) s' m' w'.
Proof.
  intros bits s' m' w' Hbad Hcall.
  destruct (InterpExternal.memcmp_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & p & q & n & result & Hargs & (_ & ordering & Horder & Hsign) & Hending).
  injection Hargs as <- <- <-. injection Hending as <-.
  pose proof (memcmp_order_unique _ _ _ _ _ _ Horder memcmp_high_less) as ->.
  destruct Hbad as [<- | [<- | [<- | []]]]; discriminate Hsign.
Qed.

(** Comparing an identical span is admitted and returns zero. *)
Example memcmp_identical :
  InterpExternal.invoke (memcmp_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 0); Arg L (Const 5)]
    [WPtr hello_ptr; WPtr hello_ptr; WInt 5] InterpRuntime.start high_byte_mem tt
    [] (CallReturn [WInt 0]) InterpRuntime.start high_byte_mem tt.
Proof.
  apply InterpExternal.memcmp_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - apply (high_five_readable 0). lia.
  - apply (high_five_readable 0). lia.
  - split; [vm_compute; split; congruence|]. exists Datatypes.Eq.
    split; [left; split; reflexivity|reflexivity].
Qed.

(** A differing byte exactly at the bound is invisible until the count
    includes it. The two selected spans overlap in the ready hello memory. *)
Example memcmp_count_boundary :
  memcmp_order hello_mem (mkPtr 1026 (Ro 1024)) (mkPtr 1027 (Ro 1024)) 1 Datatypes.Eq /\
  memcmp_order hello_mem (mkPtr 1026 (Ro 1024)) (mkPtr 1027 (Ro 1024)) 2 Datatypes.Lt.
Proof.
  split.
  - left. split; [reflexivity|]. intros i Hi. assert (i = 0) by lia. subst. reflexivity.
  - right. exists 1. split; [lia|]. split.
    + intros i Hi. assert (i = 0) by lia. subst. reflexivity.
    + split; [discriminate|reflexivity].
Qed.

(** Checking only the first span is insufficient, even with an immediate
    difference. The second span extends one byte past its object. *)
Example memcmp_second_span_required :
  ~ contract_pre (memcmp_contract unit)
    [WPtr hello_ptr; WPtr (mkPtr 1025 (Ro 1024)); WInt 6] high_byte_mem tt.
Proof.
  intros (p & q & n & Hargs & _ & _ & _ & Ha & _).
  injection Hargs as <- <- <-. discriminate Ha.
Qed.

(** Neither side's missing authority is waived by a zero count. *)
Example memcmp_zero_authority_required : forall m p q,
  ptr_cap p = CNone \/ ptr_cap q = CNone ->
  ~ contract_pre (memcmp_contract unit) [WPtr p; WPtr q; WInt 0] m tt.
Proof.
  intros m p q Hbad (left & right & n & Hargs & Hl & Hr).
  injection Hargs as <- <- <-.
  destruct Hbad as [Hbad | Hbad];
    destruct Hl as (_ & (bl & rl & [Hcl | Hcl] & _) & _);
    destruct Hr as (_ & (br & rr & [Hcr | Hcr] & _) & _);
    rewrite Hbad in *; discriminate.
Qed.

(** Both live one-past arguments remain admitted at zero count. *)
Example memcmp_zero_one_past :
  InterpExternal.invoke (memcmp_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 0); Arg L (Const 0)]
    [WPtr (mkPtr 1030 (Ro 1024)); WPtr (mkPtr 1030 (Ro 1024)); WInt 0]
    InterpRuntime.start hello_mem tt [] (CallReturn [WInt 0]) InterpRuntime.start hello_mem tt.
Proof.
  apply InterpExternal.memcmp_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - destruct (proj1 memchr_zero_one_past) as (_ & _ & k & Hk & Hread & _).
    assert (k = 0) by lia. subst. exact Hread.
  - destruct (proj1 memchr_zero_one_past) as (_ & _ & k & Hk & Hread & _).
    assert (k = 0) by lia. subst. exact Hread.
  - split; [vm_compute; split; congruence|]. exists Datatypes.Eq. split; [|reflexivity].
    left. split; [reflexivity|intros; lia].
Qed.

(** Full-span admission rejects malformed cells and noncanonical counts. *)
Example readable_bytes_bad_domain :
  ~ readable_bytes (mkMem (fun _ => 256) (m_regions hello_mem) (m_aux hello_mem)) hello_ptr 1 /\
  ~ readable_bytes high_byte_mem hello_ptr (-1).
Proof.
  split.
  - intros (_ & _ & _ & Hbytes). specialize (Hbytes 0 ltac:(lia)). simpl in Hbytes. lia.
  - intros (Hn & _). lia.
Qed.

(** Same-width ABI shortcuts cannot change the result or count class. *)
Example memcmp_wrong_abi_rejected :
  ~ memcmp_abi (CResult (TAtom "compared") L) [Arg P (Const 0); Arg P (Const 0); Arg L (Const 0)] /\
  ~ memcmp_abi CVoid [Arg P (Const 0); Arg P (Const 0); Arg W (Const 0)].
Proof.
  split.
  - intros [[H | (d & H)] _]; discriminate H.
  - intros [_ (p & q & n & H)]. discriminate H.
Qed.

(** ## Bounded string comparison controls *)

(** Three short strings in existing represented objects: "a" followed
    by z, "a" followed by b, and "ab". Differences after a shared NUL
    must not affect strncmp, unlike a binary comparison. *)
Definition string_compare_mem : mem :=
  mkMem (fun a =>
    if a =? 1024 then 97 else if a =? 1025 then 0 else if a =? 1026 then 122 else
    if a =? 2048 then 97 else if a =? 2049 then 0 else if a =? 2050 then 98 else
    if a =? 2052 then 97 else if a =? 2053 then 98 else if a =? 2054 then 0 else
    m_bytes hello_mem a) (m_regions hello_mem) (m_aux hello_mem).

(** The fixture changes only bytes below the runtime's unused space. *)
Example string_compare_ready : InterpRuntime.ready InterpRuntime.start string_compare_mem.
Proof.
  destruct (hello_ready InterpRuntime.start ltac:(unfold InterpRuntime.start, InterpRuntime.address_end; lia))
    as (Hnext & Hregions & Hunused).
  split; [exact Hnext|]. split; [exact Hregions|]. intros a Ha.
  unfold string_compare_mem. cbn -[Z.eqb].
  repeat match goal with
  | |- context [a =? ?b] => destruct (a =? b) eqn:E;
    [apply Z.eqb_eq in E; unfold InterpRuntime.start in Ha; lia|clear E]
  end. split; reflexivity.
Qed.

(** Independent short-string witnesses remain valid with a huge bound. *)
Lemma string_compare_lengths : forall n, 3 <= n < 2 ^ 64 ->
  bounded_length string_compare_mem hello_ptr n 1 /\
  bounded_length string_compare_mem (mkPtr 2048 (Ro 2048)) n 1 /\
  bounded_length string_compare_mem (mkPtr 2052 (Ro 2048)) n 2.
Proof.
  intros n Hn. assert (Hone : (1 <? n) = true) by (apply Z.ltb_lt; lia).
  assert (Htwo : (2 <? n) = true) by (apply Z.ltb_lt; lia).
  split; [|split]; unfold bounded_length.
  all: split; [lia|]; split; [lia|]; split.
  - exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
  - split; [rewrite Hone; reflexivity|]. split.
    + intros i Hi. assert (i = 0) by lia. subst. vm_compute. split; congruence.
    + intros _. reflexivity.
  - exists 2048, (mkRegion 2048 2064 Heap Live). split; [right; reflexivity|]. auto.
  - split; [rewrite Hone; reflexivity|]. split.
    + intros i Hi. assert (i = 0) by lia. subst. vm_compute. split; congruence.
    + intros _. reflexivity.
  - exists 2048, (mkRegion 2048 2064 Heap Live). split; [right; reflexivity|]. auto.
  - split; [rewrite Htwo; reflexivity|]. split.
    + intros i Hi. assert (i = 0 \/ i = 1) by lia. destruct H as [-> | ->]; vm_compute; split; congruence.
    + intros _. reflexivity.
Qed.

(** A shared NUL cuts off later differing bytes even at SIZE_MAX. *)
Example strncmp_shared_nul_huge :
  InterpExternal.invoke (strncmp_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 1); Arg L (Const (2 ^ 64 - 1))]
    [WPtr hello_ptr; WPtr (mkPtr 2048 (Ro 2048)); WInt (2 ^ 64 - 1)]
    InterpRuntime.start string_compare_mem tt [] (CallReturn [WInt 0])
    InterpRuntime.start string_compare_mem tt.
Proof.
  apply InterpExternal.strncmp_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - destruct (string_compare_lengths (2 ^ 64 - 1) ltac:(vm_compute; split; congruence)) as (Hl & Hr & _).
    exists 1, 1. split; [exact Hl|]. split; [exact Hr|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Eq. split; [|reflexivity].
    left. split; [reflexivity|].
    change (forall i, 0 <= i < 2 ->
      m_bytes string_compare_mem (1024 + i) = m_bytes string_compare_mem (2048 + i)).
    intros i Hi. assert (i = 0 \/ i = 1) by lia. destruct H as [-> | ->]; reflexivity.
Qed.

(** The earlier terminator participates in the comparison. Both signs
    permit magnitude 512 through the public invocation relation. *)
Example strncmp_terminator_magnitudes : forall reverse : bool,
  InterpExternal.invoke (strncmp_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 1); Arg L (Const 3)]
    [WPtr (if reverse then mkPtr 2052 (Ro 2048) else hello_ptr);
     WPtr (if reverse then hello_ptr else mkPtr 2052 (Ro 2048)); WInt 3]
    InterpRuntime.start string_compare_mem tt
    [] (CallReturn [WInt (if reverse then 512 else 2 ^ 32 - 512)])
    InterpRuntime.start string_compare_mem tt.
Proof.
  intros reverse. destruct (string_compare_lengths 3 ltac:(vm_compute; split; congruence)) as (Hl & _ & Hr).
  destruct reverse; apply InterpExternal.strncmp_return.
  all: try solve [split; [left; reflexivity|]; eexists _, _, _; reflexivity].
  - exists 2, 1. split; [exact Hr|]. split; [exact Hl|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Gt. split; [|reflexivity].
    right. exists 1. split; [vm_compute; split; congruence|]. split.
    + intros i Hi. assert (i = 0) by lia. subst. reflexivity.
    + split; [discriminate|reflexivity].
  - exists 1, 2. split; [exact Hl|]. split; [exact Hr|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Lt. split; [|reflexivity].
    right. exists 1. split; [vm_compute; split; congruence|]. split.
    + intros i Hi. assert (i = 0) by lia. subst. reflexivity.
    + split; [discriminate|reflexivity].
Qed.

(** A wrong sign is rejected by the invocation relation at an admitted
    call; failure of some unrelated premise is not the explanation. *)
Example strncmp_wrong_sign_rejected : forall s' m' w',
  ~ InterpExternal.invoke (strncmp_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 1); Arg L (Const 3)]
    [WPtr hello_ptr; WPtr (mkPtr 2052 (Ro 2048)); WInt 3]
    InterpRuntime.start string_compare_mem tt [] (CallReturn [WInt 512]) s' m' w'.
Proof.
  intros s' m' w' Hcall.
  destruct (InterpExternal.strncmp_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & p & q & n & bits & Hargs & Hresult & Hending).
  injection Hargs as <- <- <-. injection Hending as <-.
  destruct (InterpExternal.strncmp_invocation _ _ _ _ _ _ _ _ _ _ _ _
    (strncmp_terminator_magnitudes false))
    as (_ & _ & _ & p & q & n & bits & Hargs & Hgood & Hending).
  injection Hargs as <- <- <-. injection Hending as <-.
  pose proof (strncmp_result_sign_unique _ _ _ _ _ _ Hresult Hgood) as Hsign.
  discriminate Hsign.
Qed.

(** Both one-past pointers are admitted at zero count and return zero. *)
Example strncmp_zero_one_past :
  InterpExternal.invoke (strncmp_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 0); Arg L (Const 0)]
    [WPtr (mkPtr 1030 (Ro 1024)); WPtr (mkPtr 1030 (Ro 1024)); WInt 0]
    InterpRuntime.start hello_mem tt [] (CallReturn [WInt 0]) InterpRuntime.start hello_mem tt.
Proof.
  apply InterpExternal.strncmp_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - exists 0, 0. split; [exact strnlen_zero_one_past|]. split; [exact strnlen_zero_one_past|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Eq. split; [|reflexivity].
    left. split; [reflexivity|intros i Hi; change (0 <= i < 0) in Hi; lia].
Qed.

(** A positive exact-bound call needs no NUL or following byte. *)
Example strncmp_exact_bound :
  InterpExternal.invoke (strncmp_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 0); Arg L (Const 6)]
    [WPtr hello_ptr; WPtr hello_ptr; WInt 6] InterpRuntime.start high_byte_mem tt
    [] (CallReturn [WInt 0]) InterpRuntime.start high_byte_mem tt.
Proof.
  destruct (InterpExternal.strnlen_invocation _ _ _ _ _ _ _ _ _ _ _ _ strnlen_exact_bound)
    as (_ & _ & _ & p & n & k & Hargs & Hlength & Hending).
  injection Hargs as <- <-. injection Hending as <-.
  apply InterpExternal.strncmp_return.
  - split; [left; reflexivity|]. eexists _, _, _. reflexivity.
  - exists 6, 6. split; [exact Hlength|]. split; [exact Hlength|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Eq.
    split; [left; split; reflexivity|reflexivity].
Qed.

(** Mathematical successor before the minimum cannot wrap at SIZE_MAX. *)
Example strncmp_window_no_wrap :
  strncmp_window (2 ^ 64 - 1) (2 ^ 64 - 1) (2 ^ 64 - 1) = 2 ^ 64 - 1.
Proof. reflexivity. Qed.

(** Independent bounded-string obligations cannot be waived by an
    immediate difference or a missing capability at zero count. *)
Example strncmp_independent_inputs :
  ~ contract_pre (strncmp_contract unit)
    [WPtr hello_ptr; WPtr (mkPtr 1025 (Ro 1024)); WInt 6] high_byte_mem tt /\
  (forall m p q, ptr_cap p = CNone \/ ptr_cap q = CNone ->
    ~ contract_pre (strncmp_contract unit) [WPtr p; WPtr q; WInt 0] m tt).
Proof.
  split.
  - intros (p & q & n & left & right & Hargs & Hl & Hr). injection Hargs as <- <- <-.
    destruct Hr as (_ & Hk & _ & Ha & _ & Hnul).
    assert (Hlt : right < 6).
    { destruct (Z_lt_dec right 6); [assumption|]. assert (right = 6) by lia.
      subst. discriminate Ha. }
    assert (Hfive : right < 5).
    { destruct (Z_lt_dec right 5); [assumption|]. assert (right = 5) by lia.
      subst. discriminate Ha. }
    specialize (Hnul Hlt). change (m_bytes high_byte_mem (1025 + right) = 0) in Hnul.
    assert (Hinside : (1024 <=? 1025 + right) && (1025 + right <? 1030) = true)
      by (apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    change ((if (1024 <=? 1025 + right) && (1025 + right <? 1030)
      then if 1025 + right =? 1024 then 128 else 255 else m_bytes hello_mem (1025 + right)) = 0) in Hnul.
    rewrite Hinside in Hnul. destruct (1025 + right =? 1024); discriminate.
  - intros m p q Hbad (left & right & n & kl & kr & Hargs & Hl & Hr).
    injection Hargs as <- <- <-.
    destruct Hbad as [H | H];
      [destruct Hl as (_ & _ & (base & reg & [Hcap | Hcap] & _) & _) |
       destruct Hr as (_ & _ & (base & reg & [Hcap | Hcap] & _) & _)];
      rewrite H in Hcap; discriminate.
Qed.

(** ## Unbounded string comparison controls *)

(** The bounded fixtures are also complete terminated strings. *)
Lemma string_compare_terminated :
  terminated_length string_compare_mem hello_ptr 1 /\
  terminated_length string_compare_mem (mkPtr 2048 (Ro 2048)) 1 /\
  terminated_length string_compare_mem (mkPtr 2052 (Ro 2048)) 2.
Proof.
  destruct (string_compare_lengths (2 ^ 64 - 1) ltac:(vm_compute; split; congruence))
    as (Hl & Hr & Hab).
  split; [split; [exact Hl|vm_compute; congruence]|].
  split; split; try assumption; vm_compute; congruence.
Qed.

(** A shared NUL makes the strings equal despite different following bytes. *)
Example strcmp_shared_nul :
  InterpExternal.invoke (strcmp_contract unit) CVoid [Arg P (Const 0); Arg P (Const 1)]
    [WPtr hello_ptr; WPtr (mkPtr 2048 (Ro 2048))] InterpRuntime.start string_compare_mem tt
    [] (CallReturn [WInt 0]) InterpRuntime.start string_compare_mem tt.
Proof.
  apply InterpExternal.strcmp_return.
  - split; [left; reflexivity|]. eexists _, _. reflexivity.
  - destruct string_compare_terminated as (Hl & Hr & _).
    exists 1, 1. split; [exact Hl|]. split; [exact Hr|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Eq. split; [|reflexivity].
    left. split; [reflexivity|].
    change (forall i, 0 <= i < 2 ->
      m_bytes string_compare_mem (1024 + i) = m_bytes string_compare_mem (2048 + i)).
    intros i Hi. assert (i = 0 \/ i = 1) by lia. destruct H as [-> | ->]; reflexivity.
Qed.

(** The earlier terminator decides strict-prefix order; neither sign is
    restricted to a unit or byte-difference magnitude. *)
Example strcmp_terminator_magnitudes : forall reverse : bool,
  InterpExternal.invoke (strcmp_contract unit) CVoid [Arg P (Const 0); Arg P (Const 1)]
    [WPtr (if reverse then mkPtr 2052 (Ro 2048) else hello_ptr);
     WPtr (if reverse then hello_ptr else mkPtr 2052 (Ro 2048))]
    InterpRuntime.start string_compare_mem tt
    [] (CallReturn [WInt (if reverse then 512 else 2 ^ 32 - 512)])
    InterpRuntime.start string_compare_mem tt.
Proof.
  intros reverse. destruct string_compare_terminated as (Hl & _ & Hr).
  destruct reverse; apply InterpExternal.strcmp_return.
  all: try solve [split; [left; reflexivity|]; eexists _, _; reflexivity].
  - exists 2, 1. split; [exact Hr|]. split; [exact Hl|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Gt. split; [|reflexivity].
    right. exists 1. split; [vm_compute; split; congruence|]. split.
    + intros i Hi. assert (i = 0) by lia. subst. reflexivity.
    + split; [discriminate|reflexivity].
  - exists 1, 2. split; [exact Hl|]. split; [exact Hr|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Lt. split; [|reflexivity].
    right. exists 1. split; [vm_compute; split; congruence|]. split.
    + intros i Hi. assert (i = 0) by lia. subst. reflexivity.
    + split; [discriminate|reflexivity].
Qed.

(** Public wrong-sign rejection uses the same admitted strict-prefix call. *)
Example strcmp_wrong_sign_rejected : forall s' m' w',
  ~ InterpExternal.invoke (strcmp_contract unit) CVoid [Arg P (Const 0); Arg P (Const 1)]
    [WPtr hello_ptr; WPtr (mkPtr 2052 (Ro 2048))] InterpRuntime.start string_compare_mem tt
    [] (CallReturn [WInt 512]) s' m' w'.
Proof.
  intros s' m' w' Hcall.
  destruct (InterpExternal.strcmp_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & p & q & bits & Hargs & Hresult & Hending).
  injection Hargs as <- <-. injection Hending as <-.
  destruct (InterpExternal.strcmp_invocation _ _ _ _ _ _ _ _ _ _ _ _
    (strcmp_terminator_magnitudes false))
    as (_ & _ & _ & p & q & bits & Hargs & Hgood & Hending).
  injection Hargs as <- <-. injection Hending as <-.
  pose proof (strcmp_result_sign_unique _ _ _ _ _ Hresult Hgood) as Hsign.
  discriminate Hsign.
Qed.

(** Unsigned 128 orders above the empty string, not below it as a signed
    char would. The final live NUL is a valid empty input in either slot. *)
Example strcmp_high_empty : forall reverse : bool,
  InterpExternal.invoke (strcmp_contract unit) CVoid [Arg P (Const 0); Arg P (Const 1)]
    [WPtr (if reverse then mkPtr 1029 (Ro 1024) else hello_ptr);
     WPtr (if reverse then hello_ptr else mkPtr 1029 (Ro 1024))]
    InterpRuntime.start strlen_high_mem tt
    [] (CallReturn [WInt (if reverse then 2 ^ 32 - 512 else 512)])
    InterpRuntime.start strlen_high_mem tt.
Proof.
  intros reverse.
  pose proof (strlen_boundary_length 0 5 ltac:(simpl; auto)) as Hl.
  pose proof (strlen_boundary_length 5 0 ltac:(simpl; auto)) as Hr.
  destruct reverse; apply InterpExternal.strcmp_return.
  all: try solve [split; [left; reflexivity|]; eexists _, _; reflexivity].
  - exists 0, 5. split; [exact Hr|]. split; [exact Hl|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Lt. split; [|reflexivity].
    right. exists 0. split; [vm_compute; split; congruence|]. split.
    + intros i Hi. lia.
    + split; [discriminate|reflexivity].
  - exists 5, 0. split; [exact Hl|]. split; [exact Hr|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Gt. split; [|reflexivity].
    right. exists 0. split; [vm_compute; split; congruence|]. split.
    + intros i Hi. lia.
    + split; [discriminate|reflexivity].
Qed.

(** Identical terminated spans, including empty and interior ones, admit
    zero without requiring separate objects or disjoint input authority. *)
Example strcmp_identical_calls : forall offset count,
  In (offset, count) [(0, 5); (1, 4); (5, 0)] ->
  InterpExternal.invoke (strcmp_contract unit) (CResult (TAtom "compared") W)
    [Arg P (Const 0); Arg P (Const 0)]
    [WPtr (mkPtr (1024 + offset) (Ro 1024)); WPtr (mkPtr (1024 + offset) (Ro 1024))]
    InterpRuntime.start strlen_high_mem tt [] (CallReturn [WInt 0])
    InterpRuntime.start strlen_high_mem tt.
Proof.
  intros offset count Hcase. apply InterpExternal.strcmp_return.
  - split; [right; exists (TAtom "compared"); reflexivity|]. eexists _, _. reflexivity.
  - pose proof (strlen_boundary_length offset count Hcase) as Hl.
    exists count, count. split; [exact Hl|]. split; [exact Hl|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Eq.
    split; [left; split; [reflexivity|intros; reflexivity]|reflexivity].
Qed.

(** Overlap is admitted. An earlier 128-versus-255 difference wins over
    the opposite ordering of the final compared 255-versus-NUL pair. *)
Example strcmp_overlap :
  InterpExternal.invoke (strcmp_contract unit) CVoid [Arg P (Const 0); Arg P (Const 1)]
    [WPtr hello_ptr; WPtr (mkPtr 1025 (Ro 1024))] InterpRuntime.start strlen_high_mem tt
    [] (CallReturn [WInt (2 ^ 32 - 512)]) InterpRuntime.start strlen_high_mem tt.
Proof.
  apply InterpExternal.strcmp_return.
  - split; [left; reflexivity|]. eexists _, _. reflexivity.
  - exists 5, 4. split; [apply (strlen_boundary_length 0 5); simpl; auto|].
    split; [apply (strlen_boundary_length 1 4); simpl; auto|].
    split; [vm_compute; split; congruence|]. exists Datatypes.Lt. split; [|reflexivity].
    right. exists 0. split; [vm_compute; split; congruence|]. split.
    + intros i Hi. lia.
    + split; [discriminate|reflexivity].
Qed.

(** An immediate unequal byte cannot waive the other string's missing
    NUL, in either argument position. Both capabilities are live. *)
Example strcmp_independent_inputs :
  ~ contract_pre (strcmp_contract unit)
    [WPtr hello_ptr; WPtr (mkPtr 2048 (Ro 2048))] high_byte_mem tt /\
  ~ contract_pre (strcmp_contract unit)
    [WPtr (mkPtr 2048 (Ro 2048)); WPtr hello_ptr] high_byte_mem tt.
Proof.
  split; intros (p & q & left & right & Hargs & Hl & Hr); injection Hargs as <- <-;
    apply strlen_missing_nul_rejected.
  - exists hello_ptr, left. auto.
  - exists hello_ptr, right. auto.
Qed.

(** A numeric NUL at one-past is not a readable empty string in either
    argument position, even when the other input is an admitted string. *)
Example strcmp_one_past_rejected : forall reverse : bool,
  ~ contract_pre (strcmp_contract unit)
    [WPtr (if reverse then hello_ptr else mkPtr 1030 (Ro 1024));
     WPtr (if reverse then mkPtr 1030 (Ro 1024) else hello_ptr)] hello_mem tt.
Proof.
  intros reverse. destruct reverse;
    intros (p & q & left & right & Hargs & Hl & Hr); injection Hargs as <- <-;
    apply (proj1 strlen_bad_authority_rejected).
  - exists (mkPtr 1030 (Ro 1024)), right. auto.
  - exists (mkPtr 1030 (Ro 1024)), left. auto.
Qed.

(** No count belongs in the ABI, and size_t is not the int result channel. *)
Example strcmp_wrong_abi_rejected :
  ~ strcmp_abi (CResult (TAtom "compared") L) [Arg P (Const 0); Arg P (Const 1)] /\
  ~ strcmp_abi CVoid [Arg P (Const 0)] /\
  ~ strcmp_abi CVoid [Arg P (Const 0); Arg P (Const 1); Arg L (Const 0)].
Proof.
  split; [intros [[H | (d & H)] _]; discriminate H|].
  split; intros [_ (p & q & H)]; discriminate H.
Qed.

(** ## Unbounded character search controls *)

(** The first l of hello, not the repeated l, retains read-only authority. *)
Lemma strchr_hello_first : strchr_result hello_mem hello_ptr 108 (mkPtr 1026 (Ro 1024)).
Proof.
  exists 5. split; [exact strlen_hello_bridge|]. left. exists 2.
  repeat split; try reflexivity; try lia. intros i Hi.
  assert (i = 0 \/ i = 1) by lia. destruct H as [-> | ->]; discriminate.
Qed.

(** The source-only capability permission constructs an actual P return. *)
Example strchr_first_call :
  InterpExternal.invoke (strchr_contract unit) (CResult (TAtom "found") P)
    [Arg P (Const 0); Arg W (Const 108)] [WPtr hello_ptr; WInt 108]
    InterpRuntime.start hello_mem tt [] (CallReturn [WPtr (mkPtr 1026 (Ro 1024))])
    InterpRuntime.start hello_mem tt.
Proof.
  apply InterpExternal.strchr_return.
  - split; [right; eexists; reflexivity|]. eexists _, _. reflexivity.
  - vm_compute; split; congruence.
  - exact strchr_hello_first.
Qed.

(** At that admitted call, a later match, null, and correct-address
    capability amplification or loss fail regardless of the endpoint. *)
Example strchr_wrong_pointer_rejected : forall q s' m' w',
  In q [mkPtr 1027 (Ro 1024); mkPtr 0 CNone; mkPtr 1026 (Obj 1024); mkPtr 1026 CNone] ->
  ~ InterpExternal.invoke (strchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 108)] [WPtr hello_ptr; WInt 108]
    InterpRuntime.start hello_mem tt [] (CallReturn [WPtr q]) s' m' w'.
Proof.
  intros q s' m' w' Hbad Hcall.
  destruct (InterpExternal.strchr_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & p & c & result & Hargs & Hc & Hresult & Hending).
  injection Hargs as <- <-. injection Hending as <-.
  pose proof (strchr_result_unique _ _ _ _ _ Hresult strchr_hello_first) as Heq.
  destruct Hbad as [<- | [<- | [<- | [<- | []]]]]; discriminate Heq.
Qed.

(** Both 511 and the canonical W representation of -1 select byte 255,
    whose repeated later occurrences do not replace the first match. *)
Example strchr_high_calls : forall c, In c [511; 2 ^ 32 - 1] ->
  InterpExternal.invoke (strchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const c)] [WPtr hello_ptr; WInt c]
    InterpRuntime.start strlen_high_mem tt [] (CallReturn [WPtr (mkPtr 1025 (Ro 1024))])
    InterpRuntime.start strlen_high_mem tt.
Proof.
  intros c Hcase. apply InterpExternal.strchr_return.
  - split; [left; reflexivity|]. eexists _, _. reflexivity.
  - destruct Hcase as [<- | [<- | []]]; vm_compute; split; congruence.
  - exists 5. split; [apply (strlen_boundary_length 0 5); simpl; auto|].
    left. exists 1. split; [lia|]. split.
    + destruct Hcase as [<- | [<- | []]]; reflexivity.
    + split; [|reflexivity]. intros i Hi. assert (i = 0) by lia. subst.
      destruct Hcase as [<- | [<- | []]]; discriminate.
Qed.

(** Searching 0 or 256 returns the final live NUL, including an empty
    input; a nonzero search in that empty string instead returns null. *)
Example strchr_nul_empty_calls : forall offset c,
  In (offset, c) [(0, 0); (0, 256); (5, 0); (5, 256); (5, 108)] ->
  InterpExternal.invoke (strchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const c)]
    [WPtr (mkPtr (1024 + offset) (Ro 1024)); WInt c] InterpRuntime.start strlen_high_mem tt
    [] (CallReturn [WPtr (if c =? 108 then mkPtr 0 CNone else mkPtr 1029 (Ro 1024))])
    InterpRuntime.start strlen_high_mem tt.
Proof.
  intros offset c Hcase.
  assert (Hlength : terminated_length strlen_high_mem (mkPtr (1024 + offset) (Ro 1024)) (5 - offset)).
  { apply strlen_boundary_length. destruct Hcase as [H|[H|[H|[H|[H|[]]]]]];
      injection H as <- <-; simpl; auto. }
  apply InterpExternal.strchr_return.
  - split; [left; reflexivity|]. eexists _, _. reflexivity.
  - destruct Hcase as [H|[H|[H|[H|[H|[]]]]]]; injection H as <- <-;
      vm_compute; split; congruence.
  - exists (5 - offset). split; [exact Hlength|].
    destruct Hcase as [H|[H|[H|[H|[H|[]]]]]]; injection H as <- <-.
    + left. exists 5. split; [lia|]. split; [reflexivity|]. split; [|reflexivity].
      intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
      destruct H as [-> | [-> | [-> | [-> | ->]]]]; discriminate.
    + left. exists 5. split; [lia|]. split; [reflexivity|]. split; [|reflexivity].
      intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
      destruct H as [-> | [-> | [-> | [-> | ->]]]]; discriminate.
    + left. exists 0. repeat split; try reflexivity; lia.
    + left. exists 0. repeat split; try reflexivity; lia.
    + right. split; [|reflexivity]. intros i Hi. assert (i = 0) by lia. subst. discriminate.
Qed.

(** A byte after the first NUL is not searched, even within the live
    object; this call is admitted and returns null, not the later z. *)
Example strchr_stops_at_nul :
  InterpExternal.invoke (strchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 122)] [WPtr hello_ptr; WInt 122]
    InterpRuntime.start string_compare_mem tt [] (CallReturn [WPtr (mkPtr 0 CNone)])
    InterpRuntime.start string_compare_mem tt.
Proof.
  apply InterpExternal.strchr_return.
  - split; [left; reflexivity|]. eexists _, _. reflexivity.
  - vm_compute; split; congruence.
  - exists 1. split; [exact (proj1 string_compare_terminated)|]. right. split; [|reflexivity].
    intros i Hi. assert (i = 0 \/ i = 1) by lia. destruct H as [-> | ->]; discriminate.
Qed.

(** Writable source authority is retained too: it is not universally
    downgraded to read-only authority by a successful search. *)
Example strchr_object_source :
  InterpExternal.invoke (strchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 108)] [WPtr (mkPtr 1024 (Obj 1024)); WInt 108]
    InterpRuntime.start hello_mem tt [] (CallReturn [WPtr (mkPtr 1026 (Obj 1024))])
    InterpRuntime.start hello_mem tt.
Proof.
  apply InterpExternal.strchr_return.
  - split; [left; reflexivity|]. eexists _, _. reflexivity.
  - vm_compute; split; congruence.
  - exists 5. split.
    + destruct strlen_hello_bridge as [(Hn & Hk & _ & Ha & Hbytes & Hnul) Hmax].
      split; [|exact Hmax]. split; [exact Hn|]. split; [exact Hk|]. split.
      * exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [left; reflexivity|]. auto.
      * split; [exact Ha|]. split; assumption.
    + left. exists 2. repeat split; try reflexivity; try lia.
      intros i Hi. assert (i = 0 \/ i = 1) by lia. destruct H as [-> | ->]; discriminate.
Qed.

(** An immediate matching byte cannot excuse a missing in-object NUL. *)
Example strchr_missing_nul_rejected :
  ~ contract_pre (strchr_contract unit) [WPtr hello_ptr; WInt 128] high_byte_mem tt.
Proof.
  intros (p & c & k & Hargs & _ & Hlength). injection Hargs as <- <-.
  apply strlen_missing_nul_rejected. exists hello_ptr, k. auto.
Qed.

(** No search argument rescues one-past, null or freed input authority. *)
Example strchr_bad_authority_rejected : forall c,
  ~ contract_pre (strchr_contract unit) [WPtr (mkPtr 1030 (Ro 1024)); WInt c] hello_mem tt /\
  ~ contract_pre (strchr_contract unit) [WPtr (mkPtr 0 CNone); WInt c] hello_mem tt /\
  ~ contract_pre (strchr_contract unit) [WPtr (mkPtr 1024 (Obj 1024)); WInt c]
    (mkMem (fun _ => 0) [mkRegion 1024 1024 Heap Freed] (fun _ => CNone)) tt.
Proof.
  intros c. destruct strlen_bad_authority_rejected as (Hpast & Hnull & Hfreed).
  split; [|split]; intros (p & value & k & Hargs & _ & Hlength); injection Hargs as <- <-.
  - apply Hpast. exists (mkPtr 1030 (Ro 1024)), k. auto.
  - apply Hnull. exists (mkPtr 0 CNone), k. auto.
  - apply Hfreed. exists (mkPtr 1024 (Obj 1024)), k. auto.
Qed.

(** Int words must already be canonical, even for a valid string. *)
Example strchr_noncanonical_rejected : forall c, c < 0 \/ 2 ^ 32 <= c ->
  ~ contract_pre (strchr_contract unit) [WPtr hello_ptr; WInt c] hello_mem tt.
Proof.
  intros c Hbad (p & value & k & Hargs & Hc & _). injection Hargs as <- <-. lia.
Qed.

(** Count-free P/W arguments and a pointer result are distinct ABI
    obligations; identical machine word counts cannot change classes. *)
Example strchr_wrong_abi_rejected :
  ~ strchr_abi (CResult (TAtom "found") L) [Arg P (Const 0); Arg W (Const 0)] /\
  ~ strchr_abi CVoid [Arg P (Const 0); Arg L (Const 0)] /\
  ~ strchr_abi CVoid [Arg P (Const 0)] /\
  ~ strchr_abi CVoid [Arg P (Const 0); Arg W (Const 0); Arg L (Const 0)].
Proof.
  split; [intros [[H | (d & H)] _]; discriminate H|].
  split; [|split]; intros [_ (p & c & H)]; discriminate H.
Qed.

(** ## Last-match character search controls *)

(** The second l in hello is the last match, with the original Ro. *)
Lemma strrchr_hello_last : strrchr_result hello_mem hello_ptr 108 (mkPtr 1027 (Ro 1024)).
Proof.
  exists 5. split; [exact strlen_hello_bridge|]. left. exists 3.
  split; [lia|]. split; [reflexivity|]. split; [|reflexivity].
  intros j Hj. assert (j = 4 \/ j = 5) by lia. destruct H as [-> | ->]; discriminate.
Qed.

(** A last-match pointer is returned through the public P channel. *)
Example strrchr_last_call :
  InterpExternal.invoke (strrchr_contract unit) (CResult (TAtom "found") P)
    [Arg P (Const 0); Arg W (Const 108)] [WPtr hello_ptr; WInt 108]
    InterpRuntime.start hello_mem tt [] (CallReturn [WPtr (mkPtr 1027 (Ro 1024))])
    InterpRuntime.start hello_mem tt.
Proof.
  apply InterpExternal.strrchr_return.
  - split; [right; eexists; reflexivity|]. eexists _, _. reflexivity.
  - vm_compute; split; congruence.
  - exact strrchr_hello_last.
Qed.

(** The first match, false null and correct-address capability
    amplification/loss fail at the same admitted call. *)
Example strrchr_wrong_pointer_rejected : forall q s' m' w',
  In q [mkPtr 1026 (Ro 1024); mkPtr 0 CNone; mkPtr 1027 (Obj 1024); mkPtr 1027 CNone] ->
  ~ InterpExternal.invoke (strrchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 108)] [WPtr hello_ptr; WInt 108]
    InterpRuntime.start hello_mem tt [] (CallReturn [WPtr q]) s' m' w'.
Proof.
  intros q s' m' w' Hbad Hcall.
  destruct (InterpExternal.strrchr_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & p & c & result & Hargs & Hc & Hresult & Hending).
  injection Hargs as <- <-. injection Hending as <-.
  pose proof (strrchr_result_unique _ _ _ _ _ Hresult strrchr_hello_last) as Heq.
  destruct Hbad as [<- | [<- | [<- | [<- | []]]]]; discriminate Heq.
Qed.

(** Conversion selects the last 255 at offset four, not its first
    occurrence at offset one, for 511 and canonical negative one. *)
Example strrchr_high_calls : forall c, In c [511; 2 ^ 32 - 1] ->
  InterpExternal.invoke (strrchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const c)] [WPtr hello_ptr; WInt c]
    InterpRuntime.start strlen_high_mem tt [] (CallReturn [WPtr (mkPtr 1028 (Ro 1024))])
    InterpRuntime.start strlen_high_mem tt.
Proof.
  intros c Hcase. apply InterpExternal.strrchr_return.
  - split; [left; reflexivity|]. eexists _, _. reflexivity.
  - destruct Hcase as [<- | [<- | []]]; vm_compute; split; congruence.
  - exists 5. split; [apply (strlen_boundary_length 0 5); simpl; auto|].
    left. exists 4. split; [lia|]. split.
    + destruct Hcase as [<- | [<- | []]]; reflexivity.
    + split; [|reflexivity]. intros j Hj. assert (j = 5) by lia. subst.
      destruct Hcase as [<- | [<- | []]]; discriminate.
Qed.

(** Zero and 256 find the final NUL even for an empty input. Searching
    that empty suffix for 255 must not find earlier bytes of its object. *)
Example strrchr_nul_empty_calls : forall offset c,
  In (offset, c) [(0, 0); (0, 256); (5, 0); (5, 256); (5, 511)] ->
  InterpExternal.invoke (strrchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const c)]
    [WPtr (mkPtr (1024 + offset) (Ro 1024)); WInt c] InterpRuntime.start strlen_high_mem tt
    [] (CallReturn [WPtr (if c =? 511 then mkPtr 0 CNone else mkPtr 1029 (Ro 1024))])
    InterpRuntime.start strlen_high_mem tt.
Proof.
  intros offset c Hcase.
  assert (Hlength : terminated_length strlen_high_mem (mkPtr (1024 + offset) (Ro 1024)) (5 - offset)).
  { apply strlen_boundary_length. destruct Hcase as [H|[H|[H|[H|[H|[]]]]]];
      injection H as <- <-; simpl; auto. }
  apply InterpExternal.strrchr_return.
  - split; [left; reflexivity|]. eexists _, _. reflexivity.
  - destruct Hcase as [H|[H|[H|[H|[H|[]]]]]]; injection H as <- <-;
      vm_compute; split; congruence.
  - exists (5 - offset). split; [exact Hlength|].
    destruct Hcase as [H|[H|[H|[H|[H|[]]]]]]; injection H as <- <-.
    + left. exists 5. repeat split; try reflexivity; lia.
    + left. exists 5. repeat split; try reflexivity; lia.
    + left. exists 0. repeat split; try reflexivity; lia.
    + left. exists 0. repeat split; try reflexivity; lia.
    + right. split; [|reflexivity]. intros i Hi. assert (i = 0) by lia. subst. discriminate.
Qed.

(** A matching byte after the first NUL is outside the search domain. *)
Example strrchr_stops_at_nul :
  InterpExternal.invoke (strrchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 122)] [WPtr hello_ptr; WInt 122]
    InterpRuntime.start string_compare_mem tt [] (CallReturn [WPtr (mkPtr 0 CNone)])
    InterpRuntime.start string_compare_mem tt.
Proof.
  apply InterpExternal.strrchr_return.
  - split; [left; reflexivity|]. eexists _, _. reflexivity.
  - vm_compute; split; congruence.
  - exists 1. split; [exact (proj1 string_compare_terminated)|]. right. split; [|reflexivity].
    intros i Hi. assert (i = 0 \/ i = 1) by lia. destruct H as [-> | ->]; discriminate.
Qed.

(** A public miss cannot be replaced by an invented nonnull result,
    including the actual matching byte just beyond the logical string. *)
Example strrchr_false_hit_rejected : forall q s' m' w', q <> mkPtr 0 CNone ->
  ~ InterpExternal.invoke (strrchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 122)] [WPtr hello_ptr; WInt 122]
    InterpRuntime.start string_compare_mem tt [] (CallReturn [WPtr q]) s' m' w'.
Proof.
  intros q s' m' w' Hbad Hcall.
  destruct (InterpExternal.strrchr_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & p & c & result & Hargs & Hc & Hresult & Hending).
  injection Hargs as <- <-. injection Hending as <-.
  destruct (InterpExternal.strrchr_invocation _ _ _ _ _ _ _ _ _ _ _ _ strrchr_stops_at_nul)
    as (_ & _ & _ & p & c & result & Hargs & Hcanonical & Hgood & Hending).
  injection Hargs as <- <-. injection Hending as <-.
  apply Hbad. eapply strrchr_result_unique; eauto.
Qed.

(** Obj source authority is retained rather than stripped or downgraded. *)
Example strrchr_object_source :
  InterpExternal.invoke (strrchr_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 108)] [WPtr (mkPtr 1024 (Obj 1024)); WInt 108]
    InterpRuntime.start hello_mem tt [] (CallReturn [WPtr (mkPtr 1027 (Obj 1024))])
    InterpRuntime.start hello_mem tt.
Proof.
  apply InterpExternal.strrchr_return.
  - split; [left; reflexivity|]. eexists _, _. reflexivity.
  - vm_compute; split; congruence.
  - exists 5. split.
    + destruct strlen_hello_bridge as [(Hn & Hk & _ & Ha & Hbytes & Hnul) Hmax].
      split; [|exact Hmax]. split; [exact Hn|]. split; [exact Hk|]. split.
      * exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [left; reflexivity|]. auto.
      * split; [exact Ha|]. split; assumption.
    + left. exists 3. split; [lia|]. split; [reflexivity|]. split; [|reflexivity].
      intros j Hj. assert (j = 4 \/ j = 5) by lia. destruct H as [-> | ->]; discriminate.
Qed.

(** Full terminated-string admission is the same independent premise
    as strchr's: an immediate match cannot rescue a missing terminator. *)
Example strrchr_missing_nul_rejected :
  ~ contract_pre (strrchr_contract unit) [WPtr hello_ptr; WInt 128] high_byte_mem tt.
Proof. exact strchr_missing_nul_rejected. Qed.

(** One-past, null and freed authority remain independently invalid. *)
Example strrchr_bad_authority_rejected : forall c,
  ~ contract_pre (strrchr_contract unit) [WPtr (mkPtr 1030 (Ro 1024)); WInt c] hello_mem tt /\
  ~ contract_pre (strrchr_contract unit) [WPtr (mkPtr 0 CNone); WInt c] hello_mem tt /\
  ~ contract_pre (strrchr_contract unit) [WPtr (mkPtr 1024 (Obj 1024)); WInt c]
    (mkMem (fun _ => 0) [mkRegion 1024 1024 Heap Freed] (fun _ => CNone)) tt.
Proof. exact strchr_bad_authority_rejected. Qed.

(** Canonical int admission is not weakened by the change to last match;
    strchr's independently tested P/W ABI is reused unchanged. *)
Example strrchr_noncanonical_rejected : forall c, c < 0 \/ 2 ^ 32 <= c ->
  ~ contract_pre (strrchr_contract unit) [WPtr hello_ptr; WInt c] hello_mem tt.
Proof. exact strchr_noncanonical_rejected. Qed.

(** ## Byte-fill boundary controls *)

(** An odd-sized writable object, nonuniform raw bytes and three
    stored pointer capabilities; the pointee is a separate object. *)
Definition memset_fixture : mem :=
  mkMem (fun a => a mod 256)
    [mkRegion 1024 1053 Heap Live; mkRegion 2048 2056 Heap Live]
    (fun a => if (a =? 1024) || (a =? 1032) || (a =? 1040) then Obj 2048 else CNone).

(** Independent authority for any in-bounds fixture destination. *)
Lemma memset_fixture_domain : forall offset c n,
  0 <= offset -> 0 <= n -> offset + n <= 29 -> 0 <= c < 2 ^ 32 ->
  memset_domain memset_fixture (mkPtr (1024 + offset) (Obj 1024)) c n.
Proof.
  intros offset c n Hoffset Hn Hend Hc. split; [exact Hc|]. split.
  - change (0 <= n < 18446744073709551616). lia.
  - split.
    + split; [exact Hn|]. exists 1024, (mkRegion 1024 1053 Heap Live).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      change (Some (if (1024 <=? 1024 + offset) && (1024 + offset + n <=? 1053)
        then aligned_res (1024 + offset) 1 else RTrap OutOfBounds) = Some ok).
      assert ((1024 <=? 1024 + offset) = true) as Hlo by (apply Z.leb_le; lia).
      assert ((1024 + offset + n <=? 1053) = true) as Hhi by (apply Z.leb_le; lia).
      rewrite Hlo, Hhi. unfold aligned_res. rewrite Z.mod_1_r. reflexivity.
    + right. exists 1024. split; reflexivity.
Qed.

(** Actual calls include partial, crossing and exact-word fills,
    canonical negative int conversion, and an unaligned one-past empty
    fill. The pointer return is the destination, never the hull start. *)
Example memset_boundary_calls : forall offset c n,
  In (offset, c, n) [(7, 511, 1); (7, 511, 2); (8, 256, 8);
    (7, 2 ^ 32 - 1, 2); (29, 511, 0)] ->
  InterpExternal.invoke (memset_contract unit) (CResult (TAtom "filled") P)
    [Arg P (Const 0); Arg W (Const c); Arg L (Const n)]
    [WPtr (mkPtr (1024 + offset) (Obj 1024)); WInt c; WInt n]
    InterpRuntime.start memset_fixture tt []
    (CallReturn [WPtr (mkPtr (1024 + offset) (Obj 1024))]) InterpRuntime.start
    (memset_memory memset_fixture (mkPtr (1024 + offset) (Obj 1024)) c n) tt.
Proof.
  intros offset c n Hcases. apply InterpExternal.memset_admitted.
  - split; [right; eexists; reflexivity|]. eexists _, _, _. reflexivity.
  - apply memset_fixture_domain;
      destruct Hcases as [H|[H|[H|[H|[H|[]]]]]]; injection H as <- <- <-;
      vm_compute; intuition congruence.
Qed.

(** Every public partial or crossing completion has these observable
    cells, independently of the constructed witness: repeated low bytes,
    a cleared preceding slot, and intact byte/capability neighbours. *)
Example memset_partial_observations : forall n trace ending s' m' w', In n [1; 2] ->
  InterpExternal.invoke (memset_contract unit) CVoid
    [Arg P (Const 0); Arg W (Const 511); Arg L (Const n)]
    [WPtr (mkPtr 1031 (Obj 1024)); WInt 511; WInt n]
    InterpRuntime.start memset_fixture tt trace ending s' m' w' ->
  ending = CallReturn [WPtr (mkPtr 1031 (Obj 1024))] /\
  m_bytes m' 1030 = 6 /\ m_bytes m' 1031 = 255 /\ m_bytes m' 1033 = 9 /\
  m_aux m' 1024 = CNone /\ m_aux m' 1040 = Obj 2048 /\
  (n = 1 -> m_bytes m' 1032 = 8 /\ m_aux m' 1032 = Obj 2048) /\
  (n = 2 -> m_bytes m' 1032 = 255 /\ m_aux m' 1032 = CNone).
Proof.
  intros n trace ending s' m' w' Hn Hcall.
  destruct (InterpExternal.memset_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & p & c & size & Hargs & Hdomain & (Hframe & Hfill & Hclear) & Hending).
  injection Hargs as <- <- <-. destruct Hframe as (Hregions & Hbytes & Haux).
  split; [exact Hending|]. split.
  - rewrite Hbytes; [reflexivity|]. unfold span_contains. simpl. lia.
  - split.
    + apply Hfill. unfold span_contains. simpl. destruct Hn as [<-|[<-|[]]]; lia.
    + split.
      * rewrite Hbytes; [reflexivity|]. unfold span_contains. simpl.
        destruct Hn as [<-|[<-|[]]]; lia.
      * split.
        -- apply Hclear. destruct Hn as [<-|[<-|[]]]; reflexivity.
        -- split.
           ++ rewrite Haux; [reflexivity|]. destruct Hn as [<-|[<-|[]]]; reflexivity.
           ++ split; intros ->; split.
              ** rewrite Hbytes; [reflexivity|]. unfold span_contains. simpl. lia.
              ** rewrite Haux; reflexivity.
              ** apply Hfill. unfold span_contains. simpl. lia.
              ** apply Hclear. reflexivity.
Qed.

(** A full-word endpoint excludes the next slot. Empty fills preserve
    the actual memory record even at an unaligned one-past address. *)
Example memset_exact_endpoint_and_zero :
  m_aux (memset_memory memset_fixture (mkPtr 1032 (Obj 1024)) 256 8) 1032 = CNone /\
  m_aux (memset_memory memset_fixture (mkPtr 1032 (Obj 1024)) 256 8) 1040 = Obj 2048 /\
  memset_memory memset_fixture (mkPtr 1053 (Obj 1024)) 511 0 = memset_fixture.
Proof. repeat split; reflexivity. Qed.

(** A writable hull alone is insufficient for native-relative slot
    correspondence: this interior call still has an unaligned base. *)
Example memset_unaligned_base_rejected :
  writable_span (mkMem (fun _ => 0) [mkRegion 1025 1053 Heap Live] (fun _ => CNone))
    (memset_root (mkPtr 1033 (Obj 1025)) 1) /\
  ~ contract_pre (memset_contract unit) [WPtr (mkPtr 1033 (Obj 1025)); WInt 0; WInt 1]
    (mkMem (fun _ => 0) [mkRegion 1025 1053 Heap Live] (fun _ => CNone)) tt.
Proof.
  split.
  - split; [vm_compute; congruence|]. exists 1025, (mkRegion 1025 1053 Heap Live).
    repeat split; reflexivity.
  - intros (p & c & n & Hargs & Hc & Hn & Hw & Halign).
    injection Hargs as <- <- <-. destruct Halign as [Hbad | (base & Hcap & Hmod)].
    + discriminate.
    + injection Hcap as <-. discriminate Hmod.
Qed.

(** Ro, null and freed destinations are outside even the conservative
    zero-count domain; positive one-past writes remain out of bounds. *)
Example memset_invalid_destinations : forall p m n,
  In (p, m, n) [(mkPtr 1024 (Ro 1024), memset_fixture, 0);
    (mkPtr 0 CNone, memset_fixture, 0);
    (mkPtr 1024 (Obj 1024),
      mkMem (fun _ => 0) [mkRegion 1024 1024 Heap Freed] (fun _ => CNone), 0);
    (mkPtr 1053 (Obj 1024), memset_fixture, 1)] ->
  ~ contract_pre (memset_contract unit) [WPtr p; WInt 0; WInt n] m tt.
Proof.
  intros p m n Hcases (q & c & size & Hargs & Hc & Hsize & Hw & Halign).
  injection Hargs as <- <- <-.
  destruct Hcases as [H|[H|[H|[H|[]]]]]; injection H as <- <- <-;
    destruct Hw as (_ & base & reg & Hcap & Hr & Hl & Ha); simpl in Hcap.
  - discriminate.
  - discriminate.
  - injection Hcap as <-. simpl in Hr. injection Hr as <-. discriminate.
  - injection Hcap as <-. simpl in Hr. injection Hr as <-. discriminate Ha.
Qed.

(** Canonical scalars and the exact P/W/L-to-P ABI are independent
    obligations, not consequences of the chosen write effect. *)
Example memset_invalid_scalars_and_abi :
  (forall c n, c < 0 \/ 2 ^ 32 <= c \/ n < 0 \/ 2 ^ 64 <= n ->
    ~ contract_pre (memset_contract unit)
      [WPtr (mkPtr 1024 (Obj 1024)); WInt c; WInt n] memset_fixture tt) /\
  ~ memset_abi (CResult (TAtom "bad") L) [Arg P (Const 0); Arg W (Const 0); Arg L (Const 1)] /\
  ~ memset_abi CVoid [Arg P (Const 0); Arg L (Const 0); Arg L (Const 1)] /\
  ~ memset_abi CVoid [Arg P (Const 0); Arg W (Const 0); Arg W (Const 1)] /\
  ~ memset_abi CVoid [Arg P (Const 0); Arg W (Const 0)] /\
  ~ memset_abi CVoid [Arg P (Const 0); Arg W (Const 0); Arg L (Const 1); Arg L (Const 1)].
Proof.
  split.
  - intros c n Hbad (p & v & size & Hargs & Hc & Hn & _).
    injection Hargs as <- <- <-. lia.
  - split; [intros [[H|(d & H)] _]; discriminate H|].
    repeat split; intros [_ (p & c & n & Hargs)]; discriminate Hargs.
Qed.

(** ## Snapshot-copy controls *)

(** Finite patterned bytes and distinct Ro/Obj stored capabilities.
    The odd-sized destination permits an unaligned one-past endpoint. *)
Definition copy_fixture : mem :=
  mkMem (fun a => if (1024 <=? a) && (a <? 1053) then a mod 256 else 0)
    (m_regions memset_fixture)
    (fun a => if a =? 1024 then Ro 2048 else if a =? 1032 then Obj 2048 else CNone).

(** This positive fixture is genuinely ready, so the generic effect
    preservation theorem has a concrete ready-start instance. *)
Example copy_fixture_ready : InterpRuntime.ready InterpRuntime.start copy_fixture.
Proof.
  split; [unfold InterpRuntime.start, InterpRuntime.address_end; lia|]. split.
  - intros b reg Hr. cbn -[Z.eqb] in Hr. destruct (1024 =? b) eqn:Hb.
    + apply Z.eqb_eq in Hb. injection Hr as <-. simpl.
      unfold InterpRuntime.start. repeat split; try discriminate; lia.
    + destruct (2048 =? b) eqn:Hb'; [|discriminate].
      apply Z.eqb_eq in Hb'. injection Hr as <-. simpl.
      unfold InterpRuntime.start. repeat split; try discriminate; lia.
  - intros a Ha. unfold InterpRuntime.start in Ha.
    change ((if (1024 <=? a) && (a <? 1053) then a mod 256 else 0) = 0 /\
      (if a =? 1024 then Ro 2048 else if a =? 1032 then Obj 2048 else CNone) = CNone).
    assert ((a <? 1053) = false) as He by (apply Z.ltb_ge; lia).
    assert ((a =? 1024) = false) as H1 by (apply Z.eqb_neq; lia).
    assert ((a =? 1032) = false) as H2 by (apply Z.eqb_neq; lia).
    rewrite He, H1, H2, andb_false_r. split; reflexivity.
Qed.

(** Input-only fixture authority for byte-disjoint or overlapping
    calls. A read-only source alias never licenses destination writes. *)
Lemma copy_fixture_domain : forall overlap d src n,
  0 <= d -> 0 <= src -> 0 <= n -> d + n <= 29 -> src + n <= 29 ->
  (overlap = true \/ n = 0 \/ d + n <= src \/ src + n <= d) ->
  copy_domain overlap copy_fixture (mkPtr (1024 + d) (Obj 1024))
    (mkPtr (1024 + src) (Ro 1024)) n.
Proof.
  intros overlap d src n Hd Hsrc Hn Hdend Hsend Hsep. split.
  - change (memset_domain memset_fixture (mkPtr (1024 + d) (Obj 1024)) 0 n).
    apply memset_fixture_domain; try assumption. change (0 <= 0 < 4294967296). lia.
  - split.
    + split; [change (0 <= n < 18446744073709551616); lia|]. split.
      * exists 1024, (mkRegion 1024 1053 Heap Live).
        split; [right; reflexivity|]. repeat split; reflexivity.
      * split.
        -- change (Some (if (1024 <=? 1024 + src) && (1024 + src + n <=? 1053)
             then aligned_res (1024 + src) 1 else RTrap OutOfBounds) = Some ok).
           assert ((1024 <=? 1024 + src) = true) as Hlo by (apply Z.leb_le; lia).
           assert ((1024 + src + n <=? 1053) = true) as Hhi by (apply Z.leb_le; lia).
           rewrite Hlo, Hhi. unfold aligned_res. rewrite Z.mod_1_r. reflexivity.
        -- intros i Hi.
           change (0 <= (if (1024 <=? 1024 + src + i) && (1024 + src + i <? 1053)
             then (1024 + src + i) mod 256 else 0) < 256).
           destruct ((1024 <=? 1024 + src + i) && (1024 + src + i <? 1053));
             [apply Z.mod_pos_bound|]; lia.
    + split.
      * right. exists 1024. split; [right; reflexivity|reflexivity].
      * change (overlap = true \/ n = 0 \/ 1024 + d + n <= 1024 + src \/
          1024 + src + n <= 1024 + d).
        destruct Hsep as [H|[H|[H|H]]]; [left|right; left|right; right; left|right; right; right];
          try assumption; lia.
Qed.

(** Actual public calls cover full and partial words, both overlap
    directions, self moves, out-of-phase moves, adjacent memcpy ranges,
    CNone source metadata, and an exact one-past mempcpy return. *)
Example copy_boundary_calls : forall overlap end_return d src n,
  In (overlap, end_return, d, src, n)
    [(false, false, 16, 0, 8); (false, true, 21, 0, 8);
     (true, false, 8, 0, 16); (true, false, 0, 8, 16);
     (false, false, 1, 2, 1); (true, false, 1, 1, 1);
     (true, false, 0, 0, 8); (true, false, 9, 1, 16);
     (true, false, 0, 1, 16); (false, false, 0, 16, 8); (false, true, 29, 29, 0)] ->
  InterpExternal.invoke (copy_contract overlap end_return unit) (CResult (TAtom "copied") P)
    [Arg P (Const 0); Arg P (Const 0); Arg L (Const n)]
    [WPtr (mkPtr (1024 + d) (Obj 1024)); WPtr (mkPtr (1024 + src) (Ro 1024)); WInt n]
    InterpRuntime.start copy_fixture tt []
    (CallReturn [WPtr (copy_return end_return (mkPtr (1024 + d) (Obj 1024)) n)])
    InterpRuntime.start (copy_memory copy_fixture (mkPtr (1024 + d) (Obj 1024))
      (mkPtr (1024 + src) (Ro 1024)) n) tt.
Proof.
  intros overlap end_return d src n Hcases. apply InterpExternal.copy_admitted.
  - split; [right; eexists; reflexivity|]. eexists _, _, _. reflexivity.
  - apply copy_fixture_domain; destruct Hcases as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]];
      injection H as <- <- <- <- <-; vm_compute; intuition congruence.
Qed.

(** Hand-derived cells distinguish original snapshots, exact Ro/Obj
    retention, smidgen and phase clearing, self-copy effects, empty
    copies and neighbours. They constrain every public completion. *)
Example copy_completion_cells : forall d src n a byte capability trace ending s' m' w',
  In (d, src, n, a, byte, capability)
    [(1040, 1024, 8, 1040, 0, Ro 2048);
     (1032, 1024, 16, 1040, 8, Obj 2048);
     (1024, 1032, 16, 1024, 8, Obj 2048);
     (1024, 1032, 16, 1032, 16, CNone);
     (1033, 1025, 16, 1032, 8, CNone);
     (1033, 1025, 16, 1040, 8, Obj 2048);
     (1024, 1025, 16, 1024, 1, CNone);
     (1024, 1040, 8, 1024, 16, CNone);
     (1025, 1025, 1, 1024, 0, CNone);
     (1024, 1024, 8, 1024, 0, Ro 2048);
     (1025, 1026, 1, 1024, 0, CNone);
     (1053, 1053, 0, 1024, 0, Ro 2048)] ->
  InterpExternal.invoke (memmove_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 0); Arg L (Const n)]
    [WPtr (mkPtr d (Obj 1024)); WPtr (mkPtr src (Ro 1024)); WInt n]
    InterpRuntime.start copy_fixture tt trace ending s' m' w' ->
  m_bytes m' a = byte /\ m_aux m' a = capability.
Proof.
  intros d src n a byte capability trace ending s' m' w' Hcases Hcall.
  destruct (InterpExternal.copy_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & dst & source & count & Hargs & Hdomain & Hresult & Hend).
  injection Hargs as <- <- <-.
  destruct (copy_result_cells _ _ _ _ _ a Hresult) as [Hb Ha]. rewrite Hb, Ha.
  destruct Hcases as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]];
    injection H as <- <- <- <- <- <-; split; reflexivity.
Qed.

(** Positive overlapping bytes cannot be used under memcpy merely
    because the shared snapshot relation also supports memmove. *)
Example memcpy_overlap_rejected :
  ~ contract_pre (memcpy_contract unit)
    [WPtr (mkPtr 1032 (Obj 1024)); WPtr (mkPtr 1024 (Ro 1024)); WInt 16] copy_fixture tt.
Proof.
  intros (d & src & n & Hargs & _ & _ & _ & Hsep).
  injection Hargs as <- <- <-. simpl in Hsep. destruct Hsep as [H|[H|[H|H]]]; try discriminate; lia.
Qed.

(** The end-return expectation is a hand-written one-past pointer,
    not computed from the API's own return helper. *)
Example mempcpy_exact_return : forall trace ending s' m' w',
  InterpExternal.invoke (mempcpy_contract unit) CVoid
    [Arg P (Const 0); Arg P (Const 0); Arg L (Const 8)]
    [WPtr (mkPtr 1045 (Obj 1024)); WPtr (mkPtr 1024 (Ro 1024)); WInt 8]
    InterpRuntime.start copy_fixture tt trace ending s' m' w' ->
  ending = CallReturn [WPtr (mkPtr 1053 (Obj 1024))].
Proof.
  intros trace ending s' m' w' Hcall.
  destruct (InterpExternal.copy_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & d & src & n & Hargs & Hdomain & Hresult & Hend).
  injection Hargs as <- <- <-. exact Hend.
Qed.

(** Destination writes require Obj independently of readable source
    authority. Null sources and incorrect P/P/L ABI shapes fail too. *)
Example copy_bad_domains_and_abi :
  (forall n, ~ contract_pre (memmove_contract unit)
    [WPtr (mkPtr 1024 (Ro 1024)); WPtr (mkPtr 1024 (Ro 1024)); WInt n] copy_fixture tt) /\
  (forall n, ~ contract_pre (memmove_contract unit)
    [WPtr (mkPtr 1024 (Obj 1024)); WPtr (mkPtr 0 CNone); WInt n] copy_fixture tt) /\
  ~ copy_abi (CResult (TAtom "bad") L) [Arg P (Const 0); Arg P (Const 0); Arg L (Const 8)] /\
  ~ copy_abi CVoid [Arg P (Const 0); Arg W (Const 0); Arg L (Const 8)] /\
  ~ copy_abi CVoid [Arg P (Const 0); Arg P (Const 0); Arg W (Const 8)] /\
  ~ copy_abi CVoid [Arg P (Const 0); Arg P (Const 0)] /\
  ~ copy_abi CVoid [Arg P (Const 0); Arg P (Const 0); Arg L (Const 8); Arg L (Const 8)].
Proof.
  split.
  - intros n (d & src & count & Hargs & (_ & _ & Hw & _) & _).
    injection Hargs as <- <- <-. destruct Hw as (_ & base & reg & Hcap & _). discriminate Hcap.
  - split.
    + intros n (d & src & count & Hargs & _ & (_ & (base & reg & Hcap & _) & _) & _).
      injection Hargs as <- <- <-. destruct Hcap as [H|H]; discriminate.
    + split; [intros [[H|(d & H)] _]; discriminate H|].
      repeat split; intros [_ (d & src & n & Hargs)]; discriminate Hargs.
Qed.

(** ## Fresh allocation controls *)

(** Empty and nonmultiple sizes are actual successful calls, not just
    satisfiable postconditions. The latter has 32 bytes of capacity. *)
Example malloc_boundary_calls : forall n, n = 0 \/ n = 17 ->
  InterpExternal.invoke (malloc_contract unit) (CResult (TAtom "buffer") P)
    [Arg L (Const n)] [WInt n] InterpRuntime.start hello_mem tt []
    (CallReturn [WPtr (mkPtr (2 ^ 32) (Obj (2 ^ 32)))])
    (2 ^ 32 + req_extent (heap_req 16 n) + 16)
    (allocated hello_mem (heap_req 16 n) (2 ^ 32)) tt.
Proof.
  intros n [-> | ->]; apply InterpExternal.malloc_return.
  all: try solve [split; [right; eexists; reflexivity|eexists; reflexivity]].
  all: try solve [apply hello_ready; unfold InterpRuntime.start, InterpRuntime.address_end; lia].
  all: try solve [vm_compute; intuition congruence].
Qed.

(** Refusal at the address-space end is OOM, including for a legal
    rounded request. Oversize is separately TooBig, not NULL/panic. *)
Example malloc_resource_calls :
  InterpExternal.invoke (malloc_contract unit) CVoid [Arg L (Const 17)] [WInt 17]
    InterpRuntime.address_end hello_mem tt [] (CallResource OutOfMemory)
    InterpRuntime.address_end hello_mem tt /\
  InterpExternal.invoke (malloc_contract unit) CVoid [Arg L (Const (2 ^ 48))] [WInt (2 ^ 48)]
    InterpRuntime.start hello_mem tt [] (CallResource TooBig) InterpRuntime.start hello_mem tt.
Proof.
  split; apply InterpExternal.malloc_refused.
  all: try solve [split; [left; reflexivity|eexists; reflexivity]].
  all: try solve [vm_compute; intuition congruence].
  - eapply InterpExternal.failure_oom with (align := 16) (size := 17).
    + exists 17. auto.
    + unfold max_allocation_size; lia.
    + reflexivity.
  - eapply InterpExternal.failure_big with (align := 16) (size := 2 ^ 48).
    + exists (2 ^ 48). auto.
    + unfold max_allocation_size; lia.
Qed.

(** Every successful public call returns positive, fresh aligned Obj
    authority and frames both old cell maps. A constant NULL answer or
    changing an old pointer's capability cannot satisfy this control. *)
Example malloc_success_frame : forall n trace p s' m' w',
  InterpExternal.invoke (malloc_contract unit) CVoid [Arg L (Const n)] [WInt n]
    InterpRuntime.start hello_mem tt trace (CallReturn [WPtr p]) s' m' w' ->
  0 < ptr_addr p /\ ptr_addr p mod 16 = 0 /\ ptr_cap p = Obj (ptr_addr p) /\
  object_region (ptr_addr p) (m_regions hello_mem) = None /\
  (forall a, m_bytes m' a = m_bytes hello_mem a /\ m_aux m' a = m_aux hello_mem a).
Proof.
  intros n trace p s' m' w' Hcall.
  destruct (InterpExternal.malloc_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & size & Hargs & _ & [(base & Hr & Hend)|(why & born & Hend & _)]).
  - injection Hargs as <-. injection Hend as Hp. subst p.
    destruct (malloc_old_cells _ _ _ _ Hr) as [Hcells _].
    destruct Hr as (_ & (Hpos & Halign & _ & Hnew & _) & _).
    simpl in Halign. simpl. auto.
  - discriminate Hend.
Qed.

(** Reject noncanonical size_t and wrong ABI classes independently of
    allocation availability. A huge canonical request remains admitted. *)
Example malloc_inputs :
  ~ contract_pre (malloc_contract unit) [WInt (-1)] hello_mem tt /\
  ~ contract_pre (malloc_contract unit) [WInt (2 ^ 64)] hello_mem tt /\
  contract_pre (malloc_contract unit) [WInt (2 ^ 64 - 1)] hello_mem tt /\
  ~ malloc_abi CVoid [Arg W (Const 1)] /\
  ~ malloc_abi (CResult (TAtom "wrong") L) [Arg L (Const 1)].
Proof.
  split; [intros (n & Hargs & Hn); injection Hargs as <-; lia|].
  split; [intros (n & Hargs & Hn); injection Hargs as <-; lia|].
  split; [exists (2 ^ 64 - 1); split; [reflexivity|lia]|].
  split; [intros (_ & n & Hargs); discriminate Hargs|].
  intros ([H|(d & H)] & _); discriminate H.
Qed.

(** ## String duplication controls *)

(** Sixteen nonzero bytes followed by NUL, with distinct stored
    capabilities beneath the first two words. Finite unused bytes are
    zero, so the fixture instantiates readiness. *)
Definition strdup_fixture : mem :=
  mkMem (fun a => if (1024 <=? a) && (a <? 1040) then 65 else 0)
    (m_regions copy_fixture) (fun a => if a =? 1040 then Ro 2048 else m_aux copy_fixture a).

Example strdup_fixture_ready : InterpRuntime.ready InterpRuntime.start strdup_fixture.
Proof.
  destruct copy_fixture_ready as (Hs & Hr & Hu). split; [exact Hs|]. split; [exact Hr|].
  intros a Ha. destruct (Hu a Ha) as [_ Haux]. split.
  - change ((if (1024 <=? a) && (a <? 1040) then 65 else 0) = 0).
    assert ((a <? 1040) = false) as E by (apply Z.ltb_ge; unfold InterpRuntime.start in Ha; lia).
    rewrite E, andb_false_r. reflexivity.
  - change ((if a =? 1040 then Ro 2048 else m_aux copy_fixture a) = CNone).
    assert ((a =? 1040) = false) as E by (apply Z.eqb_neq; unfold InterpRuntime.start in Ha; lia).
    rewrite E. exact Haux.
Qed.

(** Interior starts, a partial-word NUL and empty strings use one contract. *)
Lemma strdup_fixture_domain : forall off, 0 <= off <= 16 ->
  strdup_domain strdup_fixture (mkPtr (1024 + off) (Ro 1024)) (16 - off).
Proof.
  intros off Hoff. split; [|exists 1024; split; [right; reflexivity|reflexivity]].
  split; [|lia]. split; [lia|]. split; [lia|]. split.
  - exists 1024, (mkRegion 1024 1053 Heap Live). split; [right; reflexivity|]. auto.
  - split.
    + assert ((16 - off <? 2 ^ 64 - 1) = true) as Hlt by (apply Z.ltb_lt; lia).
      rewrite Hlt. change (access_res strdup_fixture (1024 + off) (Ro 1024) (16 - off + 1) Read 1 = Some ok).
      unfold access_res, cap_access_res. cbn -[Z.add Z.sub Z.leb Z.modulo].
      assert ((1024 <=? 1024 + off) && (1024 + off + (16 - off + 1) <=? 1053) = true) as E
        by (apply andb_true_iff; split; [apply Z.leb_le|apply Z.leb_le]; lia).
      rewrite E. unfold aligned_res. rewrite Z.mod_1_r. reflexivity.
    + split.
      * intros i Hi. change (0 < (if (1024 <=? 1024 + off + i) && (1024 + off + i <? 1040) then 65 else 0) < 256).
        assert ((1024 <=? 1024 + off + i) && (1024 + off + i <? 1040) = true) as E
          by (apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
        rewrite E. lia.
      * intros _. change (m_bytes strdup_fixture (1024 + off + (16 - off)) = 0).
        replace (1024 + off + (16 - off)) with 1040 by lia. reflexivity.
Qed.

(** Actual successful calls of lengths 16, 15 and zero share the same
    unindexed registry entry, with an exact NUL-inclusive allocation. *)
Example strdup_different_lengths : forall off, off = 0 \/ off = 1 \/ off = 16 ->
  InterpExternal.invoke (strdup_contract unit) CVoid [Arg P (Const 0)]
    [WPtr (mkPtr (1024 + off) (Ro 1024))] InterpRuntime.start strdup_fixture tt []
    (CallReturn [WPtr (mkPtr (2 ^ 32) (Obj (2 ^ 32)))])
    (2 ^ 32 + req_extent (heap_req 16 (17 - off)) + 16)
    (copy_memory (allocated strdup_fixture (heap_req 16 (17 - off)) (2 ^ 32))
      (mkPtr (2 ^ 32) (Obj (2 ^ 32))) (mkPtr (1024 + off) (Ro 1024)) (17 - off)) tt.
Proof.
  intros off Hcases. replace (17 - off) with (16 - off + 1) by lia.
  eapply InterpExternal.strdup_return with (k := 16 - off).
  - split; [left; reflexivity|eexists; reflexivity].
  - apply strdup_fixture_domain. destruct Hcases as [-> | [-> | ->]]; lia.
  - destruct Hcases as [-> | [-> | ->]]; unfold max_allocation_size; lia.
  - exact strdup_fixture_ready.
  - destruct Hcases as [-> | [-> | ->]]; reflexivity.
  - apply copy_memory_result.
Qed.

(** Hand-derived cells constrain every public completion: exact
    capabilities for complete slots, phase clearing, final NUL and
    zero allocation padding. The source's own cells are unchanged. *)
Example strdup_completed_cells : forall off offset byte capability trace s' m' w',
  In (off, offset, byte, capability)
    [(0, 0, 65, Ro 2048); (0, 8, 65, Obj 2048); (0, 16, 0, CNone);
     (0, 31, 0, CNone); (1, 0, 65, CNone); (1, 15, 0, CNone); (16, 0, 0, CNone)] ->
  InterpExternal.invoke (strdup_contract unit) CVoid [Arg P (Const 0)]
    [WPtr (mkPtr (1024 + off) (Ro 1024))] InterpRuntime.start strdup_fixture tt trace
    (CallReturn [WPtr (mkPtr (2 ^ 32) (Obj (2 ^ 32)))]) s' m' w' ->
  m_bytes m' (2 ^ 32 + offset) = byte /\ m_aux m' (2 ^ 32 + offset) = capability /\
  m_bytes m' 1024 = 65 /\ m_aux m' 1024 = Ro 2048.
Proof.
  intros off offset byte capability trace s' m' w' Hcases Hcall.
  destruct (InterpExternal.strdup_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & p & k & Hargs & Hd & [(b & Hr & Hend)|(why & born & Hend & _)]); [|discriminate Hend].
  injection Hargs as <-. injection Hend as Hb. subst b.
  assert (Hoff : 0 <= off <= 16).
  { destruct Hcases as [C|[C|[C|[C|[C|[C|[C|[]]]]]]]]; injection C as <- <- <- <-; lia. }
  assert (Hk : k = 16 - off).
  { eapply terminated_length_unique; [exact (proj1 Hd)|exact (proj1 (strdup_fixture_domain off Hoff))]. }
  subst k. destruct Hr as [Hmalloc Hcopy].
  pose proof (strdup_prefix_old strdup_fixture (mkPtr (1024 + off) (Ro 1024)) (16 - off + 1)
    [2 ^ 32] m' ltac:(lia) ltac:(right; exists (2 ^ 32); split; [reflexivity|]; split; [exact Hmalloc|exact (proj1 Hcopy)]))
    as [_ Hold].
  destruct (Hold 1024 ltac:(exists 1024, (mkRegion 1024 1053 Heap Live); split; [reflexivity|simpl; lia])) as [Hsb Hsa].
  destruct (copy_result_cells _ _ _ _ _ (2 ^ 32 + offset) Hcopy) as [Hbytes Haux].
  rewrite Hbytes, Haux, Hsb, Hsa.
  destruct Hcases as [C|[C|[C|[C|[C|[C|[C|[]]]]]]]]; injection C as <- <- <- <-.
  all: repeat split; reflexivity.
Qed.

(** A fixed registry computes exact NUL-inclusive sources and request
    sizes, rather than the remainder of the source allocation. *)
Example strdup_exact_sources : forall off, 0 <= off <= 16 ->
  contract_sources (strdup_contract unit) [WPtr (mkPtr (1024 + off) (Ro 1024))] strdup_fixture tt =
    [mkSpan (mkPtr (1024 + off) (Ro 1024)) (17 - off)] /\
  contract_requests (strdup_contract unit) [WPtr (mkPtr (1024 + off) (Ro 1024))] strdup_fixture tt 16 (17 - off).
Proof.
  intros off Hoff. pose proof (terminated_string_length _ _ _ (proj1 (strdup_fixture_domain off Hoff))) as Hlen.
  split.
  - change ([mkSpan (mkPtr (1024 + off) (Ro 1024)) (string_length strdup_fixture (mkPtr (1024 + off) (Ro 1024)) + 1)] =
      [mkSpan (mkPtr (1024 + off) (Ro 1024)) (17 - off)]).
    rewrite Hlen. f_equal. f_equal. lia.
  - exists (mkPtr (1024 + off) (Ro 1024)). split; [reflexivity|]. split; [reflexivity|]. rewrite Hlen. lia.
Qed.

(** High bytes precede an early NUL; later bytes and another NUL do
    not enlarge the source span or allocation request. *)
Definition strdup_early : mem := store_bytes strlen_high_mem 1026 1 0.

Example strdup_early_span :
  contract_sources (strdup_contract unit) [WPtr hello_ptr] strdup_early tt = [mkSpan hello_ptr 3] /\
  contract_requests (strdup_contract unit) [WPtr hello_ptr] strdup_early tt 16 3 /\
  ~ contract_requests (strdup_contract unit) [WPtr hello_ptr] strdup_early tt 16 6.
Proof.
  split; [reflexivity|]. split; [exists hello_ptr; repeat split; reflexivity|].
  intros (p & Hargs & _ & Hsize). injection Hargs as <-. discriminate Hsize.
Qed.

(** Numeric exhaustion never grants string admission. Nor do null,
    one-past or expired authority become admitted empty strings. *)
Example strdup_bad_authority :
  ~ contract_pre (strdup_contract unit) [WPtr hello_ptr] high_byte_mem tt /\
  ~ contract_pre (strdup_contract unit) [WPtr (mkPtr 1030 (Ro 1024))] hello_mem tt /\
  ~ contract_pre (strdup_contract unit) [WPtr (mkPtr 0 CNone)] hello_mem tt /\
  ~ contract_pre (strdup_contract unit) [WPtr (mkPtr 1024 (Obj 1024))]
    (mkMem (fun _ => 0) [mkRegion 1024 1024 Heap Freed] (fun _ => CNone)) tt.
Proof.
  destruct strlen_bad_authority_rejected as (Hpast & Hnull & Hfreed).
  split; [|split; [|split]]; intros (p & k & Hargs & Hlength & _).
  - apply strlen_missing_nul_rejected. exists p, k. auto.
  - apply Hpast. exists p, k. auto.
  - apply Hnull. exists p, k. auto.
  - apply Hfreed. exists p, k. auto.
Qed.

(** Refusal is constructible without a success assumption. *)
Example strdup_resource_call :
  InterpExternal.invoke (strdup_contract unit) CVoid [Arg P (Const 0)] [WPtr hello_ptr]
    InterpRuntime.address_end hello_mem tt [] (CallResource OutOfMemory)
    InterpRuntime.address_end hello_mem tt.
Proof.
  eapply InterpExternal.strdup_refused with (k := 5).
  - split; [left; reflexivity|eexists; reflexivity].
  - split; [exact strlen_hello_bridge|]. exists 1024. split; [right; reflexivity|reflexivity].
  - eapply InterpExternal.failure_oom with (align := 16) (size := 6).
    + exists hello_ptr. repeat split; reflexivity.
    + unfold max_allocation_size; lia.
    + reflexivity.
Qed.

(** The same numeric address with another identity grants no string
    read. Aligned object bases are a separate conservative obligation;
    matching ABI width cannot replace a P argument with L. *)
Example strdup_identity_alignment_and_abi :
  ~ contract_pre (strdup_contract unit) [WPtr (mkPtr 1024 (Ro 2048))] hello_mem tt /\
  ~ contract_pre (strdup_contract unit) [WPtr (mkPtr 1025 (Ro 1025))]
    (mkMem (fun _ => 0) [mkRegion 1025 1030 Heap Live] (fun _ => CNone)) tt /\
  ~ strdup_abi CVoid [Arg L (Const 0)].
Proof.
  split.
  - intros (p & k & Hargs & [(Hn & Hk & _ & Ha & _) Hmax] & _). injection Hargs as <-.
    discriminate Ha.
  - split.
    + intros (p & k & Hargs & _ & b & [Hcap|Hcap] & Halign); injection Hargs as <-.
      * discriminate Hcap.
      * injection Hcap as <-. discriminate Halign.
    + intros (_ & p & Hargs). discriminate Hargs.
Qed.

(** ## Scalar string-copy controls *)

(** These calls use the ready duplication fixture: distinct source
    lengths in one registry, adjacent ranges in one object, unaligned
    operands, and a destination whose final byte receives the NUL. *)
Lemma string_copy_fixture_domain : forall d off,
  0 <= off <= 16 -> 0 <= d -> d + (17 - off) <= 29 ->
  (d + (17 - off) <= off \/ 17 <= d) ->
  string_copy_domain strdup_fixture (mkPtr (1024 + d) (Obj 1024))
    (mkPtr (1024 + off) (Ro 1024)) (16 - off).
Proof.
  intros d off Hoff Hd Hend Hsep. split.
  - exact (proj1 (strdup_fixture_domain off Hoff)).
  - split.
    + change (writable_span memset_fixture (mkSpan (mkPtr (1024 + d) (Obj 1024)) (16 - off + 1))).
      pose proof (memset_fixture_domain d 0 (16 - off + 1) Hd ltac:(lia) ltac:(lia) ltac:(lia))
        as (_ & _ & Hw & _). exact Hw.
    + change (1024 + d + (16 - off + 1) <= 1024 + off \/
        1024 + off + (16 - off + 1) <= 1024 + d).
      destruct Hsep; [left|right]; lia.
Qed.

Example string_copy_boundary_calls : forall end_return d off,
  In (d, off) [(0, 9); (1, 15); (8, 16); (21, 9)] ->
  InterpExternal.invoke (string_copy_contract end_return unit) CVoid
    [Arg P (Const 0); Arg P (Const 0)]
    [WPtr (mkPtr (1024 + d) (Obj 1024)); WPtr (mkPtr (1024 + off) (Ro 1024))]
    InterpRuntime.start strdup_fixture tt []
    (CallReturn [WPtr (copy_return end_return (mkPtr (1024 + d) (Obj 1024)) (16 - off))])
    InterpRuntime.start (string_copy_memory strdup_fixture (mkPtr (1024 + d) (Obj 1024))
      (mkPtr (1024 + off) (Ro 1024)) (16 - off + 1)) tt.
Proof.
  intros end_return d off Hcases. apply InterpExternal.string_copy_admitted.
  - split; [left; reflexivity|do 2 eexists; reflexivity].
  - apply string_copy_fixture_domain; destruct Hcases as [H|[H|[H|[H|[]]]]];
      injection H as <- <-; lia.
Qed.

(** Every completion, not just the witness: unchanged old destination
    Ro/Obj cells distinguish scalar stores from memset and memcpy.
    Source bytes, neighbours, the NUL and the exact stpcpy endpoint
    are independently fixed by this table. *)
Example string_copy_completion_cells : forall end_return d off a byte capability endpoint trace ending s' m' w',
  In (d, off, a, byte, capability, endpoint)
    [(1024, 9, 1024, 65, Ro 2048, 1031);
     (1024, 9, 1031, 0, CNone, 1031);
     (1024, 9, 1032, 65, Obj 2048, 1031);
     (1025, 15, 1024, 65, Ro 2048, 1026);
     (1025, 15, 1026, 0, CNone, 1026);
     (1025, 15, 1039, 65, CNone, 1026);
     (1032, 16, 1032, 0, Obj 2048, 1032);
     (1045, 9, 1040, 0, Ro 2048, 1052);
     (1045, 9, 1052, 0, CNone, 1052)] ->
  InterpExternal.invoke (string_copy_contract end_return unit) CVoid
    [Arg P (Const 0); Arg P (Const 0)]
    [WPtr (mkPtr d (Obj 1024)); WPtr (mkPtr (1024 + off) (Ro 1024))]
    InterpRuntime.start strdup_fixture tt trace ending s' m' w' ->
  m_bytes m' a = byte /\ m_aux m' a = capability /\
    ending = CallReturn [WPtr (if end_return then mkPtr endpoint (Obj 1024) else mkPtr d (Obj 1024))].
Proof.
  intros end_return d off a byte capability endpoint trace ending s' m' w' Hcases Hcall.
  destruct (InterpExternal.string_copy_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & dst & src & k & Hargs & Hd & Hresult & Hend).
  injection Hargs as <- <-.
  assert (Hoff : 0 <= off <= 16).
  { destruct Hcases as [H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]; injection H as <- <- <- <- <- <-; lia. }
  assert (Hk : k = 16 - off).
  { eapply terminated_length_unique; [exact (proj1 Hd)|exact (proj1 (strdup_fixture_domain off Hoff))]. }
  subst k. destruct (string_copy_cells _ _ _ _ _ a Hresult) as [Hb Ha]. rewrite Hb, Ha, Hend.
  destruct Hcases as [H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]; injection H as <- <- <- <- <- <-;
    destruct end_return; vm_compute; repeat split; reflexivity.
Qed.

(** Without auxiliary writes, neither object base needs alignment.
    A readable source is not a writable destination, even at equal bits. *)
Example string_copy_unaligned_bases :
  string_copy_domain
    (mkMem (fun _ => 0) [mkRegion 1025 1030 Heap Live; mkRegion 2049 2052 Heap Live] (fun _ => CNone))
    (mkPtr 2049 (Obj 2049)) (mkPtr 1025 (Ro 1025)) 0.
Proof.
  split.
  - split; [|lia]. split; [lia|]. split; [lia|]. split.
    + exists 1025, (mkRegion 1025 1030 Heap Live). split; [right; reflexivity|]. auto.
    + split; [reflexivity|]. split; [intros i Hi; lia|intros; reflexivity].
  - split.
    + split; [change (0 <= 1); lia|].
      exists 2049, (mkRegion 2049 2052 Heap Live). repeat split; reflexivity.
    + right. simpl. lia.
Qed.

Example string_copy_bad_destination_and_abi :
  ~ contract_pre (strcpy_contract unit)
    [WPtr (mkPtr 1024 (Ro 1024)); WPtr (mkPtr 1033 (Ro 1024))] strdup_fixture tt /\
  ~ contract_pre (stpcpy_contract unit)
    [WPtr (mkPtr 1024 (Obj 1024)); WPtr (mkPtr 1024 (Ro 1024))] strdup_fixture tt /\
  ~ string_copy_abi CVoid [Arg P (Const 0); Arg L (Const 0)].
Proof.
  split.
  - intros (d & src & k & Hargs & _ & (_ & b & reg & Hcap & _) & _).
    injection Hargs as <- <-. discriminate Hcap.
  - split.
    + intros (d & src & k & Hargs & Hlength & _ & Hsep). injection Hargs as <- <-.
      pose proof (terminated_length_unique _ _ _ _ Hlength
        (proj1 (strdup_fixture_domain 0 ltac:(lia)))) as Hk.
      change (k = 16) in Hk. subst k.
      change (1041 <= 1024 \/ 1041 <= 1024) in Hsep. destruct Hsep; lia.
    + intros (_ & d & src & Hargs). discriminate Hargs.
Qed.
