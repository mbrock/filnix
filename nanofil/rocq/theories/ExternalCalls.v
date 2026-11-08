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

(** memchr admits a canonical int bit pattern and size_t count, with a
    live capability reading the entire count of well-formed bytes.
    Unlike [bounded_length], an early match does not shorten this
    premise. Zero count still needs live authority, possibly one-past. *)
Definition memchr_input (m : mem) (p : ptr) (c n : Z) : Prop :=
  0 <= c < 2 ^ 32 /\ 0 <= n < 2 ^ 64 /\
  (exists base reg, (ptr_cap p = Obj base \/ ptr_cap p = Ro base) /\
    object_region base (m_regions m) = Some reg /\ r_life reg = Live) /\
  access_res m (ptr_addr p) (ptr_cap p) n Read 1 = Some ok /\
  (forall i, 0 <= i < n -> 0 <= m_bytes m (ptr_addr p + i) < 256).

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
    input domain and readable span, not a supplied result or invocation. *)
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
    a first-match witness in its precondition. Not native termination. *)
Theorem memchr_admitted : forall world r args p c n s m (w : world),
  memchr_abi r args -> memchr_input m p c n ->
  exists q, invoke (memchr_contract world) r args [WPtr p; WInt c; WInt n] s m w
    [] (CallReturn [WPtr q]) s m w.
Proof.
  intros world r args p c n s m w Habi Hinput.
  destruct (memchr_result_total m p c n ltac:(destruct Hinput as (_ & Hn & _); lia)) as [q Hq].
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

(** A ready memchr input's entire interval fits in the address space;
    unlike [bounded_length_extent], this includes the full maximum. *)
Lemma memchr_input_extent : forall s m p c n,
  R.ready s m -> memchr_input m p c n ->
  0 <= ptr_addr p /\ ptr_addr p + n <= 2 ^ 48.
Proof.
  intros s m p c n Hr (_ & _ & (base & reg & Hcap & Hreg & _) & Ha & _).
  pose proof (R.address_space s m Hr base reg Hreg) as [Hb Hend].
  unfold access_res in Ha. destruct Hcap as [Hcap | Hcap]; rewrite Hcap in Ha;
    cbn in Ha; rewrite Hreg in Ha.
  all: destruct ((base <=? ptr_addr p) && (ptr_addr p + n <=? r_end reg)) eqn:E;
    [|discriminate].
  all: apply andb_true_iff in E; destruct E as [Hlo Hhi];
    apply Z.leb_le in Hlo; apply Z.leb_le in Hhi; lia.
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

(** The ready high-byte fixture admits any canonical int argument,
    including values whose unsigned-char conversion changes them. *)
Lemma memchr_high_input : forall c, 0 <= c < 2 ^ 32 ->
  memchr_input high_byte_mem hello_ptr c 6.
Proof.
  intros c Hc. split; [exact Hc|]. split; [vm_compute; split; congruence|]. split.
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
  - split; [vm_compute; split; congruence|]. split; [vm_compute; split; congruence|]. split.
    + exists 1024, (mkRegion 1024 1030 GlobalData Live). split; [right; reflexivity|]. auto.
    + split; [reflexivity|]. intros; lia.
  - right. split; [intros; lia|reflexivity].
Qed.

(** A match in the first byte does not waive an unreadable suffix. *)
Example memchr_full_span_required : ~ memchr_input high_byte_mem hello_ptr 128 7.
Proof. intros (_ & _ & _ & Ha & _). discriminate Ha. Qed.

(** Null and freed authority are not admitted even at zero count. *)
Example memchr_zero_invalid_rejected :
  (forall m, ~ memchr_input m (mkPtr 0 CNone) 0 0) /\
  ~ memchr_input (mkMem (fun _ => 0) [mkRegion 1024 1024 Heap Freed] (fun _ => CNone))
    (mkPtr 1024 (Obj 1024)) 0 0.
Proof.
  split.
  - intros m (_ & _ & (base & reg & [Hcap | Hcap] & _) & _); discriminate Hcap.
  - intros (_ & _ & (base & reg & [Hcap | Hcap] & Hreg & Hlife) & _);
      [injection Hcap as <-; injection Hreg as <-; discriminate Hlife|discriminate Hcap].
Qed.

(** Wrong ABI classes and unnormalized scalar words fail independently
    of whether a finite search result can be described. *)
Example memchr_bad_domain_rejected :
  ~ memchr_abi (CResult (TAtom "found") L) [Arg P (Const 0); Arg W (Const 0); Arg L (Const 0)] /\
  ~ memchr_abi CVoid [Arg P (Const 0); Arg L (Const 0); Arg L (Const 0)] /\
  ~ memchr_input high_byte_mem hello_ptr (-1) 6.
Proof.
  split; [intros [[H | (d & H)] _]; discriminate H|]. split.
  - intros [_ (p & c & n & H)]. discriminate H.
  - intros (Hc & _). lia.
Qed.
