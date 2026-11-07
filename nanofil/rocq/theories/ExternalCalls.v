(** Campaign 4's trusted external-call boundary (docs/libc-contracts.md).

    Contracts describe libc; they do not implement or prove it. A call
    must establish its ABI and semantic premises. A missing premise is
    an unmet obligation, not a proof that native libc necessarily traps.
    In-contract calls may return, terminate, or exhaust resources, but
    cannot produce Unchecked or a capability panic.

    Memory effects are finite paths: bounded writes and authorized heap
    releases alternate with allocations by an arbitrary Runtime. Each
    prefix preserves readiness and object identities. No new assumption
    is added to Runtime, and the existing Machine is unchanged.

    StreamBytes records bytes accepted by stdio, possibly buffered; it
    is deliberately NOT a kernel write. Flush and exit handlers still
    need their own contracts before a whole-program trace is closed. *)

From Stdlib Require Import String ZArith List Bool Lia Relations.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Machine Identity.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Authority and footprints *)

Record span : Type := mkSpan { span_ptr : ptr; span_size : Z }.

Definition span_contains (s : span) (a : Z) : Prop :=
  ptr_addr (span_ptr s) <= a < ptr_addr (span_ptr s) + span_size s.

(** An explicit live, writable capability, including for a zero span.
    The life test matters for zero-length spans of freed objects. *)
Definition writable_span (m : mem) (s : span) : Prop :=
  0 <= span_size s /\
  exists base reg,
    ptr_cap (span_ptr s) = Obj base /\
    object_region base (m_regions m) = Some reg /\ r_life reg = Live /\
    access_res m (ptr_addr (span_ptr s)) (Obj base) (span_size s) Write 1 = Some ok.

(** Born objects belong to this call; old objects require an explicit
    root supplied by the contract. Auxiliary writes use the same roots
    but need not have the same byte footprint (partial memset, etc.). *)
Definition write_authority (roots : list span) (born : list Z) (m : mem) (a : Z) : Prop :=
  (exists s, In s roots /\ writable_span m s /\ span_contains s a) \/
  (exists base reg, In base born /\ object_region base (m_regions m) = Some reg /\
    r_kind reg = Heap /\ r_life reg = Live /\ base <= a < r_end reg).

(** A capability is copied, loaded through a designated readable root,
    or minted by this call's allocator. In particular, Ro never becomes
    Obj merely because their address bits coincide. Contracts needing
    pointer-copy smidgens must extend this complete-slot rule first. *)
Definition available_cap (sources : list span) (born : list Z) (m : mem) (c : cap) : Prop :=
  c = CNone \/
  (exists s, In s sources /\ c = ptr_cap (span_ptr s)) \/
  (exists s a, In s sources /\ span_contains s a /\
    a + 8 <= ptr_addr (span_ptr s) + span_size s /\
    access_res m a (ptr_cap (span_ptr s)) 8 Read 8 = Some ok /\ c = m_aux m a) \/
  (exists base, In base born /\ (c = Obj base \/ c = Ro base)).

Lemma write_authority_in : forall roots born m a,
  write_authority roots born m a -> in_object m a.
Proof.
  intros roots born m a [(s & _ & (_ & base & reg & Hcap & Hr & _ & Ha) & Hin) |
                        (base & reg & _ & Hr & _ & _ & Hin)].
  - eapply access_in; [exact Ha | exact Hin].
  - exists base, reg. auto.
Qed.

(** Byte and shadow footprints are independent, but every changed cell
    needs write authority, and a changed stored capability needs a
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

Lemma local_effect_kept : forall sources roots releases born m m',
  local_effect sources roots releases born m m' -> kept m m'.
Proof.
  intros sources roots releases born m m' (_ & Hr & Hw & _). split.
  - intros b reg' H. destruct (Hr _ _ H) as (reg & E & [-> | (_ & Hk & Hl & ->)]).
    + exists reg. auto.
    + exists reg. split; auto. right. rewrite Hk. auto.
  - intros a Hout. apply Hw. intros Ha. apply Hout. eapply write_authority_in; eauto.
Qed.

Lemma local_effect_refl : forall sources roots releases born m,
  local_effect sources roots releases born m m.
Proof.
  intros. split; [apply ids_refl|]. split; [intros b reg E; exists reg; auto |]. auto.
Qed.

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

(** ## Events and contract results *)

Inductive event : Type :=
| StreamBytes (stream : Z) (bytes : list Z)
| ProcessExit (status : Z).

Inductive call_end : Type :=
| CallReturn (values : list word)
| CallExit (status : Z)
| CallResource (why : reason).

Definition resource_reason (why : reason) : Prop :=
  why = OutOfMemory \/ why = TooBig.

(** Keep the declared return shape: an empty/singleton tuple is not a
    void/scalar return. The machine adapter must use this signature,
    not words_outcome's list-length convention. *)
Definition return_shape (ty : ret_type) (values : list word) : Prop :=
  match ty with
  | RVoid => values = []
  | RClass k => exists x, values = [x] /\ word_at_class k x = Some x
  | RTuple ks => Forall2 (fun k x => word_at_class k x = Some x) ks values
  end.

Definition word_authority (sources : list span) (born : list Z) (m : mem) (x : word) : Prop :=
  match x with
  | WPtr p => available_cap sources born m (ptr_cap p)
  | WLimit c _ => available_cap sources born m c
  | WInt _ => True
  end.

(** A contract separates the ABI, its caller obligations, write/release
    authority, normal outcomes and its resource endings. The panic set
    documents checks reachable outside the premises; it does not grant
    a transition when a premise fails. *)
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

(** ## Memory paths over any runtime *)

Module ExternalCalls (R : Runtime).

(** Each allocation extends the call's private authority. It cannot
    claim an existing object's identity: fresh_allocation proves that
    from readiness. The list is historical, so freed identities never
    become available for reuse. *)
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

(** This is a prefix theorem as well as an endpoint theorem: every
    finite prefix is itself an effects derivation. *)
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

(** Prefixes do not require an eventual return: a blocking call may
    have these finite observations. Concrete prefix coverage is trusted,
    not established by the structural preservation theorem. *)
Definition prefix {world : Type} (spec : contract world) xs s m w born trace s' m' w' : Prop :=
  effects (contract_sources spec xs m w) (contract_writes spec xs m w)
    (contract_releases spec xs m w) (contract_requests spec xs m w) s m [] s' m' born /\
  contract_prefix spec xs m w born trace m' w'.

Theorem prefix_preserve : forall world (spec : contract world) xs s m w born trace s' m' w',
  prefix spec xs s m w born trace s' m' w' -> R.ready s m ->
  R.ready s' m' /\ persists m m'.
Proof. intros world spec xs s m w born trace s' m' w' [He _] Hr. eapply effects_preserve; eauto. Qed.

(** Compare the original requested size, BEFORE heap_req rounds it up,
    exactly as Ops.v does. A legal size 2^48-1 has extent 2^48, and may
    be refused by a runtime, but is not TooBig. *)
Inductive resource_failure (requests : Z -> Z -> Prop) (s : R.state) : reason -> Prop :=
| failure_oom : forall align size,
    requests align size -> 0 <= size <= max_allocation_size ->
    R.alloc s (heap_req align size) = None -> resource_failure requests s OutOfMemory
| failure_big : forall align size,
    requests align size -> max_allocation_size < size ->
    resource_failure requests s TooBig.

(** No rule turns a failed precondition into success or a native trap.
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

Theorem invoke_prefix : forall world (spec : contract world) r args xs s m w trace ending s' m' w',
  invoke spec r args xs s m w trace ending s' m' w' ->
  exists born, prefix spec xs s m w born trace s' m' w'.
Proof. intros. destruct H; eauto. Qed.

Theorem invoke_preserve : forall world (spec : contract world) r args xs s m w trace ending s' m' w',
  invoke spec r args xs s m w trace ending s' m' w' -> R.ready s m ->
  R.ready s' m' /\ persists m m'.
Proof.
  intros world spec r args xs s m w trace ending s' m' w' H Hr.
  destruct (invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ H) as (born & He & _).
  eapply effects_preserve; eauto.
Qed.

(** Boundary checks use the caller's size, not the rounded extent.
    Successful allocation remains conditional on the runtime's answer. *)
Example rounded_maximum_extent :
  req_extent (heap_req 16 max_allocation_size) = 2 ^ 48.
Proof. reflexivity. Qed.

Example rounded_maximum_allocation : forall s m base s',
  R.alloc s (heap_req 16 max_allocation_size) = Some (base, s') ->
  effects [] [] [] (fun align size => align = 16 /\ size = max_allocation_size)
    s m [] s' (allocated m (heap_req 16 max_allocation_size) base) [base].
Proof.
  intros s m base s' Ha. eapply effects_alloc;
    [split; reflexivity | unfold max_allocation_size; lia | exact Ha | constructor].
Qed.

Example rounded_maximum_not_too_big : forall s,
  ~ resource_failure (fun align size => align = 16 /\ size = max_allocation_size) s TooBig.
Proof.
  intros s H. inversion H as [align size Hreq Hbound Ha | align size Hreq Hbig].
  destruct Hreq as [_ ->]. lia.
Qed.

Example oversized_request : forall s,
  resource_failure (fun align size => align = 16 /\ size = 2 ^ 48) s TooBig.
Proof.
  intros s. eapply failure_big with (align := 16) (size := 2 ^ 48);
    [split; reflexivity | unfold max_allocation_size; lia].
Qed.

End ExternalCalls.

(** ## The first contract: puts *)

(** The first NUL is within a readable capability. There is no bound
    on the length in the contract; examples' short strings are fixtures. *)
Fixpoint string_at (m : mem) (a : Z) (bytes : list Z) : Prop :=
  match bytes with
  | [] => m_bytes m a = 0
  | b :: rest => 0 < b < 256 /\ m_bytes m a = b /\ string_at m (a + 1) rest
  end.

Definition c_string (m : mem) (p : ptr) (bytes : list Z) : Prop :=
  access_res m (ptr_addr p) (ptr_cap p) (Z.of_nat (length bytes) + 1) Read 1 = Some ok /\
  string_at m (ptr_addr p) bytes.

(** This small world records only the currently modeled stream's
    usability and reachable writable libc roots (stdout, errno, buffer).
    Establishing those roots at startup remains an entry obligation.
    It does not claim that an arbitrary writable object is a FILE. *)
Record stdio_world : Type := mkStdioWorld {
  stdout_usable : bool;
  stdio_roots : list span
}.

Definition stdio_ready (m : mem) (w : stdio_world) : Prop :=
  stdout_usable w = true /\ Forall (writable_span m) (stdio_roots w).

Definition puts_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d W) /\ exists v, args = [Arg P v].

(** rep is the trusted relation between the abstract stream state and
    its memory representation, including ownership and pointer sources.
    No concrete FILE representation/startup instance is claimed here. *)
Definition puts_pre (rep : mem -> stdio_world -> Prop)
    (xs : list word) (m : mem) (w : stdio_world) : Prop :=
  rep m w /\ stdio_ready m w /\ exists p bytes, xs = [WPtr p] /\ c_string m p bytes.

(** A call may retain newly allocated buffers, but cannot acquire write
    authority to an unrelated old object by changing the logical world. *)
Definition stdio_delegates (roots : list span) (born : list Z) (m : mem) (w : stdio_world) : Prop :=
  forall s, In s (stdio_roots w) ->
    available_cap roots born m (ptr_cap (span_ptr s)) /\
    forall a, span_contains s a -> write_authority roots born m a.

Lemma stdio_delegates_refl : forall roots born m w,
  stdio_roots w = roots -> Forall (writable_span m) roots -> stdio_delegates roots born m w.
Proof.
  intros roots born m w <- Hroots s Hin. split.
  - right. left. exists s. auto.
  - intros a Ha. left. exists s. split; auto. split; auto.
    rewrite Forall_forall in Hroots. apply Hroots. exact Hin.
Qed.

Definition puts_prefix (rep : mem -> stdio_world -> Prop)
    (xs : list word) (m : mem) (w : stdio_world) (born : list Z)
    (trace : list event) (m' : mem) (w' : stdio_world) : Prop :=
  rep m' w' /\ stdio_ready m' w' /\ stdio_delegates (stdio_roots w) born m' w' /\
  (trace = [] \/ exists p bytes accepted tail,
    xs = [WPtr p] /\ c_string m p bytes /\ bytes ++ [10] = accepted ++ tail /\
    trace = [StreamBytes 1 accepted]).

(** Successful acceptance is the whole string plus newline. On an I/O
    error, any prefix may have been accepted (including all of it).
    EOF is -1 at this glibc pin, represented as unsigned class w bits.
    Neither event says that the bytes have reached a file descriptor. *)
Definition puts_post (xs : list word) (m : mem) (w : stdio_world) (born : list Z)
    (trace : list event) (ending : call_end) (m' : mem) (w' : stdio_world) : Prop :=
  exists p bytes accepted tail result,
    xs = [WPtr p] /\ c_string m p bytes /\
    bytes ++ [10] = accepted ++ tail /\
    ((tail = [] /\ 0 <= result < 2 ^ 31) \/ result = 2 ^ 32 - 1) /\
    trace = [StreamBytes 1 accepted] /\ ending = CallReturn [WInt result] /\
    stdio_ready m' w'.

Definition puts_panic (why : reason) : Prop :=
  In why [NullCapability; OutOfBounds; Misaligned; Readonly; ArgumentSize; ReturnSize].

Definition puts_contract (rep : mem -> stdio_world -> Prop)
    (requests : list word -> mem -> stdio_world -> Z -> Z -> Prop) : contract stdio_world :=
  mkContract stdio_world (RClass W) puts_abi (puts_pre rep)
    (fun _ _ w => stdio_roots w)
    (fun _ _ w => stdio_roots w) (fun _ _ _ => [])
    requests (puts_prefix rep) puts_post resource_reason puts_panic.

(** ## Contract boundary checks *)

Lemma puts_no_capability_panic : forall rep requests why,
  contract_resource (puts_contract rep requests) why -> ~ puts_panic why.
Proof.
  intros rep requests why [-> | ->]; unfold puts_panic; simpl; intuition discriminate.
Qed.

Lemma puts_null_not_admissible : forall m bytes,
  ~ c_string m (mkPtr 0 CNone) bytes.
Proof. intros m bytes [H _]. discriminate H. Qed.

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

Module InterpExternal := ExternalCalls InterpRuntime.

(** An abstract stream-state fixture, not a native FILE implementation.
    String, libc state and an unrelated caller object are asymmetric. *)
Definition hello_bytes : list Z := [104; 101; 108; 108; 111].
Definition hello_ptr : ptr := mkPtr 1024 (Ro 1024).
Definition stdout_span : span := mkSpan (mkPtr 2048 (Obj 2048)) 16.
Definition hello_world : stdio_world := mkStdioWorld true [stdout_span].
Definition hello_mem : mem :=
  mkMem (fun a => if a =? 1024 then 104 else if a =? 1025 then 101 else
                   if a =? 1026 then 108 else if a =? 1027 then 108 else
                   if a =? 1028 then 111 else 0)
    [mkRegion 1024 1030 GlobalData Live; mkRegion 2048 2064 Heap Live;
     mkRegion 3072 3080 Heap Live] (fun _ => CNone).

Definition fixture_rep (m : mem) (w : stdio_world) : Prop :=
  w = hello_world /\ object_region 2048 (m_regions m) = Some (mkRegion 2048 2064 Heap Live).

Definition fixture_requests (_ : list word) (_ : mem) (_ : stdio_world) (align size : Z) : Prop :=
  align = 16 /\ size = 32.

Lemma hello_string : c_string hello_mem hello_ptr hello_bytes.
Proof. vm_compute. repeat split; lia. Qed.

Lemma hello_stdio : stdio_ready hello_mem hello_world.
Proof.
  split; [reflexivity|]. constructor; [|constructor].
  split; [simpl; lia|]. exists 2048, (mkRegion 2048 2064 Heap Live).
  repeat split; reflexivity.
Qed.

Lemma hello_pre : puts_pre fixture_rep [WPtr hello_ptr] hello_mem hello_world.
Proof.
  split; [split; reflexivity|]. split; [exact hello_stdio|].
  exists hello_ptr, hello_bytes. split; [reflexivity|exact hello_string].
Qed.

(** Success and both empty/nonempty partial EOF results use the same
    public call relation. No allocation or kernel write is required. *)
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

Example hello_success :
  InterpExternal.invoke (puts_contract fixture_rep fixture_requests)
    CVoid [Arg P (Const 0)] [WPtr hello_ptr]
    InterpRuntime.start hello_mem hello_world
    [StreamBytes 1 [104; 101; 108; 108; 111; 10]] (CallReturn [WInt 0])
    InterpRuntime.start hello_mem hello_world.
Proof. apply (hello_return _ []); [reflexivity | left; auto]. Qed.

Example hello_eof_empty :
  InterpExternal.invoke (puts_contract fixture_rep fixture_requests)
    CVoid [Arg P (Const 0)] [WPtr hello_ptr]
    InterpRuntime.start hello_mem hello_world
    [StreamBytes 1 []] (CallReturn [WInt (2 ^ 32 - 1)])
    InterpRuntime.start hello_mem hello_world.
Proof. apply (hello_return _ (hello_bytes ++ [10])); [reflexivity | right; reflexivity]. Qed.

Example hello_eof_partial :
  InterpExternal.invoke (puts_contract fixture_rep fixture_requests)
    CVoid [Arg P (Const 0)] [WPtr hello_ptr]
    InterpRuntime.start hello_mem hello_world
    [StreamBytes 1 [104; 101]] (CallReturn [WInt (2 ^ 32 - 1)])
    InterpRuntime.start hello_mem hello_world.
Proof. apply (hello_return _ [108; 108; 111; 10]); [reflexivity | right; reflexivity]. Qed.

Example hello_eof_full :
  InterpExternal.invoke (puts_contract fixture_rep fixture_requests)
    CVoid [Arg P (Const 0)] [WPtr hello_ptr]
    InterpRuntime.start hello_mem hello_world
    [StreamBytes 1 (hello_bytes ++ [10])] (CallReturn [WInt (2 ^ 32 - 1)])
    InterpRuntime.start hello_mem hello_world.
Proof. apply (hello_return _ []); [reflexivity | right; reflexivity]. Qed.

Example internal_allocation :
  InterpExternal.effects [stdout_span] [stdout_span] []
    (fixture_requests [] hello_mem hello_world)
    InterpRuntime.start hello_mem [] (2 ^ 32 + 48)
    (allocated hello_mem (heap_req 16 32) (2 ^ 32)) [2 ^ 32].
Proof.
  eapply InterpExternal.effects_alloc; [split; reflexivity |
    unfold max_allocation_size; simpl; lia | reflexivity | constructor].
Qed.

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

(** These are negative contract obligations, not invented native traps. *)
Example missing_nul : ~ c_string hello_mem hello_ptr (hello_bytes ++ [65]).
Proof. intros [H _]. discriminate H. Qed.

(** All six bytes are readable, but the sixth is not a terminator. *)
Definition nonzero_mem : mem :=
  mkMem (fun _ => 65) (m_regions hello_mem) (m_aux hello_mem).

Example nonzero_readable : access_res nonzero_mem 1024 (Ro 1024) 6 Read 1 = Some ok.
Proof. reflexivity. Qed.

Example missing_nul_in_bounds : ~ c_string nonzero_mem hello_ptr [65; 65; 65; 65; 65].
Proof. intros [_ H]. vm_compute in H. intuition discriminate. Qed.

Example no_zero_span_root_injection :
  ~ stdio_delegates [stdout_span] [] hello_mem
    (mkStdioWorld true [stdout_span; mkSpan (mkPtr 1024 (Obj 1024)) 0]).
Proof.
  intros H. destruct (H (mkSpan (mkPtr 1024 (Obj 1024)) 0) (or_intror (or_introl eq_refl))) as [Ha _].
  destruct Ha as [Hc | [(s & [<- | []] & Hc) |
    [(s & a & [<- | []] & _ & _ & _ & Hc) | (b & [] & _)]]]; discriminate Hc.
Qed.

Example no_unrelated_root_coverage :
  ~ stdio_delegates [stdout_span] [] hello_mem
    (mkStdioWorld true [mkSpan (mkPtr 2048 (Obj 2048)) 2048]).
Proof.
  intros H. destruct (H (mkSpan (mkPtr 2048 (Obj 2048)) 2048) (or_introl eq_refl)) as [_ Hw].
  assert (Hin : span_contains (mkSpan (mkPtr 2048 (Obj 2048)) 2048) 3072) by (unfold span_contains; simpl; lia).
  destruct (Hw 3072 Hin) as [(s & [<- | []] & _ & Ha) | (b & reg & [] & _)].
  unfold span_contains in Ha. simpl in Ha. lia.
Qed.

Example no_unrelated_write :
  ~ local_effect [stdout_span] [stdout_span] [] [] hello_mem (store_bytes hello_mem 3072 1 7).
Proof.
  intros (_ & _ & Hw & _).
  assert (Hn : ~ write_authority [stdout_span] [] hello_mem 3072).
  { intros [(s & [<- | []] & _ & Hin) | (b & reg & [] & _)]; unfold span_contains in Hin; simpl in Hin; lia. }
  destruct (Hw _ Hn) as [Hb _]. discriminate Hb.
Qed.

Example no_forged_capability :
  ~ local_effect [stdout_span] [stdout_span] [] [] hello_mem (store_aux hello_mem 2048 (Obj 3072)).
Proof.
  intros (_ & _ & _ & Haux). destruct (Haux 2048) as [H | H]; [discriminate H|].
  destruct H as [H | [(s & [<- | []] & H) | [(s & a & [<- | []] & _ & _ & _ & H) | (b & [] & _)]]];
    discriminate H.
Qed.

Example no_readonly_upgrade :
  ~ available_cap [mkSpan hello_ptr 6] [] hello_mem (Obj 1024).
Proof.
  intros [H | [(s & [<- | []] & H) | [(s & a & [<- | []] & _ & _ & _ & H) | (b & [] & _)]]];
    discriminate H.
Qed.

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

Example no_write_after_release :
  ~ write_authority [mkSpan (mkPtr 3072 (Obj 3072)) 8] [3072]
    (mkMem (fun _ => 0) [mkRegion 3072 3072 Heap Freed] (fun _ => CNone)) 3072.
Proof.
  intros [(s & [<- | []] & (_ & b & reg & Hcap & Hr & Hl & _) & _) |
          (b & reg & [<- | []] & Hr & _ & Hl & _)]; simpl in *.
  - injection Hcap as <-. injection Hr as <-. discriminate Hl.
  - injection Hr as <-. discriminate Hl.
Qed.
