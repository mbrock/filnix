(** Hello's composite trusted libc boundary. One locale/stdio/errno/getopt
    payload accompanies the existing authoritative shutdown state;
    there is no second output queue or callback inventory. The conversion
    contract describes logical represented endpoints, not every native
    instruction or collector prefix. Libc satisfaction remains trusted. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics
  ExternalCalls LibcCalls ExternalMachine Locale Stdio Shutdown Getopt.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** A represented FILE's handle, physical pending count and private
    storage. No logical output queue is stored in this record. Owned
    heaps exclude static FILE objects and caller setvbuf storage. *)
Record libc_file : Type := mkLibcFile {
  file_handle : ptr;
  file_pending : Z;
  file_reads : list span;
  file_roots : list span;
  file_owned : list Z
}.

(** Stdout's open flag remains [stdout_usable], and its protocol remains
    [shutdown_stdout]. Stderr has its own protocol and open flag. These
    fields supply the physical information absent from [stdio_world]. *)
Record libc_stream_inventory : Type := mkLibcStreams {
  libc_stdout_file : libc_file;
  libc_stderr_file : libc_file;
  libc_stderr_open : bool;
  libc_stderr_state : stream_state
}.

Record libc_payload : Type := mkLibcPayload {
  libc_locale : locale_world;
  libc_stdio : stdio_world;
  libc_errno : ptr;
  libc_streams : libc_stream_inventory;
  libc_getopt : getopt_world
}.

(** Definitionally the payload * shutdown_state used by Linked. *)
Definition libc_world : Type := (libc_payload * shutdown_state)%type.

(** Parser state is an independent component of the same libc world;
    optarg and optind may evolve without changing locale or stdout. *)
Definition libc_getopt_view (w : libc_world) : getopt_world := libc_getopt (fst w).

(** The full representation owns coherent libc/TLS state and exclusive
    private release rights. Structural facts alone do not establish it.
    In a callback, uniqueness is not evidence that its token was popped.
    Readiness does not require stdout open: errno lookup, locale and
    conversion remain valid after fclose. Output admits an open handle
    separately. Retired stdio roots must be removed, not kept writable. *)
Definition libc_ready (rep : mem -> libc_world -> Prop) m w : Prop :=
  rep m w /\
  locale_ready (fun _ _ => True) m (libc_locale (fst w)) /\
  Forall (writable_span m) (stdio_roots (libc_stdio (fst w))) /\ errno_cell m (libc_errno (fst w)) /\
  stream_wf (shutdown_stdout (snd w)) /\ shutdown_unique (snd w) /\
  -(2 ^ 31) <= shutdown_status (snd w) < 2 ^ 31 /\
  match shutdown_at (snd w) with
  | InCallback active => In (registration_token active) (shutdown_consumed (snd w))
  | _ => True
  end.

(** Native initialization/continuation is an independent premise, not a
    consequence of the exposed option cells. Errno uses the existing TLS
    cell, not a second cell. Native representation and call admission
    must also justify separation from locale/stdout storage: a pure world
    frame is not a native-memory or cross-pool ownership frame. *)
Definition libc_getopt_rep (initialized : mem -> libc_world -> Prop) m w : Prop :=
  libc_ready initialized m w /\
  getopt_errno_cell (libc_getopt_view w) = libc_errno (fst w).

(** A separate native predicate permits unfinished parser state at a
    logical prefix. Completed public-cell coherence is required only by
    getopt_pre/post. Ordinary endpoints must satisfy BOTH running and
    initialized predicates; no implication between them is assumed. *)
Definition libc_getopt_inflight (running : mem -> libc_world -> Prop) m w : Prop :=
  libc_ready running m w /\
  getopt_errno_cell (libc_getopt_view w) = libc_errno (fst w).

(** Preserve the one locale/stdout/shutdown inventory and TLS identity.
    Diagnostic stderr retains its handle/open flag but may change private
    storage and protocol. This relation deliberately does not relate its
    FIFO to the trace, even when the trace is empty. *)
Definition libc_getopt_stable (w w' : libc_world) : Prop :=
  libc_locale (fst w') = libc_locale (fst w) /\
  libc_stdio (fst w') = libc_stdio (fst w) /\
  libc_errno (fst w') = libc_errno (fst w) /\ snd w' = snd w /\
  libc_stdout_file (libc_streams (fst w')) = libc_stdout_file (libc_streams (fst w)) /\
  file_handle (libc_stderr_file (libc_streams (fst w'))) =
    file_handle (libc_stderr_file (libc_streams (fst w))) /\
  libc_stderr_open (libc_streams (fst w')) = libc_stderr_open (libc_streams (fst w)).

(** Conservative safety binding over this same world, with no machine
    application. Native/consumer obligations still include diagnostic
    trace/protocol correspondence, stream readiness and cross-call parser
    continuity (including refreshed errno). Other libc contracts do not
    freeze this entire parser record. Input and registry are fixed for
    one launch after startup witnesses are chosen, not per permutation. *)
Definition libc_getopt_contract input initialized running
    (requests : list word -> mem -> libc_world -> Z -> Z -> Prop) : contract libc_world :=
  getopt_contract input libc_getopt_view (libc_getopt_rep initialized)
    (libc_getopt_inflight running) libc_getopt_stable requests.

(** A functional ordinary-return binding over the same payload and
    authority as [libc_getopt_contract]. Its transition must be justified
    separately; it does not follow from the safety representation. *)
Definition libc_getopt_refined_contract input initialized running
    (requests : list word -> mem -> libc_world -> Z -> Z -> Prop)
    (transition : list word -> mem -> libc_world -> list Z -> list event ->
      list word -> mem -> libc_world -> Prop) : contract libc_world :=
  getopt_refined_contract input libc_getopt_view (libc_getopt_rep initialized)
    (libc_getopt_inflight running) libc_getopt_stable requests transition.

(** Borrowed-name facts survive projection through the composite world.
    No separate ghost copy of the locale names is introduced here. *)
Lemma libc_name : forall rep m w category,
  libc_ready rep m w -> In category locale_categories ->
  ptr_addr (locale_name (libc_locale (fst w)) category) <> 0 /\
  c_string m (locale_name (libc_locale (fst w)) category)
    (locale_text (libc_locale (fst w)) category) /\
  exists base,
    (ptr_cap (locale_name (libc_locale (fst w)) category) = Obj base \/
     ptr_cap (locale_name (libc_locale (fst w)) category) = Ro base) /\ base mod 8 = 0.
Proof.
  intros rep m w category (_ & Hlocale & _) Hcategory.
  destruct Hlocale as (_ & _ & Hnames & _ & _ & Haligned).
  destruct (Hnames category Hcategory) as [Hnonnull Hstring].
  split; [exact Hnonnull|]. split; [exact Hstring|exact (Haligned category Hcategory)].
Qed.

(** These two labels identify the independently audited profiles, not
    strings from which converter behavior can be inferred. The supplied
    audit maps opaque codec identities to actual selected converters. *)
Inductive audited_codec : Type := CodecC | CodecCUtf8.

Definition audited_codec_name (kind : audited_codec) : list Z :=
  match kind with CodecC => [67] | CodecCUtf8 => [67; 46; 85; 84; 70; 45; 56] end.

Definition hello_codec_profile (audit : term -> option audited_codec) (w : libc_world) : Prop :=
  exists kind, audit (locale_codec (libc_locale (fst w))) = Some kind /\
    locale_text (libc_locale (fst w)) 0 = audited_codec_name kind.

(** The valid-state predicate is an explicit contract parameter keyed
    by codec and all eight current bytes. Initialization is a separate
    law, not a deduction from count bits or mere writable storage. *)
Definition mbstate_bytes (m : mem) (p : ptr) : list Z :=
  map (fun i => m_bytes m (ptr_addr p + Z.of_nat i)) (seq 0 8).

(** A required law for the chosen state representation, not an axiom.
    Validity must also admit completed states with residual value bytes. *)
Definition mbstate_zero_valid (valid : term -> list Z -> Prop) : Prop :=
  forall codec, valid codec (repeat 0 8).

(** Valid represented states contain bytes, not arbitrary mathematical
    integers. This independent representation law closes state reuse;
    a zero load alone cannot establish it. *)
Definition mbstate_valid_bytes (valid : term -> list Z -> Prop) : Prop :=
  forall codec bytes, valid codec bytes -> Forall (fun b => 0 <= b < 256) bytes.

Lemma mbstate_byte_range : forall valid codec m p,
  mbstate_valid_bytes valid -> valid codec (mbstate_bytes m p) ->
  forall i, 0 <= i < 8 -> 0 <= m_bytes m (ptr_addr p + i) < 256.
Proof.
  intros valid codec m p Hlaw Hvalid i Hi.
  pose proof (Hlaw _ _ Hvalid) as Hbytes. rewrite Forall_forall in Hbytes.
  apply Hbytes. unfold mbstate_bytes. apply in_map_iff.
  exists (Z.to_nat i). split.
  - rewrite Z2Nat.id by lia. reflexivity.
  - apply in_seq. split; [lia|]. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. simpl. lia.
Qed.

Lemma mbstate_zero_admitted : forall valid codec m p,
  mbstate_zero_valid valid ->
  (forall i, 0 <= i < 8 -> m_bytes m (ptr_addr p + i) = 0) ->
  valid codec (mbstate_bytes m p).
Proof.
  intros valid codec m p Hvalid Hzero.
  assert (mbstate_bytes m p = repeat 0 8) as ->.
  { unfold mbstate_bytes. simpl. repeat f_equal; apply Hzero; lia. }
  apply Hvalid.
Qed.

(** Byte-disjoint spans, even if their capabilities share an object. *)
Definition spans_apart (a b : span) : Prop :=
  ptr_addr (span_ptr a) + span_size a <= ptr_addr (span_ptr b) \/
  ptr_addr (span_ptr b) + span_size b <= ptr_addr (span_ptr a).

(** The composite setter borrows the same readable input as Locale's
    contract. Its independently writable errno cell is not private locale
    storage, release authority or a source of retained capabilities.
    Queries need none of these setter-only separation premises. *)
Definition libc_setlocale_pre rep xs m w : Prop :=
  libc_ready rep m w /\
  setlocale_pre (fun _ _ => True) xs m (libc_locale (fst w)) /\
  if locale_query xs then True else
    (forall root, In root (locale_roots (libc_locale (fst w))) ->
      spans_apart root (mkSpan (libc_errno (fst w)) 4)) /\
    (forall base, In base (locale_owned (libc_locale (fst w))) ->
      ptr_cap (libc_errno (fst w)) <> Obj base /\
      ptr_cap (libc_errno (fst w)) <> Ro base) /\
    (forall base, ptr_cap (libc_errno (fst w)) = Obj base \/
        ptr_cap (libc_errno (fst w)) = Ro base ->
      ~ available_cap (locale_sources [] m (libc_locale (fst w))) [] m (Obj base) /\
      ~ available_cap (locale_sources [] m (libc_locale (fst w))) [] m (Ro base)).

(** Refusal/loading may write errno; a query may not. No errno pointer
    is added to the capability sources or delegated private roots. *)
Definition libc_setlocale_writes xs (w : libc_world) : list span :=
  if locale_query xs then [] else
    locale_roots (libc_locale (fst w)) ++ [mkSpan (libc_errno (fst w)) 4].

(** Reuse Locale's selected/delegated endpoint rather than another locale
    inventory. Other authoritative world components remain exact. As for
    conversion, scalar errno stores leave caller aux unchanged, and the
    frame tests private authority in entry memory, not after a free. *)
Definition libc_setlocale_prefix rep xs m w born trace m' w' : Prop :=
  setlocale_prefix (fun _ _ => True) xs m (libc_locale (fst w))
    born trace m' (libc_locale (fst w')) /\
  if locale_query xs then w' = w else
    libc_ready rep m' w' /\
    libc_stdio (fst w') = libc_stdio (fst w) /\
    libc_errno (fst w') = libc_errno (fst w) /\ snd w' = snd w /\
    libc_streams (fst w') = libc_streams (fst w) /\
    (forall a, in_object m a ->
      ~ write_authority (locale_roots (libc_locale (fst w))) [] m a ->
      m_aux m' a = m_aux m a).

(** This is the composite call candidate, not a native satisfaction or
    world-interpretation theorem. Locale changes may select a new codec.
    Runtime resource endings retain only their actual coherent prefix. *)
Definition libc_setlocale_contract rep
    (requests : list word -> mem -> libc_world -> Z -> Z -> Prop) : contract libc_world :=
  mkContract libc_world (RClass P) setlocale_abi (libc_setlocale_pre rep)
    (fun xs m w => locale_sources xs m (libc_locale (fst w)))
    (fun xs _ w => libc_setlocale_writes xs w)
    (fun xs _ w => locale_releases xs (libc_locale (fst w)))
    (fun xs m w align size => locale_query xs = false /\ requests xs m w align size)
    (libc_setlocale_prefix rep)
    (fun xs m w born trace ending m' w' =>
      setlocale_post xs m (libc_locale (fst w)) born trace ending m' (libc_locale (fst w')))
    resource_reason
    (fun why => In why [NullCapability; OutOfBounds; Misaligned; Readonly; ArgumentSize; ReturnSize]).

Definition mbrtowc_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d L) /\
  exists out src n state, args = [Arg P out; Arg P src; Arg L n; Arg P state].

(** Null output/source/state forms and caller aliasing are outside this
    first slice. Private releases cannot end any argument/errno object. *)
Definition mbrtowc_pre (valid : term -> list Z -> Prop) rep xs m w : Prop :=
  libc_ready rep m w /\ mbstate_zero_valid valid /\ mbstate_valid_bytes valid /\
  exists out src n state,
    xs = [WPtr out; WPtr src; WInt n; WPtr state] /\
    ptr_addr out <> 0 /\ ptr_addr src <> 0 /\ ptr_addr state <> 0 /\
    readable_bytes m src n /\
    writable_span m (mkSpan out 4) /\ ptr_addr out mod 4 = 0 /\
    writable_span m (mkSpan state 8) /\ readable_bytes m state 8 /\ ptr_addr state mod 4 = 0 /\
    valid (locale_codec (libc_locale (fst w))) (mbstate_bytes m state) /\
    spans_apart (mkSpan src n) (mkSpan out 4) /\
    spans_apart (mkSpan src n) (mkSpan state 8) /\
    spans_apart (mkSpan out 4) (mkSpan state 8) /\
    (forall p size, In (p, size) [(src, n); (out, 4); (state, 8)] ->
      spans_apart (mkSpan (libc_errno (fst w)) 4) (mkSpan p size) /\
      forall root, In root (locale_roots (libc_locale (fst w))) ->
        spans_apart root (mkSpan p size)) /\
    (forall base, In base (locale_owned (libc_locale (fst w))) ->
      forall p, In p [out; src; state; libc_errno (fst w)] ->
        ptr_cap p <> Obj base /\ ptr_cap p <> Ro base) /\
    (forall root, In root (locale_roots (libc_locale (fst w))) ->
      spans_apart root (mkSpan (libc_errno (fst w)) 4)) /\
    (forall p, In p [out; src; state; libc_errno (fst w)] ->
      forall base, ptr_cap p = Obj base \/ ptr_cap p = Ro base ->
        ~ available_cap (locale_sources [] m (libc_locale (fst w))) [] m (Obj base) /\
        ~ available_cap (locale_sources [] m (libc_locale (fst w))) [] m (Ro base)).

(** Only old private libc sources supply capabilities to caches. Caller
    argument capabilities must not be retained in private aux slots. *)
Definition mbrtowc_sources (xs : list word) m (w : libc_world) : list span :=
  match xs with
  | [WPtr _; WPtr _; WInt n; WPtr _] =>
      if n =? 0 then [] else locale_sources [] m (libc_locale (fst w))
  | _ => []
  end.

Definition mbrtowc_writes (xs : list word) (w : libc_world) : list span :=
  match xs with
  | [WPtr out; WPtr _; WInt n; WPtr state] =>
      if n =? 0 then [] else
        locale_roots (libc_locale (fst w)) ++
        [mkSpan out 4; mkSpan state 8; mkSpan (libc_errno (fst w)) 4]
  | _ => []
  end.

Definition mbrtowc_releases (xs : list word) (w : libc_world) : list Z :=
  match xs with
  | [WPtr _; WPtr _; WInt n; WPtr _] =>
      if n =? 0 then [] else locale_owned (libc_locale (fst w))
  | _ => []
  end.

(** n=0 returns before converter lookup. All other prefixes retain the
    effective locale, stream/shutdown state and errno pointer. Private
    cache delegation deliberately excludes the caller's write roots.
    Ordinary wide/state/errno scalar writes do not change caller aux. *)
Definition mbrtowc_prefix rep xs m w born (trace : list event) m' w' : Prop :=
  trace = [] /\ match xs with
  | [WPtr _; WPtr _; WInt n; WPtr _] =>
      if n =? 0 then born = [] /\ m' = m /\ w' = w else
        libc_ready rep m' w' /\
        locale_unchanged (libc_locale (fst w)) (libc_locale (fst w')) /\
        locale_delegates [] m (libc_locale (fst w)) born m' (libc_locale (fst w')) /\
        libc_stdio (fst w') = libc_stdio (fst w) /\
        libc_errno (fst w') = libc_errno (fst w) /\ snd w' = snd w /\
        libc_streams (fst w') = libc_streams (fst w) /\
        (forall a, in_object m a ->
          ~ write_authority (locale_roots (libc_locale (fst w))) [] m a ->
          m_aux m' a = m_aux m a)
  | _ => False
  end.

(** Entry-memory byte claims never inspect an already modified input.
    Generic EILSEQ state stays unspecified. The audited stateless C
    converter rejects only non-ASCII and leaves all eight state bytes
    unchanged, including residual bytes. Both Hello codecs preserve
    valid initial count on EILSEQ and cannot reject a first-byte NUL.
    UTF-8 pending-state errors still have no reusable-state guarantee.
    Nonerror errno changes are permitted while lazy loading is unaudited. *)
Definition mbrtowc_result (valid : term -> list Z -> Prop) audit m w out src n state result m' : Prop :=
  0 <= result < 2 ^ 64 /\
  ((result = 0 /\
      valid (locale_codec (libc_locale (fst w))) (mbstate_bytes m' state) /\
      (hello_codec_profile audit w ->
        (exists i, 0 <= i < n /\ m_bytes m (ptr_addr src + i) = 0) /\
        load_bytes m' (ptr_addr out) 4 = 0 /\ load_bytes m' (ptr_addr state) 4 = 0)) \/
   (0 < result <= n /\ result < 2 ^ 64 - 2 /\
      valid (locale_codec (libc_locale (fst w))) (mbstate_bytes m' state) /\
      (hello_codec_profile audit w -> 0 < load_bytes m' (ptr_addr out) 4 < 2 ^ 32 /\
        load_bytes m' (ptr_addr state) 4 = 0 /\
        forall i, 0 <= i < result -> m_bytes m (ptr_addr src + i) <> 0)) \/
   (result = 2 ^ 64 - 1 /\ load_bytes m' (ptr_addr (libc_errno (fst w))) 4 = 84 /\
      (forall a, span_contains (mkSpan out 4) a -> m_bytes m' a = m_bytes m a) /\
      (audit (locale_codec (libc_locale (fst w))) = Some CodecC ->
        mbstate_bytes m' state = mbstate_bytes m state /\
        128 <= m_bytes m (ptr_addr src) < 256) /\
      (hello_codec_profile audit w -> load_bytes m (ptr_addr state) 4 = 0 ->
        valid (locale_codec (libc_locale (fst w))) (mbstate_bytes m state) ->
        valid (locale_codec (libc_locale (fst w))) (mbstate_bytes m' state) /\
        load_bytes m' (ptr_addr state) 4 = 0 /\ m_bytes m (ptr_addr src) <> 0)) \/
   (result = 2 ^ 64 - 2 /\
      valid (locale_codec (libc_locale (fst w))) (mbstate_bytes m' state) /\
      (forall a, span_contains (mkSpan out 4) a -> m_bytes m' a = m_bytes m a) /\
      (hello_codec_profile audit w -> n < 16 /\ forall i, 0 <= i < n ->
        m_bytes m (ptr_addr src + i) <> 0))).

Definition mbrtowc_post valid audit xs m w (_ : list Z) (_ : list event)
    ending m' (_ : libc_world) : Prop :=
  exists out src n state result,
    xs = [WPtr out; WPtr src; WInt n; WPtr state] /\
    ending = CallReturn [WInt result] /\
    if n =? 0 then result = 2 ^ 64 - 2 else
      mbrtowc_result valid audit m w out src n state result m'.

(** Plain P/P/L/P to L. Resource endpoints retain their actual effects
    prefix, not the normal completion's validity or EILSEQ guarantees. *)
Definition mbrtowc_contract valid audit rep
    (requests : list word -> mem -> libc_world -> Z -> Z -> Prop) : contract libc_world :=
  mkContract libc_world (RClass L) mbrtowc_abi (mbrtowc_pre valid rep)
    mbrtowc_sources (fun xs _ w => mbrtowc_writes xs w) (fun xs _ w => mbrtowc_releases xs w)
    (fun xs m w align size => exists out src n state,
      xs = [WPtr out; WPtr src; WInt n; WPtr state] /\ n <> 0 /\ requests xs m w align size)
    (mbrtowc_prefix rep) (mbrtowc_post valid audit) resource_reason
    (fun why => In why [NullCapability; OutOfBounds; Misaligned; Readonly; ArgumentSize; ReturnSize]).

(** Consumer lemmas share the supplied machine's exact call relations. *)
Module LibcOn (R : Runtime) (M : ExternalMachineSig R).
Module E := LibcCallsOn R M.

(** The existing TLS lookup contract with the exact composite projection.
    It exports the cell's capability, never ownership of its four bytes. *)
Definition errno_contract rep : contract libc_world :=
  errno_location_contract libc_world (fun w => libc_errno (fst w)) (libc_ready rep).

Theorem errno_admitted : forall rep r args s m w,
  errno_location_abi r args -> libc_ready rep m w ->
  E.invoke (errno_contract rep) r args [] s m w
    [] (CallReturn [WPtr (libc_errno (fst w))]) s m w.
Proof.
  intros rep r args s m w Habi Hready. apply E.errno_location_return; auto.
  exact (proj1 (proj2 (proj2 (proj2 Hready)))).
Qed.

Theorem errno_exact : forall rep r args xs s m w trace ending s' m' w',
  E.invoke (errno_contract rep) r args xs s m w trace ending s' m' w' ->
  trace = [] /\ s' = s /\ m' = m /\ w' = w /\
  ending = CallReturn [WPtr (libc_errno (fst w))].
Proof.
  intros rep r args xs s m w trace ending s' m' w' Hcall.
  destruct (E.errno_location_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & _ & _ & Htrace & Hs & Hm & Hw & Hend). auto.
Qed.

(** Admission and exact query inversion match HelloLocale's call-site
    premises over this machine, including identity of the entire world. *)
Theorem setlocale_query_pre : forall rep requests category p m w,
  libc_ready rep m w -> In category locale_categories -> ptr_addr p = 0 ->
  contract_pre (libc_setlocale_contract rep requests)
    [WInt category; WPtr p] m w.
Proof.
  intros rep requests category p m w Hready Hcat Hnull.
  split; [exact Hready|]. split.
  - split; [exact (proj1 (proj2 Hready))|]. exists category, p. auto.
  - cbn [locale_query]. rewrite Hnull. exact I.
Qed.

Theorem setlocale_query_admitted : forall rep requests r args category p s m w,
  setlocale_abi r args -> libc_ready rep m w ->
  In category locale_categories -> ptr_addr p = 0 ->
  E.invoke (libc_setlocale_contract rep requests) r args [WInt category; WPtr p] s m w []
    (CallReturn [WPtr (locale_name (libc_locale (fst w)) category)]) s m w.
Proof.
  intros rep requests r args category p s m w Habi Hready Hcat Hnull.
  assert (Hquery : locale_query [WInt category; WPtr p] = true).
  { unfold locale_query. rewrite Hnull. reflexivity. }
  eapply E.invoke_normal with (born := []).
  - exact Habi.
  - exact (setlocale_query_pre rep requests category p m w Hready Hcat Hnull).
  - split; [constructor|]. split.
    + split; [reflexivity|]. rewrite Hquery. auto.
    + rewrite Hquery. reflexivity.
  - exists category, p. split; [reflexivity|]. rewrite Hquery. reflexivity.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + eexists. split; reflexivity.
    + constructor; [apply locale_name_available; exact Hcat|constructor].
  - intros status Hbad. discriminate.
Qed.

Theorem setlocale_query_exact : forall rep requests r args category p s m w
    trace ending s' m' w',
  ptr_addr p = 0 ->
  E.invoke (libc_setlocale_contract rep requests) r args [WInt category; WPtr p]
    s m w trace ending s' m' w' ->
  trace = [] /\ s' = s /\ m' = m /\ w' = w /\
  ending = CallReturn [WPtr (locale_name (libc_locale (fst w)) category)].
Proof.
  intros rep requests r args category p s m w trace ending s' m' w' Hnull Hcall.
  assert (Hquery : locale_query [WInt category; WPtr p] = true).
  { unfold locale_query. rewrite Hnull. reflexivity. }
  destruct Hcall as [trace ending s' m' w' born Habi Hpre [He [Hp Hw]] Hpost Hresource Hvalues Hexit
    |why trace s' m' w' born Habi Hpre [He [Hp Hw]] Hfailure Hresource].
  - destruct Hp as [Htrace Hp]. rewrite Hquery in Hp, Hw. destruct Hp as (_ & Hm & _).
    destruct Hpost as (cat & q & Hxs & Hend). injection Hxs as <- <-.
    rewrite Hquery in Hend. split; [exact Htrace|]. split.
    + clear -He Hquery. induction He; [reflexivity|exact IHHe|].
      destruct H as [Hbad _]. congruence.
    + auto.
  - inversion Hfailure as [align size [Hbad _] Hsize Hrefuse|align size [Hbad _] Hsize];
      rewrite Hquery in Hbad; discriminate.
Qed.

(** These constructions require admission and, for selection, an actual
    permitted effects prefix and independently represented endpoint. They
    do not assume invocation or guarantee native selection/termination. *)
Theorem setlocale_refusal_admitted : forall rep requests r args category p s m w,
  setlocale_abi r args -> ptr_addr p <> 0 ->
  libc_setlocale_pre rep [WInt category; WPtr p] m w ->
  E.invoke (libc_setlocale_contract rep requests) r args [WInt category; WPtr p] s m w []
    (CallReturn [WPtr (mkPtr 0 CNone)]) s m w.
Proof.
  intros rep requests r args category p s m w Habi Hnonnull Hpre.
  pose proof Hpre as (Hready & Hlocale & _).
  assert (Hquery : locale_query [WInt category; WPtr p] = false)
    by (apply Z.eqb_neq; exact Hnonnull).
  eapply E.invoke_normal with (born := []).
  - exact Habi.
  - exact Hpre.
  - split; [constructor|]. split.
    + split; [reflexivity|]. rewrite Hquery. split; [exact (proj1 Hlocale)|].
      split; [apply locale_delegates_refl with (rep := fun _ _ => True); exact (proj1 Hlocale)|].
      exists category, p. split; [reflexivity|]. left. apply locale_unchanged_refl.
    + rewrite Hquery. split; [exact Hready|]. repeat split; intros; reflexivity.
  - exists category, p. split; [reflexivity|]. rewrite Hquery.
    left. split; [reflexivity|apply locale_unchanged_refl].
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + eexists. split; reflexivity.
    + constructor; [left; reflexivity|constructor].
  - intros status Hbad. discriminate.
Qed.

Theorem setlocale_selected_admitted : forall rep requests r args category p s m w
    born s' m' w',
  setlocale_abi r args -> ptr_addr p <> 0 ->
  libc_setlocale_pre rep [WInt category; WPtr p] m w ->
  E.prefix (libc_setlocale_contract rep requests) [WInt category; WPtr p]
    s m w born [] s' m' w' ->
  locale_selected category (libc_locale (fst w)) (libc_locale (fst w')) ->
  E.invoke (libc_setlocale_contract rep requests) r args [WInt category; WPtr p] s m w []
    (CallReturn [WPtr (locale_name (libc_locale (fst w')) category)]) s' m' w'.
Proof.
  intros rep requests r args category p s m w born s' m' w' Habi Hnonnull Hpre Hp Hselected.
  assert (Hcat : In category locale_categories).
  { destruct Hpre as (_ & (_ & cat & q & Hxs & Hcat & _) & _).
    injection Hxs as <- <-. exact Hcat. }
  assert (Hquery : locale_query [WInt category; WPtr p] = false)
    by (apply Z.eqb_neq; exact Hnonnull).
  pose proof Hp as (_ & (_ & Hlocale) & _). rewrite Hquery in Hlocale.
  destruct Hlocale as (_ & Hd & _).
  eapply E.invoke_normal with (born := born).
  - exact Habi.
  - exact Hpre.
  - exact Hp.
  - exists category, p. split; [reflexivity|]. rewrite Hquery. right. auto.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + eexists. split; reflexivity.
    + constructor; [|constructor]. apply locale_retained_available.
      apply (proj1 (proj2 Hd)). exact Hcat.
  - intros status Hbad. discriminate.
Qed.

(** Setter endpoints expose the selected new codec through the actual
    final locale, not a fixed codec hidden in the entry interpretation.
    New sources retain precisely Locale's old-private-or-born provenance. *)
Theorem setlocale_setter_prefix : forall rep requests r args category p s m w
    trace ending s' m' w',
  ptr_addr p <> 0 ->
  E.invoke (libc_setlocale_contract rep requests) r args [WInt category; WPtr p]
    s m w trace ending s' m' w' ->
  trace = [] /\ libc_ready rep m' w' /\
  libc_stdio (fst w') = libc_stdio (fst w) /\
  libc_errno (fst w') = libc_errno (fst w) /\ snd w' = snd w /\
  exists born,
    locale_delegates [WInt category; WPtr p] m (libc_locale (fst w)) born m' (libc_locale (fst w')) /\
    (forall source, In source (locale_private_sources (libc_locale (fst w'))) ->
      locale_retained_cap (libc_locale (fst w)) born (ptr_cap (span_ptr source))) /\
    (locale_unchanged (libc_locale (fst w)) (libc_locale (fst w')) \/
      locale_selected category (libc_locale (fst w)) (libc_locale (fst w'))).
Proof.
  intros rep requests r args category p s m w trace ending s' m' w' Hnonnull Hcall.
  assert (Hquery : locale_query [WInt category; WPtr p] = false)
    by (apply Z.eqb_neq; exact Hnonnull).
  destruct (E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall) as (born & _ & Hp & Hw).
  destruct Hp as [Htrace Hp]. rewrite Hquery in Hp, Hw.
  destruct Hp as (_ & Hd & cat & q & Hxs & Hselected). injection Hxs as <- <-.
  destruct Hw as (Hready & Hstdio & Herrno & Hshutdown & _).
  split; [exact Htrace|]. split; [exact Hready|]. split; [exact Hstdio|].
  split; [exact Herrno|]. split; [exact Hshutdown|]. exists born.
  split; [exact Hd|]. split; [|exact Hselected].
  intros source Hin. eapply locale_delegates_private; eauto.
Qed.

Theorem setlocale_setter_returned : forall rep requests r args category p s m w
    trace values s' m' w',
  ptr_addr p <> 0 ->
  E.invoke (libc_setlocale_contract rep requests) r args [WInt category; WPtr p]
    s m w trace (CallReturn values) s' m' w' ->
  (values = [WPtr (mkPtr 0 CNone)] /\
    locale_unchanged (libc_locale (fst w)) (libc_locale (fst w'))) \/
  (values = [WPtr (locale_name (libc_locale (fst w')) category)] /\
    locale_selected category (libc_locale (fst w)) (libc_locale (fst w')) /\
    c_string m' (locale_name (libc_locale (fst w')) category)
      (locale_text (libc_locale (fst w')) category)).
Proof.
  intros rep requests r args category p s m w trace values s' m' w' Hnonnull Hcall.
  destruct (setlocale_setter_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hnonnull Hcall)
    as (_ & Hready & _).
  assert (Hcat : In category locale_categories).
  { inversion Hcall; subst.
    match goal with Hpre : contract_pre _ _ _ _ |- _ =>
      destruct Hpre as (_ & (_ & cat & q & Hxs & Hcat & _) & _)
    end. injection Hxs as <- <-. exact Hcat. }
  assert (Hpost :
    setlocale_post [WInt category; WPtr p] m (libc_locale (fst w)) [] trace
      (CallReturn values) m' (libc_locale (fst w'))).
  { inversion Hcall; subst. assumption. }
  destruct Hpost as (cat & q & Hxs & Hpost). injection Hxs as <- <-.
  assert (Hquery : locale_query [WInt category; WPtr p] = false)
    by (apply Z.eqb_neq; exact Hnonnull).
  rewrite Hquery in Hpost. destruct Hpost as [[Hret Hunchanged]|[Hret Hselected]];
    injection Hret as ->; [left; auto|right; split; [reflexivity|]].
  split; [exact Hselected|].
  exact (proj1 (proj2 (libc_name rep m' w' category Hready Hcat))).
Qed.

(** Input-only n=0 admission constructs a call with the exact snapshot.
    The full valid-state/readability premises are intentionally retained. *)
Theorem mbrtowc_zero : forall valid audit rep requests r args out src state s m w,
  mbrtowc_abi r args -> mbrtowc_pre valid rep [WPtr out; WPtr src; WInt 0; WPtr state] m w ->
  E.invoke (mbrtowc_contract valid audit rep requests) r args
    [WPtr out; WPtr src; WInt 0; WPtr state] s m w
    [] (CallReturn [WInt (2 ^ 64 - 2)]) s m w.
Proof.
  intros valid audit rep requests r args out src state s m w Habi Hpre.
  eapply E.invoke_normal with (born := []).
  - exact Habi.
  - exact Hpre.
  - split; [constructor|]. repeat split; reflexivity.
  - exists out, src, 0, state, (2 ^ 64 - 2). repeat split; reflexivity.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WInt (2 ^ 64 - 2)). split; reflexivity.
    + constructor; [exact I|constructor].
  - intros status Hbad. discriminate.
Qed.

(** Non-setlocale conversion never changes effective locale/borrow facts
    or either authoritative stdio/shutdown state, including on resources. *)
Theorem mbrtowc_world : forall valid audit rep requests r args xs s m w trace ending s' m' w',
  E.invoke (mbrtowc_contract valid audit rep requests) r args xs s m w trace ending s' m' w' ->
  trace = [] /\
  locale_unchanged (libc_locale (fst w)) (libc_locale (fst w')) /\
  libc_stdio (fst w') = libc_stdio (fst w) /\
  libc_errno (fst w') = libc_errno (fst w) /\ snd w' = snd w.
Proof.
  intros valid audit rep requests r args xs s m w trace ending s' m' w' Hcall.
  assert (Hpre : mbrtowc_pre valid rep xs m w) by (inversion Hcall; assumption).
  destruct Hpre as (_ & _ & _ & out & src & n & state & -> & _).
  destruct (E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall) as (born & _ & Htrace & Hp).
  cbn [mbrtowc_prefix] in Hp. split; [exact Htrace|]. destruct (n =? 0).
  - destruct Hp as (_ & _ & ->). split; [apply locale_unchanged_refl|].
    repeat split; reflexivity.
  - destruct Hp as (_ & Hlocale & _ & Hstdio & Herrno & Hshutdown & _). auto.
Qed.

(** Nonzero normal completions need independent memory effects, endpoint
    representation/delegation and a result witness. This is not decoding
    existence or native termination, nor an assumption of invocation. *)
Theorem mbrtowc_completed : forall valid audit rep requests r args out src n state
    s m w born s' m' w' result,
  mbrtowc_abi r args ->
  mbrtowc_pre valid rep [WPtr out; WPtr src; WInt n; WPtr state] m w -> n <> 0 ->
  E.prefix (mbrtowc_contract valid audit rep requests)
    [WPtr out; WPtr src; WInt n; WPtr state] s m w born [] s' m' w' ->
  mbrtowc_result valid audit m w out src n state result m' ->
  E.invoke (mbrtowc_contract valid audit rep requests) r args
    [WPtr out; WPtr src; WInt n; WPtr state] s m w
    [] (CallReturn [WInt result]) s' m' w'.
Proof.
  intros valid audit rep requests r args out src n state s m w born s' m' w' result
    Habi Hpre Hn Hp Hresult.
  eapply E.invoke_normal with (born := born).
  - exact Habi.
  - exact Hpre.
  - exact Hp.
  - exists out, src, n, state, result. split; [reflexivity|]. split; [reflexivity|].
    rewrite (proj2 (Z.eqb_neq _ _) Hn). exact Hresult.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + exists (WInt result). split; [reflexivity|]. simpl.
      rewrite Z.mod_small; [reflexivity|exact (proj1 Hresult)].
    + constructor; [exact I|constructor].
  - intros status Hbad. discriminate.
Qed.

(** All normal return cases, extracted without assuming a particular
    decoder outcome. Resource endpoints do not obtain this theorem. *)
Theorem mbrtowc_returned : forall valid audit rep requests r args out src n state
    s m w trace values s' m' w',
  E.invoke (mbrtowc_contract valid audit rep requests) r args
    [WPtr out; WPtr src; WInt n; WPtr state] s m w trace (CallReturn values) s' m' w' ->
  exists result, values = [WInt result] /\
    if n =? 0 then result = 2 ^ 64 - 2 else
      mbrtowc_result valid audit m w out src n state result m'.
Proof.
  intros valid audit rep requests r args out src n state s m w trace values s' m' w' Hcall.
  inversion Hcall; subst.
  match goal with Hpost : contract_post _ _ _ _ _ _ _ _ _ |- _ =>
    destruct Hpost as (out' & src' & n' & state' & result & Hxs & Hend & Hresult)
  end.
  injection Hxs as <- <- <- <-. injection Hend as ->. exists result. auto.
Qed.

(** n=0 has no allocation request and cannot end for resources. Every
    completion, not just the constructed one, has the identity snapshot. *)
Theorem mbrtowc_zero_exact : forall valid audit rep requests r args out src state
    s m w trace ending s' m' w',
  E.invoke (mbrtowc_contract valid audit rep requests) r args
    [WPtr out; WPtr src; WInt 0; WPtr state] s m w trace ending s' m' w' ->
  trace = [] /\ ending = CallReturn [WInt (2 ^ 64 - 2)] /\ s' = s /\ m' = m /\ w' = w.
Proof.
  intros valid audit rep requests r args out src state s m w trace ending s' m' w' Hcall.
  destruct Hcall as [trace ending s' m' w' born Habi Hpre [He [Ht Hp]] Hpost Hresource Hvalues Hexit
    |why trace s' m' w' born Habi Hpre [He [Ht Hp]] Hfailure Hresource].
  - cbn [mbrtowc_prefix] in Hp. destruct Hp as (_ & -> & ->).
    destruct Hpost as (out' & src' & n' & state' & result & Hxs & Hend & Hresult).
    injection Hxs as <- <- <- <-. cbn in Hresult. subst result ending.
    split; [exact Ht|]. split; [reflexivity|]. split; [|auto].
    clear -He. induction He; [reflexivity|exact IHHe|].
    destruct H as (out' & src' & n' & state' & Hxs & Hn & _).
    injection Hxs as <- <- <- <-. contradiction.
  - inversion Hfailure as [align size Hrequest Hsize Hrefuse|align size Hrequest Hsize];
      destruct Hrequest as (out' & src' & n' & state' & Hxs & Hn & _);
      injection Hxs as <- <- <- <-; contradiction.
Qed.

End LibcOn.

Module Libc (R : Runtime).
Module M := ExternalMachine R.
Include LibcOn R M.
End Libc.

(** Consumer facts expose the audited profile only where it is needed.
    A complete character is initial, not necessarily eight zero bytes. *)
Theorem mbrtowc_positive : forall valid audit m w out src n state result m',
  mbrtowc_result valid audit m w out src n state result m' ->
  hello_codec_profile audit w -> 0 < result < 2 ^ 64 - 2 ->
  result <= n /\ 0 < load_bytes m' (ptr_addr out) 4 < 2 ^ 32 /\
  load_bytes m' (ptr_addr state) 4 = 0 /\
  valid (locale_codec (libc_locale (fst w))) (mbstate_bytes m' state) /\
  forall i, 0 <= i < result -> m_bytes m (ptr_addr src + i) <> 0.
Proof.
  intros valid audit m w out src n state result m' (_ & Hcases) Hprofile Hpositive.
  destruct Hcases as [(-> & _)|[(Hbound & _ & Hvalid & Hprofiled)|[(-> & _)|(-> & _)]]];
    try lia.
  destruct (Hprofiled Hprofile) as (Hwide & Hinitial & Hbytes). intuition.
Qed.

Theorem mbrtowc_incomplete : forall valid audit m w out src n state m',
  mbrtowc_result valid audit m w out src n state (2 ^ 64 - 2) m' ->
  hello_codec_profile audit w -> n < 16 /\
  forall i, 0 <= i < n -> m_bytes m (ptr_addr src + i) <> 0.
Proof.
  intros valid audit m w out src n state m' (_ & Hcases) Hprofile.
  destruct Hcases as [(Hbad & _)|[(_ & Hbad & _)|[(Hbad & _)|(_ & _ & _ & Hprofiled)]]];
    try lia. apply Hprofiled. exact Hprofile.
Qed.

Theorem mbrtowc_valid_after : forall valid audit m w out src n state result m',
  mbrtowc_result valid audit m w out src n state result m' ->
  result <> 2 ^ 64 - 1 ->
  valid (locale_codec (libc_locale (fst w))) (mbstate_bytes m' state).
Proof.
  intros valid audit m w out src n state result m' (_ & Hcases) Hnoterror.
  destruct Hcases as [(_ & Hvalid & _)|[(_ & _ & Hvalid & _)|[(Herror & _)|(_ & Hvalid & _)]]];
    congruence.
Qed.

(** Only the independently identified stateless C converter gets this
    error rule. It preserves admitted state, not necessarily zero state. *)
Theorem mbrtowc_c_error : forall valid audit m w out src n state m',
  mbrtowc_result valid audit m w out src n state (2 ^ 64 - 1) m' ->
  audit (locale_codec (libc_locale (fst w))) = Some CodecC ->
  mbstate_bytes m' state = mbstate_bytes m state /\
  128 <= m_bytes m (ptr_addr src) < 256.
Proof.
  intros valid audit m w out src n state m' (_ & Hcases) Hc.
  destruct Hcases as [(Hbad & _)|[(_ & Hbad & _)|[(_ & _ & _ & Herror & _)|(Hbad & _)]]];
    try lia. exact (Herror Hc).
Qed.

(** The selected C/UTF-8 initial-state error boundary used by gnulib's
    one-byte fallback. No promise is made about a pending UTF-8 state. *)
Theorem mbrtowc_initial_error : forall valid audit m w out src n state m',
  mbrtowc_result valid audit m w out src n state (2 ^ 64 - 1) m' ->
  hello_codec_profile audit w -> load_bytes m (ptr_addr state) 4 = 0 ->
  valid (locale_codec (libc_locale (fst w))) (mbstate_bytes m state) ->
  valid (locale_codec (libc_locale (fst w))) (mbstate_bytes m' state) /\
  load_bytes m' (ptr_addr state) 4 = 0 /\ m_bytes m (ptr_addr src) <> 0.
Proof.
  intros valid audit m w out src n state m' (_ & Hcases) Hprofile Hinitial Hvalid.
  destruct Hcases as [(Hbad & _)|[(_ & Hbad & _)|[(_ & _ & _ & _ & Herror)|(Hbad & _)]]];
    try lia. exact (Herror Hprofile Hinitial Hvalid).
Qed.

Theorem mbrtowc_valid_after_c : forall valid audit m w out src n state result m',
  mbrtowc_result valid audit m w out src n state result m' ->
  audit (locale_codec (libc_locale (fst w))) = Some CodecC ->
  valid (locale_codec (libc_locale (fst w))) (mbstate_bytes m state) ->
  valid (locale_codec (libc_locale (fst w))) (mbstate_bytes m' state).
Proof.
  intros valid audit m w out src n state result m' Hresult Hc Hvalid.
  destruct (Z.eq_dec result (2 ^ 64 - 1)) as [->|Hnoterror].
  - destruct (mbrtowc_c_error _ _ _ _ _ _ _ _ _ Hresult Hc) as [Hstate _].
    rewrite Hstate. exact Hvalid.
  - eapply mbrtowc_valid_after; eauto.
Qed.

(** Logical fixtures, not a native representation or decoder. Separate
    objects prevent a symmetric/overlapping footprint from hiding errors. *)
Definition conversion_mem : mem := mkMem
  (fun a => if a =? 1024 then 65 else if a =? 4096 then 67 else
    if a =? 3076 then 83 else 0)
  [mkRegion 1024 1056 GlobalData Live; mkRegion 2048 2056 Stack Live;
   mkRegion 3072 3080 Stack Live; mkRegion 4096 4104 GlobalData Live;
   mkRegion 5120 5128 Heap Live] (fun _ => CNone).

Definition conversion_world : libc_world :=
  (mkLibcPayload (mkLocaleWorld 0 (fun _ => mkPtr 4096 (Ro 4096))
    (fun _ => [67]) (TInt 0) [] [] []) (mkStdioWorld true []) (mkPtr 5120 (Obj 5120))
    (mkLibcStreams (mkLibcFile (mkPtr 0 CNone) 0 [] [] [])
      (mkLibcFile (mkPtr 0 CNone) 0 [] [] []) false stdout_initial)
    (mkGetoptWorld (mkPtr 0 CNone) (mkPtr 0 CNone) (mkPtr 0 CNone)
      (mkPtr 0 CNone) (mkPtr 5120 (Obj 5120)) (mkPtr 0 CNone) 1 1 0 0 [] [] []),
   mkShutdown Handlers 0 [] [] stdout_initial).

Definition conversion_args : list arg :=
  [Arg P (Const 0); Arg P (Const 1); Arg L (Const 2); Arg P (Const 3)].
Definition conversion_words (n : Z) : list word :=
  [WPtr (mkPtr 2048 (Obj 2048)); WPtr (mkPtr 1024 (Ro 1024)); WInt n;
   WPtr (mkPtr 3072 (Obj 3072))].

(** The abstract fixture admits initial states with residual bytes and
    one explicitly represented pending state. No count-bit validity rule
    is being asserted for native arbitrary-codec states. *)
Definition conversion_valid (_ : term) (bytes : list Z) : Prop :=
  Forall (fun b => 0 <= b < 256) bytes /\ length bytes = 8%nat /\
  (firstn 4 bytes = repeat 0 4 \/ bytes = [1; 0; 0; 0; 226; 0; 0; 0]).

Definition conversion_audit (_ : term) : option audited_codec := Some CodecC.
Definition conversion_spec := mbrtowc_contract conversion_valid conversion_audit
  (fun _ _ => True) (fun _ _ _ align size => align = 16 /\ size = 32).
Module InterpLibc := Libc InterpRuntime.

Lemma conversion_pre : forall n, 0 <= n <= 32 ->
  mbrtowc_pre conversion_valid (fun _ _ => True) (conversion_words n) conversion_mem conversion_world.
Proof.
  intros n Hn. split.
  - split; [exact I|]. split.
    + split; [exact I|]. split; [constructor|]. split.
      * intros category _. vm_compute. repeat split; congruence.
      * split; [constructor|]. split; [constructor|].
        intros category _. exists 4096. split; [right; reflexivity|reflexivity].
    + split; [constructor|]. split.
      * split; [discriminate|]. split; [|reflexivity]. split; [simpl; lia|].
        exists 5120, (mkRegion 5120 5128 Heap Live). repeat split; reflexivity.
      * split; [apply stdout_initial_wf|]. split; [constructor|]. split; [simpl; lia|exact I].
  - split; [intros codec; vm_compute; split; [repeat constructor; congruence|auto]|].
    split; [intros codec bytes [Hbytes _]; exact Hbytes|].
    exists (mkPtr 2048 (Obj 2048)), (mkPtr 1024 (Ro 1024)), n, (mkPtr 3072 (Obj 3072)).
    split; [reflexivity|]. split; [discriminate|]. split; [discriminate|]. split; [discriminate|].
    split.
    + split; [lia|]. split.
      * exists 1024, (mkRegion 1024 1056 GlobalData Live). repeat split; auto.
      * split.
        -- change (Some (if 1024 + n <=? 1056 then ok else RTrap OutOfBounds) = Some ok).
           rewrite (proj2 (Z.leb_le (1024 + n) 1056) ltac:(lia)). reflexivity.
        -- intros i Hi. cbn [conversion_mem m_bytes ptr_addr].
           repeat match goal with |- context [?a =? ?b] => destruct (a =? b) end; lia.
    + split.
      * split; [simpl; lia|]. exists 2048, (mkRegion 2048 2056 Stack Live).
        repeat split; reflexivity.
      * split; [reflexivity|]. split.
        -- split; [simpl; lia|]. exists 3072, (mkRegion 3072 3080 Stack Live).
           repeat split; reflexivity.
        -- split.
           ++ split; [lia|]. split.
              ** exists 3072, (mkRegion 3072 3080 Stack Live). repeat split; auto.
              ** split; [reflexivity|]. intros i Hi. cbn [conversion_mem m_bytes ptr_addr].
                 repeat match goal with |- context [?a =? ?b] => destruct (a =? b) end; lia.
           ++ split; [reflexivity|].
           split; [vm_compute; split; [repeat constructor; congruence|auto]|].
           split; [left; change (1024 + n <= 2048); lia|].
           split; [left; change (1024 + n <= 3072); lia|]. split; [left; vm_compute; congruence|]. split.
           ** intros p size [Heq|[Heq|[Heq|[]]]]; injection Heq as <- <-;
                split; [right; change (1024 + n <= 5120); lia|
                  intros root Hfalse; contradiction|
                  right; vm_compute; congruence|intros root Hfalse; contradiction|
                  right; vm_compute; congruence|intros root Hfalse; contradiction].
           ** split; [intros base Hfalse; contradiction|].
              split; [intros root Hfalse; contradiction|].
              intros p [<-|[<-|[<-|[<-|[]]]]] base [Hcap|Hcap];
                inversion Hcap; subst; split;
                intros [Hbad|[(source & Hin & Hbad)|[(source & a & Hin & _ & _ & _ & Hbad)|(b & [] & _)]]];
                try discriminate; try (change (_ = CNone) in Hbad; discriminate);
                unfold locale_sources in Hin; cbn [locale_reads locale_roots conversion_world libc_locale fst app] in Hin;
                rewrite app_nil_r in Hin; apply in_map_iff in Hin as (category & <- & _); discriminate.
Qed.

Lemma conversion_profile : hello_codec_profile conversion_audit conversion_world.
Proof. exists CodecC. split; reflexivity. Qed.

(** Zero count and real request/refusal are both public invocations. *)
Example conversion_zero_call :
  InterpLibc.E.invoke conversion_spec CVoid conversion_args (conversion_words 0)
    InterpRuntime.start conversion_mem conversion_world []
    (CallReturn [WInt (2 ^ 64 - 2)]) InterpRuntime.start conversion_mem conversion_world.
Proof.
  apply InterpLibc.mbrtowc_zero.
  - split; [left; reflexivity|]. eexists; eexists; eexists; eexists; reflexivity.
  - apply conversion_pre. lia.
Qed.

Example conversion_resource_call :
  InterpLibc.E.invoke conversion_spec CVoid conversion_args (conversion_words 1)
    InterpRuntime.address_end conversion_mem conversion_world []
    (CallResource OutOfMemory) InterpRuntime.address_end conversion_mem conversion_world.
Proof.
  eapply InterpLibc.E.invoke_resource with (born := []).
  - split; [left; reflexivity|]. eexists; eexists; eexists; eexists; reflexivity.
  - apply conversion_pre. lia.
  - split; [constructor|]. split; [reflexivity|].
    split; [exact (proj1 (conversion_pre 1 ltac:(lia)))|].
    split; [apply locale_unchanged_refl|]. split.
    + eapply locale_delegates_refl. exact (proj1 (proj2 (proj1 (conversion_pre 1 ltac:(lia))))).
    + split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. intros; reflexivity.
  - eapply InterpLibc.E.failure_oom with (align := 16) (size := 32).
    + eexists; eexists; eexists; eexists. split; [reflexivity|]. split; [discriminate|]. auto.
    + unfold max_allocation_size. lia.
    + reflexivity.
  - left. reflexivity.
Qed.

(** Scalar endpoints may change errno even on success. The residual
    value bytes are independent of the initial-state count. *)
Definition conversion_memory wide state error : mem :=
  store_bytes (store_bytes (store_bytes conversion_mem 2048 4 wide) 3072 8 state) 5120 4 error.

Lemma conversion_scalar_prefix : forall wide state error,
  InterpLibc.E.prefix conversion_spec (conversion_words 1)
    InterpRuntime.start conversion_mem conversion_world [] [] InterpRuntime.start
    (conversion_memory wide state error) conversion_world.
Proof.
  intros wide state error. split.
  - eapply InterpLibc.E.effects_local; [apply local_store_bytes|].
    + intros a Ha. left. exists (mkSpan (mkPtr 2048 (Obj 2048)) 4). split.
      * cbn [conversion_spec mbrtowc_contract contract_writes mbrtowc_writes conversion_words
          conversion_world libc_locale locale_roots fst app Z.eqb]. simpl. auto.
      * split; [|exact Ha]. split; [lia|]. exists 2048, (mkRegion 2048 2056 Stack Live).
        repeat split; reflexivity.
    + eapply InterpLibc.E.effects_local; [apply local_store_bytes|].
      * intros a Ha. left. exists (mkSpan (mkPtr 3072 (Obj 3072)) 8). split.
        -- cbn [conversion_spec mbrtowc_contract contract_writes mbrtowc_writes conversion_words
             conversion_world libc_locale locale_roots fst app Z.eqb]. simpl. auto.
        -- split; [|exact Ha]. split; [lia|]. exists 3072, (mkRegion 3072 3080 Stack Live).
           repeat split; reflexivity.
      * eapply InterpLibc.E.effects_local; [apply local_store_bytes|constructor].
        intros a Ha. left. exists (mkSpan (mkPtr 5120 (Obj 5120)) 4). split.
        -- cbn [conversion_spec mbrtowc_contract contract_writes mbrtowc_writes conversion_words
             conversion_world libc_locale libc_errno locale_roots fst app Z.eqb]. simpl. auto.
        -- split; [|exact Ha]. split; [change (0 <= 4); lia|]. exists 5120, (mkRegion 5120 5128 Heap Live).
           repeat split; reflexivity.
  - split; [reflexivity|]. split.
    + split; [exact I|]. split.
      * split; [exact I|]. split; [constructor|]. split.
        -- intros category _. vm_compute. repeat split; congruence.
        -- split; [constructor|]. split; [constructor|].
           intros category _. exists 4096. split; [right; reflexivity|reflexivity].
      * split; [constructor|]. split.
        -- split; [discriminate|]. split; [|reflexivity]. split; [change (0 <= 4); lia|].
           exists 5120, (mkRegion 5120 5128 Heap Live). repeat split; reflexivity.
        -- split; [apply stdout_initial_wf|]. split; [constructor|]. split; [simpl; lia|exact I].
    + split; [apply locale_unchanged_refl|]. split.
      * split; [intros root Hfalse; contradiction|]. split.
        -- intros category Hcat. apply locale_name_retained. exact Hcat.
        -- split; [intros source Hfalse; contradiction|intros base Hfalse; contradiction].
      * split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. intros; reflexivity.
Qed.

Example conversion_positive_call :
  let m' := conversion_memory 65 (83 * 2 ^ 32) 7 in
  InterpLibc.E.invoke conversion_spec CVoid conversion_args (conversion_words 1)
    InterpRuntime.start conversion_mem conversion_world [] (CallReturn [WInt 1])
    InterpRuntime.start m' conversion_world /\
  mbstate_bytes m' (mkPtr 3072 (Obj 3072)) = [0; 0; 0; 0; 83; 0; 0; 0] /\
  load_bytes m' 5120 4 = 7.
Proof.
  split.
  - eapply InterpLibc.mbrtowc_completed with (born := []).
    + split; [left; reflexivity|]. eexists; eexists; eexists; eexists; reflexivity.
    + apply conversion_pre. lia.
    + discriminate.
    + apply conversion_scalar_prefix.
    + split; [lia|]. right. left. split; [lia|]. split; [lia|].
      split; [vm_compute; split; [repeat constructor; congruence|auto]|].
      intros _. split; [vm_compute; auto|].
      split; [reflexivity|]. intros i Hi. assert (i = 0) by lia. subst. discriminate.
  - split; reflexivity.
Qed.

(** Scalar output/state/errno roots never confer permission to retain
    caller capabilities in aux. The public invocation rejects this even
    though the state bytes themselves are writable. *)
Example conversion_caller_aux_rejected : forall c, c <> CNone -> forall s s' trace ending,
  ~ InterpLibc.E.invoke conversion_spec CVoid conversion_args (conversion_words 1)
    s conversion_mem conversion_world trace ending s'
    (store_aux conversion_mem 3072 c) conversion_world.
Proof.
  intros c Hcap s s' trace ending Hcall.
  destruct (InterpLibc.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (born & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hframe).
  specialize (Hframe 3072).
  assert (in_object conversion_mem 3072) as Hin.
  { exists 3072, (mkRegion 3072 3080 Stack Live). split; [reflexivity|]. simpl; lia. }
  assert (~ write_authority [] [] conversion_mem 3072) as Hout.
  { intros [(root & [] & _)|(base & reg & [] & _)]. }
  apply Hcap. exact (Hframe Hin Hout).
Qed.

(** Profiled incomplete calls preserve valid continuation, not initial
    state. An unprofiled EILSEQ may still leave invalid state. *)
Example conversion_incomplete_and_error :
  mbrtowc_result conversion_valid conversion_audit conversion_mem conversion_world
    (mkPtr 2048 (Obj 2048)) (mkPtr 1024 (Ro 1024)) 1 (mkPtr 3072 (Obj 3072))
    (2 ^ 64 - 2) (conversion_memory 0 (226 * 2 ^ 32 + 1) 9) /\
  (forall audit, audit (TInt 0) <> Some CodecC -> ~ hello_codec_profile audit conversion_world ->
  mbrtowc_result conversion_valid audit conversion_mem conversion_world
    (mkPtr 2048 (Obj 2048)) (mkPtr 1024 (Ro 1024)) 1 (mkPtr 3072 (Obj 3072))
    (2 ^ 64 - 1) (conversion_memory 0 255 84)).
Proof.
  split.
  - split; [lia|]. right. right. right. split; [reflexivity|].
    split; [vm_compute; split; [repeat constructor; congruence|auto]|].
    split.
    + intros a Ha. change (2048 <= a < 2052) in Ha.
      assert (a = 2048 \/ a = 2049 \/ a = 2050 \/ a = 2051) by lia.
      destruct H as [-> | [-> | [-> | ->]]]; reflexivity.
    + intros _. split; [lia|]. intros i Hi. assert (i = 0) by lia. subst. discriminate.
  - intros audit Hnotc Hnotprofile. split; [lia|]. right. right. left.
    split; [reflexivity|]. split; [reflexivity|].
    split.
    + intros a Ha. change (2048 <= a < 2052) in Ha.
      assert (a = 2048 \/ a = 2049 \/ a = 2050 \/ a = 2051) by lia.
      destruct H as [-> | [-> | [-> | ->]]]; reflexivity.
    + split; [intros Hc; contradiction|]. intros Hprofile. contradiction.
Qed.

(** A mathematical memory write is not automatically a byte. Neither
    normal nor incomplete validity may admit this damaged state. *)
Example conversion_bad_state_byte_rejected : forall byte result,
  (byte < 0 \/ 256 <= byte) -> result <> 2 ^ 64 - 1 ->
  ~ mbrtowc_result conversion_valid conversion_audit conversion_mem conversion_world
    (mkPtr 2048 (Obj 2048)) (mkPtr 1024 (Ro 1024)) 1 (mkPtr 3072 (Obj 3072))
    result (mkMem (fun a => if a =? 3076 then byte else m_bytes conversion_mem a)
      (m_regions conversion_mem) (m_aux conversion_mem)).
Proof.
  intros byte result Hbad Hnoterror Hresult.
  pose proof (mbrtowc_valid_after _ _ _ _ _ _ _ _ _ _ Hresult Hnoterror) as Hvalid.
  assert (mbstate_valid_bytes conversion_valid) as Hlaw.
  { intros codec bytes [Hbytes _]. exact Hbytes. }
  pose proof (mbstate_byte_range _ _ _ _ Hlaw Hvalid 4 ltac:(lia)) as Hrange.
  change (0 <= byte < 256) in Hrange. lia.
Qed.

(** C error and subsequent reuse retain a nonzero residual state byte;
    they do not silently reinitialize the state. *)
Definition conversion_c_error_mem := store_bytes conversion_mem 1024 1 255.
Definition conversion_c_error_end := store_bytes conversion_c_error_mem 5120 4 84.

Example conversion_c_error_result :
  mbrtowc_result conversion_valid conversion_audit conversion_c_error_mem conversion_world
    (mkPtr 2048 (Obj 2048)) (mkPtr 1024 (Ro 1024)) 1 (mkPtr 3072 (Obj 3072))
    (2 ^ 64 - 1) conversion_c_error_end.
Proof.
  split; [lia|]. right. right. left. split; [reflexivity|]. split; [reflexivity|].
  split.
  - intros a Ha. change (2048 <= a < 2052) in Ha.
    unfold conversion_c_error_end, store_bytes. cbn [m_bytes].
    rewrite (proj2 (Z.leb_gt 5120 a) ltac:(lia)). reflexivity.
  - split.
    + intros _. split; [reflexivity|]. vm_compute. repeat split; congruence.
    + intros _ _ Hvalid. split; [exact Hvalid|]. split; [reflexivity|discriminate].
Qed.

Example conversion_c_error_valid_residual :
  conversion_valid (locale_codec (libc_locale (fst conversion_world)))
    (mbstate_bytes conversion_c_error_end (mkPtr 3072 (Obj 3072))) /\
  m_bytes conversion_c_error_end 3076 = 83.
Proof.
  split; [|reflexivity].
  eapply mbrtowc_valid_after_c; [exact conversion_c_error_result|reflexivity|].
  vm_compute. split; [repeat constructor; congruence|auto].
Qed.

Example conversion_c_error_ascii_rejected :
  ~ mbrtowc_result conversion_valid conversion_audit conversion_mem conversion_world
    (mkPtr 2048 (Obj 2048)) (mkPtr 1024 (Ro 1024)) 1 (mkPtr 3072 (Obj 3072))
    (2 ^ 64 - 1) (conversion_memory 0 (83 * 2 ^ 32) 84).
Proof.
  intros Hresult.
  destruct (mbrtowc_c_error _ _ _ _ _ _ _ _ _ Hresult eq_refl) as [_ Hbyte].
  change (128 <= 65 < 256) in Hbyte. lia.
Qed.

Example conversion_c_error_changed_state_rejected :
  ~ mbrtowc_result conversion_valid conversion_audit conversion_c_error_mem conversion_world
    (mkPtr 2048 (Obj 2048)) (mkPtr 1024 (Ro 1024)) 1 (mkPtr 3072 (Obj 3072))
    (2 ^ 64 - 1) (conversion_memory 0 (84 * 2 ^ 32) 84).
Proof.
  intros Hresult.
  destruct (mbrtowc_c_error _ _ _ _ _ _ _ _ _ Hresult eq_refl) as [Hstate _].
  discriminate Hstate.
Qed.

(** UTF-8 initial-count EILSEQ is reusable even with residual bytes;
    this fixture tests the error relation, not native locale readiness. *)
Definition conversion_utf8_world : libc_world :=
  (mkLibcPayload (mkLocaleWorld 0 (fun _ => mkPtr 4096 (Ro 4096))
    (fun _ => audited_codec_name CodecCUtf8) (TInt 0) [] [] [])
    (libc_stdio (fst conversion_world)) (libc_errno (fst conversion_world))
    (libc_streams (fst conversion_world)) (libc_getopt (fst conversion_world)),
   snd conversion_world).

Example conversion_utf8_initial_error :
  mbrtowc_result conversion_valid (fun _ => Some CodecCUtf8)
    conversion_c_error_mem conversion_utf8_world
    (mkPtr 2048 (Obj 2048)) (mkPtr 1024 (Ro 1024)) 1 (mkPtr 3072 (Obj 3072))
    (2 ^ 64 - 1) conversion_c_error_end.
Proof.
  split; [lia|]. right. right. left. split; [reflexivity|]. split; [reflexivity|].
  split.
  - intros a Ha. change (2048 <= a < 2052) in Ha.
    unfold conversion_c_error_end, store_bytes. cbn [m_bytes].
    rewrite (proj2 (Z.leb_gt 5120 a) ltac:(lia)). reflexivity.
  - split; [discriminate|]. intros _ _ Hvalid.
    split; [exact Hvalid|]. split; [reflexivity|discriminate].
Qed.

Example conversion_utf8_initial_error_changed_count_rejected :
  ~ mbrtowc_result conversion_valid (fun _ => Some CodecCUtf8)
    conversion_c_error_mem conversion_utf8_world
    (mkPtr 2048 (Obj 2048)) (mkPtr 1024 (Ro 1024)) 1 (mkPtr 3072 (Obj 3072))
    (2 ^ 64 - 1) (conversion_memory 0 (226 * 2 ^ 32 + 1) 84).
Proof.
  intros Hresult.
  destruct (mbrtowc_initial_error _ _ _ _ _ _ _ _ _ Hresult)
    as (_ & Hcount & _).
  - exists CodecCUtf8. split; reflexivity.
  - reflexivity.
  - vm_compute. split; [repeat constructor; congruence|auto].
  - discriminate Hcount.
Qed.

Example conversion_utf8_initial_error_nul_rejected :
  ~ mbrtowc_result conversion_valid (fun _ => Some CodecCUtf8)
    (store_bytes conversion_mem 1024 1 0) conversion_utf8_world
    (mkPtr 2048 (Obj 2048)) (mkPtr 1024 (Ro 1024)) 1 (mkPtr 3072 (Obj 3072))
    (2 ^ 64 - 1) conversion_c_error_end.
Proof.
  intros Hresult.
  destruct (mbrtowc_initial_error _ _ _ _ _ _ _ _ _ Hresult)
    as (_ & _ & Hbyte).
  - exists CodecCUtf8. split; reflexivity.
  - reflexivity.
  - vm_compute. split; [repeat constructor; congruence|auto].
  - apply Hbyte. reflexivity.
Qed.

(** The profiled output interpretations are not generic decoder laws. *)
Example conversion_unprofiled_outputs :
  mbrtowc_result conversion_valid (fun _ => None) conversion_mem conversion_world
    (mkPtr 2048 (Obj 2048)) (mkPtr 1024 (Ro 1024)) 1 (mkPtr 3072 (Obj 3072))
    0 (conversion_memory 937 0 7) /\
  mbrtowc_result conversion_valid (fun _ => None) conversion_mem conversion_world
    (mkPtr 2048 (Obj 2048)) (mkPtr 1024 (Ro 1024)) 1 (mkPtr 3072 (Obj 3072))
    1 (conversion_memory 0 0 7).
Proof.
  split; (split; [lia|]).
  - left. split; [reflexivity|].
    split; [vm_compute; split; [repeat constructor; congruence|auto]|].
    intros (kind & Hbad & _). discriminate.
  - right. left. split; [lia|]. split; [lia|].
    split; [vm_compute; split; [repeat constructor; congruence|auto]|].
    intros (kind & Hbad & _). discriminate.
Qed.

Example conversion_profiled_outputs_rejected : forall result,
  result = 0 \/ result = 1 ->
  ~ InterpLibc.E.invoke conversion_spec CVoid conversion_args (conversion_words 1)
    InterpRuntime.start conversion_mem conversion_world [] (CallReturn [WInt result])
    InterpRuntime.start (conversion_memory 0 0 7) conversion_world.
Proof.
  intros result Hresult Hcall.
  destruct (InterpLibc.mbrtowc_returned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (returned & Heq & Hpost). injection Heq as <-. cbn in Hpost.
  destruct Hresult as [-> | ->].
  - destruct Hpost as (_ & [(Hret & _ & Hprofile)|[(Hbad & _)|[(Hbad & _)|(Hbad & _)]]]); try lia.
    destruct (Hprofile conversion_profile) as ((i & Hi & Hbyte) & _).
    assert (i = 0) by lia. subst. discriminate Hbyte.
  - destruct (mbrtowc_positive _ _ _ _ _ _ _ _ _ _ Hpost conversion_profile ltac:(lia))
      as (_ & Hwide & _). change (0 < 0 < 2 ^ 32) in Hwide. lia.
Qed.

Example conversion_incomplete_rejected : forall n,
  n = 2 \/ n = 16 -> forall s m' w',
  ~ InterpLibc.E.invoke conversion_spec CVoid conversion_args (conversion_words n)
    s conversion_mem conversion_world [] (CallReturn [WInt (2 ^ 64 - 2)]) s m' w'.
Proof.
  intros n Hn s m' w' Hcall.
  destruct (InterpLibc.mbrtowc_returned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (returned & Heq & Hpost). injection Heq as <-.
  destruct Hn as [-> | ->]; cbn in Hpost;
    destruct (mbrtowc_incomplete _ _ _ _ _ _ _ _ _ Hpost conversion_profile) as [Hbound Hbytes].
  - specialize (Hbytes 1 ltac:(lia)). apply Hbytes. reflexivity.
  - lia.
Qed.

(** Equal-width scalar classes do not substitute for the selected ABI. *)
Example conversion_bad_abi :
  ~ mbrtowc_abi CVoid [Arg P (Const 0); Arg P (Const 1); Arg W (Const 2); Arg P (Const 3)].
Proof. intros (_ & out & src & n & state & Hbad). discriminate Hbad. Qed.

(** A temporary private allocation may receive a private capability and
    then be freed. Its historical aux entry need not be erased: the frame
    protects entry objects, not nonexistent caller ownership at 8192.
    This is a logical effects witness, not evidence of native decoding. *)
Definition conversion_cached : mem :=
  store_aux (store_bytes (allocated conversion_mem (heap_req 16 32) 8192)
    8192 8 4096) 8192 (Ro 4096).

Definition conversion_cleaned : mem := mkMem
  (m_bytes conversion_cached)
  (mkRegion 8192 8192 Heap Freed :: m_regions conversion_mem)
  (m_aux conversion_cached).

Lemma conversion_cleanup_effects :
  InterpLibc.E.effects (mbrtowc_sources (conversion_words 1) conversion_mem conversion_world)
    (mbrtowc_writes (conversion_words 1) conversion_world) []
    (contract_requests conversion_spec (conversion_words 1) conversion_mem conversion_world)
    8192 conversion_mem [] 8240 conversion_cleaned [8192].
Proof.
  eapply InterpLibc.E.effects_alloc with (align := 16) (size := 32) (base := 8192).
  - eexists; eexists; eexists; eexists. split; [reflexivity|]. split; [discriminate|]. auto.
  - unfold max_allocation_size. lia.
  - reflexivity.
  - eapply InterpLibc.E.effects_local with (m1 := conversion_cached).
    + unfold conversion_cached.
      apply (local_store_pointer _ _ _ _ _ 8192 (mkPtr 4096 (Ro 4096))).
      * intros a Ha. right. exists 8192, (mkRegion 8192 8224 Heap Live).
        split; [simpl; auto|]. split; [reflexivity|]. repeat split; try reflexivity; simpl in *; lia.
      * right. left. exists (locale_name_span (libc_locale (fst conversion_world)) 0).
        split; [|reflexivity]. unfold mbrtowc_sources, conversion_words. simpl.
        unfold locale_sources, locale_private_sources. simpl. auto.
    + eapply InterpLibc.E.effects_local; [|constructor].
      split.
      * intros base reg Hreg.
        change ((if 8192 =? base then Some (mkRegion 8192 8224 Heap Live)
          else object_region base (m_regions conversion_mem)) = Some reg) in Hreg.
        change (exists reg', (if 8192 =? base then Some (mkRegion 8192 8192 Heap Freed)
          else object_region base (m_regions conversion_mem)) = Some reg').
        destruct (8192 =? base); [eexists; reflexivity|eauto].
      * split.
        -- intros base reg Hreg.
           change ((if 8192 =? base then Some (mkRegion 8192 8192 Heap Freed)
             else object_region base (m_regions conversion_mem)) = Some reg) in Hreg.
           change (exists old,
             (if 8192 =? base then Some (mkRegion 8192 8224 Heap Live)
               else object_region base (m_regions conversion_mem)) = Some old /\
             (reg = old \/ In base ([] ++ [8192]) /\ r_kind old = Heap /\
               r_life old = Live /\ reg = mkRegion base base Heap Freed)).
           destruct (8192 =? base) eqn:Hbase.
           ++ apply Z.eqb_eq in Hbase. subst base. injection Hreg as <-.
              exists (mkRegion 8192 8224 Heap Live). split; [reflexivity|].
              right. repeat split; simpl; auto.
           ++ exists reg. auto.
        -- split.
           ++ intros a _. split; reflexivity.
           ++ intros a. left. reflexivity.
Qed.

Lemma conversion_cleanup_prefix :
  InterpLibc.E.prefix conversion_spec (conversion_words 1)
    8192 conversion_mem conversion_world [8192] [] 8240 conversion_cleaned conversion_world.
Proof.
  split.
  - exact conversion_cleanup_effects.
  - split; [reflexivity|]. split.
    + split; [exact I|]. split.
      * split; [exact I|]. split; [constructor|]. split.
        -- intros category _. vm_compute. repeat split; congruence.
        -- split; [constructor|]. split; [constructor|].
           intros category _. exists 4096. split; [right; reflexivity|reflexivity].
      * split; [constructor|]. split.
        -- split; [discriminate|]. split; [|reflexivity]. split; [change (0 <= 4); lia|].
           exists 5120, (mkRegion 5120 5128 Heap Live). repeat split; reflexivity.
        -- split; [apply stdout_initial_wf|]. split; [constructor|]. split; [simpl; lia|exact I].
    + split; [apply locale_unchanged_refl|]. split.
      * split; [intros root Hfalse; contradiction|]. split.
        -- intros category Hcat. apply locale_name_retained. exact Hcat.
        -- split; [intros source Hfalse; contradiction|intros base Hfalse; contradiction].
      * split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|].
        intros a (base & reg & Hreg & Hrange) _.
        assert (a < 5128) as Hbound.
        { cbn [conversion_mem m_regions object_region r_base] in Hreg.
          repeat match type of Hreg with
          | context [?x =? base] => destruct (x =? base) eqn:Hbase;
              [apply Z.eqb_eq in Hbase; subst base; injection Hreg as <-; cbn in Hrange; lia|clear Hbase]
          end; discriminate Hreg. }
        change ((if a =? 8192 then Ro 4096 else CNone) = CNone).
        rewrite (proj2 (Z.eqb_neq a 8192) ltac:(lia)). reflexivity.
Qed.

Example conversion_cleanup_call :
  InterpLibc.E.invoke conversion_spec CVoid conversion_args (conversion_words 1)
    8192 conversion_mem conversion_world [] (CallReturn [WInt (2 ^ 64 - 2)])
    8240 conversion_cleaned conversion_world /\
  object_region 8192 (m_regions conversion_cleaned) = Some (mkRegion 8192 8192 Heap Freed) /\
  m_aux conversion_cleaned 8192 = Ro 4096.
Proof.
  split.
  - eapply InterpLibc.mbrtowc_completed with (born := [8192]).
    + split; [left; reflexivity|]. eexists; eexists; eexists; eexists; reflexivity.
    + apply conversion_pre. lia.
    + discriminate.
    + exact conversion_cleanup_prefix.
    + split; [lia|]. right. right. right. split; [reflexivity|].
      split; [vm_compute; split; [repeat constructor; congruence|auto]|]. split.
      * intros a Ha. change (2048 <= a < 2052) in Ha.
        change ((if (8192 <=? a) && (a <? 8200) then byte_of 4096 (a - 8192)
          else m_bytes conversion_mem a) = m_bytes conversion_mem a).
        rewrite (proj2 (Z.leb_gt 8192 a) ltac:(lia)). reflexivity.
      * intros _. split; [lia|]. intros i Hi. assert (i = 0) by lia. subst. discriminate.
  - split; reflexivity.
Qed.

(** Projection/envelope controls only: the placeholder public cells are
    not admitted getopt state, and True is not native initialization. *)
Module LibcGetoptChecks.

(** Vary only the parser component of an existing libc fixture. *)
Definition world (arg : ptr) (index : Z) : libc_world :=
  (mkLibcPayload (libc_locale (fst conversion_world)) (libc_stdio (fst conversion_world))
    (libc_errno (fst conversion_world)) (libc_streams (fst conversion_world))
    (mkGetoptWorld (mkPtr 0 CNone) (mkPtr 0 CNone) (mkPtr 0 CNone)
      (mkPtr 0 CNone) (libc_errno (fst conversion_world)) arg index 1 0 0 [] [] []),
   snd conversion_world).

(** Changing optarg/optind does not force any unrelated world change. *)
Example parser_can_change :
  libc_getopt_stable (world (mkPtr 0 CNone) 1) (world (mkPtr 1025 (Ro 1024)) 2) /\
  getopt_optarg (libc_getopt_view (world (mkPtr 1025 (Ro 1024)) 2)) = mkPtr 1025 (Ro 1024) /\
  getopt_optind (libc_getopt_view (world (mkPtr 0 CNone) 1)) = 1 /\
  getopt_optind (libc_getopt_view (world (mkPtr 1025 (Ro 1024)) 2)) = 2.
Proof. repeat split; reflexivity. Qed.

(** Endpoint envelope predicates can coexist without equating their
    native parameters. This is not an invocation or adequacy witness. *)
Example completed_inflight_overlap :
  libc_getopt_rep (fun _ _ => True) conversion_mem conversion_world /\
  libc_getopt_inflight (fun _ _ => True) conversion_mem conversion_world.
Proof.
  split; split; try reflexivity; exact (proj1 (conversion_pre 1 ltac:(lia))).
Qed.

(** A running envelope cannot manufacture completed initialization. *)
Example running_not_initialized :
  libc_getopt_inflight (fun _ _ => True) conversion_mem conversion_world /\
  ~ libc_getopt_rep (fun _ _ => False) conversion_mem conversion_world.
Proof.
  split; [exact (proj2 completed_inflight_overlap)|].
  intros [[Hfalse _] _]. exact Hfalse.
Qed.

End LibcGetoptChecks.
