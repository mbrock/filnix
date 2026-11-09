(** Hello's composite trusted libc boundary. One locale/stdio/errno
    payload accompanies the existing authoritative shutdown state;
    there is no second output queue or callback inventory. The conversion
    contract describes logical represented endpoints, not every native
    instruction or collector prefix. Libc satisfaction remains trusted. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics
  ExternalCalls ExternalMachine Locale Stdio Shutdown.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Record libc_payload : Type := mkLibcPayload {
  libc_locale : locale_world;
  libc_stdio : stdio_world;
  libc_errno : ptr
}.

(** Definitionally the payload * shutdown_state used by Linked. *)
Definition libc_world : Type := (libc_payload * shutdown_state)%type.

(** The full representation owns coherent libc/TLS state and exclusive
    private release rights. Structural facts alone do not establish it.
    In a callback, uniqueness is not evidence that its token was popped. *)
Definition libc_ready (rep : mem -> libc_world -> Prop) m w : Prop :=
  rep m w /\
  locale_ready (fun _ _ => True) m (libc_locale (fst w)) /\
  stdio_ready m (libc_stdio (fst w)) /\ errno_cell m (libc_errno (fst w)) /\
  stream_wf (shutdown_stdout (snd w)) /\ shutdown_unique (snd w) /\
  -(2 ^ 31) <= shutdown_status (snd w) < 2 ^ 31 /\
  match shutdown_at (snd w) with
  | InCallback active => In (registration_token active) (shutdown_consumed (snd w))
  | _ => True
  end.

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

Definition mbrtowc_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d L) /\
  exists out src n state, args = [Arg P out; Arg P src; Arg L n; Arg P state].

(** Null output/source/state forms and caller aliasing are outside this
    first slice. Private releases cannot end any argument/errno object. *)
Definition mbrtowc_pre (valid : term -> list Z -> Prop) rep xs m w : Prop :=
  libc_ready rep m w /\ mbstate_zero_valid valid /\ exists out src n state,
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
        (forall a, in_object m a ->
          ~ write_authority (locale_roots (libc_locale (fst w))) [] m a ->
          m_aux m' a = m_aux m a)
  | _ => False
  end.

(** Entry-memory byte claims never inspect an already modified input.
    EILSEQ leaves state unspecified, but does not require it to be invalid.
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
      (forall a, span_contains (mkSpan out 4) a -> m_bytes m' a = m_bytes m a)) \/
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
Module E := M.E.

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
  destruct Hpre as (_ & _ & out & src & n & state & -> & _).
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
    (fun _ => [67]) (TInt 0) [] [] []) (mkStdioWorld true []) (mkPtr 5120 (Obj 5120)),
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
  length bytes = 8%nat /\
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
    + split; [split; [reflexivity|constructor]|]. split.
      * split; [discriminate|]. split; [|reflexivity]. split; [simpl; lia|].
        exists 5120, (mkRegion 5120 5128 Heap Live). repeat split; reflexivity.
      * split; [apply stdout_initial_wf|]. split; [constructor|]. split; [simpl; lia|exact I].
  - split; [intros codec; vm_compute; auto|].
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
           split; [vm_compute; auto|]. split; [left; change (1024 + n <= 2048); lia|].
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
    + split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity.
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
      * split; [split; [reflexivity|constructor]|]. split.
        -- split; [discriminate|]. split; [|reflexivity]. split; [change (0 <= 4); lia|].
           exists 5120, (mkRegion 5120 5128 Heap Live). repeat split; reflexivity.
        -- split; [apply stdout_initial_wf|]. split; [constructor|]. split; [simpl; lia|exact I].
    + split; [apply locale_unchanged_refl|]. split.
      * split; [intros root Hfalse; contradiction|]. split.
        -- intros category Hcat. apply locale_name_retained. exact Hcat.
        -- split; [intros source Hfalse; contradiction|intros base Hfalse; contradiction].
      * split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity.
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
      split; [vm_compute; auto|]. intros _. split; [vm_compute; auto|].
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
    as (born & _ & _ & _ & _ & _ & _ & _ & _ & Hframe).
  specialize (Hframe 3072).
  assert (in_object conversion_mem 3072) as Hin.
  { exists 3072, (mkRegion 3072 3080 Stack Live). split; [reflexivity|]. simpl; lia. }
  assert (~ write_authority [] [] conversion_mem 3072) as Hout.
  { intros [(root & [] & _)|(base & reg & [] & _)]. }
  apply Hcap. exact (Hframe Hin Hout).
Qed.

(** Profiled incomplete calls preserve valid continuation, not initial
    state. EILSEQ may instead leave an invalid state, but must set errno. *)
Example conversion_incomplete_and_error :
  mbrtowc_result conversion_valid conversion_audit conversion_mem conversion_world
    (mkPtr 2048 (Obj 2048)) (mkPtr 1024 (Ro 1024)) 1 (mkPtr 3072 (Obj 3072))
    (2 ^ 64 - 2) (conversion_memory 0 (226 * 2 ^ 32 + 1) 9) /\
  mbrtowc_result conversion_valid conversion_audit conversion_mem conversion_world
    (mkPtr 2048 (Obj 2048)) (mkPtr 1024 (Ro 1024)) 1 (mkPtr 3072 (Obj 3072))
    (2 ^ 64 - 1) (conversion_memory 0 255 84).
Proof.
  split; (split; [lia|]).
  - right. right. right. split; [reflexivity|]. split; [vm_compute; auto|].
    split.
    + intros a Ha. change (2048 <= a < 2052) in Ha.
      assert (a = 2048 \/ a = 2049 \/ a = 2050 \/ a = 2051) by lia.
      destruct H as [-> | [-> | [-> | ->]]]; reflexivity.
    + intros _. split; [lia|]. intros i Hi. assert (i = 0) by lia. subst. discriminate.
  - right. right. left. split; [reflexivity|]. split; [reflexivity|].
    intros a Ha. change (2048 <= a < 2052) in Ha.
    assert (a = 2048 \/ a = 2049 \/ a = 2050 \/ a = 2051) by lia.
    destruct H as [-> | [-> | [-> | ->]]]; reflexivity.
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
  - left. split; [reflexivity|]. split; [vm_compute; auto|]. intros (kind & Hbad & _). discriminate.
  - right. left. split; [lia|]. split; [lia|]. split; [vm_compute; auto|].
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
      * split; [split; [reflexivity|constructor]|]. split.
        -- split; [discriminate|]. split; [|reflexivity]. split; [change (0 <= 4); lia|].
           exists 5120, (mkRegion 5120 5128 Heap Live). repeat split; reflexivity.
        -- split; [apply stdout_initial_wf|]. split; [constructor|]. split; [simpl; lia|exact I].
    + split; [apply locale_unchanged_refl|]. split.
      * split; [intros root Hfalse; contradiction|]. split.
        -- intros category Hcat. apply locale_name_retained. exact Hcat.
        -- split; [intros source Hfalse; contradiction|intros base Hfalse; contradiction].
      * split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
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
      split; [vm_compute; auto|]. split.
      * intros a Ha. change (2048 <= a < 2052) in Ha.
        change ((if (8192 <=? a) && (a <? 8200) then byte_of 4096 (a - 8192)
          else m_bytes conversion_mem a) = m_bytes conversion_mem a).
        rewrite (proj2 (Z.leb_gt 8192 a) ltac:(lia)). reflexivity.
      * intros _. split; [lia|]. intros i Hi. assert (i = 0) by lia. subst. discriminate.
  - split; reflexivity.
Qed.
