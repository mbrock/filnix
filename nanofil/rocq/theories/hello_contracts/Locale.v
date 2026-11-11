(** Trusted setlocale boundary for the selected glibc categories. Names
    are borrowed strings, not caller-owned allocations. The epoch marks
    a validity window, not a claim that every stale pointer traps.
    Native representation, prefix coverage and safepoint stability remain
    independent obligations; there are no new runtime axioms. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Identity ExternalCalls ExternalMachine.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** This selected glibc has thirteen categories; CTYPE is 0 and ALL 6. *)
Definition locale_categories : list Z := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12].

(** One authoritative logical locale state. The codec is opaque, not
    inferred from an ASCII name. Representation owns internal roots and
    exclusive release permissions; names themselves confer no ownership. *)
Record locale_world : Type := mkLocaleWorld {
  locale_epoch : nat;
  locale_name : Z -> ptr;
  locale_text : Z -> list Z;
  locale_codec : term;
  locale_reads : list span;
  locale_roots : list span;
  locale_owned : list Z
}.

(** Release eligibility is distinct from writable pointer authority.
    Exclusive ownership itself belongs to the trusted representation. *)
Definition locale_heap m base : Prop := exists reg,
  object_region base (m_regions m) = Some reg /\ r_kind reg = Heap /\ r_life reg = Live.

(** The selected implementation's borrowed names have aligned object
    bases, even when the returned character address is unaligned. This
    is the source-object premise of [copy_domain], not write permission. *)
Definition locale_names_aligned w : Prop := forall category,
  In category locale_categories -> exists base,
    (ptr_cap (locale_name w category) = Obj base \/
     ptr_cap (locale_name w category) = Ro base) /\ base mod 8 = 0.

(** Every current name is readable through NUL and every write root is
    independently writable. The opaque representation includes actual
    initialized libc/environment/TLS state and exclusive release rights.
    [locale_names_aligned] holds at entry and after every setter endpoint. *)
Definition locale_ready (rep : mem -> locale_world -> Prop) m w : Prop :=
  rep m w /\ Forall (writable_span m) (locale_roots w) /\
  (forall category, In category locale_categories ->
    ptr_addr (locale_name w category) <> 0 /\
    c_string m (locale_name w category) (locale_text w category)) /\
  Forall (fun source => readable_bytes m (span_ptr source) (span_size source)) (locale_reads w) /\
  Forall (locale_heap m) (locale_owned w) /\ locale_names_aligned w.

(** A current name can supply memcpy's object-base alignment without
    aligning its character address or changing its borrowed capability. *)
Lemma locale_name_aligned : forall rep m w category,
  locale_ready rep m w -> In category locale_categories -> exists base,
    (ptr_cap (locale_name w category) = Obj base \/
     ptr_cap (locale_name w category) = Ro base) /\ base mod 8 = 0.
Proof.
  intros rep m w category (_ & _ & _ & _ & _ & Haligned) Hcat.
  exact (Haligned category Hcat).
Qed.

(** A current name's NUL-inclusive borrowed source span. *)
Definition locale_name_span w category : span :=
  mkSpan (locale_name w category) (Z.of_nat (length (locale_text w category)) + 1).

(** Private objects whose own capabilities may survive a setter. Neither
    the caller's input nor capabilities loaded from aux enter this pool. *)
Definition locale_private_sources w : list span :=
  (locale_reads w ++ locale_roots w) ++ map (locale_name_span w) locale_categories.

(** Retained authority has object-level private provenance. Zero-sized
    spans still carry their object's own capability. Fresh objects may
    be retained as Obj or Ro; old authority is never upgraded. *)
Definition locale_retained_cap w born c : Prop :=
  (exists base, In base born /\ (c = Obj base \/ c = Ro base)) \/
  (exists source, In source (locale_private_sources w) /\ c = ptr_cap (span_ptr source)).

(** Null is tested by address, as in native C. No capability or input
    string is required for the null-query operand. *)
Definition locale_query (xs : list word) : bool :=
  match xs with [WInt _; WPtr p] => ptr_addr p =? 0 | _ => false end.

(** Independent input admission; computing a source span never admits
    an unterminated or incorrectly-capabilitied setter string. *)
Definition setlocale_pre rep xs m w : Prop :=
  locale_ready rep m w /\ exists category p,
    xs = [WInt category; WPtr p] /\ In category locale_categories /\
    (ptr_addr p = 0 \/ exists bytes, c_string m p bytes).

(** Exact P result and W/P argument classes, including discarded results. *)
Definition setlocale_abi r args : Prop :=
  (r = CVoid \/ exists d, r = CResult d P) /\
  exists category name, args = [Arg W category; Arg P name].

(** Existing libc roots and current borrowed names supply retained
    authority. The setter input contributes its independently admitted
    string span, but never becomes writable merely by being an input. *)
Definition locale_sources xs m w : list span :=
  locale_private_sources w ++
  match xs with
  | [WInt _; WPtr p] => if locale_query xs then [] else
      [mkSpan p (string_length m p + 1)]
  | _ => []
  end.

(** Only setters may mutate or allocate. Querying is a pure projection. *)
Definition locale_writes xs w : list span :=
  if locale_query xs then [] else locale_roots w.

(** Queries have no release permission either. *)
Definition locale_releases xs w : list Z :=
  if locale_query xs then [] else locale_owned w.

(** Keeping an epoch preserves every current borrowed pointer. A
    successor may replace them, even when effective locale names stay
    the same; a setter never promises persistence of an old borrow. *)
Definition locale_window w w' : Prop :=
  (locale_epoch w' = locale_epoch w /\ locale_name w' = locale_name w /\
    locale_text w' = locale_text w /\ locale_codec w' = locale_codec w) \/
  locale_epoch w' = S (locale_epoch w).

(** Refusal leaves the effective locale unchanged, not necessarily all
    internal allocations or errno. Its borrow window stays valid. *)
Definition locale_unchanged w w' : Prop :=
  locale_name w' = locale_name w /\ locale_text w' = locale_text w /\
  locale_codec w' = locale_codec w /\ locale_epoch w' = locale_epoch w.

(** Successful selection may change the requested category and ALL's
    composite name. Encoding changes only for CTYPE or ALL. Empty input
    selects from the represented environment; no C/ASCII restriction. *)
Definition locale_selected category w w' : Prop :=
  locale_window w w' /\
  (forall other, In other locale_categories -> category <> 6 ->
    other <> category -> other <> 6 -> locale_text w' other = locale_text w other) /\
  (category <> 0 -> category <> 6 -> locale_codec w' = locale_codec w).

(** Retained names, read spans and roots inherit only private own
    capabilities or born objects, not the setter input or aux-loaded
    caller authority. Apply this to all three to prevent laundering on
    a later call, including through a zero-sized root. Ordinary transient
    effects still use [locale_sources]; exclusive releases stay separate. *)
Definition locale_delegates (xs : list word) (m : mem) w born m' w' : Prop :=
  (forall root, In root (locale_roots w') ->
    locale_retained_cap w born (ptr_cap (span_ptr root)) /\
    forall a, span_contains root a -> write_authority (locale_roots w) born m' a) /\
  (forall category, In category locale_categories ->
    locale_retained_cap w born (ptr_cap (locale_name w' category))) /\
  (forall source, In source (locale_reads w') ->
    locale_retained_cap w born (ptr_cap (span_ptr source))) /\
  (forall base, In base (locale_owned w') -> In base (locale_owned w ++ born) /\ locale_heap m' base).

(** The entire next private pool, not just this call's returned name,
    has private provenance. Clients apply object-level separation and
    fresh-allocation facts to this lemma across repeated setters. *)
Lemma locale_delegates_private : forall xs m w born m' w' source,
  locale_delegates xs m w born m' w' -> In source (locale_private_sources w') ->
  locale_retained_cap w born (ptr_cap (span_ptr source)).
Proof.
  intros xs m w born m' w' source (Hroots & Hnames & Hreads & _) Hin.
  unfold locale_private_sources in Hin. apply in_app_or in Hin as [Hin|Hin].
  - apply in_app_or in Hin as [Hin|Hin]; [apply Hreads|apply (proj1 (Hroots source Hin))]; auto.
  - apply in_map_iff in Hin as (category & <- & Hcat). apply Hnames. exact Hcat.
Qed.

(** Silent logical segment endpoints, NOT arbitrary native instruction
    cutpoints: setname can free before installing a replacement. Native
    allocation/resource/safepoint coverage needs an in-progress view.
    Serialized coherent locale/environment access remains trusted. *)
Definition setlocale_prefix rep xs m w born (trace : list event) m' w' : Prop :=
  trace = [] /\
  if locale_query xs then born = [] /\ m' = m /\ w' = w else
    locale_ready rep m' w' /\ locale_delegates xs m w born m' w' /\
    exists category p, xs = [WInt category; WPtr p] /\
      (locale_unchanged w w' \/ locale_selected category w w').

(** Queries return exactly the current name, never NULL at an admitted
    initialized category. Setters may refuse, or return the new current
    category's readable borrowed name. Neither path transfers ownership. *)
Definition setlocale_post (xs : list word) (m : mem) (w : locale_world)
    (born : list Z) (trace : list event) (ending : call_end) (m' : mem) (w' : locale_world) : Prop :=
  exists category p, xs = [WInt category; WPtr p] /\
    if locale_query xs then
      ending = CallReturn [WPtr (locale_name w category)] else
      (ending = CallReturn [WPtr (mkPtr 0 CNone)] /\ locale_unchanged w w') \/
      (ending = CallReturn [WPtr (locale_name w' category)] /\ locale_selected category w w').

(** The complete trusted call contract. Allocation policy is explicit;
    refusal as NULL and terminal runtime resource endings stay distinct. *)
Definition setlocale_contract rep requests : contract locale_world :=
  mkContract locale_world (RClass P) setlocale_abi (setlocale_pre rep)
    locale_sources (fun xs _ w => locale_writes xs w) (fun xs _ w => locale_releases xs w)
    (fun xs m w align size => locale_query xs = false /\ requests xs m w align size)
    (setlocale_prefix rep) setlocale_post resource_reason
    (fun why => In why [NullCapability; OutOfBounds; Misaligned; Readonly; ArgumentSize; ReturnSize]).

(** The identity evolution retains the logical locale and its window. *)
Lemma locale_unchanged_refl : forall w, locale_unchanged w w.
Proof. intros w. repeat split; reflexivity. Qed.

(** Current names are explicit sources, not unexplained return authority. *)
Lemma locale_retained_available : forall xs m w born m' c,
  locale_retained_cap w born c -> available_cap (locale_sources xs m w) born m' c.
Proof.
  intros xs m w born m' c [(base & Hin & Hcap)|(source & Hin & Hcap)].
  - right. right. right. exists base. auto.
  - right. left. exists source. split; [|exact Hcap].
    unfold locale_sources. apply in_or_app. left. exact Hin.
Qed.

Lemma locale_name_retained : forall w born category,
  In category locale_categories -> locale_retained_cap w born (ptr_cap (locale_name w category)).
Proof.
  intros w born category Hcategory. right. exists (locale_name_span w category).
  split; [|reflexivity]. unfold locale_private_sources. apply in_or_app. right.
  apply in_map. exact Hcategory.
Qed.

Lemma locale_name_available : forall xs m w born category,
  In category locale_categories ->
  available_cap (locale_sources xs m w) born m (ptr_cap (locale_name w category)).
Proof.
  intros xs m w born category Hcategory. apply locale_retained_available.
  apply locale_name_retained. exact Hcategory.
Qed.

(** An unchanged represented world requires no newly delegated authority. *)
Lemma locale_delegates_refl : forall rep xs m w,
  locale_ready rep m w -> locale_delegates xs m w [] m w.
Proof.
  intros rep xs m w (_ & Hroots & _ & Hreads & Howned & _). split.
  - intros root Hin. split.
    + right. exists root. split; [|reflexivity].
      unfold locale_private_sources. apply in_or_app. left. apply in_or_app. right. exact Hin.
    + intros a Ha. left. exists root. split; [exact Hin|]. split; [|exact Ha].
      rewrite Forall_forall in Hroots. apply Hroots. exact Hin.
  - split; [intros; apply locale_name_retained; assumption|]. split.
    + intros source Hin. right. exists source. split; [|reflexivity].
      unfold locale_private_sources. apply in_or_app. left. apply in_or_app. left. exact Hin.
    + intros base Hin. split; [apply in_or_app; left; exact Hin|].
      rewrite Forall_forall in Howned. apply Howned. exact Hin.
Qed.

(** A retained epoch preserves exact borrowed pointers, contents and
    codec interpretation. No such transport is offered after a change. *)
Theorem locale_borrow_preserved : forall rep m' w w' category,
  locale_window w w' -> locale_epoch w' = locale_epoch w ->
  locale_ready rep m' w' -> In category locale_categories ->
  c_string m' (locale_name w category) (locale_text w category) /\
  locale_codec w' = locale_codec w.
Proof.
  intros rep m' w w' category [[He [Hp [Ht Hcodec]]]|He] Hsame (_ & _ & Hnames & _) Hcat.
  - split; [rewrite <- Hp, <- Ht; exact (proj2 (Hnames category Hcat))|exact Hcodec].
  - lia.
Qed.

(** Call constructions and exact extraction over the caller's machine.
    A separately instantiated machine has different inductive types. *)
Module LocaleOn (R : Runtime) (M : ExternalMachineSig R).
Module E := M.E.

(** A null query is constructively inhabited from its independent
    represented input facts, with exact memory, world and runtime. *)
Theorem setlocale_query_admitted : forall rep requests r args category p s m w,
  setlocale_abi r args -> locale_ready rep m w ->
  In category locale_categories -> ptr_addr p = 0 ->
  E.invoke (setlocale_contract rep requests) r args [WInt category; WPtr p] s m w []
    (CallReturn [WPtr (locale_name w category)]) s m w.
Proof.
  intros rep requests r args category p s m w Habi Hready Hcat Hnull.
  assert (Hquery : locale_query [WInt category; WPtr p] = true).
  { unfold locale_query. rewrite Hnull. reflexivity. }
  eapply E.invoke_normal with (born := []).
  - exact Habi.
  - split; [exact Hready|]. exists category, p. auto.
  - split; [constructor|]. split; [reflexivity|]. rewrite Hquery. auto.
  - exists category, p. split; [reflexivity|]. rewrite Hquery. reflexivity.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + eexists. split; reflexivity.
    + constructor; [apply locale_name_available; exact Hcat|constructor].
  - intros status Hbad. discriminate.
Qed.

(** A setter's ordinary refusal is possible without allocations or
    input mutation. This is conservative specification nonvacuity,
    not a claim that native selection always fails or always returns. *)
Theorem setlocale_refusal_admitted : forall rep requests r args category p bytes s m w,
  setlocale_abi r args -> locale_ready rep m w ->
  In category locale_categories -> ptr_addr p <> 0 -> c_string m p bytes ->
  E.invoke (setlocale_contract rep requests) r args [WInt category; WPtr p] s m w []
    (CallReturn [WPtr (mkPtr 0 CNone)]) s m w.
Proof.
  intros rep requests r args category p bytes s m w Habi Hready Hcat Hnonnull Hstr.
  assert (Hquery : locale_query [WInt category; WPtr p] = false)
    by (apply Z.eqb_neq; exact Hnonnull).
  eapply E.invoke_normal with (born := []).
  - exact Habi.
  - split; [exact Hready|]. exists category, p. split; [reflexivity|].
    split; [exact Hcat|]. right. exists bytes. exact Hstr.
  - split; [constructor|]. split; [reflexivity|]. rewrite Hquery.
    split; [exact Hready|]. split; [eapply locale_delegates_refl; exact Hready|].
    exists category, p. split; [reflexivity|]. left. apply locale_unchanged_refl.
  - exists category, p. split; [reflexivity|]. rewrite Hquery.
    left. split; [reflexivity|apply locale_unchanged_refl].
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + eexists. split; reflexivity.
    + constructor; [left; reflexivity|constructor].
  - intros status Hbad. discriminate.
Qed.

(** Successful selection is inhabited from an independent effects path,
    represented result and delegated authority, not assumed merely
    because the arguments were admitted. *)
Theorem setlocale_success_admitted : forall rep requests r args category p bytes s m w born s' m' w',
  setlocale_abi r args -> locale_ready rep m w -> In category locale_categories ->
  ptr_addr p <> 0 -> c_string m p bytes ->
  E.effects (locale_sources [WInt category; WPtr p] m w) (locale_roots w) (locale_owned w)
    (fun align size => locale_query [WInt category; WPtr p] = false /\
      requests [WInt category; WPtr p] m w align size)
    s m [] s' m' born ->
  locale_ready rep m' w' -> locale_delegates [WInt category; WPtr p] m w born m' w' ->
  locale_selected category w w' ->
  E.invoke (setlocale_contract rep requests) r args [WInt category; WPtr p] s m w []
    (CallReturn [WPtr (locale_name w' category)]) s' m' w'.
Proof.
  intros rep requests r args category p bytes s m w born s' m' w'
    Habi Hready Hcat Hnonnull Hstr He Hr' Hd Hselected.
  assert (Hquery : locale_query [WInt category; WPtr p] = false)
    by (apply Z.eqb_neq; exact Hnonnull).
  eapply E.invoke_normal with (born := born).
  - exact Habi.
  - split; [exact Hready|]. exists category, p. split; [reflexivity|].
    split; [exact Hcat|]. right. exists bytes. exact Hstr.
  - split.
    + change (E.effects (locale_sources [WInt category; WPtr p] m w)
        (locale_writes [WInt category; WPtr p] w) (locale_releases [WInt category; WPtr p] w)
        (fun align size => locale_query [WInt category; WPtr p] = false /\
          requests [WInt category; WPtr p] m w align size) s m [] s' m' born).
      unfold locale_writes, locale_releases. rewrite Hquery.
      rewrite Hquery in He. exact He.
    + split; [reflexivity|]. rewrite Hquery. split; [exact Hr'|]. split; [exact Hd|].
      exists category, p. split; [reflexivity|]. right. exact Hselected.
  - exists category, p. split; [reflexivity|]. rewrite Hquery. right. auto.
  - intros why Hbad. discriminate.
  - intros values Heq. injection Heq as <-. split.
    + eexists. split; reflexivity.
    + constructor; [apply locale_retained_available; apply (proj1 (proj2 Hd)); exact Hcat|constructor].
  - intros status Hbad. discriminate.
Qed.

(** Every completion exposes the exact trace/world/effect endpoint;
    queries cannot allocate, fail for resources or change the snapshot.
    For setters, callers frame their pieces with the existing effects
    rules using roots_apart and exclusive-release separation. *)
Theorem setlocale_invocation : forall rep requests r args xs s m w trace ending s' m' w',
  E.invoke (setlocale_contract rep requests) r args xs s m w trace ending s' m' w' ->
  setlocale_pre rep xs m w /\ trace = [] /\ exists born,
    E.effects (locale_sources xs m w) (locale_writes xs w) (locale_releases xs w)
      (fun align size => locale_query xs = false /\ requests xs m w align size)
      s m [] s' m' born /\
    (if locale_query xs then born = [] /\ m' = m /\ w' = w /\
        exists category p, xs = [WInt category; WPtr p] /\
          ending = CallReturn [WPtr (locale_name w category)]
     else locale_ready rep m' w' /\ locale_delegates xs m w born m' w' /\
       (setlocale_post xs m w born trace ending m' w' \/ exists why, ending = CallResource why /\
         E.resource_failure (fun align size => locale_query xs = false /\ requests xs m w align size) s' why /\
         resource_reason why)).
Proof.
  intros rep requests r args xs s m w trace ending s' m' w' Hcall.
  destruct Hcall as [trace ending s' m' w' born Habi Hpre [He [Ht Hp]] Hpost Hresource Hvalues Hexit
    |why trace s' m' w' born Habi Hpre [He [Ht Hp]] Hfailure Hresource].
  - split; [exact Hpre|]. split; [exact Ht|]. exists born. split; [exact He|].
    destruct (locale_query xs) eqn:Hquery.
    + destruct Hp as (Hb & Hm & Hw). repeat split; try assumption.
      destruct Hpost as (category & p & Hxs & Hresult).
      rewrite Hquery in Hresult. exists category, p. auto.
    + destruct Hp as (Hr & Hd & _). auto.
  - split; [exact Hpre|]. split; [exact Ht|]. exists born. split; [exact He|].
    destruct (locale_query xs) eqn:Hquery.
    + inversion Hfailure as [align size Hrequest Hsize Hrefuse |align size Hrequest Hsize]; subst;
        destruct Hrequest as [Hnotquery _]; rewrite Hquery in Hnotquery; discriminate.
    + destruct Hp as (Hr & Hd & _). split; [exact Hr|]. split; [exact Hd|]. right.
      exists why. split; [reflexivity|]. split; [|exact Hresource].
      change (E.resource_failure (fun align size => locale_query xs = false /\
        requests xs m w align size) s' why) in Hfailure.
      rewrite Hquery in Hfailure. exact Hfailure.
Qed.

(** Queries, successful/refused setters and terminal resource endpoints
    all retain aligned current-name bases, through endpoint readiness. *)
Theorem setlocale_invocation_aligned : forall rep requests r args xs s m w trace ending s' m' w',
  E.invoke (setlocale_contract rep requests) r args xs s m w trace ending s' m' w' ->
  locale_names_aligned w'.
Proof.
  intros rep requests r args xs s m w trace ending s' m' w' Hcall.
  destruct (setlocale_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as ([Hready _] & _ & born & _ & Hend).
  destruct (locale_query xs).
  - destruct Hend as (_ & _ & -> & _).
    destruct Hready as (_ & _ & _ & _ & _ & Haligned). exact Haligned.
  - destruct Hend as [(_ & _ & _ & _ & _ & Haligned) _]. exact Haligned.
Qed.

(** The pure-query runtime cannot advance through an allocation; all
    query completions have exactly the starting runtime state too. *)
Theorem setlocale_query_invocation : forall rep requests r args category p s m w trace ending s' m' w',
  ptr_addr p = 0 ->
  E.invoke (setlocale_contract rep requests) r args [WInt category; WPtr p] s m w
    trace ending s' m' w' ->
  trace = [] /\ s' = s /\ m' = m /\ w' = w /\
  ending = CallReturn [WPtr (locale_name w category)].
Proof.
  intros rep requests r args category p s m w trace ending s' m' w' Hnull Hcall.
  assert (Hquery : locale_query [WInt category; WPtr p] = true).
  { unfold locale_query. rewrite Hnull. reflexivity. }
  destruct (setlocale_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (Hpre & Htrace & born & He & Hresult).
  rewrite Hquery in Hresult. destruct Hresult as (Hb & Hm & Hw & cat & q & Hxs & Hend).
  injection Hxs as <- Hp. split; [exact Htrace|]. split.
  - clear -He Hquery. induction He; [reflexivity|exact IHHe|].
    destruct H as [Hfalse _]. congruence.
  - auto.
Qed.

(** A setter result observed as NULL is ordinary refusal, not a
    successful locale change whose readable name happens to live at 0. *)
Theorem setlocale_null_refusal : forall rep requests r args category p q s m w trace s' m' w',
  ptr_addr p <> 0 -> ptr_addr q = 0 ->
  E.invoke (setlocale_contract rep requests) r args [WInt category; WPtr p] s m w
    trace (CallReturn [WPtr q]) s' m' w' -> locale_unchanged w w'.
Proof.
  intros rep requests r args category p q s m w trace s' m' w' Hnonzero Hzero Hcall.
  assert (Hquery : locale_query [WInt category; WPtr p] = false)
    by (apply Z.eqb_neq; exact Hnonzero).
  destruct (setlocale_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (Hpre & Htrace & born & He & Hresult).
  rewrite Hquery in Hresult. destruct Hresult as (Hr & Hd & [Hpost|(why & Hbad & _)]);
    [|discriminate Hbad].
  destruct Hpre as (_ & cat & operand & Hxs & Hcat & _). injection Hxs as <- Hp.
  destruct Hpost as (cat & operand' & Hxs & Hpost). injection Hxs as <- Hoperand.
  rewrite Hquery in Hpost. destruct Hpost as [[_ Hsame]|[Heq Hselected]]; [exact Hsame|].
  injection Heq as Hpointer. destruct Hr as (_ & _ & Hnames & _).
  pose proof (f_equal ptr_addr Hpointer) as Haddr.
  exfalso. apply (proj1 (Hnames category Hcat)). congruence.
Qed.

End LocaleOn.

(** Standalone compatibility wrapper; logic clients use [LocaleOn] with
    their actual exported machine instance instead. *)
Module Locale (R : Runtime).
Module M := ExternalMachine R.
Include LocaleOn R M.
End Locale.

(** Independent logical controls: non-C names, a separate canonical
    built-in C name, a POSIX input, a mutable empty name, and an unrelated
    caller object. These are not native locale data or a representation proof. *)
Definition locale_fixture : mem := mkMem
  (fun a => if a =? 2048 then 67 else
    if a =? 4096 then 80 else if a =? 4097 then 79 else if a =? 4098 then 83 else
    if a =? 4099 then 73 else if a =? 4100 then 88 else m_bytes hello_mem a)
  [mkRegion 1024 1030 GlobalData Live; mkRegion 2048 2056 GlobalData Live;
   mkRegion 3072 3080 Heap Live; mkRegion 4096 4104 Heap Live; mkRegion 5120 5128 Heap Live]
  (fun _ => CNone).

(** Current names have different authority; canonical C belongs only
    to the internal read-source pool, not to a current name or input. *)
Definition locale_before : locale_world := mkLocaleWorld 0
  (fun category => if category =? 5 then mkPtr 3072 (Obj 3072) else hello_ptr)
  (fun category => if category =? 5 then [] else hello_bytes) (TAtom "non-C")
  [mkSpan (mkPtr 2048 (Ro 2048)) 2] [mkSpan (mkPtr 3072 (Obj 3072)) 8] [].

(** The same physical memory can represent a selected canonical name;
    the logical window changes even though no new allocation is needed. *)
Definition locale_after : locale_world := mkLocaleWorld 1
  (fun _ => mkPtr 2048 (Ro 2048)) (fun _ => [67]) (TAtom "C")
  (locale_reads locale_before) (locale_roots locale_before) [].

(** Both fixture worlds have independently established checked names
    and roots, including the persistent internal readable source. *)
Lemma locale_fixture_ready :
  locale_ready (fun _ _ => True) locale_fixture locale_before /\
  locale_ready (fun _ _ => True) locale_fixture locale_after.
Proof.
  assert (Hroot : Forall (writable_span locale_fixture) (locale_roots locale_before)).
  { constructor; [|constructor]. split; [simpl; lia|].
    exists 3072, (mkRegion 3072 3080 Heap Live). repeat split; reflexivity. }
  assert (Hread : Forall (fun source => readable_bytes locale_fixture (span_ptr source) (span_size source))
    (locale_reads locale_before)).
  { constructor; [|constructor]. split; [simpl; lia|]. split.
    - exists 2048, (mkRegion 2048 2056 GlobalData Live). repeat split; auto.
    - split; [reflexivity|]. intros i Hi. change (0 <= m_bytes locale_fixture (2048 + i) < 256).
      assert (i = 0 \/ i = 1) by (simpl in Hi; lia).
      destruct H as [-> | ->]; vm_compute; intuition congruence. }
  split; split; [exact I| |exact I|]; (split; [exact Hroot|]); split.
  - intros category _. cbn [locale_name locale_text locale_before].
    destruct (category =? 5); vm_compute; repeat split; congruence.
  - split; [exact Hread|]. split; [constructor|].
    intros category _. cbn [locale_name locale_before]. destruct (category =? 5).
    + exists 3072. split; [left; reflexivity|reflexivity].
    + exists 1024. split; [right; reflexivity|reflexivity].
  - intros category _. vm_compute. repeat split; congruence.
  - split; [exact Hread|]. split; [constructor|].
    intros category _. exists 2048. split; [right; reflexivity|reflexivity].
Qed.

(** The character pointer need not be aligned when its object's base is. *)
Example locale_interior_name_aligned :
  let w := mkLocaleWorld 0 (fun _ => mkPtr 1025 (Ro 1024))
    (fun _ => [101; 108; 108; 111]) (TAtom "C") [] [] [] in
  locale_ready (fun _ _ => True) hello_mem w /\
  ptr_addr (locale_name w 0) mod 8 = 1.
Proof.
  split; [|reflexivity]. split; [exact I|]. split; [constructor|]. split.
  - intros category _. vm_compute; repeat split; congruence.
  - split; [constructor|]. split; [constructor|].
    intros category _. exists 1024. split; [right; reflexivity|reflexivity].
Qed.

(** Readability alone admitted this unaligned-base string before the
    strengthened readiness premise. Alignment is an independent fact. *)
Example locale_unaligned_name_rejected :
  let m := mkMem (fun _ => 0) [mkRegion 1025 1026 GlobalData Live] (fun _ => CNone) in
  let w := mkLocaleWorld 0 (fun _ => mkPtr 1025 (Ro 1025))
    (fun _ => []) (TAtom "C") [] [] [] in
  c_string m (locale_name w 0) [] /\ ~ locale_ready (fun _ _ => True) m w.
Proof.
  split; [vm_compute; repeat split; congruence|].
  intros (_ & _ & _ & _ & _ & Haligned).
  destruct (Haligned 0 (or_introl eq_refl)) as (base & [Hcap|Hcap] & Hmod);
    [discriminate Hcap|injection Hcap as <-; discriminate Hmod].
Qed.

(** Ordinary calls use the exact selected W/P signature. *)
Definition locale_call_args : list arg := [Arg W (Const 6); Arg P (Const 0)].

(** One fixed registry supports exact CTYPE and MESSAGES null queries. *)
Module InterpLocale := Locale InterpRuntime.

Example locale_query_calls : forall category, category = 0 \/ category = 5 ->
  InterpLocale.E.invoke (setlocale_contract (fun _ _ => True) (fun _ _ _ _ _ => False))
    (CResult (TAtom "name") P) locale_call_args [WInt category; WPtr (mkPtr 0 CNone)]
    InterpRuntime.start locale_fixture locale_before []
    (CallReturn [WPtr (if category =? 5 then mkPtr 3072 (Obj 3072) else mkPtr 1024 (Ro 1024))])
    InterpRuntime.start locale_fixture locale_before.
Proof.
  intros category Hcat. apply InterpLocale.setlocale_query_admitted.
  - split; [right; eexists; reflexivity|]. eexists; eexists; reflexivity.
  - exact (proj1 locale_fixture_ready).
  - destruct Hcat as [-> | ->]; vm_compute; tauto.
  - reflexivity.
Qed.

(** The source-pool fix matters: canonical C's Ro is not supplied by
    any current name or by the independently allocated POSIX input. *)
Lemma locale_canonical_delegated :
  locale_delegates [WInt 6; WPtr (mkPtr 4096 (Obj 4096))] locale_fixture locale_before []
    locale_fixture locale_after.
Proof.
  destruct (locale_delegates_refl _ [WInt 6; WPtr (mkPtr 4096 (Obj 4096))] _ _
    (proj1 locale_fixture_ready)) as [Hroots [_ [Hreads Howned]]].
  split; [exact Hroots|]. split.
  - intros category _. right. exists (mkSpan (mkPtr 2048 (Ro 2048)) 2).
    split; [unfold locale_private_sources; simpl; auto|reflexivity].
  - split; [exact Hreads|exact Howned].
Qed.

(** A non-C world can switch through POSIX to a separately represented
    canonical C name without fabricating or downgrading its capability. *)
Example locale_canonical_success :
  InterpLocale.E.invoke (setlocale_contract (fun _ _ => True) (fun _ _ _ _ _ => False))
    (CResult (TAtom "name") P) locale_call_args [WInt 6; WPtr (mkPtr 4096 (Obj 4096))]
    InterpRuntime.start locale_fixture locale_before [] (CallReturn [WPtr (mkPtr 2048 (Ro 2048))])
    InterpRuntime.start locale_fixture locale_after.
Proof.
  eapply InterpLocale.setlocale_success_admitted with (bytes := [80; 79; 83; 73; 88])
    (born := []) (w' := locale_after) (category := 6).
  - split; [right; eexists; reflexivity|]. eexists; eexists; reflexivity.
  - exact (proj1 locale_fixture_ready).
  - vm_compute; tauto.
  - discriminate.
  - vm_compute. repeat split; congruence.
  - constructor.
  - exact (proj2 locale_fixture_ready).
  - exact locale_canonical_delegated.
  - split; [right; reflexivity|]. split; intros; congruence.
Qed.

(** Empty environment selection and an input borrowed from an earlier
    query both admit ordinary refusal, without mutating caller data. *)
Example locale_setter_inputs : forall p bytes,
  (p = mkPtr 3072 (Obj 3072) /\ bytes = []) \/ (p = hello_ptr /\ bytes = hello_bytes) ->
  InterpLocale.E.invoke (setlocale_contract (fun _ _ => True) (fun _ _ _ _ _ => False))
    CVoid locale_call_args [WInt 6; WPtr p] InterpRuntime.start locale_fixture locale_before []
    (CallReturn [WPtr (mkPtr 0 CNone)]) InterpRuntime.start locale_fixture locale_before.
Proof.
  intros p bytes Hcases. eapply InterpLocale.setlocale_refusal_admitted with (bytes := bytes).
  - split; [left; reflexivity|]. eexists; eexists; reflexivity.
  - exact (proj1 locale_fixture_ready).
  - vm_compute; tauto.
  - destruct Hcases as [[-> ->]|[-> ->]]; discriminate.
  - destruct Hcases as [[-> ->]|[-> ->]]; vm_compute; repeat split; congruence.
Qed.

(** All public null-query completions have the handwritten exact
    pointer/capability, empty trace and unchanged snapshots. *)
Example locale_query_completions : forall trace ending s' m' w',
  InterpLocale.E.invoke (setlocale_contract (fun _ _ => True) (fun _ _ _ _ _ => False))
    CVoid locale_call_args [WInt 5; WPtr (mkPtr 0 CNone)] InterpRuntime.start locale_fixture
    locale_before trace ending s' m' w' ->
  trace = [] /\ s' = InterpRuntime.start /\ m' = locale_fixture /\ w' = locale_before /\
  ending = CallReturn [WPtr (mkPtr 3072 (Obj 3072))].
Proof.
  intros. eapply InterpLocale.setlocale_query_invocation with
    (category := 5) (w := locale_before) (p := mkPtr 0 CNone);
    [reflexivity|exact H].
Qed.

(** Read/write authority must not grow into exclusive release rights. *)
Example locale_no_ownership_amplification :
  ~ locale_delegates [WInt 6; WPtr hello_ptr] locale_fixture locale_before [] locale_fixture
    (mkLocaleWorld 0 (locale_name locale_before) (locale_text locale_before) (locale_codec locale_before)
      (locale_reads locale_before) (locale_roots locale_before) [3072]).
Proof. intros (_ & _ & _ & Howned). destruct (Howned 3072 (or_introl eq_refl)) as [Hbad _]. exact Hbad. Qed.

(** Equal text alone does not extend a borrow through pointer replacement. *)
Example locale_no_equal_text_window :
  ~ locale_window locale_before
    (mkLocaleWorld 0 (fun _ => mkPtr 5120 (Obj 5120)) (locale_text locale_before)
      (locale_codec locale_before) (locale_reads locale_before) (locale_roots locale_before) []).
Proof.
  intros [[_ [Hnames _]]|Hepoch]; [|discriminate Hepoch].
  pose proof (f_equal (fun names => names 0) Hnames) as H. discriminate H.
Qed.

(** A nonreturned category cannot smuggle the unrelated caller object's
    capability into the world for exposure by a later pure query. *)
Example locale_no_hidden_name :
  ~ locale_delegates [WInt 6; WPtr hello_ptr] locale_fixture locale_before [] locale_fixture
    (mkLocaleWorld 1 (fun category => if category =? 5 then mkPtr 5120 (Obj 5120)
      else locale_name locale_before category) (locale_text locale_before) (locale_codec locale_before)
      (locale_reads locale_before) (locale_roots locale_before) []).
Proof.
  intros (_ & Hnames & _).
  specialize (Hnames 5 ltac:(vm_compute; tauto)).
  assert (Hcaps : Forall (fun source => ptr_cap (span_ptr source) <> Obj 5120)
    (locale_private_sources locale_before)).
  { vm_compute. repeat constructor; discriminate. }
  destruct Hnames as [(base & [] & _)|(source & Hin & Hcap)].
  rewrite Forall_forall in Hcaps. apply (Hcaps source Hin). symmetry. exact Hcap.
Qed.

(** Both transient sources really can supply the caller capability:
    its input pointer and a complete private root slot. Neither may
    become retained authority, even through a zero-sized future span. *)
Definition locale_caller_memory : mem :=
  store_aux locale_fixture 3072 (Ro 5120).

Example locale_caller_transient_only :
  available_cap (locale_sources [WInt 6; WPtr (mkPtr 5120 (Obj 5120))]
    locale_caller_memory locale_before) [] locale_caller_memory (Obj 5120) /\
  available_cap (locale_sources [WInt 6; WPtr (mkPtr 5120 (Obj 5120))]
    locale_caller_memory locale_before) [] locale_caller_memory (Ro 5120) /\
  ~ locale_retained_cap locale_before [] (Obj 5120) /\
  ~ locale_retained_cap locale_before [] (Ro 5120).
Proof.
  split.
  - right. left. exists (mkSpan (mkPtr 5120 (Obj 5120))
      (string_length locale_caller_memory (mkPtr 5120 (Obj 5120)) + 1)).
    split; [unfold locale_sources; apply in_or_app; right; simpl; auto|reflexivity].
  - split.
    + right. right. left. exists (mkSpan (mkPtr 3072 (Obj 3072)) 8), 3072.
      split.
      * unfold locale_sources, locale_private_sources. apply in_or_app. left.
        apply in_or_app. left. apply in_or_app. right. simpl. auto.
      * split; [change (3072 <= 3072 < 3080); lia|]. split; [simpl; lia|].
        split; reflexivity.
    + assert (Hcaps : Forall (fun source => ptr_cap (span_ptr source) <> Obj 5120 /\
        ptr_cap (span_ptr source) <> Ro 5120) (locale_private_sources locale_before)).
      { vm_compute. repeat constructor; discriminate. }
      split; intros [(base & [] & _)|(source & Hin & Hcap)];
        rewrite Forall_forall in Hcaps; destruct (Hcaps source Hin) as [Hobj Hro]; congruence.
Qed.

(** Each role independently attempts the two-call laundering step:
    installing the caller as a name, a zero-sized read, or a zero-sized
    root. A subsequent query/setter can never receive such a pool. *)
Definition locale_caller_endpoint (role : Z) : locale_world :=
  mkLocaleWorld 1
    (if role =? 0 then fun _ => mkPtr 5120 (Obj 5120) else locale_name locale_before)
    (if role =? 0 then fun _ => [] else locale_text locale_before)
    (locale_codec locale_before)
    (if role =? 1 then mkSpan (mkPtr 5120 (Obj 5120)) 0 :: locale_reads locale_before
      else locale_reads locale_before)
    (if role =? 2 then mkSpan (mkPtr 5120 (Obj 5120)) 0 :: locale_roots locale_before
      else locale_roots locale_before) [].

Example locale_no_caller_endpoint : forall role, role = 0 \/ role = 1 \/ role = 2 ->
  ~ locale_delegates [WInt 6; WPtr (mkPtr 5120 (Obj 5120))]
    locale_caller_memory locale_before [] locale_caller_memory (locale_caller_endpoint role).
Proof.
  intros role Hrole Hd. apply (proj1 (proj2 (proj2 locale_caller_transient_only))).
  destruct Hrole as [-> | [-> | ->]].
  - apply (locale_delegates_private _ _ _ _ _ _
      (locale_name_span (locale_caller_endpoint 0) 0) Hd).
    unfold locale_private_sources. apply in_or_app. right. apply in_map.
    simpl. auto.
  - apply (locale_delegates_private _ _ _ _ _ _ (mkSpan (mkPtr 5120 (Obj 5120)) 0) Hd).
    unfold locale_private_sources. apply in_or_app. left. apply in_or_app. left. simpl. auto.
  - apply (locale_delegates_private _ _ _ _ _ _ (mkSpan (mkPtr 5120 (Obj 5120)) 0) Hd).
    unfold locale_private_sources. apply in_or_app. left. apply in_or_app. right. simpl. auto.
Qed.

(** Public-call rejection: no-request setters cannot install any of
    those future pools. The effects path cannot disguise caller storage
    as a fresh allocation by choosing a nonempty born list. *)
Example locale_no_caller_call : forall role r args s trace ending s',
  role = 0 \/ role = 1 \/ role = 2 ->
  ~ InterpLocale.E.invoke (setlocale_contract (fun _ _ => True) (fun _ _ _ _ _ => False))
    r args [WInt 6; WPtr (mkPtr 5120 (Obj 5120))] s locale_caller_memory locale_before
    trace ending s' locale_caller_memory (locale_caller_endpoint role).
Proof.
  intros role r args s trace ending s' Hrole Hcall.
  destruct (InterpLocale.setlocale_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as (_ & _ & born & He & Hpost).
  assert (born = []) as ->.
  { clear -He. induction He; [reflexivity|exact IHHe|]. destruct H as [_ Hfalse]. contradiction. }
  cbn [locale_query ptr_addr Z.eqb] in Hpost.
  destruct Hpost as (_ & Hd & _). exact (locale_no_caller_endpoint role Hrole Hd).
Qed.

(** Born allocation authority permits interior name pointers without
    aligning their character addresses or inventing old-object authority. *)
Example locale_fresh_interior_retained : forall base,
  locale_retained_cap locale_before [base] (ptr_cap (mkPtr (base + 1) (Obj base))) /\
  locale_retained_cap locale_before [base] (ptr_cap (mkPtr (base + 3) (Ro base))).
Proof. intros base. split; left; exists base; simpl; auto. Qed.

(** Model access at address zero can be readable, but a current locale
    name there is independently rejected as NULL. *)
Example locale_zero_name_rejected :
  let m := mkMem (fun _ => 0) [mkRegion 0 1 GlobalData Live] (fun _ => CNone) in
  let w := mkLocaleWorld 0 (fun _ => mkPtr 0 (Obj 0)) (fun _ => []) (TAtom "C") [] [] [] in
  c_string m (mkPtr 0 (Obj 0)) [] /\ ~ locale_ready (fun _ _ => True) m w.
Proof.
  split; [vm_compute; repeat split; congruence|].
  intros (_ & _ & Hnames & _). exact (proj1 (Hnames 0 (or_introl eq_refl)) eq_refl).
Qed.

(** A real runtime refusal is a different invocation from a NULL return;
    the permitted request is witnessed, not inferred from admission. *)
Example locale_resource_call :
  InterpLocale.E.invoke (setlocale_contract (fun _ _ => True)
    (fun _ _ _ align size => align = 16 /\ size = 32)) CVoid locale_call_args
    [WInt 6; WPtr hello_ptr] InterpRuntime.address_end locale_fixture locale_before []
    (CallResource OutOfMemory) InterpRuntime.address_end locale_fixture locale_before.
Proof.
  eapply InterpLocale.E.invoke_resource with (born := []).
  - split; [left; reflexivity|]. eexists; eexists; reflexivity.
  - split; [exact (proj1 locale_fixture_ready)|]. exists 6, hello_ptr. split; [reflexivity|].
    split; [vm_compute; tauto|]. right. exists hello_bytes. vm_compute. repeat split; congruence.
  - split; [constructor|]. split; [reflexivity|].
    split; [exact (proj1 locale_fixture_ready)|].
    split; [eapply locale_delegates_refl; exact (proj1 locale_fixture_ready)|].
    exists 6, hello_ptr. split; [reflexivity|]. left. apply locale_unchanged_refl.
  - eapply InterpLocale.E.failure_oom with (align := 16) (size := 32).
    + repeat split; reflexivity.
    + unfold max_allocation_size. lia.
    + reflexivity.
  - left. reflexivity.
Qed.

(** Invalid categories and ABI classes are not libc refusals. Query
    permissions and requests stay empty even under a broad setter policy. *)
Example locale_query_permissions_and_bad_abi :
  locale_writes [WInt 0; WPtr (mkPtr 0 CNone)] locale_before = [] /\
  locale_releases [WInt 0; WPtr (mkPtr 0 CNone)] locale_before = [] /\
  (forall align size, ~ contract_requests (setlocale_contract (fun _ _ => True)
    (fun _ _ _ _ _ => True)) [WInt 0; WPtr (mkPtr 0 CNone)] locale_fixture locale_before align size) /\
  ~ setlocale_abi (CResult (TAtom "bad") W) locale_call_args /\
  ~ setlocale_pre (fun _ _ => True) [WInt 13; WPtr (mkPtr 0 CNone)] locale_fixture locale_before.
Proof.
  split; [reflexivity|]. split; [reflexivity|]. split; [intros ? ? [H _]; discriminate H|]. split.
  - intros [[H|(d & H)] _]; discriminate H.
  - intros (_ & category & p & Hxs & Hcat & _). injection Hxs as <- Hp.
    vm_compute in Hcat. intuition discriminate.
Qed.
