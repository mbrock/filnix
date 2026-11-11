(** Selected stream queries and close, over explicit projections of the
    application's libc world. [stream_protocol] is a projection, not a
    second stdout queue: the composite world must use its authoritative
    shutdown stdout. Physical buffering and ownership are separate.
    These are trusted libc contracts, not a native adequacy proof. *)
From Stdlib Require Import ZArith List Bool Lia.
From Nanofil Require Import Syntax Values Memory Runtime ExternalCalls ExternalMachine Stdio.
Import ListNotations.
Open Scope Z_scope.

(** An open stream's identifier, logical protocol and physical buffered
    count. In wide mode the count is in wide characters, not bytes. *)
Record stream_info : Type := mkStreamInfo {
  stream_identifier : Z;
  stream_protocol : stream_state;
  stream_pending : Z
}.

(** The integration obligations for a selected native stream. [stream_rep]
    includes native FILE validity, lock/TLS sources, orientation, physical
    buffering, and exclusive close ownership. Releases name only owned
    heap objects, never caller-owned setvbuf storage or static FILEs.
    [stream_frame] preserves unrelated state, including the shutdown
    callback inventory, but may change errno. Effects separately frame
    caller memory. [stream_state_at] survives handle consumption and MUST
    project the same authoritative shutdown stdout, not store a copy.
    Wide realization must cover physical buffering and shared conversion
    cache mutations; a reference-count decrement is not an owned free.
    No projection grants authority merely by its address. *)
Record stream_model (world : Type) : Type := mkStreamModel {
  stream_at : world -> ptr -> option stream_info;
  stream_state_at : world -> ptr -> stream_state;
  stream_rep : mem -> world -> Prop;
  stream_sources : world -> ptr -> list span;
  stream_writes : world -> ptr -> list span;
  stream_aux_roots : world -> ptr -> list span;
  stream_releases : world -> ptr -> list Z;
  stream_requests : world -> ptr -> Z -> Z -> Prop;
  stream_frame : ptr -> world -> world -> Prop;
  stream_wide_settlement : world -> ptr -> stream_state -> stream_state -> bool -> Prop
}.
Arguments stream_at {world}.
Arguments stream_state_at {world}.
Arguments stream_rep {world}.
Arguments stream_sources {world}.
Arguments stream_writes {world}.
Arguments stream_aux_roots {world}.
Arguments stream_releases {world}.
Arguments stream_requests {world}.
Arguments stream_frame {world}.
Arguments stream_wide_settlement {world}.

(** Scalar-only roots (notably errno) need not authorize aux mutation.
    Test entry memory, not historical born objects after a release. The
    ordinary effects path still bounds all writes independently. *)
Definition stream_aux_frame {world} (model : stream_model world)
    (m : mem) (w : world) (p : ptr) (m' : mem) : Prop :=
  forall a, in_object m a ->
    ~ write_authority (stream_aux_roots model w p) [] m a -> m_aux m' a = m_aux m a.

(** Canonical physical size_t and a well-formed logical protocol. A
    physical count is deliberately not equated with outstanding output. *)
Definition stream_info_wf (info : stream_info) : Prop :=
  stream_wf (stream_protocol info) /\ 0 <= stream_pending info < 2 ^ 64.

(** A selected handle is open, represented and has writable stream roots.
    The stronger native representation is an independent premise. *)
Definition stream_open {world} (model : stream_model world)
    (m : mem) (w : world) (p : ptr) (info : stream_info) : Prop :=
  stream_rep model m w /\ stream_at model w p = Some info /\
  stream_protocol info = stream_state_at model w p /\
  stream_info_wf info /\ Forall (writable_span m) (stream_writes model w p).

(** Canonical signed int results are carried as unsigned W bits. *)
Definition negative_int (result : Z) : Prop := 2 ^ 31 <= result < 2 ^ 32.

(** EOF at this glibc pin, not a mathematical negative machine word. *)
Definition stream_eof : Z := 2 ^ 32 - 1.

(** One pointer argument and a discarded or correctly classed result. *)
Definition stream_query_abi (cls : class) (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d cls) /\ exists v, args = [Arg P v].

(** Readable caller arguments cannot delegate new persistent writable
    roots: only the old stream roots and fresh allocations may do so.
    Future private sources retain old source capabilities or born ones;
    future release rights retain old ownership or fresh allocation. A
    writable root alone is not evidence of exclusive release ownership. *)
Definition stream_delegates {world} (model : stream_model world)
    (w : world) (p : ptr) (born : list Z) (m' : mem) (w' : world) : Prop :=
  (forall root, In root (stream_writes model w' p) ->
    available_cap (stream_sources model w p) born m' (ptr_cap (span_ptr root)) /\
    forall a, span_contains root a -> write_authority (stream_writes model w p) born m' a) /\
  (forall source, In source (stream_sources model w' p) ->
    (exists old, In old (stream_sources model w p) /\
      ptr_cap (span_ptr source) = ptr_cap (span_ptr old)) \/
    (exists base, In base born /\
      (ptr_cap (span_ptr source) = Obj base \/ ptr_cap (span_ptr source) = Ro base))) /\
  (forall base, In base (stream_releases model w' p) ->
    In base (stream_releases model w p) \/ In base born).

(** Admission to queries and close is independent of the chosen result. *)
Definition stream_call_pre {world} (model : stream_model world)
    (xs : list word) (m : mem) (w : world) : Prop :=
  exists p info, xs = [WPtr p] /\ stream_open model m w p info.

(** ferror observes the error flag without changing the stream. Its
    nonzero return is not specified as one. Locks may still mutate. *)
Definition ferror_post {world} (model : stream_model world)
    (xs : list word) (m : mem) (w : world) (born : list Z)
    (trace : list event) (ending : call_end) (m' : mem) (w' : world) : Prop :=
  exists p info result, xs = [WPtr p] /\ stream_at model w p = Some info /\
    stream_open model m' w' p info /\ stream_frame model p w w' /\
    stream_delegates model w p born m' w' /\ trace = [] /\
    ending = CallReturn [WInt result] /\ 0 <= result < 2 ^ 32 /\
    (result = 0 <-> stream_error (stream_protocol info) = false).

(** __fpending returns the physical count, preserving stream state. *)
Definition fpending_post {world} (model : stream_model world)
    (xs : list word) (m : mem) (w : world) (born : list Z)
    (trace : list event) (ending : call_end) (m' : mem) (w' : world) : Prop :=
  exists p info, xs = [WPtr p] /\ stream_at model w p = Some info /\
    stream_open model m' w' p info /\ stream_frame model p w w' /\
    stream_delegates model w p born m' w' /\ trace = [] /\
    ending = CallReturn [WInt (stream_pending info)].

(** Query prefixes preserve the selected open stream and have no output.
    Queries may lock private FILE storage, but preserve caller bytes and
    scalar errno. This is a trusted entry-memory frame, not a consequence
    of the larger ordinary write footprint. Queries do not allocate,
    hence have no modeled resource ending. *)
Definition query_prefix {world} (model : stream_model world)
    (xs : list word) (m : mem) (w : world) (born : list Z)
    (trace : list event) (m' : mem) (w' : world) : Prop :=
  exists p info, xs = [WPtr p] /\ stream_at model w p = Some info /\
    stream_open model m' w' p info /\ stream_frame model p w w' /\
    stream_delegates model w p born m' w' /\ trace = [] /\ stream_aux_frame model m w p m' /\
    forall a, in_object m a ->
      ~ write_authority (stream_aux_roots model w p) [] m a -> m_bytes m' a = m_bytes m a.

(** ferror's exact P-to-W contract. *)
Definition ferror_contract {world} (model : stream_model world) : contract world :=
  mkContract world (RClass W) (stream_query_abi W) (stream_call_pre model)
    (fun xs _ w => match xs with [WPtr p] => stream_sources model w p | _ => [] end)
    (fun xs _ w => match xs with [WPtr p] => stream_writes model w p | _ => [] end)
    (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (query_prefix model) (ferror_post model) (fun _ => False) puts_panic.

(** __fpending's exact P-to-L contract; its C symbol has two underscores. *)
Definition fpending_contract {world} (model : stream_model world) : contract world :=
  mkContract world (RClass L) (stream_query_abi L) (stream_call_pre model)
    (fun xs _ w => match xs with [WPtr p] => stream_sources model w p | _ => [] end)
    (fun xs _ w => match xs with [WPtr p] => stream_writes model w p | _ => [] end)
    (fun _ _ _ => []) (fun _ _ _ _ _ => False)
    (query_prefix model) (fpending_post model) (fun _ => False) puts_panic.

(** An owned release has consumed a heap object's lifetime, including
    on EOF. The capability remains an identity, but is no longer live. *)
Definition stream_consumed (m : mem) (bases : list Z) : Prop :=
  forall base, In base bases ->
    object_region base (m_regions m) = Some (mkRegion base base Heap Freed).

(** Byte settlement uses the existing FIFO without new acceptance.
    Wide settlement instead requires independent selected native coverage
    of conversion and physical buffering, including completion when
    [complete] is true. It uses the same orientation/error projection;
    there is no wide queue hidden in the byte protocol. *)
Definition stream_settlement {world} (model : stream_model world)
    (w : world) (p : ptr) (old final : stream_state) (complete : bool) : Prop :=
  match orientation old with
  | WideOriented =>
      stream_wide_settlement model w p old final complete /\
      orientation final = WideOriented /\ outstanding final = [] /\
      (stream_error old = true -> stream_error final = true)
  | _ => exists actions,
      stream_run old actions final /\ accepted actions = [] /\
      (complete = true -> outstanding final = [])
  end.

(** Completed settlement empties the authoritative protocol; wide
    physical settlement additionally needs the supplied realization. *)
Lemma stream_settlement_complete : forall world (model : stream_model world) w p old final,
  stream_settlement model w p old final true -> outstanding final = [].
Proof.
  intros world model w p old final H. unfold stream_settlement in H.
  destruct (orientation old).
  - destruct H as (actions & _ & _ & Hdone). auto.
  - destruct H as (actions & _ & _ & Hdone). auto.
  - tauto.
Qed.

(** A close prefix may settle old output but never accept new output.
    A resource stop need not have closed the stream or released storage.
    Wide-stream settlement remains an explicit integration obligation. *)
Definition fclose_prefix {world} (model : stream_model world)
    (xs : list word) (m : mem) (w : world) (born : list Z)
    (trace : list event) (m' : mem) (w' : world) : Prop :=
  exists p info final,
    xs = [WPtr p] /\ stream_at model w p = Some info /\
    stream_settlement model w p (stream_protocol info) final false /\
    stream_state_at model w' p = final /\
    stream_rep model m' w' /\ stream_frame model p w w' /\
    stream_delegates model w p born m' w' /\ trace = [] /\
    (stream_at model w' p = None \/ exists info',
      stream_at model w' p = Some info' /\ stream_protocol info' = final) /\
    stream_aux_frame model m w p m'.

(** Close settles all old obligations in FIFO order (delivery OR error
    discard), consumes the handle and owned heaps on both result paths.
    A descriptor close failure can return EOF after all output delivered. *)
Definition fclose_post {world} (model : stream_model world)
    (xs : list word) (m : mem) (w : world) (born : list Z)
    (trace : list event) (ending : call_end) (m' : mem) (w' : world) : Prop :=
  exists p info final result,
    xs = [WPtr p] /\ stream_at model w p = Some info /\
    stream_settlement model w p (stream_protocol info) final true /\
    stream_state_at model w' p = final /\
    (result = 0 \/ result = stream_eof) /\
    stream_at model w' p = None /\ stream_consumed m' (stream_releases model w p) /\
    stream_rep model m' w' /\ stream_frame model p w w' /\ trace = [] /\
    ending = CallReturn [WInt result].

(** P-to-W close with separate ownership and request footprints. *)
Definition fclose_contract {world} (model : stream_model world) : contract world :=
  mkContract world (RClass W) (stream_query_abi W) (stream_call_pre model)
    (fun xs _ w => match xs with [WPtr p] => stream_sources model w p | _ => [] end)
    (fun xs _ w => match xs with [WPtr p] => stream_writes model w p | _ => [] end)
    (fun xs _ w => match xs with [WPtr p] => stream_releases model w p | _ => [] end)
    (fun xs _ w => match xs with [WPtr p] => stream_requests model w p | _ => fun _ _ => False end)
    (fclose_prefix model) (fclose_post model) resource_reason puts_panic.

(** Consequences of trusted calls over any runtime, without changing
    the supplied machine or adding runtime axioms. *)
Module StreamsOn (R : Runtime) (M : ExternalMachineSig R).
Module E := M.E.

(** Construct a normal query from independently established effects and
    postconditions. Prefix and native representation are not inferred. *)
Theorem ferror_return : forall world (model : stream_model world)
    r args xs s m w born trace result s' m' w',
  stream_query_abi W r args -> stream_call_pre model xs m w ->
  E.prefix (ferror_contract model) xs s m w born trace s' m' w' ->
  ferror_post model xs m w born trace (CallReturn [WInt result]) m' w' ->
  E.invoke (ferror_contract model) r args xs s m w trace (CallReturn [WInt result]) s' m' w'.
Proof.
  intros world model r args xs s m w born trace result s' m' w' Habi Hpre Hprefix Hpost.
  eapply E.invoke_normal with (born := born); try exact Habi; try exact Hpre;
    try exact Hprefix; try exact Hpost; try discriminate.
  intros values Heq. injection Heq as <-. split; [|constructor; [exact I|constructor]].
  exists (WInt result). split; [reflexivity|]. simpl.
  destruct Hpost as (p & info & n & _ & _ & _ & _ & _ & _ & Hend & Hrange & _).
  injection Hend as <-. rewrite Z.mod_small by exact Hrange. reflexivity.
Qed.

(** ferror cannot take the resource rule: its request set is empty. *)
Theorem ferror_invocation : forall world (model : stream_model world)
    r args xs s m w trace ending s' m' w',
  E.invoke (ferror_contract model) r args xs s m w trace ending s' m' w' ->
  exists born, ferror_post model xs m w born trace ending m' w'.
Proof.
  intros world model r args xs s m w trace ending s' m' w' Hcall.
  inversion Hcall; subst.
  - match goal with Hpost : contract_post _ _ _ _ ?born _ _ _ _ |- _ =>
      exists born; exact Hpost end.
  - contradiction.
Qed.

(** __fpending likewise has only ordinary query completions. *)
Theorem fpending_invocation : forall world (model : stream_model world)
    r args xs s m w trace ending s' m' w',
  E.invoke (fpending_contract model) r args xs s m w trace ending s' m' w' ->
  exists born, fpending_post model xs m w born trace ending m' w'.
Proof.
  intros world model r args xs s m w trace ending s' m' w' Hcall.
  inversion Hcall; subst.
  - match goal with Hpost : contract_post _ _ _ _ ?born _ _ _ _ |- _ =>
      exists born; exact Hpost end.
  - contradiction.
Qed.

(** A resource-ending close has no ordinary-return postcondition. *)
Theorem fclose_invocation : forall world (model : stream_model world)
    r args xs s m w trace ending s' m' w',
  E.invoke (fclose_contract model) r args xs s m w trace ending s' m' w' ->
  (exists born, fclose_post model xs m w born trace ending m' w') \/
  (exists why, ending = CallResource why /\ resource_reason why).
Proof.
  intros world model r args xs s m w trace ending s' m' w' Hcall.
  inversion Hcall; subst.
  - left. match goal with Hpost : contract_post _ _ _ _ ?born _ _ _ _ |- _ =>
      exists born; exact Hpost end.
  - right. eauto.
Qed.

(** A returning close consumes its handle and owned heap storage and
    settles the surviving authoritative protocol, on both 0 and EOF. *)
Theorem fclose_return_consumes : forall world (model : stream_model world)
    r args p s m w trace result s' m' w',
  E.invoke (fclose_contract model) r args [WPtr p] s m w trace
    (CallReturn [WInt result]) s' m' w' ->
  stream_at model w' p = None /\ stream_consumed m' (stream_releases model w p) /\
    outstanding (stream_state_at model w' p) = [] /\ (result = 0 \/ result = stream_eof).
Proof.
  intros world model r args p s m w trace result s' m' w' Hcall.
  destruct (fclose_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ Hcall)
    as [(born & q & info & final & n & Hargs & _ & Hsettle & Hfinal & Hresult & Hclosed & Hfree & _ & _ & _ & Hend)
      | (why & Hbad & _)]; [|discriminate Hbad].
  injection Hargs as <-. injection Hend as <-. rewrite Hfinal.
  repeat split; try assumption. eapply stream_settlement_complete; exact Hsettle.
Qed.

End StreamsOn.

(** Standalone compatibility wrapper; logic clients supply their own
    machine to [StreamsOn] so its invocation type is exactly theirs. *)
Module Streams (R : Runtime).
Module M := ExternalMachine R.
Include StreamsOn R M.
End Streams.

(** Physical buffering and protocol outstanding bytes are independent. *)
Example pending_is_not_outstanding :
  stream_info_wf (mkStreamInfo 1 (mkStream ByteOriented [65; 66] false) 0).
Proof.
  unfold stream_info_wf, stream_wf. simpl.
  split; [split; [repeat constructor; lia|auto]|lia].
Qed.

(** A canonical non-one error result is admitted by the result relation. *)
Example ferror_nonone : 0 <= 32 < 2 ^ 32 /\ (32 = 0 <-> true = false).
Proof. split; [lia|split; discriminate]. Qed.
