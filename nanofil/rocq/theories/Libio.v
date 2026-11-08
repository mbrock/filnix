(** A [[capability]]-backed memory view of the pinned byte stdout
    ([milestone 3c](../../docs/formal.md#campaign-4-milestone-3c-selected-native-stdout-memory)).

    Offsets are measured with the Fil-C headers, not the host's FILE.
    This is a view of the buffer/lock roots, not a complete predicate
    for native FILE validity or a proof of libio's execution. In
    particular, vtable dispatch, TLS initialization, protocol scheduling
    and native prefix coverage remain trusted realization
    [[obligation|obligations]].

    The selected malloc forwards to zgc_alloc: runtime refusal does
    not return NULL to _IO_file_doallocate. The generic libio NULL
    fallback and the pin's terminal resource ending are distinct. *)

From Stdlib Require Import ZArith List Bool Lia.
From Nanofil Require Import Syntax Values Memory Runtime Identity ExternalCalls Startup.
Import ListNotations.
Open Scope Z_scope.

(** ## Source-selected capacity and buffer paths *)

(** The byte capacity of stdout's allocated buffer, given whether stat
    succeeded and the block size it reported. As filedoalloc.c, for the
    selected stdout descriptor 1 and the pinned x86-64
    _STATBUF_ST_BLKSIZE configuration: use a positive st_blksize smaller
    than BUFSIZ (8192) only after a successful stat; otherwise retain
    BUFSIZ. This is NOT the capacity function for arbitrary
    descriptors. *)
Definition file_capacity (stat_ok : bool) (block_size : Z) : Z :=
  if stat_ok && (0 <? block_size) && (block_size <? 8192)
  then block_size else 8192.

(** The capacity is always positive and at most 8192 bytes, so the
    buffer request is never too big. *)
Lemma file_capacity_bounds : forall stat_ok block_size,
  0 < file_capacity stat_ok block_size <= 8192.
Proof.
  intros. unfold file_capacity.
  destruct (stat_ok && (0 <? block_size) && (block_size <? 8192)) eqn:E; [|lia].
  apply andb_true_iff in E as [E Hhi]. apply andb_true_iff in E as [_ Hlo].
  apply Z.ltb_lt in Hhi. apply Z.ltb_lt in Hlo. lia.
Qed.

(** Where stdout's buffer lives: no buffer yet, the one-byte buffer
    embedded in the FILE (_shortbuf), or a heap buffer of size bytes at
    base. *)
Inductive buffer_storage : Type :=
| NoBuffer
| ShortBuffer
| HeapBuffer (base size : Z).

(** Why libio picks a buffer: one already exists, the stream is
    unbuffered, malloc returned base, or malloc returned NULL. These
    causes describe libio's control flow, not R.alloc's result.
    MallocNull is useful for generic libio, but is excluded at this pin.
    Unbuffered is for a byte stream: wide orientation takes another path. *)
Inductive buffer_cause : Type :=
| Existing | Unbuffered | MallocSuccess (base : Z) | MallocNull.

(** Generic libio's buffer choice, from the old storage for a cause to
    the new: an existing buffer is kept; with no buffer, an unbuffered
    stream or a NULL malloc falls back to the embedded byte, and a
    successful malloc gives a heap buffer of the given capacity. *)
Inductive buffer_choice (capacity : Z)
    : buffer_storage -> buffer_cause -> buffer_storage -> Prop :=
| choice_existing : forall storage,
    storage <> NoBuffer -> buffer_choice capacity storage Existing storage
| choice_unbuffered : buffer_choice capacity NoBuffer Unbuffered ShortBuffer
| choice_allocated : forall base,
    buffer_choice capacity NoBuffer (MallocSuccess base) (HeapBuffer base capacity)
| choice_null : buffer_choice capacity NoBuffer MallocNull ShortBuffer.

(** The pin's buffer choice: a [buffer_choice] whose cause is not a NULL
    malloc, since this glibc's malloc ends the run on refusal instead. *)
Definition pinned_choice (capacity : Z) (old : buffer_storage)
    (cause : buffer_cause) (new : buffer_storage) : Prop :=
  buffer_choice capacity old cause new /\ cause <> MallocNull.

(** ## Measured pointer slots and writable roots *)

(** The pointers, with their capabilities, through which stdout's state
    is reached: the FILE, its lock, and errno. *)
Record stdout_roots : Type := mkStdoutRoots {
  file_ptr : ptr;
  lock_ptr : ptr;
  errno_ptr : ptr
}.

(** The writable spans of the FILE, lock and errno.
    stdfiles.c allocates _IO_FILE_plus: FILE (216) plus its vtable
    pointer (8). NPTL's lock is { int lock; int cnt; void *owner; }.
    errno is a separate four-byte TLS cell. These spans are authority
    supplied by the caller of the trusted boundary, never inferred
    just from the addresses stored in FILE. *)
Definition fixed_roots (r : stdout_roots) : list span :=
  [mkSpan (file_ptr r) 224; mkSpan (lock_ptr r) 16; mkSpan (errno_ptr r) 4].

(** A pointer to the FILE's embedded one-byte buffer (_shortbuf, at
    offset 131), with the FILE's own capability. *)
Definition short_ptr (r : stdout_roots) : ptr :=
  mkPtr (ptr_addr (file_ptr r) + 131) (ptr_cap (file_ptr r)).

(** The span of the buffer the storage names: none, the embedded byte,
    or the heap buffer with an [Obj] capability for its base. *)
Definition buffer_span (r : stdout_roots) (storage : buffer_storage) : option span :=
  match storage with
  | NoBuffer => None
  | ShortBuffer => Some (mkSpan (short_ptr r) 1)
  | HeapBuffer base size => Some (mkSpan (mkPtr base (Obj base)) size)
  end.

(** All of stdout's writable roots: the [fixed_roots], plus a heap
    buffer's span. The embedded byte needs no root of its own: it is
    inside the FILE's. *)
Definition memory_roots (r : stdout_roots) (storage : buffer_storage) : list span :=
  fixed_roots r ++
    match storage with
    | HeapBuffer base size => [mkSpan (mkPtr base (Obj base)) size]
    | _ => []
    end.

(** In memory m, the FILE's _IO_buf_base and _IO_buf_end slots (offsets
    56 and 64) hold, as a [pointer_slot] with address bytes and
    [[aux]], the start and end of the storage's buffer, or null when
    there is none. The end pointer keeps the buffer's capability. *)
Definition buffer_slots (m : mem) (r : stdout_roots) (storage : buffer_storage) : Prop :=
  let a := ptr_addr (file_ptr r) in
  match buffer_span r storage with
  | None => pointer_slot m (a + 56) (mkPtr 0 CNone) /\
            pointer_slot m (a + 64) (mkPtr 0 CNone)
  | Some s => pointer_slot m (a + 56) (span_ptr s) /\
      pointer_slot m (a + 64)
        (mkPtr (ptr_addr (span_ptr s) + span_size s) (ptr_cap (span_ptr s)))
  end.

(** Memory m holds stdout's selected state for roots r and storage:
    - every root of [memory_roots] is a [writable_span];
    - the whole FILE and its three pointer slots (56, 64 and the lock
      slot 136) are readable, 8-aligned; the lock and errno writable;
    - the lock slot points at the lock, and [buffer_slots] holds;
    - a heap buffer is nonempty and a live heap object.

    This view supplies actual address bytes and [[aux]], not a detached
    logical list of roots. Heap kind, liveness and buffer bounds are
    checked independently of the two pointer slots. It intentionally
    does not describe ownership, flags, orientation, pending bytes or
    lock state. These are selected roots, NOT a complete puts footprint:
    storing THREAD_SELF in lock.owner needs another capability source. *)
Definition stdout_memory (m : mem) (r : stdout_roots) (storage : buffer_storage) : Prop :=
  Forall (writable_span m) (memory_roots r storage) /\
  access_res m (ptr_addr (file_ptr r)) (ptr_cap (file_ptr r)) 224 Read 8 = Some ok /\
  Forall (fun offset => access_res m (ptr_addr (file_ptr r) + offset)
    (ptr_cap (file_ptr r)) 8 Read 8 = Some ok) [56; 64; 136] /\
  access_res m (ptr_addr (lock_ptr r)) (ptr_cap (lock_ptr r)) 16 Write 8 = Some ok /\
  access_res m (ptr_addr (errno_ptr r)) (ptr_cap (errno_ptr r)) 4 Write 4 = Some ok /\
  pointer_slot m (ptr_addr (file_ptr r) + 136) (lock_ptr r) /\
  buffer_slots m r storage /\
  match storage with
  | HeapBuffer base size =>
      0 < size /\ exists reg, object_region base (m_regions m) = Some reg /\
        r_kind reg = Heap /\ r_life reg = Live
  | _ => True
  end.

(** The [stdio_world] this view gives: a usable stdout whose roots are
    [memory_roots]. *)
Definition memory_world (r : stdout_roots) (storage : buffer_storage) : stdio_world :=
  mkStdioWorld true (memory_roots r storage).

(** Where [stdout_memory] holds, its world is [stdio_ready], as
    [puts_pre] requires. *)
Theorem stdout_memory_ready : forall m r storage,
  stdout_memory m r storage -> stdio_ready m (memory_world r storage).
Proof. intros m r storage [H _]. split; [reflexivity|exact H]. Qed.

(** Where the fixed roots are writable, the embedded buffer's capability
    is available from them and its byte is under their write authority:
    it neither allocates nor expands root authority. Its one byte is
    already inside the FILE root, with the SAME capability. *)
Theorem short_buffer_delegates : forall m r,
  Forall (writable_span m) (fixed_roots r) ->
  available_cap (fixed_roots r) [] m (ptr_cap (short_ptr r)) /\
  forall a, span_contains (mkSpan (short_ptr r) 1) a ->
    write_authority (fixed_roots r) [] m a.
Proof.
  intros m r Hroots. split.
  - right. left. exists (mkSpan (file_ptr r) 224). simpl. auto.
  - intros a Ha. left. exists (mkSpan (file_ptr r) 224).
    inversion Hroots as [|s rest Hw Hrest]; subst. split; [simpl; auto|].
    split; [exact Hw|]. unfold span_contains, short_ptr in *. simpl in *. lia.
Qed.

(** ## Installing a buffer from the null-buffer state

    This is _IO_setb's selected no-old-buffer case. The two pointer
    stores change bytes AND aux; the four-byte flags store changes only
    _IO_USER_BUF. No release is hidden in this construction. Selection
    of this path still needs NoBuffer and backend/mode premises. *)
Definition install_buffer (m : mem) (r : stdout_roots) (storage : buffer_storage) : mem :=
  match buffer_span r storage with
  | None => m
  | Some s =>
      let a := ptr_addr (file_ptr r) in
      let p := span_ptr s in
      let m1 := store_aux (store_bytes m (a + 56) 8 (ptr_addr p)) (a + 56) (ptr_cap p) in
      let m2 := store_aux (store_bytes m1 (a + 64) 8 (ptr_addr p + span_size s))
        (a + 64) (ptr_cap p) in
      store_bytes m2 a 4
        (match storage with
         | HeapBuffer _ _ => Z.land (load_bytes m a 4) (-2)
         | _ => Z.lor (load_bytes m a 4) 1
         end)
  end.

Theorem installed_buffer_slots : forall m r storage s,
  buffer_span r storage = Some s ->
  0 <= ptr_addr (span_ptr s) < 2 ^ 64 ->
  0 <= ptr_addr (span_ptr s) + span_size s < 2 ^ 64 ->
  buffer_slots (install_buffer m r storage) r storage.
Proof.
  intros m r storage s Hs Hp Hend. unfold buffer_slots, install_buffer. rewrite Hs. split.
  - apply pointer_slot_bytes_disjoint; [lia|right; simpl; lia|].
    eapply pointer_slot_pointer_disjoint with
      (p := mkPtr (ptr_addr (span_ptr s) + span_size s) (ptr_cap (span_ptr s)));
      [left; lia|]. apply pointer_slot_written. exact Hp.
  - apply pointer_slot_bytes_disjoint; [lia|right; simpl; lia|].
    apply (pointer_slot_written _ _
      (mkPtr (ptr_addr (span_ptr s) + span_size s) (ptr_cap (span_ptr s)))). exact Hend.
Qed.

Theorem installed_user_buffer_flag : forall m r storage s,
  buffer_span r storage = Some s ->
  load_bytes (install_buffer m r storage) (ptr_addr (file_ptr r)) 4 =
    (match storage with
     | HeapBuffer _ _ => Z.land (load_bytes m (ptr_addr (file_ptr r)) 4) (-2)
     | _ => Z.lor (load_bytes m (ptr_addr (file_ptr r)) 4) 1
     end) mod 2 ^ 32.
Proof.
  intros m r storage s Hs. unfold install_buffer. rewrite Hs.
  rewrite stored_bytes_value by lia. reflexivity.
Qed.

Lemma file_write_authority : forall m r born a,
  Forall (writable_span m) (fixed_roots r) ->
  ptr_addr (file_ptr r) <= a < ptr_addr (file_ptr r) + 224 ->
  write_authority (fixed_roots r) born m a.
Proof.
  intros m r born a Hroots Ha. left. exists (mkSpan (file_ptr r) 224).
  inversion Hroots as [|s rest Hw Hrest]; subst. split; [simpl; auto|]. split; auto.
Qed.

(** Fresh allocation leaves the null slots and every caller root valid.
    It does not install its address into FILE. *)
Lemma no_buffer_allocated : forall m r q base,
  stdout_memory m r NoBuffer -> object_region base (m_regions m) = None ->
  stdout_memory (allocated m q base) r NoBuffer.
Proof.
  intros m r q base (Hroots & Hfile & Hfields & Hlock & Herr & Hslot & Hnull & _) Hnew.
  split.
  - eapply Forall_impl; [|exact Hroots]. intros span Hspan. eapply allocated_old_span; eauto.
  - split; [eapply allocated_old_access; eauto|]. split.
    + eapply Forall_impl; [|exact Hfields]. intros offset Hfield. eapply allocated_old_access; eauto.
    + split; [eapply allocated_old_access; eauto|].
      split; [eapply allocated_old_access; eauto|]. split; [exact Hslot|]. auto.
Qed.

(** Installation preserves the checked fixed fields and lock pointer;
    target root bounds and heap lifetime are independent obligations.
    In particular, matching slot bytes alone cannot prove this view. *)
Theorem installed_memory : forall m r storage span,
  stdout_memory m r NoBuffer -> buffer_span r storage = Some span ->
  Forall (writable_span m) (memory_roots r storage) ->
  0 <= ptr_addr (span_ptr span) < 2 ^ 64 ->
  0 <= ptr_addr (span_ptr span) + span_size span < 2 ^ 64 ->
  (match storage with
   | HeapBuffer base size => 0 < size /\ exists reg,
       object_region base (m_regions m) = Some reg /\ r_kind reg = Heap /\ r_life reg = Live
   | _ => True
   end) ->
  stdout_memory (install_buffer m r storage) r storage.
Proof.
  intros m r storage span (Hroots & Hfile & Hfields & Hlock & Herr & Hslot & Hnull & _)
    Hspan Hout Hp Hend Hheap.
  assert (Hregions : m_regions (install_buffer m r storage) = m_regions m).
  { unfold install_buffer. rewrite Hspan. reflexivity. }
  split.
  - unfold writable_span, access_res. rewrite Hregions. exact Hout.
  - split; [unfold access_res; rewrite Hregions; exact Hfile|]. split.
    + unfold access_res. rewrite Hregions. exact Hfields.
    + split; [unfold access_res; rewrite Hregions; exact Hlock|].
      split; [unfold access_res; rewrite Hregions; exact Herr|]. split.
      * unfold install_buffer. rewrite Hspan.
        apply pointer_slot_bytes_disjoint; [lia|right; lia|].
        eapply pointer_slot_pointer_disjoint with
          (p := mkPtr (ptr_addr (span_ptr span) + span_size span) (ptr_cap (span_ptr span)));
          [right; lia|].
        apply pointer_slot_pointer_disjoint with (p := span_ptr span); [right; lia|exact Hslot].
      * split; [eapply installed_buffer_slots; eauto|].
        destruct storage; try exact I. rewrite Hregions. exact Hheap.
Qed.

(** ## Allocation evidence over any runtime *)

(** Buffer allocation over any [[runtime]] R. *)
Module Libio (R : Runtime).
Module E := ExternalCalls R.

(** The one allocation request stdout's buffer setup makes: 16-aligned,
    of [file_capacity] bytes. *)
Definition buffer_request (stat_ok : bool) (block_size align size : Z) : Prop :=
  align = 16 /\ size = file_capacity stat_ok block_size.

(** When the runtime, [[ready]] in state s and memory m, grants the
    buffer request at base: base was no object of m, the runtime stays
    ready, the allocation is an [effects] path with born list [base],
    and the new object's [Obj] capability and its capacity bytes are
    the call's authority.
    No theorem turns a logical HeapBuffer into an allocated object.
    This theorem starts with the runtime's actual successful answer.
    Installing its pointer slots and native flags is still a separate
    local-effects obligation. *)
Theorem allocate_buffer : forall stat_ok block_size s m base s' sources roots releases,
  R.ready s m ->
  R.alloc s (heap_req 16 (file_capacity stat_ok block_size)) = Some (base, s') ->
  let size := file_capacity stat_ok block_size in
  let m' := allocated m (heap_req 16 size) base in
  object_region base (m_regions m) = None /\
  R.ready s' m' /\
  E.effects sources roots releases (buffer_request stat_ok block_size) s m [] s' m' [base] /\
  available_cap sources [base] m' (Obj base) /\
  forall a, base <= a < base + size -> write_authority roots [base] m' a.
Proof.
  intros stat_ok block_size s m base s' sources roots releases Hr Ha.
  pose proof (file_capacity_bounds stat_ok block_size) as Hb.
  assert (He : 0 <= req_extent (heap_req 16 (file_capacity stat_ok block_size))).
  { simpl. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia|lia]. }
  destruct (R.fresh_allocation s m (heap_req 16 (file_capacity stat_ok block_size)) base s'
    Hr ltac:(simpl; lia) He Ha) as [Hfresh Hr'].
  destruct Hfresh as (Hbase & Halign & Hend & Hnone & Hrest).
  split; [exact Hnone|]. split; [exact Hr'|]. split.
  - eapply E.effects_alloc with (align := 16) (size := file_capacity stat_ok block_size).
    + split; reflexivity.
    + unfold max_allocation_size. lia.
    + exact Ha.
    + constructor.
  - split.
    + right. right. right. exists base. simpl. auto.
    + intros a Hrange. right.
      exists base, (mkRegion base (base + req_extent (heap_req 16 (file_capacity stat_ok block_size))) Heap Live).
      split; [simpl; auto|]. split.
      * simpl. rewrite Z.eqb_refl. reflexivity.
      * split; [reflexivity|]. split; [reflexivity|]. simpl.
        pose proof (Z.mod_pos_bound (file_capacity stat_ok block_size + 15) 16 ltac:(lia)) as Hmod.
        pose proof (Z.div_mod (file_capacity stat_ok block_size + 15) 16 ltac:(lia)) as Hdiv.
        lia.
Qed.

(** If the runtime refuses the buffer request, the call may end as
    [OutOfMemory] ([resource_failure]). *)
Theorem buffer_refusal : forall stat_ok block_size s,
  R.alloc s (heap_req 16 (file_capacity stat_ok block_size)) = None ->
  E.resource_failure (buffer_request stat_ok block_size) s OutOfMemory.
Proof.
  intros stat_ok block_size s H.
  pose proof (file_capacity_bounds stat_ok block_size).
  eapply E.failure_oom with (align := 16) (size := file_capacity stat_ok block_size).
  - split; reflexivity.
  - unfold max_allocation_size. lia.
  - exact H.
Qed.

(** The buffer request never fails as [TooBig]: its capacity is at most
    8192 bytes. *)
Theorem buffer_never_too_big : forall stat_ok block_size s,
  ~ E.resource_failure (buffer_request stat_ok block_size) s TooBig.
Proof.
  intros stat_ok block_size s H. inversion H as [|align size [_ ->] Hbig].
  pose proof (file_capacity_bounds stat_ok block_size). unfold max_allocation_size in Hbig. lia.
Qed.

Theorem install_short_effects : forall s m r requests,
  stdout_memory m r NoBuffer ->
  E.effects (fixed_roots r) (fixed_roots r) [] requests s m []
    s (install_buffer m r ShortBuffer) [].
Proof.
  intros s m r requests [Hroots _].
  set (a := ptr_addr (file_ptr r)). set (p := short_ptr r).
  set (m1 := store_aux (store_bytes m (a + 56) 8 (ptr_addr p)) (a + 56) (ptr_cap p)).
  set (m2 := store_aux (store_bytes m1 (a + 64) 8 (ptr_addr p + 1)) (a + 64) (ptr_cap p)).
  set (m3 := store_bytes m2 a 4 (Z.lor (load_bytes m a 4) 1)).
  change (E.effects (fixed_roots r) (fixed_roots r) [] requests s m [] s m3 []).
  eapply E.effects_local with (m1 := m1).
  - apply local_store_pointer with (p := p).
    + intros b Hb. apply file_write_authority; [exact Hroots|simpl in *; lia].
    + right. left. exists (mkSpan (file_ptr r) 224). simpl. auto.
  - eapply E.effects_local with (m1 := m2).
    + apply local_store_pointer with (p := mkPtr (ptr_addr p + 1) (ptr_cap p)).
      * intros b Hb. apply file_write_authority; [exact Hroots|simpl in *; lia].
      * right. left. exists (mkSpan (file_ptr r) 224). simpl. auto.
    + eapply E.effects_local with (m1 := m3).
      * apply local_store_bytes. intros b Hb.
        apply file_write_authority; [exact Hroots|simpl in *; lia].
      * constructor.
Qed.

Theorem install_heap_effects : forall s m r requests born base size,
  stdout_memory m r NoBuffer -> In base born ->
  E.effects (fixed_roots r) (fixed_roots r) [] requests s m born
    s (install_buffer m r (HeapBuffer base size)) born.
Proof.
  intros s m r requests born base size [Hroots _] Hborn.
  set (a := ptr_addr (file_ptr r)).
  set (m1 := store_aux (store_bytes m (a + 56) 8 base) (a + 56) (Obj base)).
  set (m2 := store_aux (store_bytes m1 (a + 64) 8 (base + size)) (a + 64) (Obj base)).
  set (m3 := store_bytes m2 a 4 (Z.land (load_bytes m a 4) (-2))).
  change (E.effects (fixed_roots r) (fixed_roots r) [] requests s m born s m3 born).
  eapply E.effects_local with (m1 := m1).
  - apply local_store_pointer with (p := mkPtr base (Obj base)).
    + intros b Hb. apply file_write_authority; [exact Hroots|simpl in *; lia].
    + right. right. right. exists base. auto.
  - eapply E.effects_local with (m1 := m2).
    + apply local_store_pointer with (p := mkPtr (base + size) (Obj base)).
      * intros b Hb. apply file_write_authority; [exact Hroots|simpl in *; lia].
      * right. right. right. exists base. auto.
    + eapply E.effects_local with (m1 := m3).
      * apply local_store_bytes. intros b Hb.
        apply file_write_authority; [exact Hroots|simpl in *; lia].
      * constructor.
Qed.

Theorem setup_short : forall s m r requests,
  R.ready s m -> stdout_memory m r NoBuffer ->
  let m' := install_buffer m r ShortBuffer in
  E.effects (fixed_roots r) (fixed_roots r) [] requests s m [] s m' [] /\
  R.ready s m' /\ persists m m' /\ stdout_memory m' r ShortBuffer /\
  stdio_delegates (fixed_roots r) [] m' (memory_world r ShortBuffer).
Proof.
  intros s m r requests Hr Hmem.
  pose proof (install_short_effects s m r requests Hmem) as He.
  destruct (E.effects_preserve _ _ _ _ _ _ _ _ _ _ He Hr) as [Hr' Hpersist].
  destruct Hmem as [Hroots Hrest].
  inversion Hroots as [|span rest Hw Htail]; subst.
  destruct Hw as (_ & base & reg & Hcap & Hreg & Hlive & Haccess).
  destruct (R.address_space s m Hr base reg Hreg) as [Hlo Hhi].
  change (access_res m (ptr_addr (file_ptr r)) (Obj base) 224 Write 1 = Some ok) in Haccess.
  unfold access_res, cap_access_res in Haccess. rewrite Hreg in Haccess.
  destruct ((base <=? ptr_addr (file_ptr r)) &&
    (ptr_addr (file_ptr r) + 224 <=? r_end reg)) eqn:E; try discriminate Haccess.
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  assert (Hpost : stdout_memory (install_buffer m r ShortBuffer) r ShortBuffer).
  { eapply installed_memory with (span := mkSpan (short_ptr r) 1).
    - split; assumption.
    - reflexivity.
    - exact Hroots.
    - unfold short_ptr. simpl. lia.
    - unfold short_ptr. simpl. lia.
    - exact I. }
  split; [exact He|]. split; [exact Hr'|]. split; [exact Hpersist|]. split; [exact Hpost|].
  apply stdio_delegates_refl; [reflexivity|exact (proj1 Hpost)].
Qed.

Theorem setup_heap : forall stat_ok block_size s m r base s',
  R.ready s m -> stdout_memory m r NoBuffer ->
  R.alloc s (heap_req 16 (file_capacity stat_ok block_size)) = Some (base, s') ->
  let size := file_capacity stat_ok block_size in
  let m1 := allocated m (heap_req 16 size) base in
  let m' := install_buffer m1 r (HeapBuffer base size) in
  E.effects (fixed_roots r) (fixed_roots r) [] (buffer_request stat_ok block_size)
    s m [] s' m' [base] /\
  R.ready s' m' /\ persists m m' /\ stdout_memory m' r (HeapBuffer base size) /\
  stdio_delegates (fixed_roots r) [base] m' (memory_world r (HeapBuffer base size)).
Proof.
  intros stat_ok block_size s m r base s' Hr Hmem Ha.
  set (size := file_capacity stat_ok block_size).
  set (q := heap_req 16 size). set (m1 := allocated m q base).
  pose proof (file_capacity_bounds stat_ok block_size) as Hsize.
  change (0 < size <= 8192) in Hsize.
  assert (Hfit : size <= req_extent q).
  { unfold q, heap_req. simpl.
    pose proof (Z.mod_pos_bound (size + 15) 16 ltac:(lia)).
    pose proof (Z.div_mod (size + 15) 16 ltac:(lia)). lia. }
  destruct (allocate_buffer stat_ok block_size s m base s' (fixed_roots r)
    (fixed_roots r) [] Hr Ha) as (Hnew & Hr1 & Healloc & Hcap & Hauthority).
  change (R.ready s' m1) in Hr1.
  pose proof (no_buffer_allocated m r q base Hmem Hnew) as Hmem1.
  assert (Hreg : object_region base (m_regions m1) = Some (mkRegion base (base + req_extent q) Heap Live)).
  { unfold m1, allocated. simpl. rewrite Z.eqb_refl. reflexivity. }
  destruct (R.address_space s' m1 Hr1 _ _ Hreg) as [Hbase Hend].
  change (base + req_extent q <= 2 ^ 48) in Hend.
  assert (Hw : writable_span m1 (mkSpan (mkPtr base (Obj base)) size)).
  { split; [simpl; lia|]. exists base, (mkRegion base (base + req_extent q) Heap Live).
    split; [reflexivity|]. split; [exact Hreg|]. split; [reflexivity|].
    change (cap_access_res (Obj base) (m_regions m1) base size Write 1 = Some ok).
    unfold cap_access_res. rewrite Hreg.
    change (Some (if (base <=? base) && (base + size <=? base + req_extent q)
      then aligned_res base 1 else RTrap OutOfBounds) = Some ok).
    assert (((base <=? base) && (base + size <=? base + req_extent q)) = true) as E.
    { apply andb_true_iff. split; apply Z.leb_le; lia. }
    rewrite E. unfold aligned_res. rewrite Z.mod_1_r. reflexivity. }
  pose proof (install_heap_effects s' m1 r (buffer_request stat_ok block_size)
    [base] base size Hmem1 ltac:(simpl; auto)) as Hetail.
  assert (He : E.effects (fixed_roots r) (fixed_roots r) [] (buffer_request stat_ok block_size)
    s m [] s' (install_buffer m1 r (HeapBuffer base size)) [base]).
  { eapply E.effects_alloc with (align := 16) (size := size).
    - split; reflexivity.
    - unfold max_allocation_size. lia.
    - exact Ha.
    - exact Hetail. }
  destruct (E.effects_preserve _ _ _ _ _ _ _ _ _ _ He Hr) as [Hr' Hpersist].
  assert (Hpost : stdout_memory (install_buffer m1 r (HeapBuffer base size)) r (HeapBuffer base size)).
  { eapply installed_memory with (span := mkSpan (mkPtr base (Obj base)) size).
    - exact Hmem1.
    - reflexivity.
    - unfold memory_roots. apply Forall_app. split; [exact (proj1 Hmem1)|]. constructor; [exact Hw|constructor].
    - change (0 <= base < 2 ^ 64). lia.
    - change (0 <= base + size < 2 ^ 64). lia.
    - split; [exact (proj1 Hsize)|]. exists (mkRegion base (base + req_extent q) Heap Live). auto. }
  split; [exact He|]. split; [exact Hr'|]. split; [exact Hpersist|]. split; [exact Hpost|].
  intros span Hin. change (In span (fixed_roots r ++ [mkSpan (mkPtr base (Obj base)) size])) in Hin.
  apply in_app_iff in Hin as [Hold|[<-|[]]].
  - split; [right; left; exists span; auto|]. intros a Hrange. left. exists span.
    split; [exact Hold|]. split; [|exact Hrange].
    pose proof (proj1 Hpost) as Hroots. rewrite Forall_forall in Hroots.
    apply Hroots. apply in_or_app. left. exact Hold.
  - split.
    + right. right. right. exists base. simpl. auto.
    + intros a Hrange. apply Hauthority. exact Hrange.
Qed.

End Libio.

(** ## Public branch and representation boundaries *)

(** Block sizes from 1 to 8191 after a successful stat are the capacity;
    8192 and above, zero, negative, or a failed stat give 8192. *)
Example capacity_edges :
  file_capacity true 1 = 1 /\ file_capacity true 8191 = 8191 /\
  file_capacity true 8192 = 8192 /\ file_capacity true 8193 = 8192 /\
  file_capacity true 0 = 8192 /\
  file_capacity true (-7) = 8192 /\ file_capacity false 4096 = 8192.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Capacity 8191 is not rounded, though [heap_req] reserves 8192. *)
Example capacity_not_rounded_extent :
  file_capacity true 8191 = 8191 /\ req_extent (heap_req 16 8191) = 8192.
Proof. vm_compute. auto. Qed.

(** Generic libio falls back to the embedded byte when malloc returns
    NULL. *)
Example generic_malloc_fallback : buffer_choice 4096 NoBuffer MallocNull ShortBuffer.
Proof. constructor. Qed.

(** At the pin, that NULL branch is never taken. *)
Example pin_cannot_return_null : forall size storage,
  ~ pinned_choice size NoBuffer MallocNull storage.
Proof. intros size storage [_ H]. apply H. reflexivity. Qed.

(** An unbuffered stdout uses the embedded byte without allocating. *)
Example unbuffered_needs_no_allocation : pinned_choice 8192 NoBuffer Unbuffered ShortBuffer.
Proof. split; [constructor|discriminate]. Qed.

(** An existing buffer has priority: no malloc replaces it. *)
Example existing_buffer_not_reallocated : forall size old new,
  old <> NoBuffer -> pinned_choice size old (MallocSuccess 4096) new -> False.
Proof. intros size old new H [Hchoice _]. inversion Hchoice; subst; contradiction. Qed.

(** The embedded buffer's pointer has the FILE's capability. *)
Example shortbuf_keeps_file_cap : forall r,
  ptr_cap (short_ptr r) = ptr_cap (file_ptr r).
Proof. reflexivity. Qed.

(** A buffer slot with the right address bytes but no capability in its
    [[aux]] does not satisfy [buffer_slots]. *)
Example buffer_address_without_aux_is_not_enough : forall m r base size,
  m_aux m (ptr_addr (file_ptr r) + 56) = CNone ->
  ~ buffer_slots m r (HeapBuffer base size).
Proof. intros m r base size Ha [[_ [_ Hcap]] _]. simpl in Hcap. rewrite Ha in Hcap. discriminate. Qed.

(** Nor does one with the right capability but other address bytes. *)
Example buffer_cap_without_address_is_not_enough : forall m r base size,
  load_bytes m (ptr_addr (file_ptr r) + 56) 8 <> base ->
  ~ buffer_slots m r (HeapBuffer base size).
Proof. intros m r base size Ha [[_ [Haddr _]] _]. apply Ha. exact Haddr. Qed.

(** Example roots: the FILE at 2048, its lock at 4096, errno at 8192.
    With the memories below, an inhabited memory view, not a fixture
    claiming to be native FILE. *)
Definition root_example : stdout_roots :=
  mkStdoutRoots (mkPtr 2048 (Obj 2048)) (mkPtr 4096 (Obj 4096)) (mkPtr 8192 (Obj 8192)).

(** A memory with null buffer slots and a capability-bearing lock slot
    pointing at 4096. *)
Definition unbuffered_example : mem :=
  mkMem (fun a => if (2184 <=? a) && (a <? 2192) then byte_of 4096 (a - 2184) else 0)
    [mkRegion 2048 2272 GlobalData Live; mkRegion 4096 4112 GlobalData Live;
     mkRegion 8192 8196 Heap Live]
    (fun a => if a =? 2184 then Obj 4096 else CNone).

(** [unbuffered_example] satisfies [stdout_memory] with no buffer. *)
Example no_buffer_memory_inhabited : stdout_memory unbuffered_example root_example NoBuffer.
Proof.
  split.
  - constructor.
    + split; [simpl; lia|]. exists 2048, (mkRegion 2048 2272 GlobalData Live). repeat split; reflexivity.
    + constructor.
      * split; [simpl; lia|]. exists 4096, (mkRegion 4096 4112 GlobalData Live). repeat split; reflexivity.
      * constructor; [|constructor].
        split; [simpl; lia|]. exists 8192, (mkRegion 8192 8196 Heap Live). repeat split; reflexivity.
  - vm_compute. repeat constructor; discriminate.
Qed.

(** Storing in the two buffer slots BOTH the address bytes (the
    embedded byte's start 2179 and end 2180) and the FILE's capability
    in their [[aux]] satisfies [stdout_memory] with the embedded
    buffer. *)
Example embedded_memory_inhabited :
  stdout_memory
    (store_aux (store_aux
      (store_bytes (store_bytes unbuffered_example 2104 8 2179) 2112 8 2180)
      2104 (Obj 2048)) 2112 (Obj 2048)) root_example ShortBuffer.
Proof.
  split.
  - constructor.
    + split; [simpl; lia|]. exists 2048, (mkRegion 2048 2272 GlobalData Live). repeat split; reflexivity.
    + constructor.
      * split; [simpl; lia|]. exists 4096, (mkRegion 4096 4112 GlobalData Live). repeat split; reflexivity.
      * constructor; [|constructor].
        split; [simpl; lia|]. exists 8192, (mkRegion 8192 8196 Heap Live). repeat split; reflexivity.
  - vm_compute. repeat constructor; discriminate.
Qed.

(** An asymmetric capacity exercises installed slots, rounded extent,
    the nontrivial flag mask, and unchanged lock/errno contents. *)
Definition heap_example : mem :=
  install_buffer
    (allocated (store_bytes (store_bytes unbuffered_example 2048 4 305419897) 8192 4 73)
      (heap_req 16 8191) 16384) root_example (HeapBuffer 16384 8191).

Example installed_heap_memory_inhabited : stdout_memory heap_example root_example (HeapBuffer 16384 8191).
Proof.
  split.
  - constructor.
    + split; [simpl; lia|]. exists 2048, (mkRegion 2048 2272 GlobalData Live). repeat split; reflexivity.
    + constructor.
      * split; [simpl; lia|]. exists 4096, (mkRegion 4096 4112 GlobalData Live). repeat split; reflexivity.
      * constructor.
        -- split; [simpl; lia|]. exists 8192, (mkRegion 8192 8196 Heap Live). repeat split; reflexivity.
        -- constructor; [|constructor].
           split; [simpl; lia|]. exists 16384, (mkRegion 16384 24576 Heap Live). repeat split; reflexivity.
  - split; [reflexivity|]. split; [repeat constructor; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [vm_compute; repeat constructor; discriminate|].
    split; [vm_compute; repeat constructor; discriminate|].
    split; [lia|]. exists (mkRegion 16384 24576 Heap Live). repeat split; reflexivity.
Qed.

Example installed_capacity_and_flag :
  pointer_slot heap_example 2104 (mkPtr 16384 (Obj 16384)) /\
  pointer_slot heap_example 2112 (mkPtr 24575 (Obj 16384)) /\
  object_region 16384 (m_regions heap_example) = Some (mkRegion 16384 24576 Heap Live) /\
  load_bytes heap_example 2048 4 = 305419896 /\
  pointer_slot heap_example 2184 (mkPtr 4096 (Obj 4096)) /\
  load_bytes heap_example 8192 4 = 73.
Proof. vm_compute. repeat constructor; discriminate. Qed.

Example installed_short_memory_inhabited :
  stdout_memory (install_buffer unbuffered_example root_example ShortBuffer) root_example ShortBuffer /\
  load_bytes (install_buffer (store_bytes unbuffered_example 2048 4 305419896)
    root_example ShortBuffer) 2048 4 = 305419897.
Proof.
  split; [|reflexivity]. eapply installed_memory.
  - exact no_buffer_memory_inhabited.
  - reflexivity.
  - exact (proj1 no_buffer_memory_inhabited).
  - change (0 <= 2179 < 2 ^ 64). lia.
  - change (0 <= 2180 < 2 ^ 64). lia.
  - exact I.
Qed.

Example installed_dead_heap_rejected :
  ~ stdout_memory (mkMem (m_bytes heap_example)
    (mkRegion 16384 16384 Heap Freed :: m_regions heap_example) (m_aux heap_example))
    root_example (HeapBuffer 16384 8191).
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & reg & Hreg & _ & Hlife).
  change (Some (mkRegion 16384 16384 Heap Freed) = Some reg) in Hreg.
  injection Hreg as <-. discriminate Hlife.
Qed.

Example installed_undersized_heap_rejected :
  ~ stdout_memory (mkMem (m_bytes heap_example)
    (mkRegion 16384 24574 Heap Live :: m_regions heap_example) (m_aux heap_example))
    root_example (HeapBuffer 16384 8191).
Proof.
  intros [Hroots _]. rewrite Forall_forall in Hroots.
  specialize (Hroots (mkSpan (mkPtr 16384 (Obj 16384)) 8191) ltac:(simpl; auto)).
  destruct Hroots as (_ & base & reg & Hcap & _ & _ & Haccess).
  change (Obj 16384 = Obj base) in Hcap. injection Hcap as <-. discriminate Haccess.
Qed.
