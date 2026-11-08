(** A capability-backed memory view of the pinned byte stdout.

    Offsets are measured with the Fil-C headers, not the host's FILE.
    This is a view of the buffer/lock roots, not a complete predicate
    for native FILE validity or a proof of libio's execution. In
    particular, vtable dispatch, TLS initialization, protocol scheduling
    and native prefix coverage remain trusted realization obligations.

    The selected malloc forwards to zgc_alloc: runtime refusal does
    not return NULL to _IO_file_doallocate. The generic libio NULL
    fallback and the pin's terminal resource ending are distinct. *)

From Stdlib Require Import ZArith List Bool Lia.
From Nanofil Require Import Syntax Values Memory Runtime ExternalCalls Startup.
Import ListNotations.
Open Scope Z_scope.

(** ## Source-selected capacity and buffer paths *)

(** filedoalloc.c, selected stdout descriptor 1 and the pinned x86-64
    _STATBUF_ST_BLKSIZE configuration: use a positive st_blksize smaller
    than BUFSIZ only after a successful stat; otherwise retain BUFSIZ.
    This is NOT the capacity function for arbitrary descriptors. *)
Definition file_capacity (stat_ok : bool) (block_size : Z) : Z :=
  if stat_ok && (0 <? block_size) && (block_size <? 8192)
  then block_size else 8192.

Lemma file_capacity_bounds : forall stat_ok block_size,
  0 < file_capacity stat_ok block_size <= 8192.
Proof.
  intros. unfold file_capacity.
  destruct (stat_ok && (0 <? block_size) && (block_size <? 8192)) eqn:E; [|lia].
  apply andb_true_iff in E as [E Hhi]. apply andb_true_iff in E as [_ Hlo].
  apply Z.ltb_lt in Hhi. apply Z.ltb_lt in Hlo. lia.
Qed.

Inductive buffer_storage : Type :=
| NoBuffer
| ShortBuffer
| HeapBuffer (base size : Z).

(** These causes describe libio's control flow, not R.alloc's result.
    MallocNull is useful for generic libio, but is excluded at this pin.
    Unbuffered is for a byte stream: wide orientation takes another path. *)
Inductive buffer_cause : Type :=
| Existing | Unbuffered | MallocSuccess (base : Z) | MallocNull.

Inductive buffer_choice (capacity : Z)
    : buffer_storage -> buffer_cause -> buffer_storage -> Prop :=
| choice_existing : forall storage,
    storage <> NoBuffer -> buffer_choice capacity storage Existing storage
| choice_unbuffered : buffer_choice capacity NoBuffer Unbuffered ShortBuffer
| choice_allocated : forall base,
    buffer_choice capacity NoBuffer (MallocSuccess base) (HeapBuffer base capacity)
| choice_null : buffer_choice capacity NoBuffer MallocNull ShortBuffer.

Definition pinned_choice (capacity : Z) (old : buffer_storage)
    (cause : buffer_cause) (new : buffer_storage) : Prop :=
  buffer_choice capacity old cause new /\ cause <> MallocNull.

(** ## Measured pointer slots and writable roots *)

Record stdout_roots : Type := mkStdoutRoots {
  file_ptr : ptr;
  lock_ptr : ptr;
  errno_ptr : ptr
}.

(** stdfiles.c allocates _IO_FILE_plus: FILE (216) plus its vtable
    pointer (8). NPTL's lock is { int lock; int cnt; void *owner; }.
    errno is a separate four-byte TLS cell. These spans are authority
    supplied by the caller of the trusted boundary, never inferred
    just from the addresses stored in FILE. *)
Definition fixed_roots (r : stdout_roots) : list span :=
  [mkSpan (file_ptr r) 224; mkSpan (lock_ptr r) 16; mkSpan (errno_ptr r) 4].

Definition short_ptr (r : stdout_roots) : ptr :=
  mkPtr (ptr_addr (file_ptr r) + 131) (ptr_cap (file_ptr r)).

Definition buffer_span (r : stdout_roots) (storage : buffer_storage) : option span :=
  match storage with
  | NoBuffer => None
  | ShortBuffer => Some (mkSpan (short_ptr r) 1)
  | HeapBuffer base size => Some (mkSpan (mkPtr base (Obj base)) size)
  end.

Definition memory_roots (r : stdout_roots) (storage : buffer_storage) : list span :=
  fixed_roots r ++
    match storage with
    | HeapBuffer base size => [mkSpan (mkPtr base (Obj base)) size]
    | _ => []
    end.

Definition buffer_slots (m : mem) (r : stdout_roots) (storage : buffer_storage) : Prop :=
  let a := ptr_addr (file_ptr r) in
  match buffer_span r storage with
  | None => pointer_slot m (a + 56) (mkPtr 0 CNone) /\
            pointer_slot m (a + 64) (mkPtr 0 CNone)
  | Some s => pointer_slot m (a + 56) (span_ptr s) /\
      pointer_slot m (a + 64)
        (mkPtr (ptr_addr (span_ptr s) + span_size s) (ptr_cap (span_ptr s)))
  end.

(** This view supplies actual address bytes and aux, not a detached
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

Definition memory_world (r : stdout_roots) (storage : buffer_storage) : stdio_world :=
  mkStdioWorld true (memory_roots r storage).

Theorem stdout_memory_ready : forall m r storage,
  stdout_memory m r storage -> stdio_ready m (memory_world r storage).
Proof. intros m r storage [H _]. split; [reflexivity|exact H]. Qed.

(** The embedded buffer neither allocates nor expands root authority.
    Its one byte is already inside the FILE root, with the SAME cap. *)
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

(** ## Allocation evidence over any runtime *)

Module Libio (R : Runtime).
Module E := ExternalCalls R.

Definition buffer_request (stat_ok : bool) (block_size align size : Z) : Prop :=
  align = 16 /\ size = file_capacity stat_ok block_size.

(** No theorem turns a logical HeapBuffer into an allocated object.
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

Theorem buffer_never_too_big : forall stat_ok block_size s,
  ~ E.resource_failure (buffer_request stat_ok block_size) s TooBig.
Proof.
  intros stat_ok block_size s H. inversion H as [|align size [_ ->] Hbig].
  pose proof (file_capacity_bounds stat_ok block_size). unfold max_allocation_size in Hbig. lia.
Qed.

End Libio.

(** ## Public branch and representation boundaries *)

Example capacity_edges :
  file_capacity true 1 = 1 /\ file_capacity true 8191 = 8191 /\
  file_capacity true 8192 = 8192 /\ file_capacity true 8193 = 8192 /\
  file_capacity true 0 = 8192 /\
  file_capacity true (-7) = 8192 /\ file_capacity false 4096 = 8192.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example capacity_not_rounded_extent :
  file_capacity true 8191 = 8191 /\ req_extent (heap_req 16 8191) = 8192.
Proof. vm_compute. auto. Qed.

Example generic_malloc_fallback : buffer_choice 4096 NoBuffer MallocNull ShortBuffer.
Proof. constructor. Qed.

Example pin_cannot_return_null : forall size storage,
  ~ pinned_choice size NoBuffer MallocNull storage.
Proof. intros size storage [_ H]. apply H. reflexivity. Qed.

Example unbuffered_needs_no_allocation : pinned_choice 8192 NoBuffer Unbuffered ShortBuffer.
Proof. split; [constructor|discriminate]. Qed.

Example existing_buffer_not_reallocated : forall size old new,
  old <> NoBuffer -> pinned_choice size old (MallocSuccess 4096) new -> False.
Proof. intros size old new H [Hchoice _]. inversion Hchoice; subst; contradiction. Qed.

Example shortbuf_keeps_file_cap : forall r,
  ptr_cap (short_ptr r) = ptr_cap (file_ptr r).
Proof. reflexivity. Qed.

Example buffer_address_without_aux_is_not_enough : forall m r base size,
  m_aux m (ptr_addr (file_ptr r) + 56) = CNone ->
  ~ buffer_slots m r (HeapBuffer base size).
Proof. intros m r base size Ha [[_ [_ Hcap]] _]. simpl in Hcap. rewrite Ha in Hcap. discriminate. Qed.

Example buffer_cap_without_address_is_not_enough : forall m r base size,
  load_bytes m (ptr_addr (file_ptr r) + 56) 8 <> base ->
  ~ buffer_slots m r (HeapBuffer base size).
Proof. intros m r base size Ha [[_ [Haddr _]] _]. apply Ha. exact Haddr. Qed.

(** An inhabited memory view, not a fixture claiming to be native FILE.
    The first image has null buffer slots and a capability-bearing lock;
    the second changes BOTH address bytes and aux to embed the buffer. *)
Definition root_example : stdout_roots :=
  mkStdoutRoots (mkPtr 2048 (Obj 2048)) (mkPtr 4096 (Obj 4096)) (mkPtr 8192 (Obj 8192)).

Definition unbuffered_example : mem :=
  mkMem (fun a => if (2184 <=? a) && (a <? 2192) then byte_of 4096 (a - 2184) else 0)
    [mkRegion 2048 2272 GlobalData Live; mkRegion 4096 4112 GlobalData Live;
     mkRegion 8192 8196 Heap Live]
    (fun a => if a =? 2184 then Obj 4096 else CNone).

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
