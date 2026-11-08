(** A selected memory view of user-glibc's exit registry, not an executor
    or proof of native satisfaction. Layout is read from the pinned
    stdlib/exit.h and checked by compiling its extracted declarations
    with Fil-C: entry 32, block 1040, next/idx/fns at 0/8/16.
    Physical slots and logical pending registrations are distinct.
    Synchronization, callback admission and ownership remain separate
    [[obligation|obligations]]. *)

From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory ExternalCalls Startup Shutdown.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(** Tags 0/1 are skipped by the exit loop. A reserved slot is not an
    installed callback; arbitrary unknown flavors are not admitted. Tokens
    are ghost registration instances, never native slot indices/addresses. *)
Inductive exit_slot : Type :=
| FreeSlot | ReservedSlot
| OnSlot (token : nat) (symbol : name) (function argument : ptr)
| AtSlot (token : nat) (symbol : name) (function : ptr)
| CxaSlot (token : nat) (symbol : name) (function argument dso : ptr).

(** A decoded function capability is not an admitted code specification. *)
Definition exit_function_slot m a symbol function : Prop :=
  pointer_slot m a function /\ ptr_cap function = Fn symbol.

(** Only the flavor-selected fields matter. In particular free/reserved
    slots impose no requirements on stale payloads. Cxa's DSO pointer is
    represented but not dereferenced by ordinary exit. Native pointer
    mangling is a no-op in this selected source, not in arbitrary glibc. *)
Definition exit_slot_memory (m : mem) (a : Z) (slot : exit_slot) : Prop :=
  match slot with
  | FreeSlot => load_bytes m a 8 = 0
  | ReservedSlot => load_bytes m a 8 = 1
  | OnSlot _ symbol function argument =>
      load_bytes m a 8 = 2 /\ exit_function_slot m (a + 8) symbol function /\
      pointer_slot m (a + 16) argument
  | AtSlot _ symbol function =>
      load_bytes m a 8 = 3 /\ exit_function_slot m (a + 8) symbol function
  | CxaSlot _ symbol function argument dso =>
      load_bytes m a 8 = 4 /\ exit_function_slot m (a + 8) symbol function /\
      pointer_slot m (a + 16) argument /\ pointer_slot m (a + 24) dso
  end.

(** Flavor, not the public API's spelling, selects the callback form.
    This pin's atexit stores ef_cxa with null argument and DSO; adapting
    that to logical AtExit requires a separate calling-convention contract. *)
Definition exit_slot_pending (slot : exit_slot) : list registration :=
  match slot with
  | FreeSlot | ReservedSlot => []
  | OnSlot token symbol _ argument => [mkRegistration token (OnExit symbol (WPtr argument))]
  | AtSlot token symbol _ => [mkRegistration token (AtExit symbol)]
  | CxaSlot token symbol _ argument _ => [mkRegistration token (CxaExit symbol (WPtr argument))]
  end.

(** Native slots are stored oldest first; exit scans downward, skipping holes. *)
Definition exit_pending (slots : list exit_slot) : list registration :=
  flat_map exit_slot_pending (rev slots).

(** The slots below idx, not an assertion that idx counts live callbacks. *)
Record exit_block : Type := mkExitBlock { block_ptr : ptr; block_slots : list exit_slot }.

(** Full readable containing-object bounds/alignment are independent of
    pointer-slot decoding. Slots at or above idx are deliberately ignored.
    Writable spans are NOT inferred from this read-only view. *)
Definition exit_block_memory (m : mem) (block : exit_block) (next : ptr) : Prop :=
  let p := block_ptr block in
  ptr_cap p = Obj (ptr_addr p) /\
  access_res m (ptr_addr p) (ptr_cap p) 1040 Read 8 = Some ok /\
  pointer_slot m (ptr_addr p) next /\
  load_bytes m (ptr_addr p + 8) 8 = Z.of_nat (length (block_slots block)) /\
  (length (block_slots block) <= 32)%nat /\
  forall i slot, nth_error (block_slots block) i = Some slot ->
    exit_slot_memory m (ptr_addr p + 16 + 32 * Z.of_nat i) slot.

(** The actual next-slot value for this finite suffix. *)
Definition exit_head (blocks : list exit_block) : ptr :=
  match blocks with [] => mkPtr 0 CNone | block :: _ => block_ptr block end.

(** A finite null-terminated chain, linked by decoded pointer capabilities. *)
Fixpoint exit_chain_memory (m : mem) (blocks : list exit_block) : Prop :=
  match blocks with
  | [] => True
  | block :: rest => exit_block_memory m block (exit_head rest) /\ exit_chain_memory m rest
  end.

(** Block identities are distinct, not merely the pointers' address bits in
    next slots. Base capabilities in exit_block_memory tie them together. *)
Definition exit_registry_memory m head blocks : Prop :=
  access_res m (ptr_addr head) (ptr_cap head) 8 Read 8 = Some ok /\
  pointer_slot m (ptr_addr head) (exit_head blocks) /\ exit_chain_memory m blocks /\
  NoDup (map (fun block => ptr_addr (block_ptr block)) blocks).

(** Blocks are visited head-first; each block is scanned in reverse slot order. *)
Definition exit_registry_pending blocks : list registration :=
  flat_map (fun block => exit_pending (block_slots block)) blocks.

(** Callback specifications and retained argument requirements are independent
    of decoded Fn capabilities. Active evidence is detached from any old
    slot: idx has already decreased, and cxa may already have cleared it. *)
Definition exit_callbacks_admitted (admitted : mem -> registration -> Prop)
    m blocks (active : option registration) : Prop :=
  Forall (admitted m) (exit_registry_pending blocks) /\
  match active with None => True | Some entry => admitted m entry end.

(** Release eligibility AFTER unlinking, not a memory transition. Explicit
    ownership, an exhausted live Heap base, enough extent, a distinct nonempty
    successor chain and the updated head are all required. Merely reading a
    block, finding it live, or observing next != NULL confers no ownership. *)
Definition exit_block_releasable owned m head block rest : Prop :=
  In (ptr_addr (block_ptr block)) owned /\ block_slots block = [] /\ rest <> [] /\
  exit_registry_memory m head rest /\ exit_block_memory m block (exit_head rest) /\
  NoDup (map (fun node => ptr_addr (block_ptr node)) (block :: rest)) /\
  exists reg, object_region (ptr_addr (block_ptr block)) (m_regions m) = Some reg /\
    r_kind reg = Heap /\ r_life reg = Live /\
    ptr_addr (block_ptr block) + 1040 <= r_end reg.

(** A free hole at the next index consumes no pending registration. *)
Lemma exit_pending_skip_free : forall slots,
  exit_pending (slots ++ [FreeSlot]) = exit_pending slots.
Proof. intros. unfold exit_pending. rewrite rev_app_distr. reflexivity. Qed.

(** Reserved physical slots are skipped too, not treated as installed code. *)
Lemma exit_pending_skip_reserved : forall slots,
  exit_pending (slots ++ [ReservedSlot]) = exit_pending slots.
Proof. intros. unfold exit_pending. rewrite rev_app_distr. reflexivity. Qed.

(** Popping an installed slot detaches its registration before callback entry.
    This is a projection lemma, not construction of native write effects. *)
Lemma exit_pending_pop : forall slots slot entry,
  exit_slot_pending slot = [entry] ->
  exit_pending (slots ++ [slot]) = entry :: exit_pending slots.
Proof.
  intros slots slot entry H. unfold exit_pending. rewrite rev_app_distr.
  simpl. rewrite H. reflexivity.
Qed.

(** Decoding a represented slot also supplies checked containing-object access. *)
Lemma exit_slot_checked : forall m block next i slot,
  exit_block_memory m block next -> nth_error (block_slots block) i = Some slot ->
  access_res m (ptr_addr (block_ptr block)) (ptr_cap (block_ptr block)) 1040 Read 8 = Some ok /\
  exit_slot_memory m (ptr_addr (block_ptr block) + 16 + 32 * Z.of_nat i) slot.
Proof. intros m block next i slot (_ & Hread & _ & _ & _ & Hslots) Hi. auto. Qed.

(** Being the last node prevents release even if the caller owns a live heap block. *)
Example exit_last_block_retained : forall owned m head block,
  ~ exit_block_releasable owned m head block [].
Proof. intros owned m head block (_ & _ & Hnonempty & _). apply Hnonempty. reflexivity. Qed.

(** A readable, writable or live block is still not a release permission. *)
Example exit_unowned_block_retained : forall m head block rest,
  ~ exit_block_releasable [] m head block rest.
Proof. intros m head block rest [Howned _]. exact Howned. Qed.

(** The array's fixed native capacity rejects idx=33, independently of memory. *)
Example exit_oversized_index_rejected : forall m p next,
  ~ exit_block_memory m (mkExitBlock p (repeat FreeSlot 33)) next.
Proof. intros m p next (_ & _ & _ & _ & Hlength & _). simpl in Hlength. lia. Qed.

(** Repeated blocks cannot form a selected registry, even if slot bytes look linked. *)
Example exit_repeated_block_rejected : forall m head block,
  ~ exit_registry_memory m head [block; block].
Proof.
  intros m head block (_ & _ & _ & Hdistinct). inversion Hdistinct; subst.
  match goal with Hnot : ~ In _ _ |- _ => apply Hnot; left; reflexivity end.
Qed.

(** Concrete model memory checks do not locate the native hidden registry. *)
Module ExitMemoryChecks.

(** Two distinct callback forms with asymmetric tokens and arguments. *)
Definition oldest : exit_slot := OnSlot 10 (TAtom "oldest")
  (mkPtr 65536 (Fn (TAtom "oldest"))) (mkPtr 4096 (Obj 4096)).
(** The newest stored callback has no argument; cxa still stores its null slot. *)
Definition newest : exit_slot := CxaSlot 11 (TAtom "newest")
  (mkPtr 65544 (Fn (TAtom "newest"))) (mkPtr 0 CNone) (mkPtr 0 CNone).
(** idx=3 describes two installed callbacks separated by a finalized hole. *)
Definition block : exit_block := mkExitBlock (mkPtr 2048 (Obj 2048)) [oldest; FreeSlot; newest].

(** Build actual address bytes and shadow capabilities with existing stores. *)
Definition memory : mem :=
  let m := mkMem (fun _ => 0)
    [mkRegion 1000 1008 GlobalData Live; mkRegion 2048 3088 GlobalData Live;
     mkRegion 4096 4104 Heap Live] (fun _ => CNone) in
  let m := startup_store m 1000 (block_ptr block) in
  let m := store_bytes m 2056 8 3 in
  let m := store_bytes m 2064 8 2 in
  let m := startup_store m 2072 (mkPtr 65536 (Fn (TAtom "oldest"))) in
  let m := startup_store m 2080 (mkPtr 4096 (Obj 4096)) in
  let m := store_bytes m 2128 8 4 in
  startup_store m 2136 (mkPtr 65544 (Fn (TAtom "newest"))).

(** The concrete bytes inhabit a checked block view, with idx counting the hole. *)
Lemma block_represented : exit_block_memory memory block (mkPtr 0 CNone).
Proof.
  split; [reflexivity|]. split; [reflexivity|]. split.
  - vm_compute. repeat split; congruence.
  - split; [reflexivity|]. split; [simpl; lia|].
    intros i slot Hi. destruct i as [|[|[|i]]]; simpl in Hi; try (destruct i; discriminate Hi);
      injection Hi as <-; vm_compute; repeat split; congruence.
Qed.

(** A readable head and a distinct, null-terminated chain inhabit the registry view. *)
Example registry_represented : exit_registry_memory memory (mkPtr 1000 (Obj 1000)) [block].
Proof.
  split; [reflexivity|]. split.
  - vm_compute. repeat split; congruence.
  - split; [split; [exact block_represented|exact I]|].
    repeat constructor. simpl. tauto.
Qed.

(** A head block precedes an older block; both scan backward and skip holes. *)
Example pending_order_with_holes :
  exit_registry_pending [block; mkExitBlock (mkPtr 8192 (Obj 8192)) [AtSlot 3 (TAtom "tail")
    (mkPtr 65552 (Fn (TAtom "tail"))); ReservedSlot]] =
  [mkRegistration 11 (CxaExit (TAtom "newest") (WPtr (mkPtr 0 CNone)));
   mkRegistration 10 (OnExit (TAtom "oldest") (WPtr (mkPtr 4096 (Obj 4096))));
   mkRegistration 3 (AtExit (TAtom "tail"))].
Proof. reflexivity. Qed.

(** After decreasing idx the former newest slot is outside the pending scan.
    Even replacing its argument capability with nonsense does not invalidate
    this shorter registry view. Active callback evidence is independent. *)
Example stale_payload_above_idx_ignored :
  exit_block_memory (store_aux (store_bytes memory 2056 8 2) 2144 (Obj 9999))
    (mkExitBlock (block_ptr block) [oldest; FreeSlot]) (mkPtr 0 CNone).
Proof.
  split; [reflexivity|]. split; [reflexivity|]. split.
  - vm_compute. repeat split; congruence.
  - split; [reflexivity|]. split; [simpl; lia|].
    intros i slot Hi. destruct i as [|[|i]]; simpl in Hi; try (destruct i; discriminate Hi);
      injection Hi as <-; vm_compute; repeat split; congruence.
Qed.

(** Correct next-pointer bits cannot compensate for its wrong capability. *)
Example incorrect_link_capability_rejected :
  ~ exit_block_memory (store_aux memory 2048 (Obj 4096)) block (mkPtr 0 CNone).
Proof. intros (_ & _ & (_ & _ & Haux) & _). discriminate Haux. Qed.

(** Correct function address bits cannot turn an object capability into Fn. *)
Example malformed_function_capability_rejected :
  ~ exit_slot_memory (store_aux memory 2072 (Obj 65536)) 2064 oldest.
Proof. intros (_ & [(_ & _ & Haux) _] & _). discriminate Haux. Qed.

(** Unknown flavors are not silently reclassified as holes. *)
Example unknown_flavor_rejected : forall slot,
  ~ exit_slot_memory (store_bytes memory 2064 8 99) 2064 slot.
Proof.
  intros slot Hslot. destruct slot; simpl in Hslot; try discriminate Hslot;
    destruct Hslot as [Htag _]; discriminate Htag.
Qed.

(** An empty pending chain cannot erase the detached active callback's contract. *)
Example detached_callback_still_needs_admission : forall m entry,
  exit_callbacks_admitted (fun _ _ => False) m [] None /\
  ~ exit_callbacks_admitted (fun _ _ => False) m [] (Some entry).
Proof. intros m entry. split; [split; constructor|]. intros [_ Hactive]. exact Hactive. Qed.

(** A represented Fn capability does not authorize a missing callback contract. *)
Example decoded_function_not_admission :
  exit_registry_memory memory (mkPtr 1000 (Obj 1000)) [block] /\
  ~ exit_callbacks_admitted (fun _ _ => False) memory [block] None.
Proof.
  split; [exact registry_represented|]. intros [Hcallbacks _].
  inversion Hcallbacks; assumption.
Qed.

End ExitMemoryChecks.
