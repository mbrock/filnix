(** A selected memory view of user-glibc's exit registry, not an executor
    or proof of native satisfaction. Layout is read from the pinned
    stdlib/exit.h and checked by compiling its extracted declarations
    with Fil-C: entry 32, block 1040, next/idx/fns at 0/8/16.
    Physical slots and logical pending registrations are distinct.
    Synchronization, callback admission and ownership remain separate
    [[obligation|obligations]]. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Identity ExternalCalls Startup Stdio Shutdown.
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

(** ## Constructing one pop, before callback execution *)

(** The native index decrement; older is the prefix left after the pop. *)
Definition exit_pop_index m p (older : list exit_slot) : mem :=
  store_bytes m (ptr_addr p + 8) 8 (Z.of_nat (length older)).

(** Native cxa removal also clears its flavor, after decrementing idx.
    Payload bytes and every auxiliary capability remain untouched. *)
Definition exit_pop_memory m p older selected : mem :=
  let m1 := exit_pop_index m p older in
  match selected with
  | CxaSlot _ _ _ _ _ => store_bytes m1 (ptr_addr p + 16 + 32 * Z.of_nat (length older)) 8 0
  | _ => m1
  end.

(** Only idx and, for cxa, the removed flavor need write authority.
    A readable containing block is not this permission. *)
Definition exit_pop_writes p (older : list exit_slot) selected : list span :=
  mkSpan (mkPtr (ptr_addr p + 8) (ptr_cap p)) 8 ::
  match selected with
  | CxaSlot _ _ _ _ _ =>
      [mkSpan (mkPtr (ptr_addr p + 16 + 32 * Z.of_nat (length older)) (ptr_cap p)) 8]
  | _ => []
  end.

(** The head cell and other block storage must not alias this block.
    Distinct object identities alone do not establish byte separation. *)
Definition exit_pop_separated head p rest : Prop :=
  (ptr_addr head + 8 <= ptr_addr p \/ ptr_addr p + 1040 <= ptr_addr head) /\
  Forall (fun block => ptr_addr (block_ptr block) + 1040 <= ptr_addr p \/
    ptr_addr p + 1040 <= ptr_addr (block_ptr block)) rest.

(** A byte store preserves all reads disjoint from its actual footprint. *)
Lemma exit_load_bytes_disjoint : forall m a n x b size,
  0 <= size -> b + size <= a \/ a + n <= b ->
  load_bytes (store_bytes m a n x) b size = load_bytes m b size.
Proof.
  intros m a n x b size Hsize Hdis. apply load_bytes_agree; [exact Hsize|].
  intros i Hi. simpl. destruct ((a <=? b + i) && (b + i <? a + n)) eqn:E; [|reflexivity].
  apply Bool.andb_true_iff in E as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi. lia.
Qed.

(** A pointer slot depends on its eight bytes and its own shadow entry. *)
Lemma exit_pointer_agree : forall m m' a p,
  m_aux m' = m_aux m ->
  (forall b, a <= b < a + 8 -> m_bytes m' b = m_bytes m b) ->
  pointer_slot m a p -> pointer_slot m' a p.
Proof.
  intros m m' a p Haux Hb (Hp & Hload & Hcap). split; [exact Hp|]. split.
  - rewrite <- Hload. apply load_bytes_agree; [lia|]. intros i Hi. apply Hb. lia.
  - rewrite Haux. exact Hcap.
Qed.

(** Physical slot decoding is framed by its 32 bytes and unchanged shadow. *)
Lemma exit_slot_memory_agree : forall m m' a slot,
  m_aux m' = m_aux m ->
  (forall b, a <= b < a + 32 -> m_bytes m' b = m_bytes m b) ->
  exit_slot_memory m a slot -> exit_slot_memory m' a slot.
Proof.
  intros m m' a slot Haux Hb Hslot.
  assert (Hload : forall off, 0 <= off <= 24 ->
    load_bytes m' (a + off) 8 = load_bytes m (a + off) 8).
  { intros off Hoff. apply load_bytes_agree; [lia|]. intros i Hi. apply Hb. lia. }
  assert (Hptr : forall off p, 0 <= off <= 24 ->
    pointer_slot m (a + off) p -> pointer_slot m' (a + off) p).
  { intros off p Hoff. apply exit_pointer_agree; [exact Haux|]. intros b Hrange. apply Hb. lia. }
  assert (Hzero : load_bytes m' a 8 = load_bytes m a 8).
  { replace a with (a + 0) by lia. apply Hload. lia. }
  destruct slot; simpl in *; rewrite Hzero; try exact Hslot.
  - destruct Hslot as (Htag & [Hfn Hcap] & Harg).
    split; [exact Htag|]. split.
    + split; [apply Hptr; [lia|exact Hfn]|exact Hcap].
    + apply Hptr; [lia|exact Harg].
  - destruct Hslot as (Htag & [Hfn Hcap]). split; [exact Htag|].
    split; [apply Hptr; [lia|exact Hfn]|exact Hcap].
  - destruct Hslot as (Htag & [Hfn Hcap] & Harg & Hdso).
    split; [exact Htag|]. split.
    + split; [apply Hptr; [lia|exact Hfn]|exact Hcap].
    + split; apply Hptr; try lia; assumption.
Qed.

(** A block view is preserved by an exact frame over its full storage. *)
Lemma exit_block_memory_agree : forall m m' block next,
  m_regions m' = m_regions m -> m_aux m' = m_aux m ->
  (forall a, ptr_addr (block_ptr block) <= a < ptr_addr (block_ptr block) + 1040 ->
    m_bytes m' a = m_bytes m a) ->
  exit_block_memory m block next -> exit_block_memory m' block next.
Proof.
  intros m m' block next Hregions Haux Hb (Hcap & Hread & Hnext & Hidx & Hlen & Hslots).
  split; [exact Hcap|]. split.
  - unfold access_res. rewrite Hregions. exact Hread.
  - split.
    + apply (exit_pointer_agree m m'); [exact Haux| |exact Hnext]. intros b Hrange. apply Hb. lia.
    + split.
      * rewrite <- Hidx. apply load_bytes_agree; [lia|]. intros i Hi. apply Hb. lia.
      * split; [exact Hlen|]. intros i slot Hi.
        apply (exit_slot_memory_agree m m'); [exact Haux| |auto].
        assert ((i < length (block_slots block))%nat) by (apply nth_error_Some; congruence).
        intros a Ha. apply Hb. apply Nat2Z.inj_lt in H. apply Nat2Z.inj_le in Hlen. lia.
Qed.

(** Exact metadata frames keep regions and shadow everywhere, and bytes
    outside the one or two narrow roots, not merely outside the block. *)
Lemma exit_pop_frame : forall m p older selected,
  m_regions (exit_pop_memory m p older selected) = m_regions m /\
  m_aux (exit_pop_memory m p older selected) = m_aux m /\
  forall a, ~ (exists root, In root (exit_pop_writes p older selected) /\ span_contains root a) ->
    m_bytes (exit_pop_memory m p older selected) a = m_bytes m a.
Proof.
  intros m p older selected. split; [destruct selected; reflexivity|].
  split; [destruct selected; reflexivity|]. intros a Hout.
  assert (Hidx : ((ptr_addr p + 8 <=? a) && (a <? ptr_addr p + 8 + 8)) = false).
  { apply Bool.not_true_is_false. intros H. apply Bool.andb_true_iff in H as [Hlo Hhi].
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi. apply Hout.
    exists (mkSpan (mkPtr (ptr_addr p + 8) (ptr_cap p)) 8).
    split; [left; reflexivity|exact (conj Hlo Hhi)]. }
  destruct selected; cbn -[Z.mul] in *; rewrite Hidx; try reflexivity.
  destruct ((ptr_addr p + 16 + 32 * Z.of_nat (length older) <=? a) &&
    (a <? ptr_addr p + 16 + 32 * Z.of_nat (length older) + 8)) eqn:E; [|reflexivity].
  exfalso. apply Hout. apply Bool.andb_true_iff in E as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
  eexists. split; [right; left; reflexivity|exact (conj Hlo Hhi)].
Qed.

(** Every constructed write lies inside the original nonempty block. *)
Lemma exit_pop_outside_block : forall m p older selected,
  (length older < 32)%nat ->
  forall a, a < ptr_addr p \/ ptr_addr p + 1040 <= a ->
    m_bytes (exit_pop_memory m p older selected) a = m_bytes m a.
Proof.
  intros m p older selected Hlen a Hout. apply (proj2 (proj2 (exit_pop_frame m p older selected))).
  intros (root & Hin & Ha). unfold exit_pop_writes in Hin.
  destruct Hin as [<-|Hin]; [unfold span_contains in Ha; simpl in Ha; lia|].
  destruct selected; try contradiction. destruct Hin as [<-|[]]. unfold span_contains in Ha.
  cbn -[Z.mul] in Ha.
  apply Nat2Z.inj_lt in Hlen. lia.
Qed.

(** Decrementing idx leaves every older slot decoded, including free holes. *)
Lemma exit_pop_index_represented : forall m p older selected next,
  exit_block_memory m (mkExitBlock p (older ++ [selected])) next ->
  exit_block_memory (exit_pop_index m p older) (mkExitBlock p older) next.
Proof.
  intros m p older selected next (Hcap & Hread & Hnext & Hidx & Hlen & Hslots).
  cbn -[Z.mul] in *. rewrite length_app in Hlen. simpl in Hlen.
  split; [exact Hcap|]. split; [exact Hread|]. split.
  - apply (pointer_slot_bytes_disjoint m (ptr_addr p + 8) 8
      (Z.of_nat (length older)) (ptr_addr p) next); [lia|left; lia|exact Hnext].
  - split.
    + unfold exit_pop_index. rewrite stored_bytes_value by lia.
      apply Z.mod_small. split; [lia|apply Nat2Z.inj_le in Hlen; cbn; lia].
    + split; [simpl; lia|]. intros i slot Hi. change (nth_error older i = Some slot) in Hi.
      apply (exit_slot_memory_agree m); [reflexivity| |].
      * intros a Ha. cbn -[Z.mul] in Ha. simpl.
        destruct ((ptr_addr p + 8 <=? a) && (a <? ptr_addr p + 8 + 8)) eqn:E; [|reflexivity].
        apply Bool.andb_true_iff in E as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi. lia.
      * apply Hslots. rewrite nth_error_app1; [exact Hi|]. apply nth_error_Some. congruence.
Qed.

(** A store beyond the represented prefix preserves its block view. *)
Lemma exit_block_store_after : forall m block next a n x,
  exit_block_memory m block next ->
  0 <= n ->
  ptr_addr (block_ptr block) + 16 + 32 * Z.of_nat (length (block_slots block)) <= a ->
  exit_block_memory (store_bytes m a n x) block next.
Proof.
  intros m block next a n x (Hcap & Hread & Hnext & Hidx & Hlen & Hslots) Hn Ha.
  split; [exact Hcap|]. split; [exact Hread|]. split.
  - apply pointer_slot_bytes_disjoint; [lia|left; lia|exact Hnext].
  - split; [rewrite exit_load_bytes_disjoint by lia; exact Hidx|]. split; [exact Hlen|].
    intros i slot Hi. apply (exit_slot_memory_agree m); [reflexivity| |auto].
    assert ((i < length (block_slots block))%nat) by (apply nth_error_Some; congruence).
    apply Nat2Z.inj_lt in H. intros b Hb. simpl.
    destruct ((a <=? b) && (b <? a + n)) eqn:E; [|reflexivity].
    apply Bool.andb_true_iff in E as [Hlo Hhi]. apply Z.leb_le in Hlo. lia.
Qed.

(** Cxa's flavor clear is outside the shortened represented prefix. *)
Theorem exit_pop_block_represented : forall m p older selected next,
  exit_block_memory m (mkExitBlock p (older ++ [selected])) next ->
  exit_block_memory (exit_pop_memory m p older selected) (mkExitBlock p older) next.
Proof.
  intros m p older selected next Hblock.
  pose proof (exit_pop_index_represented m p older selected next Hblock) as Hidx.
  destruct selected; try exact Hidx. apply exit_block_store_after; [exact Hidx|lia|simpl; lia].
Qed.

(** The containing access supplies aligned field checks for either read or
    write, but not the independent writable-root permission/liveness. *)
Lemma exit_block_field_access : forall m block next off rights,
  exit_block_memory m block next -> 0 <= off -> off + 8 <= 1040 -> off mod 8 = 0 ->
  access_res m (ptr_addr (block_ptr block) + off) (ptr_cap (block_ptr block)) 8 rights 8 = Some ok.
Proof.
  intros m block next off rights (Hcap & Hread & _) Hlo Hhi Hoff.
  rewrite Hcap in *. unfold access_res, cap_access_res in *.
  destruct (object_region (ptr_addr (block_ptr block)) (m_regions m)) as [reg|] eqn:Hr; try discriminate.
  destruct ((ptr_addr (block_ptr block) <=? ptr_addr (block_ptr block)) &&
    (ptr_addr (block_ptr block) + 1040 <=? r_end reg)) eqn:Hbounds; try discriminate.
  apply andb_true_iff in Hbounds as [_ Hend]. apply Z.leb_le in Hend.
  unfold aligned_res in Hread.
  destruct (ptr_addr (block_ptr block) mod 8 =? 0) eqn:Halign; try discriminate.
  apply Z.eqb_eq in Halign.
  assert (((ptr_addr (block_ptr block) <=? ptr_addr (block_ptr block) + off) &&
    (ptr_addr (block_ptr block) + off + 8 <=? r_end reg)) = true) as Hfield.
  { apply andb_true_iff. split; apply Z.leb_le; lia. }
  rewrite Hfield. unfold aligned_res. rewrite Z.add_mod, Halign, Hoff by lia. reflexivity.
Qed.

(** Captured payload capabilities come from complete checked source slots;
    the source span grants no write authority and no callback specification. *)
Lemma exit_block_payload_authority : forall m block next i off value,
  exit_block_memory m block next -> (i < length (block_slots block))%nat ->
  8 <= off <= 24 -> off mod 8 = 0 ->
  pointer_slot m (ptr_addr (block_ptr block) + 16 + 32 * Z.of_nat i + off) value ->
  available_cap [mkSpan (block_ptr block) 1040] [] m (ptr_cap value).
Proof.
  intros m block next i off value Hblock Hi Hoff Halign (_ & _ & Haux).
  assert (Hbound : 16 + 32 * Z.of_nat i + off + 8 <= 1040).
  { destruct Hblock as (_ & _ & _ & _ & Hlen & _).
    apply Nat2Z.inj_lt in Hi. apply Nat2Z.inj_le in Hlen. lia. }
  right. right. left. exists (mkSpan (block_ptr block) 1040),
    (ptr_addr (block_ptr block) + 16 + 32 * Z.of_nat i + off).
  split; [left; reflexivity|]. split; [unfold span_contains; cbn -[Z.add Z.mul]; lia|].
  split; [cbn -[Z.add Z.mul]; lia|]. split; [|symmetry; exact Haux].
  replace (ptr_addr (block_ptr block) + 16 + 32 * Z.of_nat i + off)
    with (ptr_addr (block_ptr block) + (16 + 32 * Z.of_nat i + off)) by lia.
  apply (exit_block_field_access m block next); [exact Hblock|lia|exact Hbound|].
  rewrite (Z.add_mod (16 + 32 * Z.of_nat i) off 8),
    (Z.add_mod 16 (32 * Z.of_nat i) 8), (Z.mul_mod 32 (Z.of_nat i) 8), Halign by lia.
  reflexivity.
Qed.

(** Capacity and containing alignment derive both native eight-byte stores. *)
Lemma exit_pop_fields : forall m p older selected next,
  exit_block_memory m (mkExitBlock p (older ++ [selected])) next ->
  (length older < 32)%nat /\
  access_res m (ptr_addr p + 8) (ptr_cap p) 8 Write 8 = Some ok /\
  access_res m (ptr_addr p + 16 + 32 * Z.of_nat (length older)) (ptr_cap p) 8 Write 8 = Some ok.
Proof.
  intros m p older selected next Hblock.
  assert (Hlen : (length older < 32)%nat).
  { destruct Hblock as (_ & _ & _ & _ & Hlen & _). simpl in Hlen.
    rewrite length_app in Hlen. simpl in Hlen. lia. }
  split; [exact Hlen|]. split.
  - exact (exit_block_field_access m (mkExitBlock p (older ++ [selected])) next 8 Write
      Hblock ltac:(lia) ltac:(lia) eq_refl).
  - replace (ptr_addr p + 16 + 32 * Z.of_nat (length older))
      with (ptr_addr p + (16 + 32 * Z.of_nat (length older))) by lia.
    apply (exit_block_field_access m (mkExitBlock p (older ++ [selected])) next); [exact Hblock|lia| |].
    + apply Nat2Z.inj_lt in Hlen. lia.
    + rewrite Z.add_mod, Z.mul_mod by lia. reflexivity.
Qed.

(** Popping a separated nonempty head preserves the head pointer, remaining
    chain and identities. Exhausting a block does not unlink or release it. *)
Theorem exit_pop_registry_represented : forall m head p older selected rest,
  exit_registry_memory m head (mkExitBlock p (older ++ [selected]) :: rest) ->
  exit_pop_separated head p rest ->
  exit_registry_memory (exit_pop_memory m p older selected) head (mkExitBlock p older :: rest).
Proof.
  intros m head p older selected rest (Hread & Hhead & [Hblock Hchain] & Hdistinct) [Hheadsep Hsep].
  destruct (exit_pop_frame m p older selected) as [Hregions [Haux Hbytes]].
  assert (Hlen : (length older < 32)%nat).
  { destruct Hblock as (_ & _ & _ & _ & Hlen & _). simpl in Hlen.
    rewrite length_app in Hlen. simpl in Hlen. lia. }
  split.
  - unfold access_res. rewrite Hregions. exact Hread.
  - split.
    + apply (exit_pointer_agree m); [exact Haux| |exact Hhead].
      intros b Hb. apply exit_pop_outside_block; [exact Hlen|lia].
    + split; [|exact Hdistinct]. split.
      * apply exit_pop_block_represented. exact Hblock.
      * clear Hhead Hheadsep Hread Hdistinct Hblock. induction rest as [|block rest IH]; [exact I|].
        destruct Hchain as [Hblock Hchain]. inversion Hsep as [|? ? Hdis Hrest]; subst.
        split; [|apply IH; assumption]. apply (exit_block_memory_agree m); try assumption.
        intros a Ha. apply exit_pop_outside_block; [exact Hlen|lia].
Qed.

(** An installed physical slot is exactly the first pending registration. *)
Lemma exit_pop_pending : forall p older selected rest entry,
  exit_slot_pending selected = [entry] ->
  exit_registry_pending (mkExitBlock p (older ++ [selected]) :: rest) =
    entry :: exit_registry_pending (mkExitBlock p older :: rest).
Proof.
  intros p older selected rest entry Hslot. change
    (exit_pending (older ++ [selected]) ++ exit_registry_pending rest =
     entry :: (exit_pending older ++ exit_registry_pending rest)).
  rewrite (exit_pending_pop older selected entry Hslot). reflexivity.
Qed.

(** Skipping a hole stutters logically; it is not a callback or TLS action. *)
Lemma exit_pop_skip : forall p older selected rest,
  selected = FreeSlot \/ selected = ReservedSlot ->
  exit_registry_pending (mkExitBlock p (older ++ [selected]) :: rest) =
    exit_registry_pending (mkExitBlock p older :: rest).
Proof.
  intros p older selected rest [-> | ->].
  - change (exit_pending (older ++ [FreeSlot]) ++ exit_registry_pending rest =
      exit_pending older ++ exit_registry_pending rest).
    rewrite exit_pending_skip_free. reflexivity.
  - change (exit_pending (older ++ [ReservedSlot]) ++ exit_registry_pending rest =
      exit_pending older ++ exit_registry_pending rest).
    rewrite exit_pending_skip_reserved. reflexivity.
Qed.

(** The installed pop constructs the existing logical callback-entry edge;
    uniqueness is supplied independently, never inferred from slot addresses. *)
Theorem exit_pop_shutdown : forall p older selected rest entry status consumed q,
  exit_slot_pending selected = [entry] ->
  let before := mkShutdown Handlers status
    (exit_registry_pending (mkExitBlock p (older ++ [selected]) :: rest)) consumed q in
  let after := mkShutdown (InCallback entry) status
    (exit_registry_pending (mkExitBlock p older :: rest))
    (consumed ++ [registration_token entry]) q in
  shutdown_unique before ->
  shutdown_step before (InvokeCallback entry status) after /\ shutdown_unique after.
Proof.
  intros p older selected rest entry status consumed q Hslot before after Hunique.
  assert (Hstep : shutdown_step before (InvokeCallback entry status) after).
  { unfold before, after. rewrite (exit_pop_pending p older selected rest entry Hslot). constructor. }
  split; [exact Hstep|]. eapply shutdown_step_unique; eauto.
Qed.

(** Admission specifications may depend on memory. Stability is a general
    footprint rule over any two snapshots, not the desired endpoint premise.
    In particular an argument that aliases idx needs separate justification. *)
Definition exit_admission_stable (admitted : mem -> registration -> Prop) (roots : list span) : Prop :=
  forall m m', m_regions m' = m_regions m -> m_aux m' = m_aux m ->
    (forall a, ~ (exists root, In root roots /\ span_contains root a) -> m_bytes m' a = m_bytes m a) ->
    forall entry, admitted m entry -> admitted m' entry.

(** The same exact frame transports every remaining and active admission. *)
Theorem exit_pop_admitted : forall admitted m p older selected rest entry,
  exit_slot_pending selected = [entry] ->
  exit_admission_stable admitted (exit_pop_writes p older selected) ->
  exit_callbacks_admitted admitted m (mkExitBlock p (older ++ [selected]) :: rest) None ->
  exit_callbacks_admitted admitted (exit_pop_memory m p older selected)
    (mkExitBlock p older :: rest) (Some entry).
Proof.
  intros admitted m p older selected rest entry Hslot Hstable [Hall _].
  rewrite (exit_pop_pending p older selected rest entry Hslot) in Hall.
  inversion Hall as [|? ? Hentry Hrest]; subst.
  destruct (exit_pop_frame m p older selected) as [Hregions [Haux Hbytes]].
  assert (Htransport : forall item, admitted m item -> admitted (exit_pop_memory m p older selected) item).
  { apply Hstable; assumption. }
  split; [|apply Htransport; exact Hentry].
  eapply Forall_impl; [|exact Hrest]. intros item Hi. apply Htransport. exact Hi.
Qed.

(** Construction uses the existing bounded-write effects, with no allocations
    or releases. Both the index-only prefix and cxa's final prefix are valid. *)
Module ExitPop (R : Runtime).
Module E := ExternalCalls R.

(** Writable roots survive these stores because their regions do not change. *)
Lemma pop_effects : forall sources s m p older selected,
  Forall (writable_span m) (exit_pop_writes p older selected) ->
  E.effects sources (exit_pop_writes p older selected) [] (fun _ _ => False)
    s m [] s (exit_pop_index m p older) [] /\
  E.effects sources (exit_pop_writes p older selected) [] (fun _ _ => False)
    s m [] s (exit_pop_memory m p older selected) [].
Proof.
  intros sources s m p older selected Hw.
  assert (Hindex : local_effect sources (exit_pop_writes p older selected) [] [] m (exit_pop_index m p older)).
  { apply local_store_bytes. intros a Ha. left.
    exists (mkSpan (mkPtr (ptr_addr p + 8) (ptr_cap p)) 8).
    split; [left; reflexivity|]. split; [inversion Hw; assumption|exact Ha]. }
  assert (Hprefix : E.effects sources (exit_pop_writes p older selected) [] (fun _ _ => False)
    s m [] s (exit_pop_index m p older) []).
  { eapply E.effects_local; [exact Hindex|constructor]. }
  split; [exact Hprefix|]. destruct selected; try exact Hprefix.
  eapply E.effects_local; [exact Hindex|]. eapply E.effects_local; [|constructor].
  apply local_store_bytes. intros a Ha. left.
  exists (mkSpan (mkPtr (ptr_addr p + 16 + 32 * Z.of_nat (length older)) (ptr_cap p)) 8).
  split; [right; left; reflexivity|]. split; [|exact Ha].
  change (writable_span m (mkSpan
    (mkPtr (ptr_addr p + 16 + 32 * Z.of_nat (length older)) (ptr_cap p)) 8)).
  inversion Hw as [|? ? _ Htail]; subst. inversion Htail; assumption.
Qed.

(** Any runtime stays ready and every identity persists at both constructed
    cutpoints. No behavior of generic runtime free is used. *)
Theorem pop_preserves : forall s m p older selected,
  Forall (writable_span m) (exit_pop_writes p older selected) -> R.ready s m ->
  (R.ready s (exit_pop_index m p older) /\ persists m (exit_pop_index m p older)) /\
  (R.ready s (exit_pop_memory m p older selected) /\ persists m (exit_pop_memory m p older selected)).
Proof.
  intros s m p older selected Hw Hr.
  destruct (pop_effects [] s m p older selected Hw) as [Hindex Hpop].
  split; eapply E.effects_preserve; eauto.
Qed.

End ExitPop.

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

(** Cxa removes exactly its newest flavor, leaving older slots and captured
    function/argument capabilities. Index-only completion is insufficient. *)
Example constructed_cxa_pop :
  let m' := exit_pop_memory memory (block_ptr block) [oldest; FreeSlot] newest in
  load_bytes m' 2056 8 = 2 /\ load_bytes m' 2128 8 = 0 /\
  load_bytes m' 2064 8 = 2 /\
  pointer_slot m' 2136 (mkPtr 65544 (Fn (TAtom "newest"))) /\
  m_aux m' = m_aux memory /\
  exit_registry_memory m' (mkPtr 1000 (Obj 1000))
    [mkExitBlock (block_ptr block) [oldest; FreeSlot]].
Proof.
  intros m'. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [vm_compute; repeat split; congruence|]. split; [reflexivity|].
  apply (exit_pop_registry_represented memory (mkPtr 1000 (Obj 1000))
    (block_ptr block) [oldest; FreeSlot] newest [] registry_represented).
  split; [left; simpl; lia|constructor].
Qed.

(** Hole and ordinary callback removal decrement idx without clearing payloads. *)
Example constructed_other_pops :
  load_bytes (exit_pop_memory memory (block_ptr block) [oldest] FreeSlot) 2056 8 = 1 /\
  load_bytes (exit_pop_memory memory (block_ptr block) [] ReservedSlot) 2056 8 = 0 /\
  load_bytes (exit_pop_memory memory (block_ptr block) [] oldest) 2064 8 = 2.
Proof. repeat split; reflexivity. Qed.

(** The narrow cxa roots are independently writable, without permitting any
    callback argument write or heap release. *)
Example pop_roots_writable :
  Forall (writable_span memory) (exit_pop_writes (block_ptr block) [oldest; FreeSlot] newest).
Proof.
  constructor.
  - split; [simpl; lia|]. exists 2048, (mkRegion 2048 3088 GlobalData Live).
    repeat split; reflexivity.
  - constructor; [|constructor]. split; [simpl; lia|]. exists 2048, (mkRegion 2048 3088 GlobalData Live).
    repeat split; reflexivity.
Qed.

(** A real changed index cannot be justified by an empty write footprint. *)
Example pop_without_write_authority_rejected :
  ~ local_effect [] [] [] [] memory (exit_pop_index memory (block_ptr block) [oldest; FreeSlot]).
Proof.
  intros (_ & _ & Hframe & _).
  assert (Hnone : ~ write_authority [] [] memory 2056).
  { intros [(root & [] & _) | (base & reg & [] & _)]. }
  destruct (Hframe 2056 Hnone) as [Hbyte _]. discriminate Hbyte.
Qed.

(** An empty physical prefix cannot be decomposed into a selected pop. *)
Example empty_pop_rejected : forall (older : list exit_slot) selected,
  [] <> older ++ [selected].
Proof. intros older selected H. apply (f_equal (@length exit_slot)) in H.
  rewrite length_app in H. simpl in H. lia. Qed.

(** Data-sensitive admission of the known callbacks, retaining the pending
    on_exit argument's checked byte. Not a native callback implementation. *)
Definition pop_admission m entry : Prop :=
  In entry (exit_registry_pending [block]) /\
  access_res m 4096 (Obj 4096) 1 Read 1 = Some ok /\ load_bytes m 4096 1 = 0.

(** Its checked data lies outside both metadata roots, so the general
    stability premise is discharged rather than assumed at the endpoint. *)
Lemma pop_admission_stable :
  exit_admission_stable pop_admission (exit_pop_writes (block_ptr block) [oldest; FreeSlot] newest).
Proof.
  intros m m' Hregions Haux Hbytes entry (Hin & Hread & Hdata).
  split; [exact Hin|]. split.
  - unfold access_res. rewrite Hregions. exact Hread.
  - rewrite <- Hdata. apply load_bytes_agree; [lia|]. intros i Hi. apply Hbytes.
    intros (root & [<- | [<- | []]] & Hrange); unfold span_contains in Hrange;
      cbn -[Z.add Z.mul] in Hrange; lia.
Qed.

(** Both the still-pending argument and the detached active callback stay
    admitted at the actual constructed endpoint. *)
Example constructed_pop_admitted :
  exit_callbacks_admitted pop_admission
    (exit_pop_memory memory (block_ptr block) [oldest; FreeSlot] newest)
    [mkExitBlock (block_ptr block) [oldest; FreeSlot]]
    (Some (mkRegistration 11 (CxaExit (TAtom "newest") (WPtr (mkPtr 0 CNone))))).
Proof.
  apply (exit_pop_admitted pop_admission memory (block_ptr block) [oldest; FreeSlot] newest []);
    [reflexivity|exact pop_admission_stable|].
  split; [|exact I]. constructor.
  - split; [left; reflexivity|]. split; reflexivity.
  - constructor; [|constructor]. split; [right; left; reflexivity|]. split; reflexivity.
Qed.

(** A specification depending on idx does NOT satisfy footprint stability. *)
Example index_dependent_admission_rejected :
  ~ exit_admission_stable (fun m _ => load_bytes m 2056 8 = 3)
    (exit_pop_writes (block_ptr block) [oldest; FreeSlot] newest).
Proof.
  intros Hstable. destruct (exit_pop_frame memory (block_ptr block) [oldest; FreeSlot] newest)
    as [Hregions [Haux Hbytes]].
  pose proof (Hstable memory (exit_pop_memory memory (block_ptr block) [oldest; FreeSlot] newest)
    Hregions Haux Hbytes (mkRegistration 11 (AtExit (TAtom "index"))) eq_refl) as Hbad.
  discriminate Hbad.
Qed.

(** A second block with one skipped physical slot is genuinely represented. *)
Definition tail_block : exit_block := mkExitBlock (mkPtr 8192 (Obj 8192)) [FreeSlot].
(** Link the original block to separate storage, preserving its callback data. *)
Definition chain_memory : mem :=
  let m := mkMem (m_bytes memory) (m_regions memory ++ [mkRegion 8192 9232 GlobalData Live]) (m_aux memory) in
  store_bytes (startup_store m 2048 (block_ptr tail_block)) 8200 8 1.

(** Both blocks and the external head cell satisfy the checked snapshot. *)
Lemma chain_represented : exit_registry_memory chain_memory (mkPtr 1000 (Obj 1000)) [block; tail_block].
Proof.
  split; [reflexivity|]. split; [vm_compute; repeat split; congruence|]. split.
  - split.
    + split; [reflexivity|]. split; [reflexivity|]. split; [vm_compute; repeat split; congruence|].
      split; [reflexivity|]. split; [simpl; lia|].
      intros i slot Hi. destruct i as [|[|[|i]]]; simpl in Hi; try (destruct i; discriminate Hi);
        injection Hi as <-; vm_compute; repeat split; congruence.
    + split; [|exact I]. split; [reflexivity|]. split; [reflexivity|].
      split; [vm_compute; repeat split; congruence|]. split; [reflexivity|]. split; [simpl; lia|].
      intros i slot Hi. destruct i; simpl in Hi; [injection Hi as <-; reflexivity|destruct i; discriminate Hi].
  - repeat constructor; simpl; intuition congruence.
Qed.

(** A constructed cxa pop preserves a nonempty separated suffix, not only
    singleton registries. No block is freed at this cutpoint. *)
Example constructed_multiblock_pop :
  exit_registry_memory (exit_pop_memory chain_memory (block_ptr block) [oldest; FreeSlot] newest)
    (mkPtr 1000 (Obj 1000)) [mkExitBlock (block_ptr block) [oldest; FreeSlot]; tail_block].
Proof.
  apply (exit_pop_registry_represented chain_memory (mkPtr 1000 (Obj 1000))
    (block_ptr block) [oldest; FreeSlot] newest [tail_block] chain_represented).
  split; [left; simpl; lia|]. constructor; [right; simpl; lia|constructor].
Qed.

(** A snapshot can alias its own head cell with idx; distinct block
    identities alone therefore do not justify metadata-write preservation. *)
Definition aliased_memory : mem :=
  store_aux (store_bytes (mkMem (fun _ => 0) [mkRegion 8 1048 GlobalData Live] (fun _ => CNone))
    16 8 8) 16 (Obj 8).

(** Eight free physical slots make both interpretations of that cell agree. *)
Lemma aliased_head_represented :
  exit_registry_memory aliased_memory (mkPtr 16 (Obj 8))
    [mkExitBlock (mkPtr 8 (Obj 8)) (repeat FreeSlot 8)].
Proof.
  split; [reflexivity|]. split; [vm_compute; repeat split; congruence|]. split.
  - split; [|exact I]. split; [reflexivity|]. split; [reflexivity|].
    split; [vm_compute; repeat split; congruence|]. split; [reflexivity|]. split; [simpl; lia|].
    intros i slot Hi. apply nth_error_In in Hi. apply repeat_spec in Hi. subst slot.
    change (load_bytes (store_bytes
      (mkMem (fun _ => 0) [mkRegion 8 1048 GlobalData Live] (fun _ => CNone)) 16 8 8)
      (8 + 16 + 32 * Z.of_nat i) 8 = 0).
    rewrite exit_load_bytes_disjoint by lia. reflexivity.
  - constructor; [simpl; tauto|constructor].
Qed.

(** The actual decrement destroys that aliased head; the separation premise
    excludes this valid counterexample to the unrestricted theorem. *)
Example aliased_head_pop_rejected :
  ~ exit_pop_separated (mkPtr 16 (Obj 8)) (mkPtr 8 (Obj 8)) [] /\
  ~ exit_registry_memory
    (exit_pop_memory aliased_memory (mkPtr 8 (Obj 8)) (repeat FreeSlot 7) FreeSlot)
    (mkPtr 16 (Obj 8)) [mkExitBlock (mkPtr 8 (Obj 8)) (repeat FreeSlot 7)].
Proof.
  split; [intros [H _]; simpl in H; lia|].
  intros (_ & (_ & Hload & _) & _). discriminate Hload.
Qed.

End ExitMemoryChecks.
