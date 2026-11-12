(** The Fil-C launcher's entry contract, before libc calls main
    ([milestone 3a](../../../docs/formal.md#campaign-4-milestone-3a-launcher-entry-memory)).

    The pinned filc_start_program.c copies argv and environ into fresh
    [[capability]]-bearing objects. Pointer arrays include a null sentinel;
    strings include an in-object first NUL. Lengths and contents are not
    restricted to the native probes. The launcher asserts argc >= 1.

    These are concrete predicates on model memory, not new
    [[runtime|runtime axioms]] or a proof of the native launcher.
    Establishing the full entry image from startup allocations, including
    libc/TLS and finalizer roots, remains a separate
    [[obligation]]. Resource refusal before entry
    must not be confused with a malformed entry or deleted execution. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Identity ExternalCalls ExternalMachine.
Import ListNotations.
Open Scope Z_scope.

(** The eight-byte cell at address a of memory m holds pointer p: its
    bytes read as p's address and its [[aux]] entry is p's capability.
    A slot carries address bits AND the corresponding capability.
    Bounding the address below 2^64 prevents an integer outside the
    word range from standing for the same stored bytes. *)
Definition pointer_slot (m : mem) (a : Z) (p : ptr) : Prop :=
  0 <= ptr_addr p < 2 ^ 64 /\
  load_bytes m a 8 = ptr_addr p /\ m_aux m a = ptr_cap p.

(** The same address/aux store used by store_res constructs an actual
    decoded slot. No access or capability authority is inferred here;
    local_store_pointer supplies the separate footprint obligation. *)
Lemma pointer_slot_written : forall m a p,
  0 <= ptr_addr p < 2 ^ 64 ->
  pointer_slot (store_aux (store_bytes m a 8 (ptr_addr p)) a (ptr_cap p)) a p.
Proof.
  intros m a p Hp. split; [exact Hp|]. split.
  - change (load_bytes (store_bytes m a 8 (ptr_addr p)) a 8 = ptr_addr p).
    rewrite stored_bytes_value by lia. apply Z.mod_small. exact Hp.
  - simpl. rewrite Z.eqb_refl. reflexivity.
Qed.

(** A byte store of size bytes at address a keeps a [pointer_slot] at
    b that it does not overlap. *)
Lemma pointer_slot_bytes_disjoint : forall m a size x b p,
  0 <= size -> b + 8 <= a \/ a + size <= b -> pointer_slot m b p ->
  pointer_slot (store_bytes m a size x) b p.
Proof.
  intros m a size x b p Hsize Hdis [Hp [Hbytes Haux]]. split; [exact Hp|]. split; [|exact Haux].
  rewrite <- Hbytes. apply load_bytes_agree; [lia|]. intros i Hi. simpl.
  destruct ((a <=? b + i) && (b + i <? a + size)) eqn:E; [|reflexivity].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

(** A pointer store at address a keeps a [pointer_slot] at b eight or
    more bytes away. *)
Lemma pointer_slot_pointer_disjoint : forall m a p b q,
  b + 8 <= a \/ a + 8 <= b -> pointer_slot m b q ->
  pointer_slot (store_aux (store_bytes m a 8 (ptr_addr p)) a (ptr_cap p)) b q.
Proof.
  intros m a p b q Hdis Hslot.
  destruct (pointer_slot_bytes_disjoint m a 8 (ptr_addr p) b q ltac:(lia) Hdis Hslot)
    as [Hq [Hbytes Haux]]. split; [exact Hq|]. split; [exact Hbytes|]. simpl.
  assert ((b =? a) = false) as E by (apply Z.eqb_neq; lia).
  rewrite E. exact Haux.
Qed.

(** From address a on, memory m holds one [pointer_slot] per text,
    each pointing at a [c_string] with that text, then a null slot. *)
Fixpoint string_slots (m : mem) (a : Z) (texts : list (list Z)) : Prop :=
  match texts with
  | [] => pointer_slot m a (mkPtr 0 CNone)
  | text :: rest => exists p,
      pointer_slot m a p /\ c_string m p text /\ string_slots m (a + 8) rest
  end.

(** Pointer table points at a null-terminated array of C strings with
    the given texts, as argv and envp are. Check the entire pointer
    array, including its sentinel, with the array's capability and
    pointer alignment. A raw address whose [[aux]]
    metadata was lost does not satisfy the string slots. *)
Definition string_vector (m : mem) (table : ptr) (texts : list (list Z)) : Prop :=
  access_res m (ptr_addr table) (ptr_cap table)
    (8 * (Z.of_nat (length texts) + 1)) Read 8 = Some ok /\
  string_slots m (ptr_addr table) texts.

(** Memory m is the launcher's entry image for main's arguments argc,
    argv and envp, with argument strings args and environment strings
    environment: argc is a positive int counting args, and argv and
    envp are [string_vector]s of them. *)
Definition startup_at (m : mem) (argc : Z) (argv envp : ptr)
    (args environment : list (list Z)) : Prop :=
  1 <= argc < 2 ^ 31 /\ argc = Z.of_nat (length args) /\
  string_vector m argv args /\ string_vector m envp environment.

(** A libc-exposed pointer cell has its own writable object authority
    and decoded value. Authority to its pointee is not authority to
    change the cell, nor does this predicate establish FILE validity. *)
Definition exposed_pointer_cell (m : mem) (cell value : ptr) : Prop :=
  writable_span m (mkSpan cell 8) /\
  access_res m (ptr_addr cell) (ptr_cap cell) 8 Read 8 = Some ok /\
  access_res m (ptr_addr cell) (ptr_cap cell) 8 Write 8 = Some ok /\
  pointer_slot m (ptr_addr cell) value.

(** Distinct symbolic roles, not an assertion that their storage is
    disjoint. The program-name aliases may name the same native cells. *)
Record libc_global_cells : Type := mkLibcGlobalCells {
  stdout_cell : ptr;
  stderr_cell : ptr;
  invocation_name_cell : ptr;
  short_name_cell : ptr
}.

(** Symbol resolution reaches the cells themselves, not the FILE or
    character buffer stored in them. Module linking supplies this map. *)
Definition libc_globals_bound (ge : genv) (g : libc_global_cells) : Prop :=
  lookup (TAtom "stdout") (ge_globals ge) = Some (stdout_cell g) /\
  lookup (TAtom "stderr") (ge_globals ge) = Some (stderr_cell g) /\
  lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (invocation_name_cell g) /\
  lookup (TAtom "program_invocation_short_name") (ge_globals ge) = Some (short_name_cell g).

(** Concrete exposed cells at a successful entry. Program names have
    independently readable NUL-terminated contents; they are not
    silently identified with the launcher's copied argv[0]. Program
    code may subsequently replace their pointer values. Stream object
    validity, libc/TLS state and separation remain separate premises. *)
Definition libc_globals_at (m : mem) (g : libc_global_cells)
    (out err full short : ptr) : Prop :=
  exposed_pointer_cell m (stdout_cell g) out /\
  exposed_pointer_cell m (stderr_cell g) err /\
  exposed_pointer_cell m (invocation_name_cell g) full /\
  exposed_pointer_cell m (short_name_cell g) short /\
  (exists bytes, c_string m full bytes) /\ (exists bytes, c_string m short bytes).

(** The ordinary non-atomic pointer-load protocol recovers exactly
    the stored address AND capability, not an external/null surrogate. *)
Lemma exposed_pointer_load : forall m cell value,
  exposed_pointer_cell m cell value ->
  pointer_load_effects m (ptr_addr cell) [AuxRead; LowerResolve; AddressRead] = Some value.
Proof.
  intros m cell [a c] (_ & _ & _ & _ & Hbytes & Haux).
  unfold pointer_load_effects, pointer_load_effect, aux_at. simpl.
  rewrite Hbytes, Haux. reflexivity.
Qed.

(** The three words the launcher passes to main: argc, argv, envp. *)
Definition main_arguments (argc : Z) (argv envp : ptr) : list word :=
  [WInt argc; WPtr argv; WPtr envp].

(** Hello's two-parameter main binds the first two launcher words and
    ignores the extra environment word. This gives its actual fresh
    frame, without restricting the strings or resetting runtime state. *)
Lemma main_argv_frame : forall f b blocks argc_name argv_name argc argv envp,
  fn_params f = [(W, argc_name); (P, argv_name)] -> fn_blocks f = b :: blocks ->
  variadic_func f = false ->
  call_frame f (main_arguments argc argv envp) = Some
    (mkFrame f (put argv_name (WPtr argv) (put argc_name (WInt argc) []))
      (map (fun xs => (fst xs, None)) (local_objects f)) None (Enter (b_label b) None)).
Proof. intros f b blocks an vn argc argv envp Hp Hb Hv. unfold call_frame.
  rewrite Hp, Hb, Hv. reflexivity.
Qed.

(** The byte size of the launcher's argv copy, 8 * (argc + 1).
    The native expression argc + 1 is evaluated as int BEFORE the
    checked size multiplication. Readable entry and successful copying
    are distinct: INT_MAX is an ABI value but overflows that expression. *)
Definition argv_copy_size (argc : Z) : Z := 8 * (argc + 1).

(** For argc from 1 below INT_MAX (2^31 - 1), argc + 1 does not
    overflow int and the copy size is a positive legal allocation size
    ([max_allocation_size]). *)
Lemma argv_copy_bounds : forall argc,
  1 <= argc < 2 ^ 31 - 1 ->
  0 < argc + 1 < 2 ^ 31 /\ 0 < argv_copy_size argc <= max_allocation_size.
Proof. intros argc H. unfold argv_copy_size, max_allocation_size. lia. Qed.

(** If [string_slots] holds from a, the slot of the i-th text, at
    a + 8 * i, points at a C string with that text. *)
Lemma string_slots_nth : forall m texts a i text,
  string_slots m a texts -> nth_error texts i = Some text ->
  exists p, pointer_slot m (a + 8 * Z.of_nat i) p /\ c_string m p text.
Proof.
  intros m texts. induction texts as [|head rest IH]; intros a i text Hslots Hi.
  - destruct i; discriminate Hi.
  - destruct Hslots as (p & Hp & Hs & Hrest). destruct i as [|i].
    + injection Hi as <-. replace (a + 8 * Z.of_nat 0) with a by lia. eauto.
    + simpl in Hi. destruct (IH _ _ _ Hrest Hi) as (q & Hq & Htext).
      exists q. replace (a + 8 * Z.of_nat (S i)) with (a + 8 + 8 * Z.of_nat i) by lia. auto.
Qed.

(** If [string_slots] holds from a, the slot after the last text is
    null. *)
Lemma string_slots_sentinel : forall m texts a,
  string_slots m a texts ->
  pointer_slot m (a + 8 * Z.of_nat (length texts)) (mkPtr 0 CNone).
Proof.
  intros m texts. induction texts as [|text rest IH]; intros a H.
  - replace (a + 8 * Z.of_nat (length [])) with a by (simpl; lia). exact H.
  - destruct H as (p & _ & _ & H). specialize (IH _ H).
    change (pointer_slot m (a + 8 * Z.of_nat (S (length rest))) (mkPtr 0 CNone)).
    rewrite Nat2Z.inj_succ.
    replace (a + 8 * Z.succ (Z.of_nat (length rest))) with
      (a + 8 + 8 * Z.of_nat (length rest)) by lia. exact IH.
Qed.

(** In an entry image ([startup_at]), argv's i-th slot points at a C
    string with the i-th argument, for any finite arguments. *)
Theorem startup_argument : forall m argc argv envp args environment i text,
  startup_at m argc argv envp args environment -> nth_error args i = Some text ->
  exists p, pointer_slot m (ptr_addr argv + 8 * Z.of_nat i) p /\ c_string m p text.
Proof.
  intros m argc argv envp args environment i text (_ & _ & [_ H] & _) Hi.
  exact (string_slots_nth _ _ _ _ _ H Hi).
Qed.

(** Likewise, envp's i-th slot points at the i-th environment string. *)
Theorem startup_environment : forall m argc argv envp args environment i text,
  startup_at m argc argv envp args environment -> nth_error environment i = Some text ->
  exists p, pointer_slot m (ptr_addr envp + 8 * Z.of_nat i) p /\ c_string m p text.
Proof.
  intros m argc argv envp args environment i text (_ & _ & _ & [_ H]) Hi.
  exact (string_slots_nth _ _ _ _ _ H Hi).
Qed.

(** In an entry image, argv's slot argc and envp's slot after the last
    environment string are null. *)
Theorem startup_sentinels : forall m argc argv envp args environment,
  startup_at m argc argv envp args environment ->
  pointer_slot m (ptr_addr argv + 8 * argc) (mkPtr 0 CNone) /\
  pointer_slot m (ptr_addr envp + 8 * Z.of_nat (length environment)) (mkPtr 0 CNone).
Proof.
  intros m argc argv envp args environment (_ & -> & [_ Ha] & [_ He]).
  split; apply string_slots_sentinel; assumption.
Qed.

(** For a function f with no parameters, a first [[block]] b and no
    variadic arguments, [call_frame] with the launcher's three words
    gives the same fresh [[frame]] as with none: C's main(void) ignores
    the launcher's extra arguments. Do not replace a general entry by a
    launcher with an empty argv. *)
Lemma main_void_entry : forall f b blocks argc argv envp,
  fn_params f = [] -> fn_blocks f = b :: blocks -> variadic_func f = false ->
  call_frame f (main_arguments argc argv envp) =
    Some (mkFrame f [] (map (fun xs => (fst xs, None)) (local_objects f)) None
      (Enter (b_label b) None)).
Proof.
  intros f b blocks argc argv envp Hp Hb Hv. unfold call_frame.
  rewrite Hp, Hb, Hv. reflexivity.
Qed.

(** The exit status the process reports for main's or exit's status:
    its low byte, not a second acceptance or flush event. This
    conversion will be used only AFTER shutdown. *)
Definition process_status (status : Z) : Z := status mod 256.

(** A process status is a byte. *)
Lemma process_status_range : forall status, 0 <= process_status status < 256.
Proof. intros status. unfold process_status. apply Z.mod_pos_bound. lia. Qed.

(** ## Constructing the launcher's copied strings

    The source bytes here describe native argv/environ strings, before
    they enter the capability model. This is the memcpy suboperation,
    including the NUL. It never creates a pointer capability by copying
    raw bytes; only the actual allocator answer creates that identity. *)
(** Copy bytes to address a, then write one NUL; copy no [[capability]]. *)
Fixpoint copy_c_bytes (m : mem) (a : Z) (bytes : list Z) : mem :=
  match bytes with
  | [] => store_bytes m a 1 0
  | b :: rest => copy_c_bytes (store_bytes m a 1 b) (a + 1) rest
  end.

(** Copying the bytes and NUL leaves every object's region unchanged. *)
Lemma copy_c_bytes_regions : forall bytes m a,
  m_regions (copy_c_bytes m a bytes) = m_regions m.
Proof. induction bytes; intros; simpl; [reflexivity|rewrite IHbytes; reflexivity]. Qed.

(** Byte copying changes no stored [[aux|capabilities]], even inside the copy. *)
Lemma copy_c_bytes_aux : forall bytes m a,
  m_aux (copy_c_bytes m a bytes) = m_aux m.
Proof. induction bytes; intros; simpl; [reflexivity|rewrite IHbytes; reflexivity]. Qed.

(** Bytes before the copy or at and beyond its end keep their old values. *)
Lemma copy_c_bytes_outside : forall bytes m a b,
  b < a \/ a + Z.of_nat (length bytes) + 1 <= b ->
  m_bytes (copy_c_bytes m a bytes) b = m_bytes m b.
Proof.
  induction bytes as [|head rest IH]; intros m a b Hout.
  - simpl. destruct ((a <=? b) && (b <? a + 1)) eqn:E; [|reflexivity].
    apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. simpl in Hout. lia.
  - change (m_bytes (copy_c_bytes (store_bytes m a 1 head) (a + 1) rest) b = m_bytes m b).
    change (b < a \/ a + Z.of_nat (S (length rest)) + 1 <= b) in Hout.
    rewrite Nat2Z.inj_succ in Hout. rewrite IH by lia.
    simpl. destruct ((a <=? b) && (b <? a + 1)) eqn:E; [|reflexivity].
    apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    lia.
Qed.

(** Nonzero byte values are copied exactly, with the first NUL just after them. *)
Theorem copied_string_bytes : forall bytes m a,
  Forall (fun b => 0 < b < 256) bytes -> string_at (copy_c_bytes m a bytes) a bytes.
Proof.
  induction bytes as [|b rest IH]; intros m a Hbytes.
  - simpl. rewrite Z.leb_refl.
    assert ((a <? a + 1) = true) as E by (apply Z.ltb_lt; lia). rewrite E.
    replace (a - a) with 0 by lia. reflexivity.
  - inversion Hbytes as [|head tail Hb Hrest]; subst. simpl. split; [exact Hb|]. split.
    + rewrite copy_c_bytes_outside by lia.
      pose proof (stored_byte m a 1 b 0 ltac:(lia)) as Hstored.
      replace (a + 0) with a in Hstored by lia. rewrite Hstored.
      unfold byte_of. change ((b / 1) mod 256 = b).
      rewrite Z.div_1_r. apply Z.mod_small. lia.
    + apply IH. exact Hrest.
Qed.

(** A copied fresh string cannot modify any old object, not just an
    enumerated set of startup roots. This frame will retain earlier
    strings while subsequent launcher allocations/copies take place. *)
Theorem copied_string_old_object : forall m q base bytes a,
  fresh m q base -> Z.of_nat (length bytes) + 1 <= req_extent q -> in_object m a ->
  m_bytes (copy_c_bytes (allocated m q base) base bytes) a = m_bytes m a /\
  m_aux (copy_c_bytes (allocated m q base) base bytes) a = m_aux m a.
Proof.
  intros m q base bytes a (_ & _ & _ & _ & Hdis & _) Hsize (old & reg & Hreg & Hrange).
  specialize (Hdis old reg Hreg). split.
  - rewrite copy_c_bytes_outside by lia. reflexivity.
  - rewrite copy_c_bytes_aux. reflexivity.
Qed.

(** Startup keeps all old regions exactly and all old-object bytes and
    capabilities outside the pointer slots it is filling. New objects
    need not be unchanged; their contents are constructed separately. *)
Definition startup_frame (m m' : mem) (lo hi : Z) : Prop :=
  (forall b reg, object_region b (m_regions m) = Some reg ->
    object_region b (m_regions m') = Some reg) /\
  (forall a, in_object m a -> a < lo \/ hi <= a ->
    m_bytes m' a = m_bytes m a /\ m_aux m' a = m_aux m a).

(** Allocating and copying a fresh string frames every old object. *)
Lemma copied_string_frame : forall m q base bytes lo hi,
  fresh m q base -> Z.of_nat (length bytes) + 1 <= req_extent q ->
  startup_frame m (copy_c_bytes (allocated m q base) base bytes) lo hi.
Proof.
  intros m q base bytes lo hi Hfresh Hsize. split.
  - intros b reg H. rewrite copy_c_bytes_regions. eapply allocated_old_region; [|exact H].
    exact (proj1 (proj2 (proj2 (proj2 Hfresh)))).
  - intros a Hin _. eapply copied_string_old_object; eauto.
Qed.

(** A startup frame transports old access checks without ending lifetimes. *)
Lemma startup_frame_access : forall m m' lo hi a c size rights align,
  startup_frame m m' lo hi -> access_res m a c size rights align = Some ok ->
  access_res m' a c size rights align = Some ok.
Proof.
  intros m m' lo hi a c size rights align [Hr _] Ha.
  unfold access_res, cap_access_res in Ha. destruct c as [|b|b|f|f]; try discriminate.
  all: destruct (object_region b (m_regions m)) as [reg|] eqn:E; try discriminate;
    unfold access_res, cap_access_res; rewrite (Hr _ _ E); exact Ha.
Qed.

(** Framing an old object leaves it an object for later allocations. *)
Lemma startup_frame_in : forall m m' lo hi a,
  startup_frame m m' lo hi -> in_object m a -> in_object m' a.
Proof. intros m m' lo hi a [Hr _] (b & reg & E & H). exists b, reg. auto. Qed.

(** Consecutive construction steps may write in adjoining slot ranges. *)
Lemma startup_frame_join : forall m m1 m2 lo mid hi,
  lo <= mid <= hi -> startup_frame m m1 lo mid -> startup_frame m1 m2 mid hi ->
  startup_frame m m2 lo hi.
Proof.
  intros m m1 m2 lo mid hi Hbounds [Hr1 Hb1] [Hr2 Hb2]. split.
  - intros b reg H. auto.
  - intros a Hin Hout.
    assert (Hin1 : in_object m1 a).
    { destruct Hin as (b & reg & E & H). exists b, reg. auto. }
    destruct (Hb2 a Hin1 ltac:(lia)) as [Hbytes Haux].
    rewrite Hbytes, Haux. apply Hb1; auto; lia.
Qed.

(** A store writes the address bytes and the capability of a pointer. *)
Definition startup_store (m : mem) (a : Z) (p : ptr) : mem :=
  store_aux (store_bytes m a 8 (ptr_addr p)) a (ptr_cap p).

(** A pointer store frames every old byte and capability outside its slot. *)
Lemma startup_store_frame : forall m a p, startup_frame m (startup_store m a p) a (a + 8).
Proof.
  intros m a p. split; [intros; assumption|]. intros b Hin Hout.
  unfold startup_store. simpl.
  assert (((a <=? b) && (b <? a + 8)) = false) as E.
  { apply Bool.not_true_is_false. intros H. apply andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. }
  assert ((b =? a) = false) as E' by (apply Z.eqb_neq; lia).
  rewrite E, E'. auto.
Qed.

(** An old checked pointer slot survives a frame disjoint from its eight bytes. *)
Lemma startup_frame_slot : forall m m' lo hi a p,
  startup_frame m m' lo hi -> (forall b, a <= b < a + 8 -> in_object m b) ->
  (forall b, a <= b < a + 8 -> b < lo \/ hi <= b) ->
  pointer_slot m a p -> pointer_slot m' a p.
Proof.
  intros m m' lo hi a p [_ Hb] Ha Hdis [Hp [Hbytes Haux]].
  split; [exact Hp|]. split.
  - rewrite <- Hbytes. apply load_bytes_agree; [lia|]. intros i Hi.
    apply (proj1 (Hb (a + i) (Ha (a + i) ltac:(lia)) (Hdis (a + i) ltac:(lia)))).
  - rewrite (proj2 (Hb a (Ha a ltac:(lia)) (Hdis a ltac:(lia)))). exact Haux.
Qed.

(** C-string contents depend only on their payload bytes and final NUL. *)
Lemma string_at_agree : forall bytes m m' a,
  (forall b, a <= b < a + Z.of_nat (length bytes) + 1 -> m_bytes m' b = m_bytes m b) ->
  string_at m a bytes -> string_at m' a bytes.
Proof.
  induction bytes as [|b rest IH]; intros m m' a Hb Hs.
  - simpl in *. rewrite Hb by lia. exact Hs.
  - destruct Hs as [Hbyte [Hhead Hrest]]. simpl. split; [exact Hbyte|]. split.
    + rewrite Hb; [exact Hhead|simpl; lia].
    + apply (IH m m'); [|exact Hrest]. intros x Hx. apply Hb.
      change (a <= x < a + Z.of_nat (S (length rest)) + 1).
      rewrite Nat2Z.inj_succ. lia.
Qed.

(** A frame disjoint from an old string preserves its complete checked NUL. *)
Lemma startup_frame_string : forall m m' lo hi p bytes,
  startup_frame m m' lo hi -> c_string m p bytes ->
  (forall a, ptr_addr p <= a < ptr_addr p + Z.of_nat (length bytes) + 1 ->
    a < lo \/ hi <= a) -> c_string m' p bytes.
Proof.
  intros m m' lo hi p bytes Hf [Ha Hs] Hdis. split.
  - eapply startup_frame_access; eauto.
  - eapply string_at_agree; [|exact Hs]. intros a Hrange.
    apply (proj1 (proj2 Hf a ltac:(eapply access_in; [exact Ha|lia]) (Hdis a Hrange))).
Qed.

(** A construction that frames every old object retains old vectors too. *)
Lemma startup_frame_slots : forall texts m m' a,
  startup_frame m m' 0 0 ->
  (forall b, a <= b < a + 8 * (Z.of_nat (length texts) + 1) -> in_object m b) ->
  string_slots m a texts -> string_slots m' a texts.
Proof.
  induction texts as [|text rest IH]; intros m m' a Hf Hin Hslots.
  - eapply startup_frame_slot; [exact Hf| |intros; lia|exact Hslots].
    intros b Hb. apply Hin. simpl. lia.
  - destruct Hslots as (p & Hp & Hs & Hr). exists p. split.
    + eapply startup_frame_slot; [exact Hf| |intros; lia|exact Hp].
      intros b Hb. apply Hin. change (a <= b < a + 8 * (Z.of_nat (S (length rest)) + 1)).
      rewrite Nat2Z.inj_succ. lia.
    + split.
      * eapply startup_frame_string; [exact Hf|exact Hs|]. intros; lia.
      * apply (IH m m'); [exact Hf| |exact Hr]. intros b Hb. apply Hin.
        change (a <= b < a + 8 * (Z.of_nat (S (length rest)) + 1)).
        rewrite Nat2Z.inj_succ. lia.
Qed.

(** The readable pointer array and every pointed-to string survive later copies. *)
Lemma startup_frame_vector : forall m m' table texts,
  startup_frame m m' 0 0 -> string_vector m table texts -> string_vector m' table texts.
Proof.
  intros m m' table texts Hf [Ha Hslots]. split.
  - eapply startup_frame_access; eauto.
  - eapply startup_frame_slots; [exact Hf| |exact Hslots].
    intros b Hb. eapply access_in; [exact Ha|exact Hb].
Qed.

(** Launcher allocation/copying preserves each exposed old pointer
    cell, including its write authority, address bytes and capability. *)
Lemma startup_frame_exposed_cell : forall m m' cell value,
  startup_frame m m' 0 0 -> exposed_pointer_cell m cell value ->
  exposed_pointer_cell m' cell value.
Proof.
  intros m m' cell value Hframe (Hw & Hr & Hwr & Hslot).
  split.
  - destruct Hw as (Hn & b & reg & Hcap & Hreg & Hlive & Ha).
    split; [exact Hn|]. exists b, reg. split; [exact Hcap|]. split.
    + apply (proj1 Hframe). exact Hreg.
    + split; [exact Hlive|]. eapply startup_frame_access; eauto.
  - split; [eapply startup_frame_access; eauto|].
    split; [eapply startup_frame_access; eauto|].
    eapply startup_frame_slot; [exact Hframe| |intros; lia|exact Hslot].
    intros a Ha. eapply access_in; [exact Hr|exact Ha].
Qed.

(** Exposed libc cells and their readable name payloads survive the
    two successful launcher-copy loops. This preserves module data;
    it does not construct or assume native FILE/TLS validity. *)
Theorem startup_frame_libc_globals : forall m m' g out err full short,
  startup_frame m m' 0 0 -> libc_globals_at m g out err full short ->
  libc_globals_at m' g out err full short.
Proof.
  intros m m' g out err full short Hf (Ho & He & Hn & Hs & Hfull & Hshort).
  split; [eapply startup_frame_exposed_cell; eauto|].
  split; [eapply startup_frame_exposed_cell; eauto|].
  split; [eapply startup_frame_exposed_cell; eauto|].
  split; [eapply startup_frame_exposed_cell; eauto|]. split.
  - destruct Hfull as [bytes H]. exists bytes. eapply startup_frame_string; eauto. intros; lia.
  - destruct Hshort as [bytes H]. exists bytes. eapply startup_frame_string; eauto. intros; lia.
Qed.

(** Sixteen-byte rounding provides at least the original positive request. *)
Lemma startup_extent : forall size, 0 < size -> size <= req_extent (heap_req 16 size).
Proof.
  intros size Hsize. unfold heap_req. simpl.
  pose proof (Z.mod_pos_bound (size + 15) 16 ltac:(lia)).
  pose proof (Z.div_mod (size + 15) 16 ltac:(lia)). lia.
Qed.

(** The table's actual object, bounds and alignment justify each slot access. *)
Lemma startup_table_access : forall m table end_ a size rights align,
  object_region table (m_regions m) = Some (mkRegion table end_ Heap Live) ->
  table <= a -> a + size <= end_ -> a mod align = 0 ->
  access_res m a (Obj table) size rights align = Some ok.
Proof.
  intros m table end_ a size rights align Hr Hlo Hhi Ha.
  unfold access_res, cap_access_res. rewrite Hr. simpl.
  assert (((table <=? a) && (a + size <=? end_)) = true) as E.
  { apply andb_true_iff. split; apply Z.leb_le; lia. }
  rewrite E. unfold aligned_res. rewrite Ha. reflexivity.
Qed.

(** Startup copying over the caller's exact machine instance. *)
Module StartupOn (R : Runtime) (M : ExternalMachineSig R).
(** The external-call effects of this machine. *)
Module E := M.E.

(** Copying through supplied write authority is a finite path of local effects. *)
Lemma copy_c_bytes_effects : forall bytes sources roots releases requests s m born a,
  (forall b, a <= b < a + Z.of_nat (length bytes) + 1 -> write_authority roots born m b) ->
  E.effects sources roots releases requests s m born s (copy_c_bytes m a bytes) born.
Proof.
  induction bytes as [|head rest IH]; intros sources roots releases requests s m born a Hw.
  - eapply E.effects_local with (m1 := store_bytes m a 1 0).
    + apply local_store_bytes. intros b Hb. apply Hw. simpl. lia.
    + constructor.
  - eapply E.effects_local with (m1 := store_bytes m a 1 head).
    + apply local_store_bytes. intros b Hb. apply Hw.
      change (a <= b < a + Z.of_nat (S (length rest)) + 1). rewrite Nat2Z.inj_succ. lia.
    + apply IH. intros b Hb. apply Hw.
      change (a <= b < a + Z.of_nat (S (length rest)) + 1). rewrite Nat2Z.inj_succ. lia.
Qed.

(** Success remains conditional on the runtime's real answer, for the
    original strlen + 1 request. No small fixed bound or NULL-success
    case is introduced. The result includes the entire checked NUL. *)
Theorem copy_string : forall bytes sources roots releases requests s m born base s',
  R.ready s m -> Forall (fun b => 0 < b < 256) bytes ->
  Z.of_nat (length bytes) + 1 <= max_allocation_size ->
  requests 16 (Z.of_nat (length bytes) + 1) ->
  R.alloc s (heap_req 16 (Z.of_nat (length bytes) + 1)) = Some (base, s') ->
  let q := heap_req 16 (Z.of_nat (length bytes) + 1) in
  let m' := copy_c_bytes (allocated m q base) base bytes in
  E.effects sources roots releases requests s m born s' m' (base :: born) /\
  R.ready s' m' /\ persists m m' /\ c_string m' (mkPtr base (Obj base)) bytes /\
  writable_span m' (mkSpan (mkPtr base (Obj base)) (Z.of_nat (length bytes) + 1)) /\
  0 <= base < 2 ^ 64 /\
  (forall a, in_object m a -> m_bytes m' a = m_bytes m a /\ m_aux m' a = m_aux m a).
Proof.
  intros bytes sources roots releases requests s m born base s' Hr Hbytes Hmax Hrequest Ha.
  set (size := Z.of_nat (length bytes) + 1). set (q := heap_req 16 size).
  assert (Hsize : 0 < size) by (unfold size; lia).
  assert (Hfit : size <= req_extent q).
  { unfold q, heap_req. simpl.
    pose proof (Z.mod_pos_bound (size + 15) 16 ltac:(lia)).
    pose proof (Z.div_mod (size + 15) 16 ltac:(lia)). lia. }
  destruct (R.fresh_allocation s m q base s' Hr ltac:(simpl; lia) ltac:(lia) Ha) as [Hfresh Hr1].
  assert (Hreg : object_region base (m_regions (allocated m q base)) =
    Some (mkRegion base (base + req_extent q) Heap Live)).
  { simpl. rewrite Z.eqb_refl. reflexivity. }
  assert (He : E.effects sources roots releases requests s m born s'
    (copy_c_bytes (allocated m q base) base bytes) (base :: born)).
  { eapply E.effects_alloc with (align := 16) (size := size).
    - exact Hrequest.
    - split; [lia|exact Hmax].
    - exact Ha.
    - apply copy_c_bytes_effects. intros a Hrange. right.
      exists base, (mkRegion base (base + req_extent q) Heap Live).
      split; [simpl; auto|]. split; [exact Hreg|]. split; [reflexivity|].
      split; [reflexivity|]. change (base <= a < base + req_extent q).
      unfold size in Hfit. lia. }
  destruct (E.effects_preserve _ _ _ _ _ _ _ _ _ _ He Hr) as [Hr' Hpersist].
  assert (Haccess : access_res (copy_c_bytes (allocated m q base) base bytes)
    base (Obj base) size Write 1 = Some ok).
  { unfold access_res. rewrite copy_c_bytes_regions. unfold cap_access_res. rewrite Hreg.
    change (Some (if (base <=? base) && (base + size <=? base + req_extent q)
      then aligned_res base 1 else RTrap OutOfBounds) = Some ok).
    assert (((base <=? base) && (base + size <=? base + req_extent q)) = true) as E.
    { apply andb_true_iff. split; apply Z.leb_le; lia. }
    rewrite E. unfold aligned_res. rewrite Z.mod_1_r. reflexivity. }
  split; [exact He|]. split; [exact Hr'|]. split; [exact Hpersist|]. split.
  - split; [exact Haccess|]. apply copied_string_bytes. exact Hbytes.
  - split.
    + split; [simpl; lia|]. exists base, (mkRegion base (base + req_extent q) Heap Live).
      split; [reflexivity|]. split; [rewrite copy_c_bytes_regions; exact Hreg|].
      split; [reflexivity|exact Haccess].
    + split.
      * destruct Hfresh as (Hbase & _ & Hend & _). lia.
      * intros a Hin. eapply copied_string_old_object; eauto.
Qed.

(** Append two actual effect paths, retaining the same contract authority. *)
Lemma effects_trans : forall sources roots releases requests s m born s1 m1 born1 s2 m2 born2,
  E.effects sources roots releases requests s m born s1 m1 born1 ->
  E.effects sources roots releases requests s1 m1 born1 s2 m2 born2 ->
  E.effects sources roots releases requests s m born s2 m2 born2.
Proof.
  intros sources roots releases requests s m born s1 m1 born1 s2 m2 born2 H.
  induction H; intros Htail; eauto using E.effects_local, E.effects_alloc.
Qed.

(** Preconditions on copied pre-NUL payloads and their original allocation sizes. *)
Definition payloads_allowed (requests : Z -> Z -> Prop) (texts : list (list Z)) : Prop :=
  Forall (fun text => Forall (fun b => 0 < b < 256) text /\
    Z.of_nat (length text) + 1 <= max_allocation_size /\
    requests 16 (Z.of_nat (length text) + 1)) texts.

(** Fill a preallocated pointer table in forward order. None says only
    that this successful construction did not complete, not why native
    startup ended. Each allocation uses the preceding runtime state. *)
Fixpoint copy_slots (texts : list (list Z)) (s : R.state) (m : mem)
    (born : list Z) (cursor : Z) : option (R.state * mem * list Z) :=
  match texts with
  | [] => Some (s, m, born)
  | text :: rest =>
      match R.alloc s (heap_req 16 (Z.of_nat (length text) + 1)) with
      | None => None
      | Some (base, s1) =>
          let m1 := copy_c_bytes (allocated m (heap_req 16 (Z.of_nat (length text) + 1)) base)
            base text in
          copy_slots rest s1 (startup_store m1 cursor (mkPtr base (Obj base)))
            (base :: born) (cursor + 8)
      end
  end.

(** Allocate the pointer table first, even when there are no strings.
    Fresh zero bytes and capabilities supply its sentinel, not a
    synthetic final store. Allocation failures remain unclassified. *)
Definition copy_vector (texts : list (list Z)) (s : R.state) (m : mem) (born : list Z)
    : option (ptr * R.state * mem * list Z) :=
  let size := 8 * (Z.of_nat (length texts) + 1) in
  match R.alloc s (heap_req 16 size) with
  | None => None
  | Some (table, s1) =>
      match copy_slots texts s1 (allocated m (heap_req 16 size) table) (table :: born) table with
      | None => None
      | Some (s2, m2, born2) => Some (mkPtr table (Obj table), s2, m2, born2)
      end
  end.

(** The forward loop retains earlier strings and the sentinel while
    writing only its remaining slots in the already-born table. *)
Theorem copy_slots_correct : forall texts s m born cursor s' m' born' sources roots releases requests table end_,
  copy_slots texts s m born cursor = Some (s', m', born') ->
  R.ready s m -> payloads_allowed requests texts -> In table born ->
  object_region table (m_regions m) = Some (mkRegion table end_ Heap Live) ->
  table <= cursor -> cursor + 8 * (Z.of_nat (length texts) + 1) <= end_ -> cursor mod 8 = 0 ->
  pointer_slot m (cursor + 8 * Z.of_nat (length texts)) (mkPtr 0 CNone) ->
  E.effects sources roots releases requests s m born s' m' born' /\
  R.ready s' m' /\ persists m m' /\
  startup_frame m m' cursor (cursor + 8 * Z.of_nat (length texts)) /\
  string_slots m' cursor texts.
Proof.
  induction texts as [|text rest IH]; intros s m born cursor s' m' born' sources roots releases requests table end_
    Hcopy Hr Hallowed Hborn Htable Hlo Hhi Halign Hsent.
  - simpl in Hcopy. injection Hcopy as <- <- <-.
    split; [constructor|]. split; [exact Hr|]. split; [apply persists_refl|]. split.
    + split; [auto|auto].
    + replace (cursor + 8 * Z.of_nat (length [])) with cursor in Hsent by (simpl; lia). exact Hsent.
  - cbn [copy_slots] in Hcopy.
    destruct (R.alloc s (heap_req 16 (Z.of_nat (length text) + 1))) as [[base s1]|] eqn:Ha;
      [|discriminate Hcopy].
    inversion Hallowed as [|head tail [Hbytes [Hmax Hrequest]] Hrest]; subst head tail.
    set (q := heap_req 16 (Z.of_nat (length text) + 1)).
    set (m1 := copy_c_bytes (allocated m q base) base text).
    set (m2 := startup_store m1 cursor (mkPtr base (Obj base))).
    assert (Hfit : Z.of_nat (length text) + 1 <= req_extent q) by (apply startup_extent; lia).
    destruct (R.fresh_allocation s m q base s1 Hr ltac:(simpl; lia) ltac:(lia) Ha) as [Hfresh Hready1].
    assert (Hframe1 : startup_frame m m1 cursor cursor) by (apply copied_string_frame; auto).
    assert (Htable1 : object_region table (m_regions m1) = Some (mkRegion table end_ Heap Live))
      by (apply (proj1 Hframe1); exact Htable).
    destruct (copy_string text sources roots releases requests s m born base s1 Hr Hbytes Hmax Hrequest Ha)
      as (He1 & Hr1 & Hp1 & Hstring & Hwrite & Hbase & Hold).
    fold q m1 in He1, Hr1, Hp1, Hstring, Hwrite, Hold.
    assert (Hstore : local_effect sources roots releases (base :: born) m1 m2).
    { apply local_store_pointer.
      - intros a Hrange. right. exists table, (mkRegion table end_ Heap Live).
        split; [simpl; auto|]. split; [exact Htable1|].
        change (cursor + 8 * (Z.of_nat (S (length rest)) + 1) <= end_) in Hhi.
        rewrite Nat2Z.inj_succ in Hhi. repeat split; simpl; try reflexivity; lia.
      - right. right. right. exists base. simpl. auto. }
    assert (Hr2 : R.ready s1 m2) by (eapply R.ready_kept; [exact Hr1|apply local_effect_kept in Hstore; exact Hstore]).
    assert (Hframe2 : startup_frame m m2 cursor (cursor + 8)).
    { eapply startup_frame_join with (mid := cursor); [lia|exact Hframe1|apply startup_store_frame]. }
    assert (Htable2 : object_region table (m_regions m2) = Some (mkRegion table end_ Heap Live))
      by (apply (proj1 Hframe2); exact Htable).
    assert (Hsent2 : pointer_slot m2 (cursor + 8 + 8 * Z.of_nat (length rest)) (mkPtr 0 CNone)).
    { replace (cursor + 8 + 8 * Z.of_nat (length rest)) with
        (cursor + 8 * Z.of_nat (S (length rest))) by (rewrite Nat2Z.inj_succ; lia).
      eapply startup_frame_slot; [exact Hframe2| | |exact Hsent].
      - intros a Hrange. exists table, (mkRegion table end_ Heap Live). split; [exact Htable|].
        simpl. change (cursor + 8 * (Z.of_nat (S (length rest)) + 1) <= end_) in Hhi. lia.
      - intros a Hrange. rewrite Nat2Z.inj_succ in Hrange. lia. }
    destruct (IH s1 m2 (base :: born) (cursor + 8) s' m' born' sources roots releases requests table end_
      Hcopy Hr2 Hrest ltac:(simpl; auto) Htable2 ltac:(lia)
      ltac:(change (cursor + 8 * (Z.of_nat (S (length rest)) + 1) <= end_) in Hhi;
        rewrite Nat2Z.inj_succ in Hhi; lia)
      ltac:(rewrite Z.add_mod by lia; rewrite Halign; reflexivity) Hsent2)
      as (He2 & Hr' & Hp2 & Hframe3 & Hslots).
    split.
    + eapply effects_trans; [exact He1|]. eapply E.effects_local; [exact Hstore|exact He2].
    + split; [exact Hr'|]. split.
      * eapply persists_trans; [exact Hp1|]. eapply persists_trans;
          [apply kept_ids_persists; [apply local_effect_kept in Hstore; exact Hstore|exact (proj1 Hstore)]|exact Hp2].
      * split.
        -- replace (cursor + 8 * Z.of_nat (length (text :: rest))) with
             (cursor + 8 + 8 * Z.of_nat (length rest)) by (simpl length; rewrite Nat2Z.inj_succ; lia).
           eapply startup_frame_join with (mid := cursor + 8); [lia|exact Hframe2|exact Hframe3].
        -- exists (mkPtr base (Obj base)). split.
           ++ eapply startup_frame_slot; [exact Hframe3| |intros; lia|].
              ** intros a Hrange. exists table, (mkRegion table end_ Heap Live). split; [exact Htable2|].
                 simpl. change (cursor + 8 * (Z.of_nat (S (length rest)) + 1) <= end_) in Hhi.
                 rewrite Nat2Z.inj_succ in Hhi. lia.
              ** apply pointer_slot_written. exact Hbase.
           ++ split; [|exact Hslots].
              assert (Hdis : forall a, base <= a < base + Z.of_nat (length text) + 1 ->
                a < cursor \/ end_ <= a).
              { intros a Hrange. destruct Hfresh as (_ & _ & _ & _ & Hseparate & _).
                specialize (Hseparate _ _ Htable).
                change (~ (base < end_ /\ table < base + req_extent q)) in Hseparate. lia. }
              assert (Hstring2 : c_string m2 (mkPtr base (Obj base)) text).
              { eapply startup_frame_string; [apply startup_store_frame|exact Hstring|].
                intros a Hrange. simpl in Hrange. specialize (Hdis a Hrange). lia. }
              eapply startup_frame_string; [exact Hframe3|exact Hstring2|].
              intros a Hrange. simpl in Hrange. specialize (Hdis a Hrange).
              change (cursor + 8 * (Z.of_nat (S (length rest)) + 1) <= end_) in Hhi.
              rewrite Nat2Z.inj_succ in Hhi. lia.
Qed.

(** A successful table-first construction gives a checked writable
    vector and frames every object that existed before its table. *)
Theorem copy_vector_correct : forall texts s m born table s' m' born' sources roots releases requests,
  copy_vector texts s m born = Some (table, s', m', born') ->
  R.ready s m -> payloads_allowed requests texts ->
  8 * (Z.of_nat (length texts) + 1) <= max_allocation_size ->
  requests 16 (8 * (Z.of_nat (length texts) + 1)) ->
  E.effects sources roots releases requests s m born s' m' born' /\
  R.ready s' m' /\ persists m m' /\ startup_frame m m' 0 0 /\
  string_vector m' table texts /\
  writable_span m' (mkSpan table (8 * (Z.of_nat (length texts) + 1))).
Proof.
  intros texts s m born table s' m' born' sources roots releases requests Hcopy Hr Hallowed Hmax Hrequest.
  unfold copy_vector in Hcopy.
  destruct (R.alloc s (heap_req 16 (8 * (Z.of_nat (length texts) + 1)))) as [[base s1]|] eqn:Ha;
    [|discriminate Hcopy].
  set (size := 8 * (Z.of_nat (length texts) + 1)) in *.
  set (q := heap_req 16 size) in *.
  destruct (copy_slots texts s1 (allocated m q base) (base :: born) base)
    as [[[s2 m2] born2]|] eqn:Hslots; [|discriminate Hcopy].
  injection Hcopy as <- <- <- <-.
  assert (Hsize : 0 < size) by (unfold size; lia).
  assert (Hfit : size <= req_extent q) by (apply startup_extent; exact Hsize).
  destruct (R.fresh_allocation s m q base s1 Hr ltac:(simpl; lia) ltac:(lia) Ha) as [Hfresh Hr1].
  assert (Htable : object_region base (m_regions (allocated m q base)) =
    Some (mkRegion base (base + req_extent q) Heap Live)) by (simpl; rewrite Z.eqb_refl; reflexivity).
  assert (Halign : base mod 8 = 0).
  { destruct Hfresh as (_ & Halign & _). change (base mod 16 = 0) in Halign.
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in Halign; [|lia].
    destruct Halign as [k Hk]. exists (2 * k). lia. }
  assert (Hsent : pointer_slot (allocated m q base)
    (base + 8 * Z.of_nat (length texts)) (mkPtr 0 CNone)).
  { destruct Hfresh as (_ & _ & _ & _ & _ & Hzero).
    unfold pointer_slot. split; [simpl; lia|]. split.
    - transitivity (load_bytes (mkMem (fun _ => 0) [] (fun _ => CNone))
        (base + 8 * Z.of_nat (length texts)) 8); [|reflexivity].
      apply load_bytes_agree; [lia|]. intros i Hi. simpl.
      apply (proj1 (Hzero (base + 8 * Z.of_nat (length texts) + i) ltac:(unfold size in Hfit; lia))).
    - simpl. apply (proj2 (Hzero (base + 8 * Z.of_nat (length texts)) ltac:(unfold size in Hfit; lia))). }
  destruct (copy_slots_correct texts s1 (allocated m q base) (base :: born) base s2 m2 born2
    sources roots releases requests base (base + req_extent q) Hslots Hr1 Hallowed
    ltac:(simpl; auto) Htable ltac:(lia) ltac:(unfold size in Hfit; lia) Halign Hsent)
    as (He & Hr2 & Hp & Hframe & Hvector).
  assert (Heall : E.effects sources roots releases requests s m born s2 m2 born2).
  { eapply E.effects_alloc; [exact Hrequest|split; lia|exact Ha|exact He]. }
  destruct (E.effects_preserve _ _ _ _ _ _ _ _ _ _ Heall Hr) as [Hr' Hpall].
  split; [exact Heall|]. split; [exact Hr'|]. split; [exact Hpall|]. split.
  - split.
    + intros b reg Hold. apply (proj1 Hframe). eapply allocated_old_region; [|exact Hold].
      exact (proj1 (proj2 (proj2 (proj2 Hfresh)))).
    + intros a Hin _. apply (proj2 Hframe a).
      * destruct Hin as (b & reg & E & Hrange). exists b, reg. split; [|exact Hrange].
        eapply allocated_old_region; [|exact E]. exact (proj1 (proj2 (proj2 (proj2 Hfresh)))).
      * destruct Hin as (b & reg & E & Hrange).
        destruct Hfresh as (_ & _ & _ & _ & Hdis & _). specialize (Hdis _ _ E).
        unfold size in Hfit. lia.
  - assert (Htable' : object_region base (m_regions m2) =
      Some (mkRegion base (base + req_extent q) Heap Live)) by (apply (proj1 Hframe); exact Htable).
    split.
    + split; [|exact Hvector].
      apply (startup_table_access m2 base (base + req_extent q) base size Read 8 Htable' ltac:(lia) ltac:(lia) Halign).
    + split; [simpl; unfold size; lia|]. exists base, (mkRegion base (base + req_extent q) Heap Live).
      split; [reflexivity|]. split; [exact Htable'|]. split; [reflexivity|].
      apply (startup_table_access m2 base (base + req_extent q) base size Write 1 Htable' ltac:(lia) ltac:(lia) (Z.mod_1_r base)).
Qed.

(** The environment's count, increment and checked multiplication fit
    size_t whenever its original table request is legal. Unlike argv,
    this count is not restricted to signed int. *)
Lemma environment_copy_bounds : forall n,
  8 * (Z.of_nat n + 1) <= max_allocation_size ->
  0 <= Z.of_nat n < 2 ^ 64 - 1 /\ 0 < 8 * (Z.of_nat n + 1) < 2 ^ 64.
Proof. intros n H. unfold max_allocation_size in H. lia. Qed.

(** Compose the argv and environment memory constructions. This is not
    the complete native launcher trace: obtaining/tracking main between
    the two loops, auxv and libc initialization still need coverage. *)
Theorem copied_startup : forall args environment s m born argv s1 m1 born1 envp s2 m2 born2
    sources roots releases requests,
  copy_vector args s m born = Some (argv, s1, m1, born1) ->
  copy_vector environment s1 m1 born1 = Some (envp, s2, m2, born2) ->
  R.ready s m -> 1 <= Z.of_nat (length args) < 2 ^ 31 - 1 ->
  payloads_allowed requests args -> payloads_allowed requests environment ->
  8 * (Z.of_nat (length environment) + 1) <= max_allocation_size ->
  requests 16 (8 * (Z.of_nat (length args) + 1)) ->
  requests 16 (8 * (Z.of_nat (length environment) + 1)) ->
  E.effects sources roots releases requests s m born s2 m2 born2 /\
  R.ready s2 m2 /\ persists m m2 /\ startup_frame m m2 0 0 /\
  startup_at m2 (Z.of_nat (length args)) argv envp args environment.
Proof.
  intros args environment s m born argv s1 m1 born1 envp s2 m2 born2 sources roots releases requests
    Ha He Hr Hargc Hargs Henv Hmax Hrequesta Hrequeste.
  pose proof (proj2 (argv_copy_bounds _ Hargc)) as Hargmax.
  unfold argv_copy_size in Hargmax.
  destruct (copy_vector_correct args s m born argv s1 m1 born1 sources roots releases requests
    Ha Hr Hargs ltac:(lia) Hrequesta) as (Hea & Hr1 & Hp1 & Hf1 & Hva & Hwa).
  destruct (copy_vector_correct environment s1 m1 born1 envp s2 m2 born2 sources roots releases requests
    He Hr1 Henv Hmax Hrequeste) as (Hee & Hr2 & Hp2 & Hf2 & Hve & Hwe).
  split; [eapply effects_trans; eauto|]. split; [exact Hr2|]. split.
  - eapply persists_trans; eauto.
  - split.
    + eapply startup_frame_join with (mid := 0); [lia|exact Hf1|exact Hf2].
    + split; [lia|]. split; [reflexivity|]. split; [|exact Hve].
      eapply startup_frame_vector; eauto.
Qed.

(** A ready entry frame for a linked two-parameter main after the
    successful launcher copies. Existing global cells and name strings
    survive; the linked symbol map and exact runtime state are retained.
    FILE/TLS validity and the program's logical precondition are still
    separate trusted entry obligations, not consequences of copying. *)
Theorem copied_startup_main : forall args environment s m born argv s1 m1 born1 envp s2 m2 born2
    sources roots releases requests ge g out err full short f b blocks an vn fuel,
  copy_vector args s m born = Some (argv, s1, m1, born1) ->
  copy_vector environment s1 m1 born1 = Some (envp, s2, m2, born2) ->
  R.ready s m -> 1 <= Z.of_nat (length args) < 2 ^ 31 - 1 ->
  payloads_allowed requests args -> payloads_allowed requests environment ->
  8 * (Z.of_nat (length environment) + 1) <= max_allocation_size ->
  requests 16 (8 * (Z.of_nat (length args) + 1)) ->
  requests 16 (8 * (Z.of_nat (length environment) + 1)) ->
  libc_globals_bound ge g -> libc_globals_at m g out err full short ->
  find_fn ge (TAtom "main") = Some (Defined f) ->
  fn_params f = [(W, an); (P, vn)] -> fn_blocks f = b :: blocks -> variadic_func f = false ->
  exists fr,
    call_frame f (main_arguments (Z.of_nat (length args)) argv envp) = Some fr /\
    find_fn ge (TAtom "main") = Some (Defined f) /\
    E.effects sources roots releases requests s m born s2 m2 born2 /\
    R.ready s2 (c_mem (mkConfig fr [] m2 fuel)) /\
    persists m m2 /\ startup_frame m m2 0 0 /\
    startup_at m2 (Z.of_nat (length args)) argv envp args environment /\
    libc_globals_bound ge g /\ libc_globals_at m2 g out err full short.
Proof.
  intros args environment s m born argv s1 m1 born1 envp s2 m2 born2
    sources roots releases requests ge g out err full short f b blocks an vn fuel
    Ha He Hr Hargc Hargs Henv Hmax Hra Hre Hbound Hglobals Hfind Hp Hb Hv.
  destruct (copied_startup args environment s m born argv s1 m1 born1 envp s2 m2 born2
    sources roots releases requests Ha He Hr Hargc Hargs Henv Hmax Hra Hre)
    as (Heffects & Hr2 & Hpersists & Hframe & Hstartup).
  eexists. split; [eapply main_argv_frame; eauto|].
  split; [exact Hfind|]. split; [exact Heffects|]. split; [exact Hr2|].
  split; [exact Hpersists|]. split; [exact Hframe|]. split; [exact Hstartup|].
  split; [exact Hbound|]. eapply startup_frame_libc_globals; eauto.
Qed.

End StartupOn.

(** Standalone wrapper for existing entry clients. *)
Module Startup (R : Runtime).
Module M := ExternalMachine R.
Include StartupOn R M.
End Startup.
