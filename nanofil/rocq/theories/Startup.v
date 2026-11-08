(** The Fil-C launcher's entry contract, before libc calls main
    ([milestone 3a](../../docs/formal.md#campaign-4-milestone-3a-launcher-entry-memory)).

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
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Identity ExternalCalls.
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

(** The three words the launcher passes to main: argc, argv, envp. *)
Definition main_arguments (argc : Z) (argv envp : ptr) : list word :=
  [WInt argc; WPtr argv; WPtr envp].

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

(** Startup copying over an arbitrary [[runtime]]. *)
Module Startup (R : Runtime).
(** The external-call effects of this runtime. *)
Module E := ExternalCalls R.

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

End Startup.

(** ## Entry regressions

    Two arguments of unequal lengths, including the empty string, and
    an empty environment distinguish argc, slot spacing and sentinels.
    The fixture reuses the independent hello string, not its fake ABI. *)

(** argv: a three-slot array at 4096. *)
Definition entry_argv : ptr := mkPtr 4096 (Obj 4096).
(** envp: a one-slot array at 4200, the sentinel alone. *)
Definition entry_envp : ptr := mkPtr 4200 (Obj 4200).
(** [hello_mem] plus the two arrays: argv's slots point at hello (with
    its read-only capability) and at an empty string in the object at
    3072, then null; envp's only slot is null. *)
Definition entry_mem : mem :=
  mkMem (fun a =>
    if (4096 <=? a) && (a <? 4104) then byte_of 1024 (a - 4096) else
    if (4104 <=? a) && (a <? 4112) then byte_of 3072 (a - 4104) else
    m_bytes hello_mem a)
    (mkRegion 4096 4120 Heap Live :: mkRegion 4200 4208 Heap Live :: m_regions hello_mem)
    (fun a => if a =? 4096 then Ro 1024 else if a =? 4104 then Obj 3072 else CNone).

(** [entry_mem] is an entry image with argc 2, arguments hello and the
    empty string, and no environment. *)
Example entry_two_arguments : startup_at entry_mem 2 entry_argv entry_envp [hello_bytes; []] [].
Proof.
  split; [lia|]. split; [reflexivity|]. split.
  - split; [reflexivity|]. exists hello_ptr. split; [vm_compute; repeat split; congruence|].
    split; [vm_compute; repeat split; congruence|]. exists (mkPtr 3072 (Obj 3072)).
    vm_compute. repeat split; congruence.
  - vm_compute. repeat split; congruence.
Qed.

(** argc must count the arguments. *)
Example entry_bad_count : ~ startup_at entry_mem 1 entry_argv entry_envp [hello_bytes; []] [].
Proof. intros (_ & H & _). discriminate H. Qed.

(** A nonzero address in argv's sentinel slot is not a [string_vector]. *)
Example entry_nonnull_sentinel :
  ~ string_vector (store_bytes entry_mem 4112 8 1024) entry_argv [hello_bytes; []].
Proof.
  intros [_ H]. pose proof (string_slots_sentinel _ _ _ H) as (_ & Hbits & _).
  discriminate Hbits.
Qed.

(** Nor is a slot whose [[aux]] lost its capability, though its address
    bytes are right. *)
Example entry_missing_capability :
  ~ string_vector (store_aux entry_mem 4096 CNone) entry_argv [hello_bytes; []].
Proof.
  intros [_ (p & (_ & Hbits & Hcap) & [Hread _] & _)].
  change (1024 = ptr_addr p) in Hbits. change (CNone = ptr_cap p) in Hcap.
  rewrite <- Hbits, <- Hcap in Hread. discriminate Hread.
Qed.

(** Nor an argv object too small to hold the sentinel slot. *)
Example entry_missing_sentinel_bounds :
  ~ string_vector (mkMem (m_bytes entry_mem)
    (mkRegion 4096 4112 Heap Live :: m_regions hello_mem) (m_aux entry_mem))
    entry_argv [hello_bytes; []].
Proof. intros [H _]. discriminate H. Qed.

(** Nor a slot whose address bytes point one byte into the string. *)
Example entry_wrong_address :
  ~ string_vector (store_bytes entry_mem 4096 8 1025) entry_argv [hello_bytes; []].
Proof.
  intros [_ (p & (_ & Hbits & _) & [_ Hstring] & _)].
  change (1025 = ptr_addr p) in Hbits. rewrite <- Hbits in Hstring.
  destruct Hstring as (_ & Hbyte & _). discriminate Hbyte.
Qed.

(** Nor a string whose NUL was overwritten. *)
Example entry_missing_nul :
  ~ string_vector (store_bytes entry_mem 1029 1 65) entry_argv [hello_bytes; []].
Proof.
  intros [_ (p & (_ & Hbits & _) & [_ Hstring] & _)].
  change (1024 = ptr_addr p) in Hbits. rewrite <- Hbits in Hstring.
  destruct Hstring as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnul).
  discriminate Hnul.
Qed.

(** The largest argc whose copy size is computable, INT_MAX - 1, gives
    17179869176 bytes; at INT_MAX, argc + 1 overflows int. *)
Example argv_copy_boundary :
  argv_copy_size (2 ^ 31 - 2) = 17179869176 /\
  ~ (0 < (2 ^ 31 - 1) + 1 < 2 ^ 31).
Proof. split; [reflexivity|lia]. Qed.

(** Status 513 reports 1, and -1 reports 255. *)
Example exit_status_low_byte : process_status 513 = 1 /\ process_status (-1) = 255.
Proof. split; reflexivity. Qed.

(** Construction, not a preassumed final entry image. All old argument
    table bytes/capabilities stay; high bytes are not interpreted as
    text, and the NUL must fit the new object's checked bounds. *)
Definition copied_entry_string : mem :=
  copy_c_bytes (allocated entry_mem (heap_req 16 4) 16384) 16384 [1; 128; 255].

(** An empty string needs one byte for its NUL, within a rounded 16-byte object. *)
Example copy_empty_string :
  c_string (copy_c_bytes (allocated entry_mem (heap_req 16 1) 16384) 16384 [])
    (mkPtr 16384 (Obj 16384)) [] /\ req_extent (heap_req 16 1) = 16.
Proof. repeat split; reflexivity. Qed.

(** High bytes survive exactly, along with the old pointer slot and environment. *)
Example copy_high_bytes_and_old_slot :
  c_string copied_entry_string (mkPtr 16384 (Obj 16384)) [1; 128; 255] /\
  m_bytes copied_entry_string 16387 = 0 /\
  pointer_slot copied_entry_string 4096 hello_ptr /\
  string_vector copied_entry_string entry_envp [].
Proof. vm_compute. repeat constructor; discriminate. Qed.

(** Sixteen payload bytes need a seventeenth NUL byte and a 32-byte extent. *)
Example copy_crosses_rounding_boundary :
  c_string (copy_c_bytes (allocated entry_mem (heap_req 16 17) 16384) 16384 (repeat 255 16))
    (mkPtr 16384 (Obj 16384)) (repeat 255 16) /\ req_extent (heap_req 16 17) = 32.
Proof. vm_compute. repeat constructor; discriminate. Qed.

(** Correct payload bytes are insufficient when the NUL lies outside the object. *)
Example copied_nul_needs_bounds :
  ~ c_string (mkMem (m_bytes copied_entry_string)
    [mkRegion 16384 16387 Heap Live] (m_aux copied_entry_string))
    (mkPtr 16384 (Obj 16384)) [1; 128; 255].
Proof. intros [H _]. discriminate H. Qed.

(** A pre-NUL payload contains neither a zero nor a value outside the byte range. *)
Example pre_nul_representation :
  ~ Forall (fun b => 0 < b < 256) [65; 0; 66] /\
  ~ Forall (fun b => 0 < b < 256) [65; 256].
Proof.
  split; intros H; inversion H as [|head rest Hb Hrest]; subst;
    inversion Hrest as [|head tail Hbad Htail]; subst; lia.
Qed.
