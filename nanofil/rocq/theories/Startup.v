(** The Fil-C launcher's entry contract, before libc calls main
    ([milestone 3a](../../docs/formal.md#campaign-4-milestone-3a-launcher-entry-memory)).

    The pinned filc_start_program.c copies argv and environ into fresh
    [[capability]]-bearing objects. Pointer arrays include a null sentinel;
    strings include an in-object first NUL. Lengths and contents are not
    restricted to the native probes. The launcher asserts argc >= 1.

    These are concrete predicates on model memory, not new
    [[runtime|runtime axioms]] or a proof of the native launcher.
    Establishing them from successful startup allocations, including
    libc/TLS and finalizer roots, remains a separate
    [[obligation]]. Resource refusal before entry
    must not be confused with a malformed entry or deleted execution. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics ExternalCalls.
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
