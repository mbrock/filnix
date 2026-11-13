(** Before a C program's `c: main` function begins executing under Fil-C,
    the runtime launcher in `filc_start_program.c` copies the operating
    system's raw `c: argv` and `c: environ` strings into fresh,
    [[capability]]-backed heap allocations. Each string object holds its
    non-zero character bytes followed by a terminating NUL byte inside the
    object's bounds, and each pointer array ends with a null sentinel slot
    before the launcher calls `c: main(argc, argv, environ)`.

    This module specifies that initial memory layout and proves that the
    launcher's allocation and byte-copy loops construct it without disturbing
    existing module data. The predicate [pointer_slot] describes an
    eight-byte memory cell whose primary bytes and shadow [[aux]] slot decode
    to a pointer and its capability, while [startup_at] packages the
    complete entry image for `c: argc`, `c: argv`, and `c: envp`.

    Every definition in this module is a concrete predicate or theorem over
    the memory model rather than a new [[runtime]] axiom. Proving that
    process startup also initializes userland libc streams and thread-local
    storage remains a separate [[obligation]], and out-of-memory failures
    during startup are kept distinct from malformed entry states. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Identity ExternalCalls ExternalMachine.
Import ListNotations.
Open Scope Z_scope.

(** ## Entry memory layout and pointer arrays

    To pass `c: argv` and `c: envp` to `c: main`, the launcher stores an
    array of pointers in memory, where each element points to a
    NUL-terminated string object. This section defines the layout of pointer
    slots, string vectors, and global pointer cells at program entry, and
    shows how `c: main` reads individual argument and environment strings
    from [startup_at].

    In Fil-C memory, an eight-byte pointer cell stores its integer address in
    primary bytes and its pointer [[capability]] in the shadow [[aux]] entry
    at the base address. The predicate [pointer_slot] states that the cell at
    address a decodes to the pointer p with a 64-bit unsigned address and a
    matching shadow capability. *)
Definition pointer_slot (m : mem) (a : Z) (p : ptr) : Prop :=
  0 <= ptr_addr p < 2 ^ 64 /\
  load_bytes m a 8 = ptr_addr p /\ m_aux m a = ptr_cap p.

(** Storing a pointer's 64-bit address into eight primary bytes at address a
    and recording its capability in the shadow [[aux]] slot at a creates a
    valid [pointer_slot] at that address. *)
Lemma pointer_slot_written : forall m a p,
  0 <= ptr_addr p < 2 ^ 64 ->
  pointer_slot (store_aux (store_bytes m a 8 (ptr_addr p)) a (ptr_cap p)) a p.
Proof.
  intros m a p Hp. split; [exact Hp|]. split.
  - change (load_bytes (store_bytes m a 8 (ptr_addr p)) a 8 = ptr_addr p).
    rewrite stored_bytes_value by lia. apply Z.mod_small. exact Hp.
  - simpl. rewrite Z.eqb_refl. reflexivity.
Qed.

(** Writing raw bytes at address a leaves any non-overlapping [pointer_slot]
    at address b intact, because neither the eight primary bytes nor the
    shadow capability at b changes. *)
Lemma pointer_slot_bytes_disjoint : forall m a size x b p,
  0 <= size -> b + 8 <= a \/ a + size <= b -> pointer_slot m b p ->
  pointer_slot (store_bytes m a size x) b p.
Proof.
  intros m a size x b p Hsize Hdis [Hp [Hbytes Haux]]. split; [exact Hp|]. split; [|exact Haux].
  rewrite <- Hbytes. apply load_bytes_agree; [lia|]. intros i Hi. simpl.
  destruct ((a <=? b + i) && (b + i <? a + size)) eqn:E; [|reflexivity].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

(** Storing a pointer and its shadow capability at address a preserves any
    existing [pointer_slot] at an address b that is at least eight bytes away. *)
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

(** Starting at address a, [string_slots] states that consecutive eight-byte
    [pointer_slot] cells point to valid [c_string] objects for each byte list
    in texts, followed immediately by a null sentinel slot holding address
    zero and [CNone]. *)
Fixpoint string_slots (m : mem) (a : Z) (texts : list (list Z)) : Prop :=
  match texts with
  | [] => pointer_slot m a (mkPtr 0 CNone)
  | text :: rest => exists p,
      pointer_slot m a p /\ c_string m p text /\ string_slots m (a + 8) rest
  end.

(** A pointer table forms a [string_vector] for a list of strings when the
    table pointer's [[capability]] authorizes reading the entire
    8-byte-aligned pointer array—including its trailing null sentinel—and the
    array's cells satisfy [string_slots]. *)
Definition string_vector (m : mem) (table : ptr) (texts : list (list Z)) : Prop :=
  access_res m (ptr_addr table) (ptr_cap table)
    (8 * (Z.of_nat (length texts) + 1)) Read 8 = Some ok /\
  string_slots m (ptr_addr table) texts.

(** A memory state m satisfies [startup_at] when argc is a positive 32-bit
    signed integer matching the length of args, argv is a readable
    [string_vector] for args, and envp is a readable [string_vector] for the
    environment strings. *)
Definition startup_at (m : mem) (argc : Z) (argv envp : ptr)
    (args environment : list (list Z)) : Prop :=
  1 <= argc < 2 ^ 31 /\ argc = Z.of_nat (length args) /\
  string_vector m argv args /\ string_vector m envp environment.

(** Global pointer variables exported by libc, such as `c: stdout` or
    `c: program_invocation_name`, reside in global-data cells that the
    program can read and overwrite. A cell satisfies [exposed_pointer_cell]
    when its pointer carries live 8-byte read and write authority over the
    cell itself and its contents decode to value via [pointer_slot]. *)
Definition exposed_pointer_cell (m : mem) (cell value : ptr) : Prop :=
  writable_span m (mkSpan cell 8) /\
  access_res m (ptr_addr cell) (ptr_cap cell) 8 Read 8 = Some ok /\
  access_res m (ptr_addr cell) (ptr_cap cell) 8 Write 8 = Some ok /\
  pointer_slot m (ptr_addr cell) value.

(** The record [libc_global_cells] collects the global variable pointers for
    `c: stdout`, `c: stderr`, `c: program_invocation_name`, and
    `c: program_invocation_short_name` in a linked module. *)
Record libc_global_cells : Type := mkLibcGlobalCells {
  stdout_cell : ptr;
  stderr_cell : ptr;
  invocation_name_cell : ptr;
  short_name_cell : ptr
}.

(** A global environment ge satisfies [libc_globals_bound] when looking up
    each of the four exported libc variable names resolves to the
    corresponding cell pointer in g. *)
Definition libc_globals_bound (ge : genv) (g : libc_global_cells) : Prop :=
  lookup (TAtom "stdout") (ge_globals ge) = Some (stdout_cell g) /\
  lookup (TAtom "stderr") (ge_globals ge) = Some (stderr_cell g) /\
  lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (invocation_name_cell g) /\
  lookup (TAtom "program_invocation_short_name") (ge_globals ge) = Some (short_name_cell g).

(** Before `c: main` runs, the four global variable cells in g hold the
    stream pointers out and err together with the program-name pointers full
    and short. The predicate [libc_globals_at] states that all four cells are
    writable [exposed_pointer_cell] slots and that both program-name pointers
    address readable NUL-terminated C strings. *)
Definition libc_globals_at (m : mem) (g : libc_global_cells)
    (out err full short : ptr) : Prop :=
  exposed_pointer_cell m (stdout_cell g) out /\
  exposed_pointer_cell m (stderr_cell g) err /\
  exposed_pointer_cell m (invocation_name_cell g) full /\
  exposed_pointer_cell m (short_name_cell g) short /\
  (exists bytes, c_string m full bytes) /\ (exists bytes, c_string m short bytes).

(** Loading an eight-byte pointer from an [exposed_pointer_cell] through the
    ordinary non-atomic [pointer_load_effects] sequence recovers the exact
    stored pointer address and capability. *)
Lemma exposed_pointer_load : forall m cell value,
  exposed_pointer_cell m cell value ->
  pointer_load_effects m (ptr_addr cell) [AuxRead; LowerResolve; AddressRead] = Some value.
Proof.
  intros m cell [a c] (_ & _ & _ & _ & Hbytes & Haux).
  unfold pointer_load_effects, pointer_load_effect, aux_at. simpl.
  rewrite Hbytes, Haux. reflexivity.
Qed.

(** When the Fil-C launcher invokes `c: main`, [main_arguments] packages the
    integer word argc together with the pointer words argv and envp as the
    call's three argument words. *)
Definition main_arguments (argc : Z) (argv envp : ptr) : list word :=
  [WInt argc; WPtr argv; WPtr envp].

(** When `c: main` is declared as a non-variadic two-parameter function
    taking `c: argc` and `c: argv`, [call_frame] binds those two parameters
    to the first two words of [main_arguments] and ignores the extra envp
    argument, which [copied_startup_main] uses to build the initial call
    frame. *)
Lemma main_argv_frame : forall f b blocks argc_name argv_name argc argv envp,
  fn_params f = [(W, argc_name); (P, argv_name)] -> fn_blocks f = b :: blocks ->
  variadic_func f = false ->
  call_frame f (main_arguments argc argv envp) = Some
    (mkFrame f (put argv_name (WPtr argv) (put argc_name (WInt argc) []))
      (map (fun xs => (fst xs, None)) (local_objects f)) None (Enter (b_label b) None)).
Proof. intros f b blocks an vn argc argv envp Hp Hb Hv. unfold call_frame.
  rewrite Hp, Hb, Hv. reflexivity.
Qed.

(** To allocate the `c: argv` pointer array, the launcher computes
    [argv_copy_size] as eight bytes for each of the argc argument pointers
    plus eight bytes for the trailing null sentinel. Because the C launcher
    evaluates `c: argc + 1` in signed 32-bit `c: int` arithmetic before
    multiplying by eight, `c: argc` must stay strictly below `c: INT_MAX` to
    avoid signed overflow. *)
Definition argv_copy_size (argc : Z) : Z := 8 * (argc + 1).

(** Whenever argc is at least 1 and strictly below `2 ^ 31 - 1`, adding 1 for
    the null sentinel does not overflow signed 32-bit `c: int` and
    [argv_copy_size] lies within [max_allocation_size]. *)
Lemma argv_copy_bounds : forall argc,
  1 <= argc < 2 ^ 31 - 1 ->
  0 < argc + 1 < 2 ^ 31 /\ 0 < argv_copy_size argc <= max_allocation_size.
Proof. intros argc H. unfold argv_copy_size, max_allocation_size. lia. Qed.

(** By induction on the string list, [string_slots_nth] shows that the i-th
    eight-byte slot of [string_slots] starting at address a holds a pointer
    to a valid [c_string] containing the i-th byte list. *)
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

(** Immediately after the slots for texts, the eight-byte cell at offset
    `8 * length texts` of [string_slots] holds the null sentinel pointer. *)
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

(** In any memory state satisfying [startup_at], [startup_argument] uses
    [string_slots_nth] to show that the i-th slot of argv holds a pointer to
    a readable [c_string] with the i-th command-line argument. *)
Theorem startup_argument : forall m argc argv envp args environment i text,
  startup_at m argc argv envp args environment -> nth_error args i = Some text ->
  exists p, pointer_slot m (ptr_addr argv + 8 * Z.of_nat i) p /\ c_string m p text.
Proof.
  intros m argc argv envp args environment i text (_ & _ & [_ H] & _) Hi.
  exact (string_slots_nth _ _ _ _ _ H Hi).
Qed.

(** Similarly, [startup_environment] shows that the i-th slot of envp in a
    [startup_at] memory state holds a pointer to a readable [c_string] with
    the i-th environment variable string. *)
Theorem startup_environment : forall m argc argv envp args environment i text,
  startup_at m argc argv envp args environment -> nth_error environment i = Some text ->
  exists p, pointer_slot m (ptr_addr envp + 8 * Z.of_nat i) p /\ c_string m p text.
Proof.
  intros m argc argv envp args environment i text (_ & _ & _ & [_ H]) Hi.
  exact (string_slots_nth _ _ _ _ _ H Hi).
Qed.

(** In any memory state satisfying [startup_at], [startup_sentinels] uses
    [string_slots_sentinel] to show that slot argc of argv and the slot after
    the last environment entry of envp both hold null pointers. *)
Theorem startup_sentinels : forall m argc argv envp args environment,
  startup_at m argc argv envp args environment ->
  pointer_slot m (ptr_addr argv + 8 * argc) (mkPtr 0 CNone) /\
  pointer_slot m (ptr_addr envp + 8 * Z.of_nat (length environment)) (mkPtr 0 CNone).
Proof.
  intros m argc argv envp args environment (_ & -> & [_ Ha] & [_ He]).
  split; apply string_slots_sentinel; assumption.
Qed.

(** When `c: main` is declared with no parameters as `c: int main(void)`,
    [call_frame] ignores all three words of [main_arguments] and enters the
    first [[block]] with an empty parameter environment. *)
Lemma main_void_entry : forall f b blocks argc argv envp,
  fn_params f = [] -> fn_blocks f = b :: blocks -> variadic_func f = false ->
  call_frame f (main_arguments argc argv envp) =
    Some (mkFrame f [] (map (fun xs => (fst xs, None)) (local_objects f)) None
      (Enter (b_label b) None)).
Proof.
  intros f b blocks argc argv envp Hp Hb Hv. unfold call_frame.
  rewrite Hp, Hb, Hv. reflexivity.
Qed.

(** When a process terminates by returning from `c: main` or calling
    `c: exit`, the operating system observes only the low eight bits of the
    status code, which [process_status] computes modulo 256. *)
Definition process_status (status : Z) : Z := status mod 256.

(** For any integer status code, [process_status] always lies in the unsigned
    byte range from 0 to 255. *)
Lemma process_status_range : forall status, 0 <= process_status status < 256.
Proof. intros status. unfold process_status. apply Z.mod_pos_bound. lia. Qed.

(** ## Constructing the launcher's copied strings

    Before entering `c: main`, the launcher allocates a fresh heap object for
    each argument and environment string, copies the raw character bytes and
    terminating NUL into that object, and stores the resulting pointer into
    the preallocated pointer table. This section defines the byte-copying
    operation [copy_c_bytes], the pointer-table store [startup_store], and
    the frame relation [startup_frame] that keeps earlier allocations and
    existing module globals intact while later strings are copied. *)
(** Given a memory state m, a starting address a, and a list of character
    bytes, [copy_c_bytes] writes each byte sequentially starting at a and
    writes a terminating zero byte immediately after the last character,
    without modifying any shadow [[capability]] slots. *)
Fixpoint copy_c_bytes (m : mem) (a : Z) (bytes : list Z) : mem :=
  match bytes with
  | [] => store_bytes m a 1 0
  | b :: rest => copy_c_bytes (store_bytes m a 1 b) (a + 1) rest
  end.

(** Copying string bytes and the trailing NUL with [copy_c_bytes] leaves the
    list of registered memory regions unchanged. *)
Lemma copy_c_bytes_regions : forall bytes m a,
  m_regions (copy_c_bytes m a bytes) = m_regions m.
Proof. induction bytes; intros; simpl; [reflexivity|rewrite IHbytes; reflexivity]. Qed.

(** Copying string bytes with [copy_c_bytes] leaves every shadow [[aux]]
    capability slot in memory unchanged. *)
Lemma copy_c_bytes_aux : forall bytes m a,
  m_aux (copy_c_bytes m a bytes) = m_aux m.
Proof. induction bytes; intros; simpl; [reflexivity|rewrite IHbytes; reflexivity]. Qed.

(** Every byte address that lies below the start of [copy_c_bytes] or past
    its terminating NUL byte retains the value it held before the copy. *)
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

(** When every byte in bytes is non-zero and fits in an unsigned byte,
    running [copy_c_bytes] at address a establishes a NUL-terminated
    [string_at] payload at a. *)
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

(** Because a [[fresh]] heap allocation does not overlap any previously
    registered object, allocating a fresh buffer and filling it with
    [copy_c_bytes] leaves the primary bytes and shadow capabilities of every
    pre-existing object unchanged. *)
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

(** While the launcher fills a pointer array between addresses lo and hi,
    every previously allocated object outside that slot range must keep its
    contents. The relation [startup_frame] states that all existing regions
    in m remain in m' and that every byte and shadow capability of an
    existing object outside the range from lo to hi is unchanged. *)
Definition startup_frame (m m' : mem) (lo hi : Z) : Prop :=
  (forall b reg, object_region b (m_regions m) = Some reg ->
    object_region b (m_regions m') = Some reg) /\
  (forall a, in_object m a -> a < lo \/ hi <= a ->
    m_bytes m' a = m_bytes m a /\ m_aux m' a = m_aux m a).

(** Allocating a [[fresh]] heap object and copying a string into it with
    [copy_c_bytes] satisfies [startup_frame] for any slot range, because the
    new string lies entirely outside all pre-existing objects. *)
Lemma copied_string_frame : forall m q base bytes lo hi,
  fresh m q base -> Z.of_nat (length bytes) + 1 <= req_extent q ->
  startup_frame m (copy_c_bytes (allocated m q base) base bytes) lo hi.
Proof.
  intros m q base bytes lo hi Hfresh Hsize. split.
  - intros b reg H. rewrite copy_c_bytes_regions. eapply allocated_old_region; [|exact H].
    exact (proj1 (proj2 (proj2 (proj2 Hfresh)))).
  - intros a Hin _. eapply copied_string_old_object; eauto.
Qed.

(** Because [startup_frame] preserves every existing region in memory, any
    capability access check that succeeded before the step continues to
    succeed after it. *)
Lemma startup_frame_access : forall m m' lo hi a c size rights align,
  startup_frame m m' lo hi -> access_res m a c size rights align = Some ok ->
  access_res m' a c size rights align = Some ok.
Proof.
  intros m m' lo hi a c size rights align [Hr _] Ha.
  unfold access_res, cap_access_res in Ha. destruct c as [|b|b|f|f]; try discriminate.
  all: destruct (object_region b (m_regions m)) as [reg|] eqn:E; try discriminate;
    unfold access_res, cap_access_res; rewrite (Hr _ _ E); exact Ha.
Qed.

(** Any byte address that belonged to a registered object before a
    [startup_frame] transition still belongs to that object afterward. *)
Lemma startup_frame_in : forall m m' lo hi a,
  startup_frame m m' lo hi -> in_object m a -> in_object m' a.
Proof. intros m m' lo hi a [Hr _] (b & reg & E & H). exists b, reg. auto. Qed.

(** As the launcher fills a pointer array one slot at a time, two consecutive
    [startup_frame] steps over adjacent address intervals from lo to mid and
    from mid to hi combine into a single frame over the interval from lo to
    hi. *)
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

(** The helper [startup_store] writes a pointer's eight-byte address into
    primary memory at address a and records its capability in the shadow
    [[aux]] slot at a. *)
Definition startup_store (m : mem) (a : Z) (p : ptr) : mem :=
  store_aux (store_bytes m a 8 (ptr_addr p)) a (ptr_cap p).

(** Writing a pointer into the eight-byte cell at address a with
    [startup_store] leaves every existing object's bytes and capabilities
    outside the range from a to `a + 8` unchanged. *)
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

(** Any [pointer_slot] inside an existing object whose eight bytes lie
    outside the modified interval from lo to hi remains intact across a
    [startup_frame] step. *)
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

(** If two memory states agree on every primary byte across the character
    payload and terminating NUL of a string at address a, then [string_at]
    holds in the second state whenever it held in the first. *)
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

(** A valid [c_string] whose bytes and terminating NUL lie outside the
    modified interval from lo to hi remains a valid [c_string] after a
    [startup_frame] transition. *)
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

(** When a [startup_frame] transition has an empty modified interval on
    existing objects, an entire [string_slots] array inside an existing
    object—together with all the strings it points to—survives unchanged. *)
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

(** When the launcher allocates and fills `c: envp` after finishing `c: argv`,
    every object that belonged to `c: argv` already exists in memory. Any
    [startup_frame] transition that leaves existing objects untouched
    therefore preserves an earlier [string_vector] in its entirety. *)
Lemma startup_frame_vector : forall m m' table texts,
  startup_frame m m' 0 0 -> string_vector m table texts -> string_vector m' table texts.
Proof.
  intros m m' table texts Hf [Ha Hslots]. split.
  - eapply startup_frame_access; eauto.
  - eapply startup_frame_slots; [exact Hf| |exact Hslots].
    intros b Hb. eapply access_in; [exact Ha|exact Hb].
Qed.

(** Allocating and copying startup strings in new heap buffers leaves every
    existing object in memory untouched. Consequently, any global pointer
    variable satisfying [exposed_pointer_cell] keeps its write permissions,
    stored address, and shadow capability across the copy. *)
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

(** Combining [startup_frame_exposed_cell] and [startup_frame_string] shows
    that the four exported libc pointer cells and their program-name strings
    in [libc_globals_at] survive the launcher's `c: argv` and `c: envp`
    allocations unchanged. *)
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

(** Rounding a positive allocation size up to a 16-byte heap extent in
    [heap_req] always provides at least the requested number of bytes. *)
Lemma startup_extent : forall size, 0 < size -> size <= req_extent (heap_req 16 size).
Proof.
  intros size Hsize. unfold heap_req. simpl.
  pose proof (Z.mod_pos_bound (size + 15) 16 ltac:(lia)).
  pose proof (Z.div_mod (size + 15) 16 ltac:(lia)). lia.
Qed.

(** When a live heap region at base address table covers a range of size
    bytes at an aligned address a, [access_res] authorizes reading or writing
    that range through the capability `Obj table`. *)
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

(** ## Startup copying as external-call effects

    To connect the launcher's memory construction to the external-call
    semantics of [ExternalCalls](ExternalCalls.v), this section shows that
    allocating and filling `c: argv` and `c: envp` forms a valid sequence of
    external-call [E.effects]. Parameterizing the functor [StartupOn] over an
    existing [ExternalMachineSig] instance M lets callers apply these startup
    theorems directly to their own machine instance. *)
Module StartupOn (R : Runtime) (M : ExternalMachineSig R).
(** The alias [E] re-exports the external-call definitions and effect
    relations from the machine instance M. *)
Module E := M.E.

(** Once the launcher has allocated a writable buffer for a string, writing
    the character bytes and terminating NUL into that buffer with
    [copy_c_bytes] is a valid sequence of local byte-store effects. *)
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

(** To copy one startup string into the heap, the launcher requests a
    16-byte-aligned block of `length bytes + 1` bytes from the allocator and
    writes the characters and terminating NUL into the new block. When the
    allocation succeeds, [copy_string] shows that this step is a valid
    external-call effect that keeps the runtime [[ready]], leaves all
    existing objects unchanged, and produces a readable and writable
    [c_string]. *)
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

(** Because the launcher performs a sequence of allocations and byte copies
    one after another, [effects_trans] joins two consecutive [E.effects]
    traces under the same contract permissions into a single combined trace. *)
Lemma effects_trans : forall sources roots releases requests s m born s1 m1 born1 s2 m2 born2,
  E.effects sources roots releases requests s m born s1 m1 born1 ->
  E.effects sources roots releases requests s1 m1 born1 s2 m2 born2 ->
  E.effects sources roots releases requests s m born s2 m2 born2.
Proof.
  intros sources roots releases requests s m born s1 m1 born1 s2 m2 born2 H.
  induction H; intros Htail; eauto using E.effects_local, E.effects_alloc.
Qed.

(** A list of byte strings satisfies [payloads_allowed] when every string
    contains only non-zero unsigned bytes, fits with its terminating NUL
    inside [max_allocation_size], and has its 16-byte-aligned allocation size
    permitted by the contract's requests predicate. *)
Definition payloads_allowed (requests : Z -> Z -> Prop) (texts : list (list Z)) : Prop :=
  Forall (fun text => Forall (fun b => 0 < b < 256) text /\
    Z.of_nat (length text) + 1 <= max_allocation_size /\
    requests 16 (Z.of_nat (length text) + 1)) texts.

(** Given a preallocated pointer table and a write cursor, [copy_slots]
    iterates through texts in forward order, calling [R.alloc] and
    [copy_c_bytes] for each string and writing the resulting pointer into the
    table with [startup_store]. If any string allocation is refused by the
    runtime, [copy_slots] returns `None`. *)
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

(** To construct a complete string vector, [copy_vector] first allocates the
    pointer table for `length texts + 1` eight-byte slots and then fills the
    leading slots with [copy_slots]. Because a fresh heap allocation starts
    zero-initialized with [CNone] shadow capabilities, the final slot already
    holds the required null sentinel without an extra store. *)
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

(** As [copy_slots] walks across a preallocated pointer table, each iteration
    allocates one string on the heap and writes its capability-bearing
    pointer into the current table slot. By induction on the string list,
    [copy_slots_correct] proves that a successful loop keeps the runtime
    [[ready]], leaves all memory outside the filled slots unchanged, and
    populates a null-terminated [string_slots] sequence. *)
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

(** A complete vector copy allocates the pointer array first and then fills
    each entry with a freshly copied string while leaving the final zeroed
    slot as the null sentinel. When all allocations succeed,
    [copy_vector_correct] shows that [copy_vector] produces a valid
    [string_vector] without modifying any object that existed before the
    array was allocated. *)
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

(** Whenever the byte size `8 * (n + 1)` of an environment pointer table fits
    within [max_allocation_size], both the entry count n and the table byte
    size fit within unsigned 64-bit `c: size_t` arithmetic. *)
Lemma environment_copy_bounds : forall n,
  8 * (Z.of_nat n + 1) <= max_allocation_size ->
  0 <= Z.of_nat n < 2 ^ 64 - 1 /\ 0 < 8 * (Z.of_nat n + 1) < 2 ^ 64.
Proof. intros n H. unfold max_allocation_size in H. lia. Qed.

(** The launcher builds the program's initial arguments by running
    [copy_vector] first for the command-line strings in `c: argv` and then
    for the environment strings in `c: envp`. Because the second copy leaves
    all objects from the first copy untouched, [copied_startup] establishes
    the complete [startup_at] memory layout while preserving every object
    that existed before startup. *)
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

(** Once the launcher has copied `c: argv` and `c: envp` into heap memory, it
    creates the initial call frame for a two-parameter `c: main` function.
    Theorem [copied_startup_main] packages that entry frame together with the
    [startup_at] layout and shows that the module's exported libc pointer
    cells in [libc_globals_at] remain intact at entry to `c: main`. *)
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

(** For callers that do not already hold an [ExternalMachine] instance, the
    functor [Startup] instantiates [ExternalMachine] over R and includes
    [StartupOn] directly. *)
Module Startup (R : Runtime).
Module M := ExternalMachine R.
Include StartupOn R M.
End Startup.
