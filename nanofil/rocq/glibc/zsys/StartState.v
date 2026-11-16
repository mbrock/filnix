(** A whole-program proof that starts at `c: __libc_start_main` must say
    which machine states the program can start in. Fil-C's runtime builds
    that state in `c: really_start_program` (`filc/src/filc_start_program.c`
    in the pinned sources) before it calls into user glibc. This module
    states, as one definition [start_state], every state that the runtime
    can build for a linked image, so that a never-panics theorem can
    quantify over all of them.

    ## What the runtime hands to user glibc

    The runtime calls `c: __libc_start_main(main, argc, argv, environ, auxv)`
    with five arguments. It asserts that argc is at least 1. It copies
    argv into a fresh heap array of argc + 1 pointers, each pointing to its
    own heap copy of a NUL-terminated string, with a null pointer last. It
    copies the environment the same way, ending with a null pointer. The
    auxiliary vector is a heap array of integers only: key and value pairs
    for the keys present, in ascending key order, ended by a zero key.
    Every key and value is arbitrary, including `AT_SECURE`, and so is
    every CPUID answer that startup later asks for.

    At that point the runtime has set no thread cookie, has registered no
    errno or dlerror handler, and has run no deferred constructor. If `c: __libc_start_main` ever
    returns, the runtime panics with "unexpected return from
    `c: __libc_start_main`", so a never-panics theorem from these states
    has the postcondition False.

    ## The image and the constructor table

    The image is the linked module with the constructor runner of
    [StartCtors](StartCtors.v) appended. Its initial memory gives every
    global its bytes and capabilities. A start state keeps all of those
    except the runner's table, which holds the saved argc, argv and
    environ and the constructors in some order. Every order is allowed,
    because the image does not record the one the dynamic loader chose. *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import String ZArith List Lia Sorting.Sorted Sorting.Permutation.
From Nanofil Require Import Term Syntax Values Memory Semantics Run Runtime Pieces.
From Glibc Require Import OsWorld OsStart StartCtors.
Import ListNotations.
Open Scope Z_scope.

(** ## Objects the runtime allocates

    Every object the runtime builds for the program comes from
    `c: filc_allocate`, so it is a live heap object that the program may
    later free. The definitions below describe one such object and the
    words and strings stored in it. *)

(** This predicate holds when a live heap object starts at base b and
    has room for at least n bytes. *)
Definition heap_object (m : mem) (b n : Z) : Prop :=
  exists reg, live_at m b reg /\ r_kind reg = Heap /\ b + n <= r_end reg.

(** The 8-byte slot at address a holds pointer p, with its capability in
    the slot's [[aux]] entry. *)
Definition ptr_slot (m : mem) (a : Z) (p : ptr) : Prop :=
  load_bytes m a 8 = ptr_addr p /\ m_aux m a = ptr_cap p.

(** The 8-byte slot at address a holds the integer v and no capability. *)
Definition int_slot (m : mem) (a v : Z) : Prop :=
  load_bytes m a 8 = v /\ m_aux m a = CNone.

(** A heap object at b holds the NUL-terminated string s, which has no
    NUL byte of its own. *)
Definition c_string (m : mem) (b : Z) (s : list Z) : Prop :=
  heap_object m b (Z.of_nat (length s) + 1) /\
  (forall i, (i < length s)%nat -> exists x, nth_error s i = Some x /\ x <> 0 /\ m_bytes m (b + Z.of_nat i) = x) /\
  m_bytes m (b + Z.of_nat (length s)) = 0.

(** A heap array at b holds pointers to the n strings ss, each in its own
    heap object, followed by a null pointer. argv and environ both have
    this shape. *)
Definition string_array (m : mem) (b : Z) (ss : list (Z * list Z)) : Prop :=
  heap_object m b (8 * (Z.of_nat (length ss) + 1)) /\
  (forall i sb s, nth_error ss i = Some (sb, s) ->
     ptr_slot m (b + 8 * Z.of_nat i) (mkPtr sb (Obj sb)) /\ c_string m sb s) /\
  ptr_slot m (b + 8 * Z.of_nat (length ss)) (mkPtr 0 CNone).

(** The auxiliary vector is a list of integer key and value pairs that
    describes the process to libc. This predicate says that a heap array at b
    holds the integer pairs ps, whose keys are positive and ascending,
    followed by a zero key, and that no slot of the array holds a
    capability. *)
Definition auxv_array (m : mem) (b : Z) (ps : list (Z * Z)) : Prop :=
  heap_object m b (8 * (2 * Z.of_nat (length ps) + 1)) /\
  Sorted Z.lt (map fst ps) /\ Forall (fun kv => 0 < fst kv) ps /\
  (forall i k v, nth_error ps i = Some (k, v) ->
     int_slot m (b + 16 * Z.of_nat i) k /\ int_slot m (b + 16 * Z.of_nat i + 8) v) /\
  int_slot m (b + 16 * Z.of_nat (length ps)) 0.

(** ## The image's memory and the runner's table

    When the program starts, its globals hold what the linked image put
    there, except for the constructor table. The image leaves that table
    zero, and the start state puts the saved arguments and constructor
    pointers into it.
    A start state therefore agrees with the image's initial memory on
    every global except that table. The definitions below state that
    agreement and say what the table contains. *)

(** Address a lies inside some object of memory m0. *)
Definition in_image (m0 : mem) (a : Z) : Prop :=
  exists reg, In reg (m_regions m0) /\ r_base reg <= a < r_end reg.

(** Memory m keeps every object of the image's initial memory m0 and the
    contents of every byte and aux slot in them, except inside the table
    object tb. Every other object of m is a heap object. *)
Definition keeps_image (m0 m : mem) (tb : Z) (tsize : Z) : Prop :=
  (forall b reg, object_region b (m_regions m0) = Some reg -> object_region b (m_regions m) = Some reg) /\
  (forall b reg, object_region b (m_regions m) = Some reg -> object_region b (m_regions m0) = None ->
     r_kind reg = Heap) /\
  (forall a, in_image m0 a -> ~ (tb <= a < tb + tsize) ->
     m_bytes m a = m_bytes m0 a /\ m_aux m a = m_aux m0 a).

(** The table at tb holds argc, argv and environ, then a pointer to
    each constructor in order, each pointer taken from the image's
    symbol table g. *)
Definition ctor_table (m : mem) (g : list (name * ptr)) (tb argc : Z) (argv env : ptr) (order : list name) : Prop :=
  int_slot m tb argc /\ ptr_slot m (tb + 8) argv /\ ptr_slot m (tb + 16) env /\
  (forall i f, nth_error order i = Some f ->
     exists p, lookup f g = Some p /\ ptr_slot m (tb + 24 + 8 * Z.of_nat i) p).

(** ## The allowed starting states

    The last definition collects everything above. It also fixes the OS
    world, whose cookie is null and whose handlers are unregistered, and
    the five arguments of the entry call. *)

(** Before startup, the world has no cookie, no errno handler and no
    dlerror handler. Its errno cell is the image's `c: __libc_errno`, and
    none of its descriptors is libpizlo's log descriptor. *)
Definition start_os (g : list (name * ptr)) (w0 : os_world) (w : os_world) : Prop :=
  lookup (TAtom "__libc_errno") g = Some (ow_errno_cell w0) /\
  Forall (fun fd => ow_log_fd w0 <> Some fd) (ow_fds w0) /\
  w = start_world w0 (mkPtr 0 CNone) false false.

(** [start_state] md m w xs holds when the runtime can start the image md
    with memory m, OS world w over the base world w0, and entry arguments
    xs for `c: __libc_start_main`. The image md must already contain the
    constructor runner. *)
Definition start_state (md : module) (w0 : os_world) (m : mem) (w : os_world) (xs : list word) : Prop :=
  exists g m0 mainp tb argc argv env av ps order,
    initial_memory md = Some (g, m0) /\
    lookup (TAtom "main") g = Some mainp /\
    lookup ctor_table_name g = Some (mkPtr tb (Ro tb)) /\
    xs = [WPtr mainp; WInt argc; WPtr (mkPtr (fst argv) (Obj (fst argv)));
          WPtr (mkPtr (fst env) (Obj (fst env))); WPtr (mkPtr av (Obj av))] /\
    argc = Z.of_nat (length (snd argv)) /\ 1 <= argc < 2 ^ 31 /\
    string_array m (fst argv) (snd argv) /\
    string_array m (fst env) (snd env) /\
    auxv_array m av ps /\
    live_disjoint m /\
    keeps_image m0 m tb (ctor_table_size (length (ctor_names md))) /\
    Permutation order (ctor_names md) /\
    ctor_table m g tb argc (mkPtr (fst argv) (Obj (fst argv))) (mkPtr (fst env) (Obj (fst env))) order /\
    start_os g w0 w.
