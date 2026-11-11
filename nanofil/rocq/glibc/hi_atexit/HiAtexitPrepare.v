(** The main-entry boundary needs a registered thread, initialized
    stream links and the single-thread flag. This file defines a finite
    host preparation of the loader image that supplies those fields.
    It is not an execution of compiled startup code. Relating this
    preparation to real process startup remains a separate obligation.

    Glibc startup allocates a thread object, initializes its self
    pointers and records that the process has one thread. The pinned
    sources for those operations are libc-tls.c, x86-64 tls.h and
    libc_early_init.c. The native probe records the object's 2560-byte
    size and cleanup-field offsets. Other real-startup effects are
    outside this projection. *)

From Stdlib Require Import ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Syntax Values Memory Runtime Run Pieces.
From Glibc Require Import OsWorld HiAtexitInitial.
Import ListNotations.
Open Scope Z_scope.

(** Host preparation requests an ordinary, aligned heap object using
    the interpreter allocator, without changing the runtime's rules. *)
Definition hi_tcb_req : alloc_req := heap_req 16 2560.

(** These stores install the backward stream links, thread headers and
    cleanup pointers. The saved jump-buffer pointer is a parameter;
    preparation does not require it to be null. *)
Definition hi_entry_ptrs (tb : Z) (jb : ptr) : list (Z * ptr) :=
  [(69512, mkPtr 70048 (Obj 70048));
   (69992, mkPtr 69432 (Obj 69328));
   (69752, mkPtr 69912 (Obj 69808));
   (tb, mkPtr tb (Obj tb)); (tb + 16, mkPtr tb (Obj tb));
   (tb + 776, null); (tb + 784, jb)].

(** A host pointer store changes its eight address bytes and its
    capability slot, exactly as the model represents pointer values. *)
Definition hi_host_ptr (m : mem) (ap : Z * ptr) : mem :=
  store_aux (store_bytes m ap.1 8 (ptr_addr ap.2)) ap.1 (ptr_cap ap.2).

(** The host writes only these named fields. In particular, the model
    makes no claim that all other real-startup memory is unchanged. *)
Definition hi_entry_writes (m : mem) (tb : Z) (jb : ptr) : mem :=
  fold_left hi_host_ptr (hi_entry_ptrs tb jb)
    (store_bytes (store_bytes m 73808 1 1) (tb + 792) 4 0).

(** System calls identify this thread by its new object's pointer.
    The program uses the three standard descriptors and no log file.
    Its error cell remains at the linked TLS address. *)
Definition hi_entry_world (tb : Z) : os_world :=
  mkOsWorld (Some (mkPtr 68176 (Obj 68176))) (mkPtr tb (Obj tb)) None [0; 1; 2].

(** Allocation failure produces no prepared state and performs none
    of the finite writes. Success registers the new region before
    initializing it and publishing its cookie in the returned world. *)
Definition hi_host_prepare (m : mem) (next : InterpRuntime.state) (jb : ptr)
    : option (mem * InterpRuntime.state * os_world) :=
  match InterpRuntime.alloc next hi_tcb_req with
  | None => None
  | Some (tb, next') =>
      Some (hi_entry_writes (allocated m hi_tcb_req tb) tb jb, next', hi_entry_world tb)
  end.

(** There is an explicit failure outcome rather than an assumed
    successful allocation hidden in the preparation definition. *)
Lemma hi_host_prepare_failure m next jb :
  InterpRuntime.alloc next hi_tcb_req = None -> hi_host_prepare m next jb = None.
Proof. intros H. unfold hi_host_prepare. rewrite H. reflexivity. Qed.

(** The interpreter's initial cursor leaves room for this request. *)
Lemma hi_tcb_allocation : InterpRuntime.alloc InterpRuntime.start hi_tcb_req =
  Some (4294967296, 4294969872).
Proof. reflexivity. Qed.

(** This is the physical memory at the explicitly prepared boundary,
    not the loader's untouched initial memory. *)
Definition hi_entry_mem (jb : ptr) : mem :=
  hi_entry_writes (allocated hi_m0 hi_tcb_req 4294967296) 4294967296 jb.

(** Preparation of the linked loader image succeeds for every saved
    jump-buffer pointer. Later files check that this physical memory
    supports main's complete starting state. *)
Lemma hi_host_prepare_success jb :
  hi_host_prepare hi_m0 InterpRuntime.start jb =
    Some (hi_entry_mem jb, 4294969872, hi_entry_world 4294967296).
Proof. reflexivity. Qed.

(** The named writes never change the region table. *)
Lemma hi_entry_writes_regions m tb jb :
  m_regions (hi_entry_writes m tb jb) = m_regions m.
Proof. reflexivity. Qed.

(** The returned cookie carries the registered object's capability,
    whose exact bounds cover all 2560 bytes of the TCB. *)
Lemma hi_entry_tcb_registered jb :
  object_region 4294967296 (m_regions (hi_entry_mem jb)) =
    Some (mkRegion 4294967296 4294969856 Heap Live).
Proof. reflexivity. Qed.

(** Both header pointers contain the returned cookie, including its
    capability. The single-thread flag and cancelhandling have their
    declared entry values. *)
Lemma hi_entry_fields jb :
  load_bytes (hi_entry_mem jb) 4294967296 8 = 4294967296 /\
  m_aux (hi_entry_mem jb) 4294967296 = Obj 4294967296 /\
  load_bytes (hi_entry_mem jb) 4294967312 8 = 4294967296 /\
  m_aux (hi_entry_mem jb) 4294967312 = Obj 4294967296 /\
  load_bytes (hi_entry_mem jb) 73808 1 = 1 /\
  load_bytes (hi_entry_mem jb) 4294968088 4 = 0.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Every destination field permits its write through the owning
    object's capability. This checks the flag byte, cancellation word,
    stream links and all four thread pointers at their actual alignments. *)
Lemma hi_entry_write_access jb :
  access_res (hi_entry_mem jb) 73808 (Obj 73808) 1 Write 1 = Some (RVal tt) /\
  access_res (hi_entry_mem jb) 4294968088 (Obj 4294967296) 4 Write 4 = Some (RVal tt) /\
  Forall (fun ac => access_res (hi_entry_mem jb) ac.1.1 ac.2 8 Write 8 = Some (RVal tt))
    (combine (hi_entry_ptrs 4294967296 jb)
      [Obj 69328; Obj 69808; Obj 69568; Obj 4294967296; Obj 4294967296;
       Obj 4294967296; Obj 4294967296]).
Proof. vm_compute. repeat constructor. Qed.
