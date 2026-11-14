(** The invariants of user glibc's narrow stdio state
    (docs/glibc-ir.md) that hi_atexit.c's `atexit(close_stdout);
    puts("hello"); exit(0);` keeps: a `c: FILE` ([file_inv]), the list
    of open streams ([io_list_inv]), the jump tables ([vtables_ro]),
    the calling thread's cleanup fields ([tcb_cleanup_inv]) and
    `c: __libc_single_threaded` ([single_ro]).

    Each is stated over the pieces of Logic.v and MemLogic.v at the
    offsets glibc 2.44's x86-64 layout gives (libio/bits/types/
    struct_FILE.h, nptl/descr.h), which the IR of LibioReadCode.v and
    the others reads: the triples of LibioRead.v and SysWrappers.v take
    exactly the fields a function touches, and [file_inv] is the whole
    stream those fields are opened from.

    ## The layout

    | offset | field | owned as |
    |---|---|---|
    | 0 | `c: int _flags` | 4 [bytes] |
    | 8 to 96 | the twelve buffer pointers, `c: _IO_read_ptr` to `c: _markers` | [pcell] each |
    | 104 | `c: _chain` | [pcell], by [io_list_inv] |
    | 112, 116 | `c: _fileno`, `c: _flags2` (24 bits) and `c: _short_backupbuf` | 4 [bytes] each |
    | 120 | `c: _old_offset` | [icell] |
    | 128 | `c: _cur_column`, `c: _vtable_offset`, `c: _shortbuf` (131) and padding | 8 [bytes] |
    | 136 | `c: _lock` | [pcell] |
    | 144 | `c: _offset` | [icell] |
    | 152 to 176 | `c: _codecvt`, `c: _wide_data`, `c: _freeres_list`, `c: _freeres_buf` | [pcell] each |
    | 184 | `c: _prevchain` | [pcell], by [io_list_inv] |
    | 192 | `c: int _mode` | 4 [bytes] |
    | 200 | `c: _total_written` | [icell] |
    | 216 | the jump table pointer of `c: struct _IO_FILE_plus` | [pcell] |

    `c: _IO_lock_t` is `c: { int lock; int cnt; void *owner; }`; the
    thread's `c: struct pthread` has `c: cleanup` at 776,
    `c: cleanup_jmp_buf` at 784 and `c: int cancelhandling` at 792.

    ## The decisions

    | Decision | Why |
    |---|---|
    | a stream's jump table is [VtFile] while `c: _mode` is 0 or -1, and [VtWFile] at 1 | `c: _IO_fwide` sets the mode once; `c: _IO_unbuffer_all` sets -1 on a narrow stream and keeps its table |
    | the jump table pointer is `c: __io_vtables + 336` or `+ 840`, both below 2352, so `c: IO_validate_vtable` never calls `c: _IO_vtable_check` | [vt_valid] |
    | `c: cancelhandling` is 0 | `c: __libc_cleanup_push_defer` then stores canceltype 0 and `c: __libc_cleanup_pop_restore` neither CASes nor unwinds |
    | `c: __libc_single_threaded` is a read-only share holding 1 | the lock macros take the single-thread path, and nothing in the narrow path writes it |
    | the lock is (0, 0, null) or (1, cnt, the thread's cookie) | `c: _IO_lock_lock` and `c: _IO_lock_unlock` in one thread |
    | `c: _chain` and `c: _prevchain` belong to the list, not the stream | `c: _IO_un_link` rewrites a neighbour's links | *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  Pieces Heap StringLogic Logic MemLogic.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** ## Offsets and flags *)

(** `c: struct _IO_FILE`'s fields, and the jump table field of
    `c: struct _IO_FILE_plus`. *)
Definition off_flags : Z := 0.
#[export] Hint Unfold off_flags : offs.
Definition off_read_ptr : Z := 8.
#[export] Hint Unfold off_read_ptr : offs.
Definition off_write_base : Z := 32.
#[export] Hint Unfold off_write_base : offs.
Definition off_write_ptr : Z := 40.
#[export] Hint Unfold off_write_ptr : offs.
Definition off_write_end : Z := 48.
#[export] Hint Unfold off_write_end : offs.
Definition off_buf_base : Z := 56.
#[export] Hint Unfold off_buf_base : offs.
Definition off_buf_end : Z := 64.
#[export] Hint Unfold off_buf_end : offs.
Definition off_chain : Z := 104.
#[export] Hint Unfold off_chain : offs.
Definition off_fileno : Z := 112.
#[export] Hint Unfold off_fileno : offs.
Definition off_flags2 : Z := 116.
#[export] Hint Unfold off_flags2 : offs.
Definition off_old_offset : Z := 120.
#[export] Hint Unfold off_old_offset : offs.
Definition off_column : Z := 128.
#[export] Hint Unfold off_column : offs.      (* `c: _cur_column`, `c: _vtable_offset`, `c: _shortbuf` at 131, padding *)
Definition off_shortbuf : Z := 131.
#[export] Hint Unfold off_shortbuf : offs.
Definition off_lock : Z := 136.
#[export] Hint Unfold off_lock : offs.
Definition off_offset : Z := 144.
#[export] Hint Unfold off_offset : offs.
Definition off_codecvt : Z := 152.
#[export] Hint Unfold off_codecvt : offs.
Definition off_wide : Z := 160.
#[export] Hint Unfold off_wide : offs.
Definition off_freeres_list : Z := 168.
#[export] Hint Unfold off_freeres_list : offs.
Definition off_freeres_buf : Z := 176.
#[export] Hint Unfold off_freeres_buf : offs.
Definition off_prevchain : Z := 184.
#[export] Hint Unfold off_prevchain : offs.
Definition off_mode : Z := 192.
#[export] Hint Unfold off_mode : offs.
Definition off_total_written : Z := 200.
#[export] Hint Unfold off_total_written : offs.
Definition off_vtable : Z := 216.
#[export] Hint Unfold off_vtable : offs.
(** The offsets in `c: struct pthread`. *)
Definition off_cleanup : Z := 776.
#[export] Hint Unfold off_cleanup : offs.
Definition off_cleanup_jmp : Z := 784.
#[export] Hint Unfold off_cleanup_jmp : offs.
Definition off_cancelhandling : Z := 792.
#[export] Hint Unfold off_cancelhandling : offs.

(** The offsets of `c: _IO_lock_t`. *)
Definition off_lk_lock : Z := 0.
#[export] Hint Unfold off_lk_lock : offs.
Definition off_lk_cnt : Z := 4.
#[export] Hint Unfold off_lk_cnt : offs.
Definition off_lk_owner : Z := 8.
#[export] Hint Unfold off_lk_owner : offs.

(** The size of `c: struct _IO_FILE_plus`. *)
Definition file_size : Z := 224.

(** The offset of the i-th of the twelve pointers from `c: _IO_read_ptr`. *)
Definition off_ptr (i : nat) : Z := 8 + 8 * Z.of_nat i.
#[export] Hint Unfold off_ptr : offs.

(** `c: _IO_MAGIC`, in the high half of `c: _flags`, and the bits
    the narrow path tests. *)
Definition io_magic : Z := 4222418944.                 (* 0xFBAD0000 *)
Definition io_user_buf : Z := 1.
Definition io_unbuffered : Z := 2.
Definition io_no_writes : Z := 8.
Definition io_err_seen : Z := 32.
Definition io_linked : Z := 128.
Definition io_in_backup : Z := 256.
Definition io_line_buf : Z := 512.
Definition io_currently_putting : Z := 2048.
Definition io_is_appending : Z := 4096.
Definition io_is_filebuf : Z := 8192.
Definition io_user_lock : Z := 32768.
(** `c: _IO_FLAGS2_NEED_LOCK`, in `c: _flags2`. *)
Definition io_need_lock : Z := 128.

(** The bit mask of a flag word: set or clear. *)
Definition has (flags bit : Z) : bool := negb (Z.land flags bit =? 0).

(** ## The jump tables *)

(** `c: __io_vtables` holds fourteen jump tables of 21 pointers, 168
    bytes each: 2352 bytes. *)
Definition io_vtables_size : Z := 2352.
(** The offsets of `c: _IO_file_jumps` and `c: _IO_wfile_jumps` in it. *)
Definition vt_file : Z := 336.
#[export] Hint Unfold vt_file : offs.
Definition vt_wfile : Z := 840.
#[export] Hint Unfold vt_wfile : offs.

(** The slots of a jump table (`c: struct _IO_jump_t`). *)
Definition slot_finish : Z := 16.
#[export] Hint Unfold slot_finish : offs.
Definition slot_overflow : Z := 24.
#[export] Hint Unfold slot_overflow : offs.
Definition slot_xsputn : Z := 56.
#[export] Hint Unfold slot_xsputn : offs.
Definition slot_doallocate : Z := 104.
#[export] Hint Unfold slot_doallocate : offs.
Definition slot_write : Z := 120.
#[export] Hint Unfold slot_write : offs.
Definition slot_close : Z := 136.
#[export] Hint Unfold slot_close : offs.
Definition slot_stat : Z := 144.
#[export] Hint Unfold slot_stat : offs.

(** The functions of `c: _IO_file_jumps` the narrow path calls, by
    slot: the names the linked module's table points at, aliases
    resolved (LibioReadCode.v and the others hold them). *)
Definition file_jumps : list (Z * string) :=
  [(slot_finish, "_IO_new_file_finish"); (slot_overflow, "_IO_new_file_overflow");
   (slot_xsputn, "_IO_new_file_xsputn"); (slot_doallocate, "__GI__IO_file_doallocate");
   (slot_write, "_IO_new_file_write"); (slot_close, "__GI__IO_file_close");
   (slot_stat, "__GI__IO_file_stat")].

(** The pointer ge's symbol n is, or null. *)
Definition sym_ptr (ge : genv) (n : string) : ptr :=
  match lookup (TAtom n) (ge_globals ge) with Some p => p | None => mkPtr 0 CNone end.

(** `c: IO_validate_vtable` passes a pointer o bytes into
    `c: __io_vtables` when o is below its size: neither table offset
    calls `c: _IO_vtable_check`. *)
Lemma vt_valid vb : (vb + vt_file - vb) mod 2 ^ 64 < io_vtables_size /\
                    (vb + vt_wfile - vb) mod 2 ^ 64 < io_vtables_size.
Proof. unfold vt_file, vt_wfile, io_vtables_size. split; rewrite Z.add_simpl_l; reflexivity. Qed.

(** A stream's jump table, one way from its mode: narrow while 0 or -1
    ([2 ^ 32 - 1] as the `c: int`'s bits), wide at 1. *)
Definition mode_vtable (mode : Z) (vt_off : Z) : Prop :=
  ((mode = 0 \/ mode = 2 ^ 32 - 1) /\ vt_off = vt_file) \/ (mode = 1 /\ vt_off = vt_wfile).

(** A narrow stream's table is [vt_file]. *)
Lemma mode_vtable_narrow mode vt_off : mode_vtable mode vt_off -> mode <> 1 -> vt_off = vt_file.
Proof. intros [[_ ->] | [-> _]] Hm; [reflexivity | contradiction]. Qed.

(** ## Over a Logic instance *)


Module ML := MemLogicOn R LG0.
Module LG := ML.LG.
Module L := LG.L.
Import L LG ML.

Section inv.
Context `{!gen_heapGS piece pval Σ}.

(** The four little-endian bytes of the `c: int` with bits x. *)
Definition int_bytes (x : Z) : list Z := le_bytes x 4.

(** [int_cell] b o x: owning the `c: int` at offset o of b, with bits x
    below 2^32. *)
Definition int_cell (b o x : Z) : iProp Σ := ⌜0 <= x < 2 ^ 32⌝ ∗ bytes b o (int_bytes x).

(** [int_cellq] dq b o x: [int_cell] at the share dq. *)
Definition int_cellq (dq : dfrac) (b o x : Z) : iProp Σ := ⌜0 <= x < 2 ^ 32⌝ ∗ bytesq dq b o (int_bytes x).

(** ## The jump tables, read-only *)

(** [vtables_ro] ge vb vreg: `c: __io_vtables`, the read-only object
    vb with the region vreg, is ge's symbol, ends past its 2352 bytes,
    and holds at each slot of [file_jumps] in [vt_file] ge's function
    of that name: a persistent read-only share of its life and of
    those slots. `c: IO_accept_foreign_vtables` is never read, since
    every table offset passes [vt_valid]. *)
Definition vtables_ro (ge : genv) (vb : Z) (vreg : region) : iProp Σ :=
  ⌜lookup (TAtom "__io_vtables") (ge_globals ge) = Some (mkPtr vb (Ro vb)) /\
   vb + io_vtables_size <= r_end vreg /\ vb mod 8 = 0 /\ 0 < vb /\ r_end vreg <= 2 ^ 48⌝ ∗
  liveq DfracDiscarded vb vreg ∗
  [∗ list] sl ∈ file_jumps, pcellq DfracDiscarded vb (vt_file + sl.1) (sym_ptr ge sl.2).

(** [vtables_ro] is persistent. *)
Global Instance vtables_ro_persistent ge vb vreg : Persistent (vtables_ro ge vb vreg).
Proof. rewrite /vtables_ro /liveq /pcellq. apply _. Qed.

(** One slot of [file_jumps], read from [vtables_ro]. *)
Lemma vtables_slot ge vb vreg sl n :
  In (sl, n) file_jumps -> vtables_ro ge vb vreg -∗ pcellq DfracDiscarded vb (vt_file + sl) (sym_ptr ge n).
Proof.
  iIntros (Hin) "(_ & _ & Hs)". apply list_elem_of_In in Hin.
  iApply (big_sepL_elem_of (fun sl => pcellq DfracDiscarded vb (vt_file + sl.1) (sym_ptr ge sl.2)) _ (sl, n)
            with "Hs"). exact Hin.
Qed.

(** ## The single-thread flag *)

(** [single_ro] ge sb sreg: `c: __libc_single_threaded` (the byte
    object sb, ge's `c: __libc_single_threaded_internal`) holds 1, at
    a persistent read-only share, so `c: SINGLE_THREAD_P` holds and
    the lock macros take their single-thread path. *)
Definition single_ro (ge : genv) (sb : Z) (sreg : region) : iProp Σ :=
  ⌜lookup (TAtom "__libc_single_threaded_internal") (ge_globals ge) = Some (mkPtr sb (Obj sb)) /\
   sb + 1 <= r_end sreg⌝ ∗ liveq DfracDiscarded sb sreg ∗ bytesq DfracDiscarded sb 0 [1].

(** [single_ro] is persistent. *)
Global Instance single_ro_persistent ge sb sreg : Persistent (single_ro ge sb sreg).
Proof. rewrite /single_ro /liveq /bytesq. apply _. Qed.

(** ## The thread's cleanup fields *)

(** [tcb_cleanup_inv] self: the calling thread's cookie self, not
    null, is the object tb's own pointer; the thread owns tb's life and
    the fields the cleanup calls touch: `c: cleanup` null, as it is
    outside a push and pop, `c: cleanup_jmp_buf`, and
    `c: cancelhandling` 0, so `c: (cancelhandling & CANCELTYPE_BITMASK)
    == 0` and neither a CAS nor `c: __pthread_unwind` is reached. *)
Definition tcb_cleanup_inv (self : ptr) : iProp Σ :=
  ∃ tb treg jb, ⌜self = mkPtr tb (Obj tb) /\ 0 < tb /\ tb mod 8 = 0 /\
                 tb + off_cancelhandling + 4 <= r_end treg /\ r_end treg <= 2 ^ 63⌝ ∗
    live tb treg ∗ pcell tb off_cleanup null ∗ pcell tb off_cleanup_jmp jb ∗
    int_cell tb off_cancelhandling 0.

(** [tcb_pushed] self buf: the same, inside a push of the cleanup
    buffer buf, which `c: cleanup` then points at. *)
Definition tcb_pushed (self buf : ptr) : iProp Σ :=
  ∃ tb treg jb, ⌜self = mkPtr tb (Obj tb) /\ 0 < tb /\ tb mod 8 = 0 /\
                 tb + off_cancelhandling + 4 <= r_end treg /\ r_end treg <= 2 ^ 63⌝ ∗
    live tb treg ∗ pcell tb off_cleanup buf ∗ pcell tb off_cleanup_jmp jb ∗
    int_cell tb off_cancelhandling 0.

(** ## Locks *)

(** [lock_state] lb lk cnt owner: owning the `c: _IO_lock_t` lb, its
    life and its three fields. *)
Definition lock_state (lb : Z) (lreg : region) (lk cnt : Z) (owner : ptr) : iProp Σ :=
  ⌜lb mod 8 = 0 /\ lb + 16 <= r_end lreg /\ r_end lreg <= 2 ^ 63⌝ ∗
  live lb lreg ∗ int_cell lb off_lk_lock lk ∗ int_cell lb off_lk_cnt cnt ∗ pcell lb off_lk_owner owner.

(** [lock_inv] self lp: the stream lock lp is free, (0, 0, null), or
    held by the thread self, (1, cnt, self). *)
Definition lock_inv (self lp : ptr) (held : option Z) : iProp Σ :=
  ∃ lb lreg, ⌜lp = mkPtr lb (Obj lb)⌝ ∗
    match held with
    | None => lock_state lb lreg 0 0 null
    | Some cnt => lock_state lb lreg 1 cnt self
    end.

(** ## A stream *)

(** The narrow buffer of a stream:
    - [NbNone]: none yet, every buffer pointer null;
    - [NbShort]: unbuffered, the one byte `c: _shortbuf` at offset 131;
    - [NbHeap] bb sz: the heap object bb of sz bytes, `c: malloc`'s;
    - [NbFreeres] bb: a heap buffer `c: _IO_unbuffer_all` handed to
      the freeres list, no longer the stream's. *)
Inductive nbuf : Type :=
| NbNone
| NbShort
| NbHeap (bb sz : Z)
| NbFreeres (bb : Z).

(** The raw state of a stream: every field the narrow path reads, as
    owned values. *)
Record fstate : Type := mkFstate {
  fs_flags : Z;          (* `c: _flags`'s bits *)
  fs_ptrs : list ptr;    (* the twelve pointers from offset 8 *)
  fs_fileno : Z;
  fs_flags2 : Z;         (* the 4 bytes at 116 *)
  fs_old_offset : Z;
  fs_column : list Z;    (* the 8 bytes at 128, `c: _shortbuf` among them *)
  fs_lock : ptr;
  fs_offset : Z;
  fs_codecvt : ptr;
  fs_wide : ptr;
  fs_freeres_list : ptr;
  fs_freeres_buf : ptr;
  fs_mode : Z;           (* `c: _mode`'s bits *)
  fs_total : Z;          (* `c: _total_written` *)
  fs_vtable : ptr
}.

(** The i-th buffer pointer, null past twelve. *)
Definition fs_ptr (st : fstate) (i : nat) : ptr := nth i (fs_ptrs st) null.

(** [file_fields] fb st: owning stream fb's fields, as [fstate] st
    says; `c: _chain` and `c: _prevchain` are [io_list_inv]'s. *)
Definition file_fields (fb : Z) (st : fstate) : iProp Σ :=
  ⌜length (fs_ptrs st) = 12%nat⌝ ∗
  int_cell fb off_flags (fs_flags st) ∗
  ([∗ list] i ↦ p ∈ fs_ptrs st, pcell fb (off_ptr i) p) ∗
  int_cell fb off_fileno (fs_fileno st) ∗ int_cell fb off_flags2 (fs_flags2 st) ∗
  icell fb off_old_offset (fs_old_offset st) ∗
  ⌜length (fs_column st) = 8%nat⌝ ∗ bytes fb off_column (fs_column st) ∗
  pcell fb off_lock (fs_lock st) ∗ icell fb off_offset (fs_offset st) ∗
  pcell fb off_codecvt (fs_codecvt st) ∗ pcell fb off_wide (fs_wide st) ∗
  pcell fb off_freeres_list (fs_freeres_list st) ∗ pcell fb off_freeres_buf (fs_freeres_buf st) ∗
  int_cell fb off_mode (fs_mode st) ∗ icell fb off_total_written (fs_total st) ∗
  pcell fb off_vtable (fs_vtable st).

(** The buffer pointers of a stream with the buffer nb, as glibc
    leaves them between calls: none, or the base and end of the
    buffer and every read and write pointer inside it. *)
Definition buf_ptrs_ok (fb : Z) (nb : nbuf) (ps : list ptr) : Prop :=
  match nb with
  | NbNone | NbFreeres _ => take 8 ps = replicate 8 null
  | NbShort => nth 6 ps null = mkPtr (fb + 131) (Obj fb) /\ nth 7 ps null = mkPtr (fb + 132) (Obj fb) /\
      Forall (fun p => ptr_cap p = Obj fb /\ fb + 131 <= ptr_addr p <= fb + 132) (take 8 ps)
  | NbHeap bb sz => nth 6 ps null = mkPtr bb (Obj bb) /\ nth 7 ps null = mkPtr (bb + sz) (Obj bb) /\
      Forall (fun p => ptr_cap p = Obj bb /\ bb <= ptr_addr p <= bb + sz) (take 8 ps)
  end.

(** What [file_inv] asks of the flags: the magic, a file stream, no
    backup area, and the user-lock and need-lock bits clear, so the
    lock macros take the lock and `c: _IO_ferror` does not. *)
Definition flags_ok (st : fstate) : Prop :=
  0 <= fs_flags st < 2 ^ 32 /\ Z.land (fs_flags st) 4294901760 = io_magic /\
  has (fs_flags st) io_is_filebuf = true /\ has (fs_flags st) io_in_backup = false /\
  has (fs_flags st) io_user_lock = false /\ Z.land (fs_flags2 st) io_need_lock = 0 /\
  (has (fs_flags st) io_unbuffered = true -> has (fs_flags st) io_user_buf = true).

(** The buffer object of [NbHeap], owned with its life, any bytes. *)
Definition buf_own (nb : nbuf) : iProp Σ :=
  match nb with
  | NbHeap bb sz => ∃ breg xs, ⌜r_kind breg = Heap /\ bb + sz <= r_end breg /\ r_end breg <= 2 ^ 63 /\
                               0 < sz /\ length xs = Z.to_nat sz⌝ ∗ live bb breg ∗ bytes bb 0 xs
  | _ => True
  end.

(** [file_inv] ge vb self fp: fp is the stream fb's own pointer, a
    224-byte object whose life is owned, with fields [file_fields]
    whose flags pass [flags_ok], whose jump table is
    `c: __io_vtables` (vb) at the offset its mode allows
    ([mode_vtable]), whose lock is [lock_inv] for the thread self and
    whose buffer pointers fit its narrow buffer ([buf_ptrs_ok]),
    owned by [buf_own]. *)
Definition file_inv (vb : Z) (self fp : ptr) : iProp Σ :=
  ∃ fb freg st nb vt_off held, ⌜fp = mkPtr fb (Obj fb) /\ fb mod 8 = 0 /\ 0 < fb /\
     fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63 /\ flags_ok st /\
     mode_vtable (fs_mode st) vt_off /\ fs_vtable st = mkPtr (vb + vt_off) (Ro vb) /\
     buf_ptrs_ok fb nb (fs_ptrs st)⌝ ∗
    live fb freg ∗ file_fields fb st ∗ lock_inv self (fs_lock st) held ∗ buf_own nb.

(** ## The list of streams *)

(** The head of a list of streams, or null. *)
Definition head_ptr (fs : list ptr) : ptr := match fs with [] => null | f :: _ => f end.

(** [chain_links] prev fs: each stream of fs, in order, has
    `c: _prevchain` the address prev of the link before it and
    `c: _chain` the next stream, the last null. *)
Fixpoint chain_links (prev : ptr) (fs : list ptr) : iProp Σ :=
  match fs with
  | [] => True
  | f :: fs' => ∃ fb, ⌜f = mkPtr fb (Obj fb)⌝ ∗ pcell fb off_prevchain prev ∗
      pcell fb off_chain (head_ptr fs') ∗ chain_links (mkPtr (fb + off_chain) (Obj fb)) fs'
  end.

(** [io_list_inv] ge fs: `c: _IO_list_all`, ge's
    `c: __GI__IO_list_all`, heads the streams fs, linked both ways
    ([chain_links]); `c: list_all_lock` is free, (0, 0, null); and
    `c: run_fp` is null. After `c: _IO_stdfiles_init` fs is stderr,
    stdout, stdin. *)
Definition io_list_inv (ge : genv) (fs : list ptr) : iProp Σ :=
  ∃ la lareg lk lkreg rf rfreg,
    ⌜lookup (TAtom "__GI__IO_list_all") (ge_globals ge) = Some (mkPtr la (Obj la)) /\
     lookup (TAtom "glibc_genops#list_all_lock") (ge_globals ge) = Some (mkPtr lk (Obj lk)) /\
     lookup (TAtom "glibc_genops#run_fp") (ge_globals ge) = Some (mkPtr rf (Obj rf)) /\
     la mod 8 = 0 /\ la + 8 <= r_end lareg /\ rf mod 8 = 0 /\ rf + 8 <= r_end rfreg⌝ ∗
    live la lareg ∗ pcell la 0 (head_ptr fs) ∗ chain_links (mkPtr la (Obj la)) fs ∗
    lock_state lk lkreg 0 0 null ∗ live rf rfreg ∗ pcell rf 0 null.

End inv.
