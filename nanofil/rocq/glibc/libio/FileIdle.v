(** Hello calls `c: fputs`, `c: printf` and `c: close_stdout` one
    after another on the same three streams, and each call relies on
    the state the previous one left. Glibc leaves a stream in a tidy
    state between calls: nobody holds its lock, it writes to one of the
    three standard descriptors, and it keeps no saved or backup input.
    Nothing it has read is waiting to be read again, and output is
    pending only while the stream is in the middle of putting. This
    file names that tidy state, so that each contract can promise it to
    the next call.

    Some fields still change from one call to the next. A narrow print
    may orient the stream, give it a buffer, set its putting,
    line-buffering and error bits, and advance its offset. The idle
    state leaves those fields free. It does keep the stream narrow or
    unoriented, because only `c: wprintf` makes stdout wide, and its
    contract hands stdout back in a separate wide form. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  Pieces Heap StringLogic Logic MemLogic.
From Glibc Require Import Fix FileInv.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

Section idle.
Context `{!gen_heapGS piece pval Σ}.

(** ## The wide data

    A stream that is still narrow already points at objects for wide
    output. Someone must own them before a wide call can use them. *)

(** Every stream points at a `c: struct _IO_wide_data` and a
    `c: struct _IO_codecvt` from the time it is loaded, and
    `c: _IO_fwide` writes them when it first makes the stream wide.
    While the stream is not wide, its owner owns the wide data object
    in the state the linker gives it: 224 zero bytes, which hold the
    wide buffer's pointers and conversion state, and at offset 224
    `c: _wide_vtable`, which points at the wide jump table of
    `c: __io_vtables`. The stream has no conversion object yet, so its
    codecvt pointer is null. Narrow code never reads or writes these
    objects, so every narrow contract passes [wide_idle] through
    unchanged, and a wide call can rely on finding them in this state. *)
Definition wide_idle (vb : Z) (wd cv : ptr) : iProp Σ :=
  ∃ wb wreg, ⌜wd = mkPtr wb (Obj wb) /\ cv = null /\ 0 < wb /\ wb mod 8 = 0 /\
              wb + 232 <= r_end wreg /\ r_end wreg <= 2 ^ 63⌝ ∗
    live wb wreg ∗ bytes wb 0 (replicate 224 0) ∗ auxes wb 0 (replicate 224 CNone) ∗
    pcell wb 224 (mkPtr (vb + vt_wfile) (Ro vb)).

(** ## The buffer

    An idle stream may own a heap buffer that holds pending output.
    The print functions copy into that buffer directly. *)

(** The print functions copy text into the stream's buffer with
    `c: memcpy`, and a copy rewrites the capability slots beside the
    bytes it overwrites. So whoever owns the buffer must own those
    slots too, and the buffer must start on an 8-byte boundary. The
    allocation in `c: _IO_file_doallocate` already provides both. The
    predicate [buf_idle] nb owns the heap buffer, its byte values and
    its slots. A buffer handed to the freeres list is not idle. *)
Definition buf_idle (nb : nbuf) : iProp Σ :=
  match nb with
  | NbNone | NbShort => True
  | NbHeap bb sz =>
      ∃ breg xs cs, ⌜r_kind breg = Heap /\ bb + sz <= r_end breg /\ r_end breg <= 2 ^ 63 /\
                     0 < bb /\ bb mod 8 = 0 /\ 0 < sz /\
                     length xs = Z.to_nat sz /\ Forall (fun x => 0 <= x < 256) xs /\
                     length cs = Z.to_nat sz⌝ ∗
        live bb breg ∗ bytes bb 0 xs ∗ auxes bb 0 cs
  | NbFreeres _ => False
  end.

(** ## The fields

    Most of what makes a stream idle is a fact about its fields. These
    facts decide which branch each libio function takes. *)

(** [idle_ok] fd st collects the facts about the fields of an idle
    stream. The twelve buffer pointers start at `c: _IO_read_ptr`
    (index 0), and the write base, write pointer and write end are
    indices 3, 4 and 5. The saved, backup and marker pointers are
    indices 8, 9 and 11. The input-only stream, descriptor 0, has
    `c: _IO_NO_WRITES` set, and the other two have it clear. *)
Definition idle_ok (fd : Z) (st : fstate) : Prop :=
  (fd = 0 \/ fd = 1 \/ fd = 2) /\ fs_fileno st = fd /\
  (fs_mode st = 0 \/ fs_mode st = 2 ^ 32 - 1) /\
  fs_ptr st 8 = null /\ fs_ptr st 9 = null /\ fs_ptr st 11 = null /\
  fs_ptr st 0 = fs_ptr st 1 /\ fs_ptr st 1 = fs_ptr st 3 /\
  ptr_addr (fs_ptr st 3) <= ptr_addr (fs_ptr st 4) /\
  (ptr_addr (fs_ptr st 3) < ptr_addr (fs_ptr st 4) \/ ptr_addr (fs_ptr st 4) < ptr_addr (fs_ptr st 5) ->
   has (fs_flags st) io_currently_putting = true) /\
  (fd <> 0 -> has (fs_flags st) io_no_writes = false) /\
  has (fs_flags st) io_is_appending = false /\
  Z.land (fs_flags2 st) 2 = 0 /\ Z.land (fs_flags2 st) 32 = 0 /\
  take 2 (fs_column st) = [0; 0].

(** ## An idle stream

    Each output call in Hello takes a stream from its caller and must
    hand it back in a state the next call accepts. This section puts
    that state into one predicate. *)

(** A caller that holds a stream between two calls owns its object,
    its fields, its free lock, its buffer and its wide data. The
    predicate [file_idle] vb self fp fd says that the stream fp writes
    to descriptor fd, that its fields meet [idle_ok], and that it uses
    the narrow jump table. It has the shape of [file_inv] with the
    lock free. *)
Definition file_idle (vb : Z) (self fp : ptr) (fd : Z) : iProp Σ :=
  ∃ fb freg st nb, ⌜fp = mkPtr fb (Obj fb) /\ fb mod 8 = 0 /\ 0 < fb /\
     fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63 /\ flags_ok st /\ idle_ok fd st /\
     fs_vtable st = mkPtr (vb + vt_file) (Ro vb) /\ buf_ptrs_ok fb nb (fs_ptrs st)⌝ ∗
    live fb freg ∗ file_fields fb st ∗ lock_inv self (fs_lock st) None ∗ buf_idle nb ∗
    wide_idle vb (fs_wide st) (fs_codecvt st).

(** Many existing libio proofs ask for a stream in the wider form
    [file_inv]. A caller holding an idle stream can still use them,
    because an idle stream has every part [file_inv] needs. The
    conversion forgets the capability slots and the wide data. *)
Lemma file_idle_inv vb self fp fd : file_idle vb self fp fd ⊢ file_inv vb self fp.
Proof using Type.
  iIntros "(%fb & %freg & %st & %nb & %Hp & Hl & Hf & Hlk & Hb & _)".
  destruct Hp as (? & ? & ? & ? & ? & ? & (_ & _ & Hm & _) & ? & ?).
  iExists fb, freg, st, nb, vt_file, None. iFrame "Hl Hf Hlk". iSplit.
  { iPureIntro. unfold mode_vtable. eauto 20. }
  destruct nb; cbn; try done.
  iDestruct "Hb" as (breg xs cs (? & ? & ? & _ & _ & ? & ? & _ & _)) "(Hl & Hx & _)".
  iExists breg, xs. iFrame. done.
Qed.

End idle.
