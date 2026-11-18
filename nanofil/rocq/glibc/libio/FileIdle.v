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
    `c: _IO_NO_WRITES` set, and the other two have it clear. Every
    standard stream stays on glibc's list of open streams, with
    `c: _IO_LINKED` set, until `c: fclose` unlinks it. Its lock is a
    static object at a nonzero address. *)
Definition idle_ok (fd : Z) (st : fstate) : Prop :=
  (fd = 0 \/ fd = 1 \/ fd = 2) /\ fs_fileno st = fd /\
  (fs_mode st = 0 \/ fs_mode st = 2 ^ 32 - 1) /\
  fs_ptr st 8 = null /\ fs_ptr st 9 = null /\ fs_ptr st 11 = null /\
  fs_ptr st 0 = fs_ptr st 1 /\ fs_ptr st 1 = fs_ptr st 3 /\
  ptr_addr (fs_ptr st 3) <= ptr_addr (fs_ptr st 4) /\
  (ptr_addr (fs_ptr st 3) < ptr_addr (fs_ptr st 4) \/ ptr_addr (fs_ptr st 4) < ptr_addr (fs_ptr st 5) ->
   has (fs_flags st) io_currently_putting = true) /\
  (fd <> 0 -> has (fs_flags st) io_no_writes = false) /\
  has (fs_flags st) io_is_appending = false /\ has (fs_flags st) io_linked = true /\
  Z.land (fs_flags2 st) 2 = 0 /\ Z.land (fs_flags2 st) 32 = 0 /\
  take 2 (fs_column st) = [0; 0] /\ 0 < ptr_addr (fs_lock st).

(** An unbuffered stream writes through its one-byte `c: _shortbuf`
    and keeps nothing in it between calls. Glibc gives that buffer only
    to an unbuffered stream, and it never makes an unbuffered stream
    line-buffered or gives it a heap buffer: `c: setvbuf` clears
    `c: _IO_LINE_BUF` and frees the heap buffer when it makes a stream
    unbuffered, and `c: _IO_file_doallocate`, which sets the line bit
    for a terminal, runs only for a buffered stream. The overflow
    function sets the write end of an unbuffered stream to its write
    pointer, and `c: new_do_write` sets the write base, the write
    pointer and the write end to the buffer's base, whether the write
    succeeds or fails. The write base therefore stays at the start of
    `c: _shortbuf`, so the next byte goes into that buffer. So the stream has no pending output and no room,
    and the next call never copies into the buffer.

    A stream that only writes keeps its read base and its write base at
    the start of its heap buffer. Its first overflow sets the read
    pointers and the write pointers to the buffer's base, and every
    flush by `c: new_do_write` sets them there again. A stream without a
    buffer has never written, so it is not putting. Its heap buffer
    comes from `c: _IO_file_doallocate`, whose call of `c: _IO_setb`
    clears `c: _IO_USER_BUF`, so closing the stream frees the buffer. Nor is a stream
    that may not be written, because the overflow function returns
    before it sets the putting bit of such a stream. A writable stream
    gets its heap buffer from that overflow, which sets the putting
    bit, and no output call clears the bit again. So a writable stream
    with a heap buffer is putting. The predicate
    [short_idle] nb st states these facts for the stream's buffer nb. *)
Definition short_idle (nb : nbuf) (st : fstate) : Prop :=
  ((has (fs_flags st) io_unbuffered = true -> has (fs_flags st) io_line_buf = false) /\
   (has (fs_flags st) io_no_writes = true -> has (fs_flags st) io_currently_putting = false)) /\
  match nb with
  | NbShort => has (fs_flags st) io_unbuffered = true /\
      fs_ptr st 4 = fs_ptr st 3 /\ fs_ptr st 5 = fs_ptr st 4 /\ fs_ptr st 3 = fs_ptr st 6
  | NbHeap _ _ => has (fs_flags st) io_unbuffered = false /\
      fs_ptr st 2 = fs_ptr st 6 /\ fs_ptr st 3 = fs_ptr st 6 /\ has (fs_flags st) io_user_buf = false /\
      (has (fs_flags st) io_no_writes = false -> has (fs_flags st) io_currently_putting = true)
  | NbNone => has (fs_flags st) io_currently_putting = false
  | NbFreeres _ => True
  end.

(** ## An idle stream

    Each output call in Hello takes a stream from its caller and must
    hand it back in a state the next call accepts. This section puts
    that state into one predicate. *)

(** A caller that holds a stream between two calls owns the whole
    stream: its object, its fields, its free lock, its buffer and its
    wide data. The stream writes to one descriptor and uses the narrow
    jump table. Its fields meet the facts above, and so do its buffer
    and its unbuffered bit. The predicate [file_idle] vb self fp fd
    says all this for the stream fp and the descriptor fd. It has the
    shape of [file_inv] with the lock free. *)
Definition file_idle (vb : Z) (self fp : ptr) (fd : Z) : iProp Σ :=
  ∃ fb freg st nb, ⌜fp = mkPtr fb (Obj fb) /\ fb mod 8 = 0 /\ 0 < fb /\
     fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63 /\ flags_ok st /\ idle_ok fd st /\
     fs_vtable st = mkPtr (vb + vt_file) (Ro vb) /\ buf_ptrs_ok fb nb (fs_ptrs st) /\
     short_idle nb st⌝ ∗
    live fb freg ∗ file_fields fb st ∗ lock_inv self (fs_lock st) None ∗ buf_idle nb ∗
    wide_idle vb (fs_wide st) (fs_codecvt st).

(** Many existing libio proofs ask for a stream in the wider form
    [file_inv]. A caller holding an idle stream can still use them,
    because an idle stream has every part [file_inv] needs. The
    conversion forgets the capability slots and the wide data. *)
Lemma file_idle_inv vb self fp fd : file_idle vb self fp fd ⊢ file_inv vb self fp.
Proof using Type.
  iIntros "(%fb & %freg & %st & %nb & %Hp & Hl & Hf & Hlk & Hb & _)".
  destruct Hp as (? & ? & ? & ? & ? & ? & (_ & _ & Hm & _) & ? & ? & _).
  iExists fb, freg, st, nb, vt_file, None. iFrame "Hl Hf Hlk". iSplit.
  { iPureIntro. unfold mode_vtable. eauto 20. }
  destruct nb; cbn; try done.
  iDestruct "Hb" as (breg xs cs (? & ? & ? & _ & _ & ? & ? & _ & _)) "(Hl & Hx & _)".
  iExists breg, xs. iFrame. done.
Qed.

End idle.
