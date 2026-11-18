(** Hello prints its greeting with `c: wprintf`, which turns stdout into
    a wide stream before it writes anything. From then on the stream
    keeps its wide characters in a second buffer, converts them to bytes
    through the C locale's ASCII step, and hands the bytes to its narrow
    buffer and the descriptor. The call that closes stdout at exit must
    accept the stream in that state. This file names the state a wide
    stream is in between two calls, as [file_idle] in
    [FileIdle](FileIdle.v) names it for a narrow stream.

    A wide stream still has the narrow fields that the close path reads,
    and they obey the same rules as before, except that the mode is 1
    and the jump table is the wide one. The wide data object now holds the wide buffer's
    pointers and the two conversion descriptors that glibc fills in when
    it first makes the stream wide. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  Pieces Heap StringLogic Logic MemLogic.
From Glibc Require Import Fix FileInv FileIdle.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** ## The wide data object

    The wide data object of a stream is 232 bytes long. The offsets
    below come from glibc's `c: struct _IO_wide_data`, and the file
    [LibioXsputnLayout](LibioXsputnLayout.v) records the same layout as
    the compiler laid it out. *)

(** The wide buffer's eleven pointers start the object, in the order of
    the narrow ones: read pointer, read end, read base, write base,
    write pointer, write end, buffer base, buffer end, save base, backup
    base and save end. *)
Definition woff_ptr (i : nat) : Z := 8 * Z.of_nat i.

(** The conversion state `c: _IO_state` sits at offset 88 and
    `c: _IO_last_state` at 96. *)
Definition woff_state : Z := 88.

(** The conversion descriptors start at 104. Each `c: _IO_iconv_t` is a
    step pointer followed by 48 bytes of step data, so the output
    descriptor starts at 160. *)
Definition woff_cd_in : Z := 104.
Definition woff_cd_out : Z := 160.

(** The one-character `c: _shortbuf` of an unbuffered wide stream sits
    at 216, and the wide jump table's pointer at 224. *)
Definition woff_shortbuf : Z := 216.
Definition woff_vtable : Z := 224.

(** The step data flags that `c: _IO_fwide` writes. The input side is
    the last step of its chain, and the output side also
    transliterates. A conversion of an illegal character may set bit 30,
    `c: __GCONV_ENCOUNTERED_ILLEGAL_INPUT`, on the output side. *)
Definition gconv_is_last : Z := 1.
Definition gconv_translit : Z := 8.
Definition gconv_illegal_seen : Z := 2 ^ 30.

Section wide.
Context `{!gen_heapGS piece pval Σ}.

(** ## One conversion descriptor

    When glibc makes a stream wide, it copies the locale's conversion
    steps into two descriptors and gives each some fixed bookkeeping.
    Each later conversion writes the output descriptor's buffer bounds,
    its flags and its call counter, so the predicate below leaves those
    values free. *)

(** A descriptor names a conversion step and keeps the output bounds,
    flags and call count of the conversion in progress. The predicate
    [iconv_cell] wd o step ob oe fl n owns the descriptor at offset o of
    the wide data object wd, with those values. The descriptor marks
    the conversion as internal and points its state at the stream's
    conversion state. Nobody reads its own state field, so the
    predicate keeps that field as eight bytes of any value. *)
Definition iconv_cell (wd o : Z) (step ob oe : ptr) (fl n : Z) : iProp Σ :=
  ∃ st, ⌜length st = 8%nat⌝ ∗
    pcell wd o step ∗ pcell wd (o + 8) ob ∗ pcell wd (o + 16) oe ∗
    int_cell wd (o + 24) fl ∗ int_cell wd (o + 28) n ∗ int_cell wd (o + 32) 1 ∗
    bytes wd (o + 36) [0; 0; 0; 0] ∗
    pcell wd (o + 40) (mkPtr (wd + woff_state) (Obj wd)) ∗ bytes wd (o + 48) st.

(** ## The wide buffer

    A wide stream gets its wide buffer on its first output. Until then
    every wide pointer is null. An unbuffered stream uses its
    one-character `c: _shortbuf`, and any other stream a heap buffer
    that `c: _IO_wfile_doallocate` allocates. *)

(** A wide stream has no wide buffer yet, or it uses the short buffer
    inside its wide data object, or it owns the heap object wb of wsz
    bytes. *)
Inductive wbuf : Type :=
| WbNone
| WbShort
| WbHeap (wb wsz : Z).

(** A wide cursor must stay inside its buffer and on a character
    boundary, because `c: _IO_wfile_overflow` stores four bytes at the
    write pointer after testing only that it differs from the buffer's
    end. The predicate [wcursor] b e c p says that the pointer p into the
    buffer [b, e) with capability c lies between b and e, a whole number
    of wide characters past b. *)
Definition wcursor (b e : Z) (c : cap) (p : ptr) : Prop :=
  ptr_cap p = c /\ b <= ptr_addr p <= e /\ (ptr_addr p - b) mod 4 = 0.

(** Every path that touches the wide pointers sets the read pointer,
    the read end, the read base and the write base to the buffer's
    base, and only the write pointer and the write end move. The write
    end is the base on a line-buffered or unbuffered stream, so the
    write pointer can pass it, and is the buffer's end otherwise. The
    predicate [wbuf_at] b e c ps says this for the buffer [b, e). *)
Definition wbuf_at (b e : Z) (c : cap) (ps : list ptr) : Prop :=
  take 4 ps = replicate 4 (mkPtr b c) /\ wcursor b e c (nth 4 ps null) /\ wcursor b e c (nth 5 ps null) /\
  nth 6 ps null = mkPtr b c /\ nth 7 ps null = mkPtr e c.

(** The predicate [wbuf_ptrs_ok] wd w ps says where the eleven wide
    pointers ps point for the wide buffer w of the wide data object wd.
    A stream without a wide buffer has them all null. The short buffer
    holds one character at wd + 216, and a heap buffer is the object wb
    of wsz bytes. The save, backup and save-end pointers stay null,
    because the wide write path never backs up. *)
Definition wbuf_ptrs_ok (wd : Z) (w : wbuf) (ps : list ptr) : Prop :=
  length ps = 11%nat /\ drop 8 ps = replicate 3 null /\
  match w with
  | WbNone => take 8 ps = replicate 8 null
  | WbShort => wbuf_at (wd + woff_shortbuf) (wd + woff_shortbuf + 4) (Obj wd) ps
  | WbHeap wb wsz => wbuf_at wb (wb + wsz) (Obj wb) ps
  end.

(** Closing a wide stream frees its wide buffer with `c: _IO_wsetb`,
    unless bit 8 of `c: _flags2`, `c: _IO_FLAGS2_USER_WBUF`, says the
    stream does not own it. `c: _IO_wdoallocbuf` sets that bit when it
    gives an unbuffered stream its short buffer, and
    `c: _IO_wfile_doallocate` clears it for a heap buffer. The
    predicate [wbuf_user_ok] w f2 records this for the wide buffer w
    and the flags f2, so that the close never frees a pointer into the
    wide data object and always frees the heap buffer it owns. *)
Definition wbuf_user_ok (w : wbuf) (f2 : Z) : Prop :=
  match w with
  | WbNone => True
  | WbShort => Z.land f2 8 = 8
  | WbHeap _ _ => Z.land f2 8 = 0
  end.

(** The predicate [wbuf_idle] w owns a heap wide buffer: its life, its
    bytes and its capability slots, as [buf_idle] does for a narrow
    one. The allocation is 8-aligned and holds whole wide characters. *)
Definition wbuf_idle (w : wbuf) : iProp Σ :=
  match w with
  | WbNone | WbShort => True
  | WbHeap wb wsz =>
      ∃ wreg xs cs, ⌜r_kind wreg = Heap /\ wb + wsz <= r_end wreg /\ r_end wreg <= 2 ^ 63 /\
                     0 < wb /\ wb mod 8 = 0 /\ 0 < wsz /\ wsz mod 4 = 0 /\
                     length xs = Z.to_nat wsz /\ Forall (fun x => 0 <= x < 256) xs /\
                     length cs = Z.to_nat wsz⌝ ∗
        live wb wreg ∗ bytes wb 0 xs ∗ auxes wb 0 cs
  end.

(** ## Who owns the wide data

    The owner of a wide stream owns its whole wide data object. The
    predicate splits the object into the fields the wide functions read
    and write. *)

(** Each wide call reads and writes some of these fields, and the
    close path frees the wide buffer, so the stream's owner must hold
    them all. The predicate [wide_data_at] owns the wide data with a
    given region and pointer list. Its eleven
    pointers point into that buffer as described above. Both conversion states stay zero, because the C
    locale's ASCII steps keep no state. The input descriptor runs the
    step tw and the output descriptor runs the step tm. The short
    buffer holds four bytes of any value, and the jump table pointer
    still holds the wide table that the linker put there. The owner
    also holds the capability slots of the states and of the short
    buffer, because `c: memset` and a copy into the short buffer
    rewrite them. *)
Definition wide_data_at (vb : Z) (tw tm : ptr) (wd : Z) (w : wbuf) (wreg : region) (ps : list ptr) : iProp Σ :=
  ∃ ib ie ob oe ifl icnt ofl ocnt sb scs,
    ⌜0 < wd /\ wd mod 8 = 0 /\ wd + 232 <= r_end wreg /\ r_end wreg <= 2 ^ 63 /\
     wbuf_ptrs_ok wd w ps /\ ifl = gconv_is_last /\
     (ofl = Z.lor gconv_is_last gconv_translit \/
      ofl = Z.lor (Z.lor gconv_is_last gconv_translit) gconv_illegal_seen) /\
     length sb = 4%nat /\ Forall (fun x => 0 <= x < 256) sb /\ length scs = 8%nat⌝ ∗
    live wd wreg ∗ ([∗ list] i ↦ p ∈ ps, pcell wd (woff_ptr i) p) ∗
    bytes wd woff_state (replicate 16 0) ∗ auxes wd woff_state (replicate 16 CNone) ∗
    iconv_cell wd woff_cd_in tw ib ie ifl icnt ∗ iconv_cell wd woff_cd_out tm ob oe ofl ocnt ∗
    bytes wd woff_shortbuf sb ∗ bytes wd (woff_shortbuf + 4) [0; 0; 0; 0] ∗ auxes wd woff_shortbuf scs ∗
    pcell wd woff_vtable (mkPtr (vb + vt_wfile) (Ro vb)) ∗ wbuf_idle w.

(** Between calls, the stream keeps its wide data without exposing the
    pointer list. A writer opens it to read the base and cursor that
    determine how many characters it passes to conversion. *)
Definition wide_data (vb : Z) (tw tm : ptr) (wd : Z) (w : wbuf) : iProp Σ :=
  ∃ wreg ps, wide_data_at vb tw tm wd w wreg ps.

(** ## A wide stream between calls

    Hello's exit path closes stdout, and it reads the narrow fields of
    stdout whether or not the stream is wide. This section states the
    facts it needs for a wide stream, which are the narrow ones with
    the mode set aside. *)

(** The function [with_mode0] replaces the mode of the fields st by 0,
    so that a wide stream can meet [idle_ok] in this form. *)
Definition with_mode0 (st : fstate) : fstate :=
  mkFstate (fs_flags st) (fs_ptrs st) (fs_fileno st) (fs_flags2 st) (fs_old_offset st) (fs_column st)
    (fs_lock st) (fs_offset st) (fs_codecvt st) (fs_wide st) (fs_freeres_list st) (fs_freeres_buf st)
    0 (fs_total st) (fs_vtable st).

(** The narrow buffer of a wide stream follows the rules of wide mode,
    which are not those of an idle narrow stream. The first wide output
    rewinds the narrow cursors to the buffer's base but sets the narrow
    write end to the buffer's end, and only a write of converted bytes
    moves it back, so a wide output that ends without writing leaves it
    there. And `c: _IO_doallocbuf` calls the wide stream's allocator
    even when the stream is unbuffered, so an unbuffered wide stream can
    own a narrow heap buffer, and the terminal test inside
    `c: _IO_file_doallocate` can make it line-buffered as well. No wide
    call stores into the narrow buffer through the extra room:
    `c: _IO_wdo_write` converts through a stack buffer whenever the
    narrow buffer has fewer than sixteen bytes free.

    The predicate [wflags_ok] st keeps the parts of [flags_ok] that do
    not concern buffering: the magic, the file-buffer bit, no backup
    area, and the user-lock and need-lock bits clear. *)
Definition wflags_ok (st : fstate) : Prop :=
  0 <= fs_flags st < 2 ^ 32 /\ Z.land (fs_flags st) 4294901760 = io_magic /\
  has (fs_flags st) io_is_filebuf = true /\ has (fs_flags st) io_in_backup = false /\
  has (fs_flags st) io_user_lock = false /\ Z.land (fs_flags2 st) io_need_lock = 0.

(** The predicate [wshort_ok] nb st states what wide mode keeps of the
    narrow buffer nb. A stream that cannot write is not putting. The
    one-byte short buffer, which only a stream unbuffered before it
    became wide can have, is marked as a user buffer, so that closing
    the stream does not free it, and its write pointer is its base. A
    heap buffer is not a user buffer, so that closing frees it, and its
    read base and write base are its base. *)
Definition wshort_ok (nb : nbuf) (st : fstate) : Prop :=
  (has (fs_flags st) io_no_writes = true -> has (fs_flags st) io_currently_putting = false) /\
  match nb with
  | NbShort => has (fs_flags st) io_user_buf = true /\ fs_ptr st 4 = fs_ptr st 3 /\ fs_ptr st 3 = fs_ptr st 6
  | NbHeap _ _ => has (fs_flags st) io_user_buf = false /\ fs_ptr st 2 = fs_ptr st 6 /\ fs_ptr st 3 = fs_ptr st 6
  | NbNone => has (fs_flags st) io_currently_putting = false
  | NbFreeres _ => True
  end.

(** An idle narrow stream meets the wide-mode rules, so orienting a
    stream keeps them. The short buffer's user-buffer mark comes from
    [flags_ok], since only an unbuffered stream has that buffer. *)
Lemma idle_wide_rules fb nb st : flags_ok st -> buf_ptrs_ok fb nb (fs_ptrs st) ->
  short_idle nb st -> wflags_ok st /\ wshort_ok nb st.
Proof using Type.
  unfold flags_ok, wflags_ok, short_idle, wshort_ok. intros (? & ? & ? & ? & ? & ? & Hub) Hb Hs.
  split; [tauto|]. destruct nb; try tauto.
  destruct Hs as (? & Hu & ? & _ & ?). destruct (Hub Hu) as [|Hn]; [tauto|]. exfalso.
  destruct Hb as (Hsix & _). unfold fs_ptr in *.
  rewrite <- (take_drop 8 (fs_ptrs st)), app_nth1, Hn in Hsix;
    [| rewrite length_take; destruct (Nat.min_spec 8 (length (fs_ptrs st))) as [[? ->]|[? ->]]; try lia;
       apply (f_equal (@length ptr)) in Hn; rewrite length_take length_replicate in Hn; lia].
  cbn in Hsix. discriminate.
Qed.

(** A caller that holds a wide stream between two calls owns all of it,
    as it would own a narrow one. The predicate [file_wide_at] owns the
    wide stream on the given descriptor: its object, its
    fields, its free lock, its narrow buffer and its wide data. The
    narrow buffer obeys the wide-mode rules of [wshort_ok]. It may still
    hold bytes written before the stream became wide, because
    [file_idle] does not rule them out, and the first wide output
    drops them when it rewinds the narrow cursors. The stream's mode is
    1, its jump table is the wide one, and its codecvt pointer names the
    descriptors inside its wide data. Its `c: _flags2` says whether it
    owns its wide buffer, as [wbuf_user_ok] states. The descriptors run
    the C locale's conversion steps, which glibc calls `c: to_wc` and
    `c: to_mb`. A stream without a narrow buffer has no wide buffer
    either, because orientation leaves the wide buffer empty and the
    wide allocation gives the stream a narrow buffer first. *)
Definition file_wide_at (ge : genv) (vb : Z) (self fp : ptr) (fd fb : Z) (freg : region)
    (st : fstate) (nb : nbuf) (wd : Z) (w : wbuf) (tw tm : ptr) (data : iProp Σ) : iProp Σ :=
    ⌜fp = mkPtr fb (Obj fb) /\ fb mod 8 = 0 /\ 0 < fb /\
     fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63 /\ wflags_ok st /\
     idle_ok fd (with_mode0 st) /\ fs_mode st = 1 /\
     fs_vtable st = mkPtr (vb + vt_wfile) (Ro vb) /\ buf_ptrs_ok fb nb (fs_ptrs st) /\
     wshort_ok nb st /\ wbuf_user_ok w (fs_flags2 st) /\
     fs_wide st = mkPtr wd (Obj wd) /\ fs_codecvt st = mkPtr (wd + woff_cd_in) (Obj wd) /\
     lookup (TAtom "glibc_wcsmbsload#to_wc") (ge_globals ge) = Some tw /\
     lookup (TAtom "glibc_wcsmbsload#to_mb") (ge_globals ge) = Some tm /\
     (nb = NbNone -> w = WbNone)⌝ ∗
    live fb freg ∗ file_fields fb st ∗ lock_inv self (fs_lock st) None ∗ buf_idle nb ∗ data.

(** An idle wide stream hides the values of its fields. A caller that
    has just read the wide cursors can use [file_wide_at] with
    [wide_data_at] to keep their values until the call. *)
Definition file_wide (ge : genv) (vb : Z) (self fp : ptr) (fd : Z) : iProp Σ :=
  ∃ fb freg st nb wd w tw tm,
    file_wide_at ge vb self fp fd fb freg st nb wd w tw tm (wide_data vb tw tm wd w).

(** ## The wide jump table

    A wide stream's calls go through the wide jump table of
    `c: __io_vtables`, which starts at [vt_wfile]. The wide printf
    proof calls the table's xsputn slot directly, so it needs to know
    which function that slot holds. *)

(** The slots of the wide jump table that Hello's wide path reads, with
    the function each holds in Hello's image. The table shares its
    finish, write, close and stat functions with the narrow one. *)
Definition wfile_jumps : list (Z * string) :=
  [(slot_finish, "_IO_new_file_finish"); (slot_overflow, "__GI__IO_wfile_overflow");
   (slot_xsputn, "__GI__IO_wfile_xsputn"); (slot_sync, "__GI__IO_wfile_sync");
   (slot_doallocate, "_IO_wfile_doallocate");
   (slot_write, "_IO_new_file_write"); (slot_close, "__GI__IO_file_close");
   (slot_stat, "__GI__IO_file_stat")].

(** The predicate [wvtables_ro] ge vb holds a persistent read-only
    share of each slot in [wfile_jumps], as [vtables_ro] does for the
    narrow table. The share of the table's life comes from
    [vtables_ro]. *)
Definition wvtables_ro (ge : genv) (vb : Z) : iProp Σ :=
  [∗ list] sl ∈ wfile_jumps, pcellq DfracDiscarded vb (vt_wfile + sl.1) (sym_ptr ge sl.2).

(** A caller keeps the shares across every call, because nobody writes
    the table. *)
Global Instance wvtables_ro_persistent ge vb : Persistent (wvtables_ro ge vb).
Proof using Type. rewrite /wvtables_ro /pcellq. apply _. Qed.

(** One slot of the wide table, read from [wvtables_ro]. *)
Lemma wvtables_slot ge vb sl n :
  In (sl, n) wfile_jumps -> wvtables_ro ge vb -∗ pcellq DfracDiscarded vb (vt_wfile + sl) (sym_ptr ge n).
Proof using Type.
  iIntros (Hin) "Hs". apply list_elem_of_In in Hin.
  iApply (big_sepL_elem_of (fun sl => pcellq DfracDiscarded vb (vt_wfile + sl.1) (sym_ptr ge sl.2)) _ (sl, n)
            with "Hs"). exact Hin.
Qed.

End wide.
