(** GNU Hello prints through `c: fprintf`, `c: printf`, `c: error` and
    the diagnostics of `c: getopt`, and all of them reach glibc's
    `c: __vfprintf_internal`. This module states the contracts of the
    formatter and of the functions it is built from, in one place, so
    that every proof and every caller reads the same statements.

    The contracts say that a call is safe and that it gives back what
    it was lent. They say nothing about the bytes that reach the
    stream. That is all Hello's proof needs of a print.

    The formatter's contract covers the formats that Hello uses. Such a
    format is literal text with the conversions `%s`, `%c`, `%d` and
    `%%`, and none of them has a flag, a width or a precision. The
    grammar of [NarrowFormat](NarrowFormat.v) describes exactly these
    formats, and its parser is a function, so a caller shows that a
    constant format is covered by computing the parser on its bytes. *)

From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic MemLogic VariadicLogic.
From Glibc Require Import Fix OsBlocks OsWorld AllocRo FileInv FileIdle LibioFputsSpec WordString PrintfStreamInv
  FileTidy FxprintfStream NarrowFormat NarrowArgs FormatterCode FormatterStringTable CStruct PrintfLayout PrintfOut StrchrnulLogic.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

(** ## The formatter's read-only data *)

Definition jump_table : string := "glibc_vfprintf_internal#jump_table".
Definition step0_jumps : string := "glibc_vfprintf_internal#__printf_buffer.step0_jumps.277".

(** The function [loaded_bytes] reads the bytes of a data object of
    the captured unit. It reads them from the memory that the loader
    builds for the formatter's two tables. *)
Definition loaded_bytes (n : string) : list Z :=
  match lookup (TAtom n) (fst formatter_tables_loaded),
        find (fun i => match i with IData m _ _ _ => term_eqb m (TAtom n) | _ => false end) formatter_string_tables with
  | Some p, Some (IData _ _ _ items) =>
      map (fun i => load_bytes (snd formatter_tables_loaded) (ptr_addr p + Z.of_nat i) 1)
        (seq 0 (Z.to_nat (items_size items)))
  | _, _ => []
  end.

Definition jump_table_bytes : list Z := Eval vm_compute in loaded_bytes jump_table.
Definition step0_jumps_bytes : list Z := Eval vm_compute in loaded_bytes step0_jumps.

(** The conversion `%d` turns a number into text with
    `c: _itoa_word`, which reads each digit's character from a table
    in another unit. The table holds the ten digits and then the 26
    lower-case letters, for bases up to 36. The linked program knows
    it under the name below. *)
Definition lower_digits : string := "__GI__itoa_lower_digits".
Definition lower_digits_bytes : list Z :=
  Eval vm_compute in map (fun i => 48 + Z.of_nat i) (seq 0 10) ++ map (fun i => 97 + Z.of_nat i) (seq 0 26).

(** The conversion `%s` prints this constant for a null argument. Its
    characters spell `(null)`. *)
Definition null_text : string := "glibc_vfprintf_internal#null".
Definition null_text_bytes : list Z := [40; 110; 117; 108; 108; 41].

(** The function [table_bytes] gives the bytes of one of the
    formatter's tables: its two dispatch tables and the table of
    digits. *)
Definition table_bytes (n : string) : list Z :=
  if String.eqb n jump_table then jump_table_bytes else
  if String.eqb n step0_jumps then step0_jumps_bytes else
  if String.eqb n lower_digits then lower_digits_bytes else [].

(** Each table has its bytes, so the definition above did not fall
    back to the empty list. *)
Lemma table_bytes_sizes :
  (length (table_bytes jump_table), length (table_bytes step0_jumps), length (table_bytes lower_digits)) =
  (91, 128, 36)%nat.
Proof. vm_compute. reflexivity. Qed.

Section spec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The linked program has the table n, and anyone may read its bytes. *)
Definition ro_table (n : string) : iProp Σ :=
  ∃ b reg, ⌜lookup (TAtom n) (ge_globals ge) = Some (mkPtr b (Ro b)) /\ 0 < b /\
            b + Z.of_nat (length (table_bytes n)) <= r_end reg /\ r_end reg <= 2 ^ 63⌝ ∗
    liveq DfracDiscarded b reg ∗ bytesq DfracDiscarded b 0 (table_bytes n).

(** The global n holds a null pointer, and nobody can write it. *)
Definition null_global (n : string) : iProp Σ :=
  ∃ b reg, ⌜lookup (TAtom n) (ge_globals ge) = Some (mkPtr b (Obj b)) /\ 0 < b /\ b mod 8 = 0 /\
            b + 8 <= r_end reg /\ r_end reg <= 2 ^ 63⌝ ∗
    liveq DfracDiscarded b reg ∗ pcellq DfracDiscarded b 0 null.

(** The global n is a string constant with the characters s, and
    anyone may read it. *)
Definition ro_string (n : string) (s : list Z) : iProp Σ :=
  ∃ b, ⌜lookup (TAtom n) (ge_globals ge) = Some (mkPtr b (Ro b))⌝ ∗ word_string DfracDiscarded (mkPtr b (Ro b)) s.

(** The formatter reads its two dispatch tables, and the conversion
    `%d` reads the table of digits. The conversion `%s` prints the
    constant `(null)` when its argument is the null pointer. The
    formatter also reads three globals that are null while the program
    has registered no conversion of its own, and Hello registers
    none. *)
Definition printf_ro : iProp Σ :=
  ro_table jump_table ∗ ro_table step0_jumps ∗ ro_table lower_digits ∗
  ro_string null_text null_text_bytes ∗
  null_global "__printf_function_table" ∗ null_global "__printf_modifier_table" ∗
  null_global "__printf_va_arg_table".

(** A caller keeps the formatter's read-only data across a call,
    because anyone may read it at any time. *)
#[global] Instance printf_ro_persistent : Persistent printf_ro.
Proof using Type. rewrite /printf_ro /ro_table /ro_string /null_global. apply _. Qed.

(** ## Arguments *)

(** The formatter's arguments are the string arguments [str_arg] of
    [WordString](../string/WordString.v): integers, null pointers and
    pointers into read-only strings. *)

(** The argument cursor ap points skip bytes into a snapshot of the
    call's arguments xs, past the named ones. The cursor is an object
    of its own at an 8-aligned address, and the formatter loads a
    pointer from it. That pointer does not point past the end of the
    snapshot. *)
Definition va_at (ap : ptr) (skip : Z) (xs : list word) : iProp Σ :=
  ∃ cb sb, ⌜ap = mkPtr cb (Obj cb) /\ 0 < cb /\ cb mod 8 = 0 /\ cb + 32 <= 2 ^ 48 /\ 0 < sb /\ sb mod 16 = 0 /\
            sb + req_extent (fx_req xs) <= 2 ^ 48 /\ 0 <= skip <= 8 * Z.of_nat (length xs)⌝ ∗
    pts (va_cursor_ps cb (mkRegion cb (cb + 32) Heap Live) (mkPtr (sb + skip) (Ro sb))) ∗
    pts (snapshot_ps xs sb (fx_req xs)).

(** ## The formatter *)

(** The record [vfp_in] is the logical input of a call of the
    formatter. *)
Record vfp_in : Type := VfpIn {
  vi_vb : Z;                      (* the stream jump tables *)
  vi_fp : ptr;                    (* the stream *)
  vi_fd : Z;                      (* the stream's descriptor *)
  vi_flags2 : Z; vi_held : option Z;
  vi_fmt : ptr; vi_dq : dfrac; vi_bytes : list Z;
  vi_ds : list narrow_directive;  (* the parsed format *)
  vi_ap : ptr; vi_skip : Z; vi_xs : list word; vi_rest : list word;
  vi_eb : Z                       (* errno *)
}.

(** The formatter is safe only for some formats and arguments, and
    the predicate [vfp_fits] collects what it needs of them. The
    format must parse in the narrow grammar. The arguments after the
    named ones must fit its conversions: a pointer for each `%s` and an
    integer for each `%c` and `%d`. The cursor must stand at the start
    of an argument, and each argument is 8 bytes wide. When the buffer
    is full the formatter writes to the stream's descriptor, so that
    descriptor must be open. The formatter saves errno when it starts,
    and it reads errno through the global `c: __libc_errno`, so this
    global must be the errno cell of the thread. *)
Definition vfp_fits (x : vfp_in) : Prop :=
  parse_narrow (vi_bytes x) = Some (vi_ds x) /\
  narrow_fits (vi_ds x) (skipn (Z.to_nat (vi_skip x / 8)) (vi_xs x)) (vi_rest x) /\
  0 <= vi_skip x /\ vi_skip x mod 8 = 0 /\
  ow_errno w0 = Some (mkPtr (vi_eb x) (Obj (vi_eb x))) /\ In (vi_fd x) (ow_fds w0) /\
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr (vi_eb x) (Obj (vi_eb x))).

(** This is the contract of `c: __vfprintf_internal (fp, fmt, ap, 0)`.
    The call is safe when the format and the arguments meet [vfp_fits]
    and the stream is tidy. Each argument after the named ones must be
    an integer, null or a read-only string. The contract asks nothing
    of the named arguments that the cursor has already passed, because
    the formatter never reads them.

    The caller also lends three kinds of read-only data. The first is
    the formatter's own tables, [printf_ro]. The second is what
    `c: fputs` reads as well, [fputs_ro]: the stream's jump table and
    the flag that says the process has one thread. The third is what
    `c: malloc` reads, [malloc_ro] of [AllocRo](../stdlib/AllocRo.v).
    The formatter needs it because a stream gets its buffer on its
    first write, and the buffer comes from `c: malloc`.

    The function returns an int and gives back the format and errno.
    It gives back the stream as tidy as it got it, with the same
    descriptor, the same second flags word and the same lock state. *)
Definition vfprintf_spec : fspec Σ :=
  FSpec vfp_in
    (fun x => [WPtr (vi_fp x); WPtr (vi_fmt x); WPtr (vi_ap x); WInt 0])
    (fun x =>
       ⌜vfp_fits x⌝ ∗
       file_tidy (vi_vb x) (ow_self w0) (vi_fp x) (vi_fd x) (vi_flags2 x) (vi_held x) ∗
       word_string (vi_dq x) (vi_fmt x) (vi_bytes x) ∗ va_at (vi_ap x) (vi_skip x) (vi_xs x) ∗
       ([∗ list] a ∈ skipn (Z.to_nat (vi_skip x / 8)) (vi_xs x), str_arg a) ∗ errno_any (vi_eb x) ∗
       printf_ro ∗ fputs_ro (vi_vb x) ∗ malloc_ro)%I
    (fun x o =>
       ∃ n, ⌜o = Ret (WInt n) /\ 0 <= n < 2 ^ 32⌝ ∗
       file_tidy (vi_vb x) (ow_self w0) (vi_fp x) (vi_fd x) (vi_flags2 x) (vi_held x) ∗
       word_string (vi_dq x) (vi_fmt x) (vi_bytes x) ∗ errno_any (vi_eb x))%I.

(** ## The variadic wrappers *)

(** A program does not call the formatter itself. It calls
    `c: fprintf` or `c: printf`, and each of them is a few instructions
    around one call of the formatter. A variadic function gets a
    read-only copy of all its arguments on entry. Each wrapper points a
    cursor past the named arguments in that copy and passes the cursor
    on. The contracts below are therefore the formatter's contract
    without the cursor, stated over the arguments of the call. A
    program calls a wrapper on a stream that it has not locked, so the
    contracts take an idle stream and give one back. *)

(** The record [pf_in] is the logical input of a call of a wrapper.
    Its field pf_ys holds the arguments after the format. *)
Record pf_in : Type := PfIn {
  pf_vb : Z;                      (* the stream jump tables *)
  pf_fp : ptr;                    (* the stream *)
  pf_fd : Z;                      (* the stream's descriptor *)
  pf_fmt : ptr; pf_dq : dfrac; pf_bytes : list Z;
  pf_ds : list narrow_directive;  (* the parsed format *)
  pf_ys : list word; pf_rest : list word;
  pf_eb : Z                       (* errno *)
}.

(** A wrapper asks of the format and its arguments what the formatter
    asks. The format must parse in the narrow grammar. The arguments
    after the format must fit its conversions. The entry copy holds
    only integers and pointers, so each argument must be one of the
    two. The stream's descriptor must be open, and the global
    `c: __libc_errno` must be the errno cell of the thread. *)
Definition pf_fits (x : pf_in) : Prop :=
  parse_narrow (pf_bytes x) = Some (pf_ds x) /\ narrow_fits (pf_ds x) (pf_ys x) (pf_rest x) /\
  forallb snapshot_word (pf_ys x) = true /\
  ow_errno w0 = Some (mkPtr (pf_eb x) (Obj (pf_eb x))) /\ In (pf_fd x) (ow_fds w0) /\
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr (pf_eb x) (Obj (pf_eb x))).

(** A wrapper borrows an idle stream, the format, errno and the
    read-only data of the formatter, of `c: fputs` and of `c: malloc`.
    Each argument after the format must be an integer, null or a
    read-only string. *)
Definition pf_pre (x : pf_in) : iProp Σ :=
  file_idle (pf_vb x) (ow_self w0) (pf_fp x) (pf_fd x) ∗
  word_string (pf_dq x) (pf_fmt x) (pf_bytes x) ∗
  ([∗ list] a ∈ pf_ys x, str_arg a) ∗ errno_any (pf_eb x) ∗ printf_ro ∗ fputs_ro (pf_vb x) ∗ malloc_ro.

(** A wrapper returns the formatter's int. It gives back the format
    and errno, and the stream is idle again with the same descriptor,
    so that a call of `c: fputs` or another print can follow. *)
Definition pf_post (x : pf_in) (o : outcome) : iProp Σ :=
  ∃ n, ⌜o = Ret (WInt n) /\ 0 <= n < 2 ^ 32⌝ ∗
  file_idle (pf_vb x) (ow_self w0) (pf_fp x) (pf_fd x) ∗
  word_string (pf_dq x) (pf_fmt x) (pf_bytes x) ∗ errno_any (pf_eb x).

(** `c: fprintf (fp, fmt, ...)` formats to the stream fp. *)
Definition fprintf_spec : fspec Σ :=
  FSpec pf_in (fun x => WPtr (pf_fp x) :: WPtr (pf_fmt x) :: pf_ys x)
    (fun x => ⌜pf_fits x⌝ ∗ pf_pre x)%I pf_post.

(** The global `c: stdout` holds a pointer to the stream fp, and the
    owner of this predicate may read it. *)
Definition stdout_is (dq : dfrac) (fp : ptr) : iProp Σ :=
  ∃ so soreg, ⌜lookup (TAtom "stdout") (ge_globals ge) = Some (mkPtr so (Obj so)) /\ so mod 8 = 0 /\
               so + 8 <= r_end soreg⌝ ∗
    liveq dq so soreg ∗ pcellq dq so 0 fp.

(** `c: printf (fmt, ...)` formats to the stream that `c: stdout`
    points to. It reads that global, so the caller lends a reader's
    share of it and gets the share back. *)
Definition printf_spec : fspec Σ :=
  FSpec (dfrac * pf_in) (fun '(_, x) => WPtr (pf_fmt x) :: pf_ys x)
    (fun '(dq, x) => ⌜pf_fits x⌝ ∗ stdout_is dq (pf_fp x) ∗ pf_pre x)%I
    (fun '(dq, x) o => stdout_is dq (pf_fp x) ∗ pf_post x o)%I.

(** ## Appending to a buffer *)

(** Each contract below has the two parameters of the invariant
    [printf_out]. The first parameter k is the mode that the buffer is
    in while it has not failed. The second parameter R owns what the
    function that flushes the buffer needs, such as the stream. *)

(** `c: __printf_buffer_putc (buf, ch)` appends one character. It
    keeps the buffer usable with the same backend. The out-of-line
    `c: __printf_buffer_putc_1` has the same contract. *)
Definition putc_spec (k : Z) (R : Z -> region -> Z * region * Z * Z -> iProp Σ) : fspec Σ :=
  FSpec (Z * Z) (fun '(bb, c) => [WPtr (mkPtr bb (Obj bb)); WInt c])
    (fun '(bb, c) => ⌜0 <= c < 2 ^ 32⌝ ∗ printf_out k R bb)%I
    (fun '(bb, c) o => ⌜o = RetVoid⌝ ∗ printf_out k R bb)%I.

(** `c: __printf_buffer_has_failed (buf)` reads the buffer's mode and
    answers 1 when an earlier append has failed. The invariant does
    not say which mode the buffer is in, so a caller must handle both
    answers. *)
Definition has_failed_spec (k : Z) (R : Z -> region -> Z * region * Z * Z -> iProp Σ) : fspec Σ :=
  FSpec Z (fun bb => [WPtr (mkPtr bb (Obj bb))])
    (fun bb => printf_out k R bb)
    (fun bb o => ∃ b, ⌜o = Ret (WInt b) /\ (b = 0 \/ b = 1)⌝ ∗ printf_out k R bb)%I.

(** `c: __printf_buffer_flush (buf)` makes room in the window. It
    answers 1 when the window has a free byte afterwards, and the
    buffer has then not failed. It answers 0 when the buffer has
    failed. The postcondition shows the window, so that a caller can
    use the free byte. *)
Definition flush_spec (k : Z) (R : Z -> region -> Z * region * Z * Z -> iProp Σ) : fspec Σ :=
  FSpec Z (fun bb => [WPtr (mkPtr bb (Obj bb))])
    (fun bb => printf_out k R bb)
    (fun bb o => ∃ b breg w written mode,
       ⌜o = Ret (WInt b) /\ (b = 0 \/ b = 1) /\ (mode = mode_failed \/ mode = k) /\
        (b = 1 -> pw_ptr w < pw_end w)⌝ ∗
       printf_buf bb breg w written mode ∗ R bb breg (pw_place w))%I.

(** `c: __printf_buffer_write (buf, s, count)` appends the first count
    bytes of the string at s. The caller keeps the string. *)
Definition write_spec (k : Z) (R : Z -> region -> Z * region * Z * Z -> iProp Σ) : fspec Σ :=
  FSpec (Z * dfrac * ptr * list Z * Z)
    (fun '(bb, _, p, _, n) => [WPtr (mkPtr bb (Obj bb)); WPtr p; WInt n])
    (fun '(bb, dq, p, s, n) => ⌜0 <= n <= Z.of_nat (length s)⌝ ∗ printf_out k R bb ∗ word_string dq p s)%I
    (fun '(bb, dq, p, s, _) o => ⌜o = RetVoid⌝ ∗ printf_out k R bb ∗ word_string dq p s)%I.

(** The formatter also appends bytes that are not a string. The
    conversion `%d` writes the digits of a number into a work buffer,
    and those digits have no NUL after them. The predicate [byte_run]
    is a share of a run of bytes ys at the pointer p. The run lies in
    the object sb, which is alive and starts at an 8-aligned address,
    and every byte of the run has the value of a byte. *)
Definition byte_run (dq : dfrac) (p : ptr) (sb : Z) (sreg : region) (ys : list Z) : iProp Σ :=
  (⌜(ptr_cap p = Obj sb \/ ptr_cap p = Ro sb) /\ sb mod 8 = 0 /\ 0 < sb <= ptr_addr p /\
    ptr_addr p + Z.of_nat (length ys) <= r_end sreg /\ r_end sreg <= 2 ^ 48 /\ Forall (fun y => 0 <= y < 256) ys⌝ ∗
   liveq dq sb sreg ∗ bytesq dq sb (ptr_addr p - sb) ys)%I.

(** `c: __printf_buffer_write (buf, s, count)` appends a run of count
    bytes at s, and the caller keeps the run. This contract is the
    general one, and [write_spec] above follows from it, because a
    string lends any run of its bytes. *)
Definition write_bytes_spec (k : Z) (R : Z -> region -> Z * region * Z * Z -> iProp Σ) : fspec Σ :=
  FSpec (Z * dfrac * ptr * Z * region * list Z * Z)
    (fun '(bb, _, p, _, _, _, n) => [WPtr (mkPtr bb (Obj bb)); WPtr p; WInt n])
    (fun '(bb, dq, p, sb, sreg, ys, n) =>
       ⌜n = Z.of_nat (length ys)⌝ ∗ printf_out k R bb ∗ byte_run dq p sb sreg ys)%I
    (fun '(bb, dq, p, sb, sreg, ys, _) o => ⌜o = RetVoid⌝ ∗ printf_out k R bb ∗ byte_run dq p sb sreg ys)%I.

(** `c: __printf_buffer_pad (buf, ch, width)` appends width copies of
    a character, and it appends nothing when the width is zero or
    negative. The width is a signed 64-bit number, which the contract
    takes as the word that holds it. The function keeps the buffer
    usable with the same backend. *)
Definition pad_spec (k : Z) (R : Z -> region -> Z * region * Z * Z -> iProp Σ) : fspec Σ :=
  FSpec (Z * Z * Z) (fun '(bb, c, w) => [WPtr (mkPtr bb (Obj bb)); WInt c; WInt w])
    (fun '(bb, c, w) => ⌜0 <= c < 2 ^ 32 /\ 0 <= w < 2 ^ 64⌝ ∗ printf_out k R bb)%I
    (fun '(bb, _, _) o => ⌜o = RetVoid⌝ ∗ printf_out k R bb)%I.

(** `c: memcpy (dest, src, n)` copies n bytes into a window. The
    caller lends the window with its capability slots, the lifetime of
    the window's object and a reader's share of the source bytes, and
    it gets all of them back. The window starts at an 8-aligned
    address, because the copy rewrites whole capability slots. This is
    the contract of `c: memcpy` that the appending functions use. *)
Definition win_copy_spec : fspec Σ :=
  FSpec (Z * region * Z * Z * Z * dfrac * Z * region * ptr * list Z)
    (fun '(b, _, _, _, a, _, _, _, q, ys) => [WPtr (mkPtr a (Obj b)); WPtr q; WInt (Z.of_nat (length ys))])
    (fun '(b, reg, lo, hi, a, dq, sb, sreg, q, ys) =>
       ⌜b mod 8 = 0 /\ lo mod 8 = 0 /\ b <= lo /\ lo <= a /\ a + Z.of_nat (length ys) <= hi /\ hi <= r_end reg /\
        (ptr_cap q = Obj sb \/ ptr_cap q = Ro sb) /\ sb mod 8 = 0 /\ sb <= ptr_addr q /\
        ptr_addr q + Z.of_nat (length ys) <= r_end sreg /\ Z.of_nat (length ys) < 2 ^ 64 /\
        Forall (fun y => 0 <= y < 256) ys⌝ ∗
       live b reg ∗ win_own b lo hi ∗ liveq dq sb sreg ∗ bytesq dq sb (ptr_addr q - sb) ys)%I
    (fun '(b, reg, lo, hi, a, dq, sb, sreg, q, ys) o =>
       ⌜o = Ret (WPtr (mkPtr a (Obj b)))⌝ ∗
       live b reg ∗ win_own b lo hi ∗ liveq dq sb sreg ∗ bytesq dq sb (ptr_addr q - sb) ys)%I.

(** ## The formatter's loop *)

(** `c: __find_specmb (format)` returns a pointer to the first percent
    sign of a string, or to its end when it has none. *)
Definition find_spec_spec : fspec Σ :=
  FSpec (dfrac * ptr * list Z) (fun '(_, p, _) => [WPtr p])
    (fun '(dq, p, s) => word_string dq p s)
    (fun '(dq, p, s) o => ⌜o = Ret (WPtr (ptr_add p (Z.of_nat (chr_idx 37 s))))⌝ ∗ word_string dq p s)%I.

(** The record [pb_in] is the logical input of a call of the loop
    that walks a format. It names the buffer, the format with its
    parsed directives, the argument cursor and errno. *)
Record pb_in : Type := PbIn {
  pb_buf : Z;
  pb_fmt : ptr; pb_dq : dfrac; pb_bytes : list Z;
  pb_ds : list narrow_directive;
  pb_ap : ptr; pb_skip : Z; pb_xs : list word; pb_rest : list word;
  pb_eb : Z
}.

(** The formatter reads errno once, when it starts. The function that
    flushes the buffer may set errno, so errno belongs to what that
    function needs, which is the part R of the buffer's invariant. The
    predicate [lends_errno] says that this part lends errno for a
    while: it gives errno up and takes it back unchanged in every
    other respect. *)
Definition lends_errno (R : Z -> region -> Z * region * Z * Z -> iProp Σ) (bb eb : Z) : iProp Σ :=
  □ ∀ breg pl, R bb breg pl -∗ errno_any eb ∗ (errno_any eb -∗ R bb breg pl).

(** `c: __printf_buffer (buf, format, ap, 0)` appends the formatted
    text to the buffer. The contract asks of the format and the
    arguments what [vfprintf_spec] asks, and it has a usable buffer in
    the place of the stream.
    The function returns nothing. A failure shows only in the buffer's
    mode, which the invariant hides.
    The function saves errno when it starts, and it reads errno
    through the global `c: __libc_errno`. So the contract asks that
    this global is the errno cell of the thread, and that the buffer's
    invariant lends errno. *)
Definition printf_buffer_spec (k : Z) (R : Z -> region -> Z * region * Z * Z -> iProp Σ) : fspec Σ :=
  FSpec pb_in
    (fun x => [WPtr (mkPtr (pb_buf x) (Obj (pb_buf x))); WPtr (pb_fmt x); WPtr (pb_ap x); WInt 0])
    (fun x =>
       ⌜parse_narrow (pb_bytes x) = Some (pb_ds x) /\
        narrow_fits (pb_ds x) (skipn (Z.to_nat (pb_skip x / 8)) (pb_xs x)) (pb_rest x) /\
        0 <= pb_skip x /\ pb_skip x mod 8 = 0 /\
        ow_errno w0 = Some (mkPtr (pb_eb x) (Obj (pb_eb x))) /\
        lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr (pb_eb x) (Obj (pb_eb x)))⌝ ∗
       printf_out k R (pb_buf x) ∗
       word_string (pb_dq x) (pb_fmt x) (pb_bytes x) ∗ va_at (pb_ap x) (pb_skip x) (pb_xs x) ∗
       ([∗ list] a ∈ skipn (Z.to_nat (pb_skip x / 8)) (pb_xs x), str_arg a) ∗
       lends_errno R (pb_buf x) (pb_eb x) ∗ printf_ro)%I
    (fun x o => ⌜o = RetVoid⌝ ∗ printf_out k R (pb_buf x) ∗ word_string (pb_dq x) (pb_fmt x) (pb_bytes x))%I.

(** ## The file-backed buffer *)

(** A file-backed buffer writes into the character buffer of its
    stream when the stream has room there. Otherwise it writes into its
    own staging array. Two functions make this choice, and they read
    the stream's write pointer and write end to make it.

    The record [fchars] describes a stream whose two pointers point
    into a character buffer. It names the buffer's object, gives the
    offsets of the write pointer and the write end in it, and gives
    the share of the buffer's lifetime that the caller lends. The
    character buffer may be the stream's own object, as it is for an
    unbuffered stream. *)
Record fchars : Type := FChars {
  fc_data : Z; fc_reg : region;
  fc_bo : Z; fc_eo : Z;
  fc_dq : dfrac
}.

(** The record [fwin_in] is the logical input of both functions. It
    names the buffer and the stream. Its last field is the stream's
    character buffer. That field is empty for a stream that has no
    buffer yet, whose write pointer and write end are null. The
    loader leaves `c: stderr` in that state. *)
Record fwin_in : Type := FWinIn {
  fi_buf : Z; fi_breg : region;
  fi_file : Z; fi_freg : region;
  fi_dqf : dfrac;
  fi_chars : option fchars
}.

(** The stream's two offsets lie in its character buffer. *)
Definition fchars_ok (c : fchars) : Prop :=
  0 < fc_data c /\ 0 <= fc_bo c /\ 0 <= fc_eo c /\ fc_data c + fc_bo c <= r_end (fc_reg c) /\
  fc_data c + fc_eo c <= r_end (fc_reg c) /\ r_end (fc_reg c) <= 2 ^ 63.

(** The function [fwin_ptrs] gives the stream's write pointer and
    write end. *)
Definition fwin_ptrs (cs : option fchars) : ptr * ptr :=
  match cs with
  | Some c => (mkPtr (fc_data c + fc_bo c) (Obj (fc_data c)), mkPtr (fc_data c + fc_eo c) (Obj (fc_data c)))
  | None => (null, null)
  end.

(** Both functions read two fields of the stream to make the choice:
    the write pointer and the write end. The predicate [fwin_stream]
    owns these two fields. It also owns a reader's share of the
    stream's lifetime, and a reader's share of the lifetime of the
    character buffer when the stream has one. *)
Definition fwin_stream (i : fwin_in) : iProp Σ :=
  file_liveq (fi_dqf i) (fi_file i) (fi_freg i) ∗
  file_cells (fi_file i)
    [("_IO_write_ptr", VPtr (fwin_ptrs (fi_chars i)).1); ("_IO_write_end", VPtr (fwin_ptrs (fi_chars i)).2)] ∗
  match fi_chars i with
  | Some c => ⌜fchars_ok c⌝ ∗ liveq (fc_dq c) (fc_data c) (fc_reg c)
  | None => True
  end.

(** The function [fwin_choice] gives the window that is chosen. It is
    the room in the stream's character buffer when there is some, and
    the staging array otherwise. *)
Definition fwin_choice (i : fwin_in) : pwin :=
  match fi_chars i with
  | Some c => if fc_bo c <? fc_eo c then data_win (fc_data c) (fc_reg c) (fc_bo c) (fc_eo c)
              else stage_win (fi_buf i) (fi_breg i)
  | None => stage_win (fi_buf i) (fi_breg i)
  end.

Definition fwin_fp (i : fwin_in) : list (string * fval) :=
  [("fp", VPtr (mkPtr (fi_file i) (Obj (fi_file i))))].

(** `c: __printf_buffer_to_file_switch (buf)` points the buffer's three
    pointers at the chosen window. *)
Definition switch_spec : fspec Σ :=
  FSpec fwin_in (fun i => [WPtr (mkPtr (fi_buf i) (Obj (fi_buf i)))])
    (fun i => fwin_stream i ∗ pbuf_file_live (fi_buf i) (fi_breg i) ∗ pbuf_file (fi_buf i) (fwin_fp i) ∗
       ∃ ob op oe, pbuf (fi_buf i) [("write_base", VPtr ob); ("write_ptr", VPtr op); ("write_end", VPtr oe)])%I
    (fun i o => ⌜o = RetVoid⌝ ∗ fwin_stream i ∗ pbuf_file_live (fi_buf i) (fi_breg i) ∗
       pbuf_file (fi_buf i) (fwin_fp i) ∗ pbuf (fi_buf i) (pbuf_ptrs (fwin_choice i)))%I.

(** `c: __printf_buffer_to_file_init (buf, fp)` sets every field of the
    buffer: no bytes written, the mode of a file-backed buffer, the
    stream, and the chosen window. *)
Definition file_init_spec : fspec Σ :=
  FSpec fwin_in (fun i => [WPtr (mkPtr (fi_buf i) (Obj (fi_buf i))); WPtr (mkPtr (fi_file i) (Obj (fi_file i)))])
    (fun i => fwin_stream i ∗ pbuf_file_live (fi_buf i) (fi_breg i) ∗
       (∃ ofp, pbuf_file (fi_buf i) [("fp", VPtr ofp)]) ∗
       ∃ ob op oe written mode, pbuf (fi_buf i)
         [("write_base", VPtr ob); ("write_ptr", VPtr op); ("write_end", VPtr oe);
          ("written", VInt written); ("mode", VInt mode)])%I
    (fun i o => ⌜o = RetVoid⌝ ∗ fwin_stream i ∗ pbuf_file_live (fi_buf i) (fi_breg i) ∗
       pbuf_file (fi_buf i) (fwin_fp i) ∗ pbuf (fi_buf i) (pbuf_vals (fwin_choice i) 0 4))%I.

End spec.

#[global] Hint Unfold fwin_fp : structs.
