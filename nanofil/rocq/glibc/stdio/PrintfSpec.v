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
From Glibc Require Import Fix OsBlocks OsWorld FileInv WordString PrintfStreamInv FxprintfStream
  NarrowFormat NarrowArgs FormatterCode FormatterStringTable CStruct PrintfLayout PrintfOut StrchrnulLogic.
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

(** The function [table_bytes] gives the bytes of one of the
    formatter's two dispatch tables. *)
Definition table_bytes (n : string) : list Z :=
  if String.eqb n jump_table then jump_table_bytes else
  if String.eqb n step0_jumps then step0_jumps_bytes else [].

(** Both tables have their bytes, so the definition above did not fall
    back to the empty list. *)
Lemma table_bytes_sizes : (length (table_bytes jump_table), length (table_bytes step0_jumps)) = (91, 128)%nat.
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

(** The formatter reads its two dispatch tables. It also reads three
    globals that are null while the program has registered no
    conversion of its own, and Hello registers none. *)
Definition printf_ro : iProp Σ :=
  ro_table jump_table ∗ ro_table step0_jumps ∗
  null_global "__printf_function_table" ∗ null_global "__printf_modifier_table" ∗
  null_global "__printf_va_arg_table".

(** ## Arguments *)

(** The formatter's arguments are the string arguments [str_arg] of
    [WordString](../string/WordString.v): integers, null pointers and
    pointers into read-only strings. *)

(** The argument cursor ap points skip bytes into a snapshot of the
    call's arguments xs, past the named ones. *)
Definition va_at (ap : ptr) (skip : Z) (xs : list word) : iProp Σ :=
  ∃ cb sb, ⌜ap = mkPtr cb (Obj cb) /\ 0 < sb /\ sb mod 16 = 0 /\ sb + req_extent (fx_req xs) <= 2 ^ 48⌝ ∗
    pts (va_cursor_ps cb (mkRegion cb (cb + 32) Heap Live) (mkPtr (sb + skip) (Ro sb))) ∗
    pts (snapshot_ps xs sb (fx_req xs)).

(** ## The formatter *)

(** The record [vfp_in] is the logical input of a call of the
    formatter. *)
Record vfp_in : Type := VfpIn {
  vi_vb : Z;                      (* the stream jump tables *)
  vi_fp : ptr;                    (* the stream *)
  vi_mode : Z; vi_flags2 : Z; vi_held : option Z;
  vi_fmt : ptr; vi_dq : dfrac; vi_bytes : list Z;
  vi_ds : list narrow_directive;  (* the parsed format *)
  vi_ap : ptr; vi_skip : Z; vi_xs : list word; vi_rest : list word;
  vi_eb : Z                       (* errno *)
}.

(** `c: __vfprintf_internal (fp, fmt, ap, 0)` is safe when the format
    parses in the narrow grammar, the arguments after the named ones
    fit its conversions, and every argument is an integer, null or a
    read-only string. It returns an int and gives back the stream, the
    format and errno. The stream may have become narrow. *)
Definition vfprintf_spec : fspec Σ :=
  FSpec vfp_in
    (fun x => [WPtr (vi_fp x); WPtr (vi_fmt x); WPtr (vi_ap x); WInt 0])
    (fun x =>
       ⌜parse_narrow (vi_bytes x) = Some (vi_ds x) /\
        narrow_progress (vi_ds x) (skipn (Z.to_nat (vi_skip x / 8)) (vi_xs x)) (vi_rest x) /\
        ow_errno w0 = Some (mkPtr (vi_eb x) (Obj (vi_eb x)))⌝ ∗
       printf_stream (vi_vb x) (ow_self w0) (vi_fp x) (vi_mode x) (vi_flags2 x) (vi_held x) ∗
       word_string (vi_dq x) (vi_fmt x) (vi_bytes x) ∗ va_at (vi_ap x) (vi_skip x) (vi_xs x) ∗
       ([∗ list] a ∈ vi_xs x, str_arg a) ∗ errno_any (vi_eb x) ∗ printf_ro)%I
    (fun x o =>
       ∃ n mode', ⌜o = Ret (WInt n) /\ 0 <= n < 2 ^ 32⌝ ∗
       printf_stream (vi_vb x) (ow_self w0) (vi_fp x) mode' (vi_flags2 x) (vi_held x) ∗
       word_string (vi_dq x) (vi_fmt x) (vi_bytes x) ∗ errno_any (vi_eb x))%I.

(** ## Appending to a buffer *)

(** Each contract below has the two parameters of the invariant
    [printf_out]. The first parameter k is the mode that the buffer is
    in while it has not failed. The second parameter R owns what the
    function that flushes the buffer needs, such as the stream. *)

(** `c: __printf_buffer_putc (buf, ch)` appends one character. It
    keeps the buffer usable with the same backend. The out-of-line
    `c: __printf_buffer_putc_1` has the same contract. *)
Definition putc_spec (k : Z) (R : Z * region * Z * Z -> iProp Σ) : fspec Σ :=
  FSpec (Z * Z) (fun '(bb, c) => [WPtr (mkPtr bb (Obj bb)); WInt c])
    (fun '(bb, c) => ⌜0 <= c < 2 ^ 32⌝ ∗ printf_out k R bb)%I
    (fun '(bb, c) o => ⌜o = RetVoid⌝ ∗ printf_out k R bb)%I.

(** `c: __printf_buffer_has_failed (buf)` reads the buffer's mode and
    answers 1 when an earlier append has failed. The invariant does
    not say which mode the buffer is in, so a caller must handle both
    answers. *)
Definition has_failed_spec (k : Z) (R : Z * region * Z * Z -> iProp Σ) : fspec Σ :=
  FSpec Z (fun bb => [WPtr (mkPtr bb (Obj bb))])
    (fun bb => printf_out k R bb)
    (fun bb o => ∃ b, ⌜o = Ret (WInt b) /\ (b = 0 \/ b = 1)⌝ ∗ printf_out k R bb)%I.

(** `c: __printf_buffer_flush (buf)` makes room in the window. It
    answers 1 when the window has a free byte afterwards, and the
    buffer has then not failed. It answers 0 when the buffer has
    failed. The postcondition shows the window, so that a caller can
    use the free byte. *)
Definition flush_spec (k : Z) (R : Z * region * Z * Z -> iProp Σ) : fspec Σ :=
  FSpec Z (fun bb => [WPtr (mkPtr bb (Obj bb))])
    (fun bb => printf_out k R bb)
    (fun bb o => ∃ b breg w written mode,
       ⌜o = Ret (WInt b) /\ (b = 0 \/ b = 1) /\ (mode = mode_failed \/ mode = k) /\
        (b = 1 -> pw_ptr w < pw_end w)⌝ ∗
       printf_buf bb breg w written mode ∗ R (pw_place w))%I.

(** `c: __printf_buffer_write (buf, s, count)` appends the first count
    bytes of the string at s. The caller keeps the string. *)
Definition write_spec (k : Z) (R : Z * region * Z * Z -> iProp Σ) : fspec Σ :=
  FSpec (Z * dfrac * ptr * list Z * Z)
    (fun '(bb, _, p, _, n) => [WPtr (mkPtr bb (Obj bb)); WPtr p; WInt n])
    (fun '(bb, dq, p, s, n) => ⌜0 <= n <= Z.of_nat (length s)⌝ ∗ printf_out k R bb ∗ word_string dq p s)%I
    (fun '(bb, dq, p, s, _) o => ⌜o = RetVoid⌝ ∗ printf_out k R bb ∗ word_string dq p s)%I.

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

(** `c: __printf_buffer (buf, format, ap, 0)` appends the formatted
    text to the buffer. The contract has the premises of
    [vfprintf_spec], with a usable buffer in the place of the stream.
    Its parameter cover says which directives a proof handles, so that
    a proof of some conversions states exactly what it covers. The
    function returns nothing. A failure shows only in the buffer's
    mode, which the invariant hides. *)
Definition printf_buffer_spec (cover : narrow_directive -> Prop) (k : Z) (R : Z * region * Z * Z -> iProp Σ) :
    fspec Σ :=
  FSpec pb_in
    (fun x => [WPtr (mkPtr (pb_buf x) (Obj (pb_buf x))); WPtr (pb_fmt x); WPtr (pb_ap x); WInt 0])
    (fun x =>
       ⌜parse_narrow (pb_bytes x) = Some (pb_ds x) /\ Forall cover (pb_ds x) /\
        narrow_progress (pb_ds x) (skipn (Z.to_nat (pb_skip x / 8)) (pb_xs x)) (pb_rest x) /\
        ow_errno w0 = Some (mkPtr (pb_eb x) (Obj (pb_eb x)))⌝ ∗
       printf_out k R (pb_buf x) ∗
       word_string (pb_dq x) (pb_fmt x) (pb_bytes x) ∗ va_at (pb_ap x) (pb_skip x) (pb_xs x) ∗
       ([∗ list] a ∈ pb_xs x, str_arg a) ∗ errno_any (pb_eb x) ∗ printf_ro)%I
    (fun x o => ⌜o = RetVoid⌝ ∗ printf_out k R (pb_buf x) ∗
       word_string (pb_dq x) (pb_fmt x) (pb_bytes x) ∗ errno_any (pb_eb x))%I.

(** A literal byte and the conversion `%s` are the directives of the
    formats that print only strings. *)
Definition lit_or_str (d : narrow_directive) : Prop :=
  match d with FmtLit _ | FmtStr => True | _ => False end.

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
