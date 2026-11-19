(** Glibc's string writer and character overflow operate on the same
    three kinds of stream. An input-only stream refuses the write, an
    unbuffered stream uses its short byte, and a buffered stream may
    allocate or reuse a heap buffer. This file combines the three cases
    so callers can pass a tidy stream without opening it themselves. *)

From Glibc Require Import Unit_io_write_nocancel_os Unit_io_write_os Unit_libio_fileops_os Unit_libio_genops_os.
From Glibc Require Import GlibcProgram GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld OsRegistry SysWrappers FileInv FileIdle FileTidy
  PrintfStreamInv LibioFputsSpec AllocRo LibioSetb LibioLogic
  LibioOverflowShort LibioXsputnShort LibioOverflowNoWrite LibioXsputnNoWrite.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A buffered stream may not have allocated its buffer yet. The rule
    for writing a string therefore takes the allocator's read-only data
    as well as the stream fields and the caller's share of the string.
    The string's object must start on an eight-byte boundary, because the
    runtime copy reads the capability slots of the source object; the
    string pointer itself may have any offset. *)
Definition xsputn_heap_rule : Prop := forall fr vb self fb freg st nb flags2 held dq b reg o c ys eb Φ,
  let fp := mkPtr fb (Obj fb) in let n := Z.of_nat (length ys) in let fd := fs_fileno st in
  call_frame Unit_libio_fileops_os.fn__IO_new_file_xsputn [WPtr fp; WPtr (mkPtr (b+o) c); WInt n] = Some fr ->
  fb mod 8 = 0 -> 0 < fb -> fb+file_size <= r_end freg -> r_end freg <= 2^63 -> flags_ok st ->
  idle_ok fd (fs_with_flags2 st 0) -> fs_flags2 st = flags2 -> fs_vtable st = mkPtr (vb+vt_file) (Ro vb) ->
  buf_ptrs_ok fb nb (fs_ptrs st) -> short_idle nb st -> has (fs_flags st) io_unbuffered = false ->
  has (fs_flags st) io_no_writes = false ->
  (Z.land flags2 2 = 0 \/ Z.land flags2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined Unit_io_write_nocancel_os.fn___GI___write_nocancel)) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  (c = Obj b \/ c = Ro b) -> 0 < b -> b mod 8 = 0 -> 0 <= o -> b+o+n <= r_end reg -> r_end reg <= 2^63 -> Forall (fun y => 0 <= y < 256) ys ->
  fputs_ro vb -∗ malloc_ro -∗ live fb freg -∗ file_fields fb st -∗ lock_inv self (fs_lock st) held -∗ buf_idle nb -∗
  wide_idle vb (fs_wide st) (fs_codecvt st) -∗ errno_any eb -∗ liveq dq b reg -∗ bytesq dq b o ys -∗
  ▷ (∀ r, ⌜r = 2^64-1 \/ 0 <= r <= n⌝ -∗ file_tidy vb self fp fd flags2 held -∗ errno_any eb -∗
     liveq dq b reg -∗ bytesq dq b o ys -∗ Φ (Ret (WInt r))) -∗ WP (ERun fr : gexpr) {{ Φ }}.

(** The buffered character rule has the same allocation case, but the
    caller passes a byte rather than lending a source object. *)
Definition overflow_heap_rule : Prop := forall fr vb self fb freg st nb flags2 held ch eb Φ,
  let fp := mkPtr fb (Obj fb) in let fd := fs_fileno st in
  call_frame Unit_libio_genops_os.fn___GI___overflow [WPtr fp; WInt ch] = Some fr -> 0 <= ch < 256 ->
  fb mod 8 = 0 -> 0 < fb -> fb+file_size <= r_end freg -> r_end freg <= 2^63 -> flags_ok st ->
  idle_ok fd (fs_with_flags2 st 0) -> fs_flags2 st = flags2 -> fs_vtable st = mkPtr (vb+vt_file) (Ro vb) ->
  buf_ptrs_ok fb nb (fs_ptrs st) -> short_idle nb st -> has (fs_flags st) io_unbuffered = false ->
  has (fs_flags st) io_no_writes = false ->
  (Z.land flags2 2 = 0 \/ Z.land flags2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined Unit_io_write_nocancel_os.fn___GI___write_nocancel)) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  fputs_ro vb -∗ malloc_ro -∗ live fb freg -∗ file_fields fb st -∗ lock_inv self (fs_lock st) held -∗ buf_idle nb -∗
  wide_idle vb (fs_wide st) (fs_codecvt st) -∗ errno_any eb -∗
  ▷ (∀ r, ⌜r = ch \/ r = 2^32-1⌝ -∗ file_tidy vb self fp fd flags2 held -∗ errno_any eb -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.

Context (Hreg : holds_os registry) (Hext : sys_external ge) (Hfree : free_rule w0 registry ge).
Context `{!Defines ge "__GI__IO_doallocbuf" Unit_libio_genops_os.fn___GI__IO_doallocbuf}.
Context `{!Defines ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb}.
Context `{!Defines ge "__GI___write" Unit_io_write_os.fn___GI___libc_write}.
Context `{!Defines ge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write}.
Context (Hfw : ge_fn ge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write)
  (Hov : ge_fn ge "_IO_new_file_overflow" Unit_libio_fileops_os.fn__IO_new_file_overflow).

(** The string writer hands back the caller's source share on every
    path, even when a stream refuses the write. The descriptor, second
    flags word and lock state are the same in the next call. *)
Lemma wp_xsputn_tidy (Hxs_heap : xsputn_heap_rule) fr vb self fp fd flags2 held dq b reg o c ys eb Φ :
  let n := Z.of_nat (length ys) in
  call_frame Unit_libio_fileops_os.fn__IO_new_file_xsputn [WPtr fp; WPtr (mkPtr (b+o) c); WInt n] = Some fr ->
  (Z.land flags2 2 = 0 \/ Z.land flags2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined Unit_io_write_nocancel_os.fn___GI___write_nocancel)) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  (c = Obj b \/ c = Ro b) -> 0 < b -> b mod 8 = 0 -> 0 <= o -> b+o+n <= r_end reg -> r_end reg <= 2^63 -> Forall (fun y => 0 <= y < 256) ys ->
  fputs_ro vb -∗ malloc_ro -∗ file_tidy vb self fp fd flags2 held -∗ errno_any eb -∗ liveq dq b reg -∗ bytesq dq b o ys -∗
  ▷ (∀ r, ⌜r = 2^64-1 \/ 0 <= r <= n⌝ -∗ file_tidy vb self fp fd flags2 held -∗ errno_any eb -∗
     liveq dq b reg -∗ bytesq dq b o ys -∗ Φ (Ret (WInt r))) -∗ WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros n Hfr Hready He Hg Hin Hc Hb Hb8 Ho Hend Hreg' Hy.
  iIntros "#Hro #Hm (%fb & %freg & %st & %nb & %Hp & Hl & Hf & Hlk & Hb & Hw) Herr Hbl Hys HK".
  destruct Hp as (-> & Hal & Hfb & Hsize & Hrf & Hok & Hi & Hf2 & Hvt & Hbp & Hshort).
  pose proof Hi as (_ & Hfd & _). change (fs_fileno st = fd) in Hfd. subst fd.
  destruct (has (fs_flags st) io_no_writes) eqn:Hnw.
  - iApply (wp_xsputn_nowrite Hov fr vb self fb freg st nb flags2 held dq b reg o c ys eb with "Hro Hl Hf Hlk Hb Hw Herr Hbl Hys HK"); assumption.
  - destruct (has (fs_flags st) io_unbuffered) eqn:Hu.
    + iApply (wp_xsputn_short Hreg Hext Hfree Hfw Hov fr vb self fb freg st nb flags2 held dq b reg o c ys eb with "Hro Hl Hf Hlk Hb Hw Herr Hbl Hys HK"); assumption.
    + iApply (Hxs_heap fr vb self fb freg st nb flags2 held dq b reg o c ys eb with "Hro Hm Hl Hf Hlk Hb Hw Herr Hbl Hys HK"); assumption.
Qed.

(** Character overflow tests the write permission before it needs a
    buffer. Every branch gives the caller back its tidy stream, whether
    it returns the byte or reports EOF. *)
Lemma wp_overflow_tidy (Hov_heap : overflow_heap_rule) fr vb self fp fd flags2 held ch eb Φ :
  call_frame Unit_libio_genops_os.fn___GI___overflow [WPtr fp; WInt ch] = Some fr -> 0 <= ch < 256 ->
  (Z.land flags2 2 = 0 \/ Z.land flags2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined Unit_io_write_nocancel_os.fn___GI___write_nocancel)) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  fputs_ro vb -∗ malloc_ro -∗ file_tidy vb self fp fd flags2 held -∗ errno_any eb -∗
  ▷ (∀ r, ⌜r = ch \/ r = 2^32-1⌝ -∗ file_tidy vb self fp fd flags2 held -∗ errno_any eb -∗ Φ (Ret (WInt r))) -∗ WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hch Hready He Hg Hin.
  iIntros "#Hro #Hm (%fb & %freg & %st & %nb & %Hp & Hl & Hf & Hlk & Hb & Hw) Herr HK".
  destruct Hp as (-> & Hal & Hfb & Hsize & Hrf & Hok & Hi & Hf2 & Hvt & Hbp & Hshort).
  pose proof Hi as (_ & Hfd & _). change (fs_fileno st = fd) in Hfd. subst fd.
  destruct (has (fs_flags st) io_no_writes) eqn:Hnw.
  - iApply (wp_overflow_nowrite Hov fr vb self fb freg st nb flags2 held ch eb with "Hro Hl Hf Hlk Hb Hw Herr HK"); assumption.
  - destruct (has (fs_flags st) io_unbuffered) eqn:Hu.
    + iApply (wp_overflow_short Hreg Hext Hfree Hfw Hov fr vb self fb freg st nb flags2 held ch eb with "Hro Hl Hf Hlk Hb Hw Herr HK"); assumption.
    + iApply (Hov_heap fr vb self fb freg st nb flags2 held ch eb with "Hro Hm Hl Hf Hlk Hb Hw Herr HK"); assumption.
Qed.
End rules.
