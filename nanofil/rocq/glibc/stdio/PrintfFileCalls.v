(** When `c: vfprintf` prints to a file, each append either uses the current
    window or flushes it to make room. Both the formatting loop and the
    final character count use the same stream and errno cell. *)

From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Runtime Semantics ExternalCalls.
From Glibc Require Import Unit_io_write_nocancel_os Unit_io_write_os Unit_libio_fileops_os Unit_libio_genops_os Unit_stdioZ2dcommon__fitoa_word_os.
From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_done_os Unit_stdioZ2dcommon_printf_buffer_flush_os Unit_stdioZ2dcommon_printf_buffer_pad_1_os Unit_stdioZ2dcommon_printf_buffer_putc_1_os Unit_stdioZ2dcommon_printf_buffer_to_file_os.
From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_write_os Unit_stdioZ2dcommon_vfprintfZ2dinternal_os Unit_string_memcpy_os Unit_string_memset_os Unit_string_strchrnul_os.
From Glibc Require Import GlibcProgram GlibcSpec Fix OsWorld OsRegistry SysWrappers
  LibioLogic LibioSetb LibioStreamTidy
  PrintfFileOut PrintfFlushTidy PrintfSpec PrintfDone
  StrlenLogic StrlenWord PrintfStagingCopy PrintfCopy PrintfWrite PrintfSmall
  FormatterScan FormatterLiteral PrintfPutcSlow PrintfPutc
  PrintfFill PrintfPad ItoaWord CBlocks PrintfLoopState PrintfLoop PrintfFileEntry.
Import ListNotations ProgramAbbreviations OsWorld.
Open Scope Z_scope.

Section calls.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge) (Hfree : free_rule w0 registry ge).
Context `{!Defines ge "__GI__IO_doallocbuf" Unit_libio_genops_os.fn___GI__IO_doallocbuf}.
Context `{!Defines ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb}.
Context `{!Defines ge "__GI___write" Unit_io_write_os.fn___GI___libc_write}.
Context `{!Defines ge "__GI___write_nocancel" Unit_io_write_nocancel_os.fn___GI___write_nocancel}.
Context `{!Defines ge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write}.
Context (Hfw : ge_fn ge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write)
  (Hov : ge_fn ge "_IO_new_file_overflow" Unit_libio_fileops_os.fn__IO_new_file_overflow)
  (Hxs : ge_fn ge "_IO_new_file_xsputn" Unit_libio_fileops_os.fn__IO_new_file_xsputn).
Context `{!Defines ge "__GI___overflow" Unit_libio_genops_os.fn___GI___overflow}.
Context `{!Defines ge "__printf_buffer_to_file_switch" Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_to_file_switch}.
Context `{!Defines ge "__printf_buffer_flush_to_file" Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_flush_to_file}.
Context (Hxs_heap : xsputn_heap_rule) (Hov_heap : overflow_heap_rule).

(** The second bit of the flags word selects the write wrapper. The
    linked image supplies the noncancelling wrapper, so either setting
    of that bit is supported. *)
Local Lemma file_write_ready f2 :
  Z.land f2 2 = 0 \/ Z.land f2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined Unit_io_write_nocancel_os.fn___GI___write_nocancel).
Proof using Type*.
  destruct (Z.testbit f2 1) eqn:H; [right; split; [|exact defines] | left].
  all: change 2 with (2^1); apply Z.bits_inj; intro i; rewrite Z.land_spec, Z.pow2_bits_eqb by lia;
    rewrite ?Z.pow2_bits_eqb, ?Z.bits_0 by lia; destruct (Z.eqb_spec 1 i) as [<-|];
    [rewrite H | destruct (Z.testbit f2 i)]; reflexivity.
Qed.

Variable a : fout.
Hypothesis Hok : fout_ok a.

(** Finishing the file uses the stream's flush rule and the rule for
    counting the bytes written. Neither call needs the caller to
    provide a separate proof about the printf buffer. *)
Lemma file_done_tidy_has_spec `{!Defines ge "__printf_buffer_done" Unit_stdioZ2dcommon_printf_buffer_done_os.fn___printf_buffer_done}
    `{!Defines ge "__printf_buffer_to_file_done" Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_to_file_done} :
  HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_to_file_done") (file_done_spec (file_R a)).
Proof using Type*.
  destruct Hok as (_ & He & Hin & Hg).
  apply file_done_has_spec; first [apply flush_to_file_tidy_has_spec; first [assumption | apply file_write_ready]
    | apply buffer_done_has_spec; assumption | assumption].
Qed.

Context `{!Defines ge "__printf_buffer_write" Unit_stdioZ2dcommon_printf_buffer_write_os.fn___printf_buffer_write}.
Context `{!Defines ge "__printf_buffer_flush" Unit_stdioZ2dcommon_printf_buffer_flush_os.fn___printf_buffer_flush}.
Context `{!Defines ge "__GI_memcpy" Unit_string_memcpy_os.fn___GI_memcpy} `{!Defines ge "__GI_memset" Unit_string_memset_os.fn___GI_memset}.
Context `{!Defines ge "__printf_buffer_putc_1" Unit_stdioZ2dcommon_printf_buffer_putc_1_os.fn___printf_buffer_putc_1}.
Context `{!Defines ge "__printf_buffer_pad_1" Unit_stdioZ2dcommon_printf_buffer_pad_1_os.fn___printf_buffer_pad_1}.
Context `{!Defines ge "glibc_vfprintf_internal#__printf_buffer_putc" Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn_glibc_vfprintf_internal'23__printf_buffer_putc}.
Context `{!Defines ge "glibc_vfprintf_internal#__printf_buffer_pad" Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn_glibc_vfprintf_internal'23__printf_buffer_pad}.
Context `{!Defines ge "glibc_vfprintf_internal#__printf_buffer_has_failed" glibc_format_failed}.
Context `{!Defines ge "glibc_vfprintf_internal#__find_specmb.gnu_inline" glibc_find_specmb}.
Context `{!Defines ge "__GI___strchrnul" Unit_string_strchrnul_os.fn___GI___strchrnul} `{!Defines ge "__GI_strlen" glibc_strlen}.
Context `{!Defines ge "_itoa_word" Unit_stdioZ2dcommon__fitoa_word_os.fn__itoa_word}.
Context (Hmove : find_fn ge (TAtom "zmemmove") = None /\ lookup (TAtom "zmemmove") (ge_globals ge) = None)
  (Hset : find_fn ge (TAtom "zmemset") = None /\ lookup (TAtom "zmemset") (ge_globals ge) = None).

(** The formatter uses the file flush for single characters, padding and
    runs of bytes. Its two calls to the byte writer differ only in what
    the caller lends: a string or the digits of an integer. *)
Lemma file_format_tidy_has_spec `{!Defines ge "__printf_buffer" Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer} :
  HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer") (printf_buffer_spec 4 (file_R a)).
Proof using Type*.
  destruct Hmove, Hset.
  assert (Hflush : HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_flush") (flush_spec 4 (file_R a))).
  { apply flush_file_tidy_has_spec; first [assumption | apply file_write_ready | unfold fout_ok in Hok; tauto]. }
  assert (Hfill : HasSpec registry (os_wi w0) ge (TAtom "__GI_memset") win_fill_spec).
  { apply memset_window_has_spec; first [assumption | apply Hreg; reflexivity]. }
  assert (Hw : Callees [(TAtom "__printf_buffer_flush", flush_spec 4 (file_R a)); (TAtom "__GI_memcpy", win_copy_spec)]).
  { constructor; [exact Hflush|]. constructor; [|constructor].
    apply win_copy_of_window, memcpy_window_spec_valid; first [assumption | apply Hreg; reflexivity | apply defines]. }
  assert (Hc : Callees [(TAtom "__printf_buffer_putc_1", putc_spec 4 (file_R a))]).
  { constructor; [apply putc_one_has_spec; assumption | constructor]. }
  apply printf_buffer_has_spec; try assumption. unfold Callees. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - apply write_has_spec; assumption.
  - apply has_failed_has_spec; assumption.
  - apply find_spec_has_spec; assumption.
  - apply strlen_has_spec; first [assumption | apply os_wi_stable].
  - apply pad_has_spec; assumption.
  - apply putc_has_spec; assumption.
  - apply write_bytes_has_spec; assumption.
  - apply itoa_word_has_spec; assumption.
Qed.
End calls.
