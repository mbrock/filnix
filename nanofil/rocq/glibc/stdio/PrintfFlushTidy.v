(** A file-backed printf buffer calls the stream's string writer for a
    staged string and the overflow wrapper for a staged byte. Each call
    returns a tidy stream even if it cannot write all the bytes. This
    lets the formatter inspect the stream again after a successful call
    and mark its own buffer failed after an error. *)

From Glibc Require Import Unit_io_write_nocancel_os Unit_io_write_os Unit_libio_fileops_os Unit_libio_genops_os Unit_stdioZ2dcommon_printf_buffer_flush_os.
From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_to_file_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Machine ExternalCalls ExternalMachine Pieces Heap Language Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld OsRegistry SysWrappers FileInv FileTidy LibioLogic LibioFputsSpec AllocRo
  LibioSetb LibioStreamTidy
  PrintfSpec PrintfFileOut PrintfBufferXsputnCall PrintfBufferOverflowCall PrintfFlush PrintfFlushFileSpec.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.

Section flush.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge) (Hfree : free_rule w0 registry ge).
Context `{!Defines ge "__GI__IO_doallocbuf" Unit_libio_genops_os.fn___GI__IO_doallocbuf}.
Context `{!Defines ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb}.
Context `{!Defines ge "__GI___write" Unit_io_write_os.fn___GI___libc_write}.
Context `{!Defines ge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write}.
Context (Hfw : ge_fn ge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write)
  (Hov : ge_fn ge "_IO_new_file_overflow" Unit_libio_fileops_os.fn__IO_new_file_overflow).
Context (Hxs_heap : xsputn_heap_rule) (Hov_heap : overflow_heap_rule).
Variable a : fout.
Let F fp := file_tidy (fo_vb a) (fo_self a) fp (fo_fd a) (fo_flags2 a) (fo_held a).
Let E := (errno_any (fo_eb a) ∗ fputs_ro (fo_vb a) ∗ malloc_ro)%I.
Context (Hready : Z.land (fo_flags2 a) 2 = 0 \/ Z.land (fo_flags2 a) 2 = 2 /\
      find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined Unit_io_write_nocancel_os.fn___GI___write_nocancel))
  (He : ow_errno w0 = Some (mkPtr (fo_eb a) (Obj (fo_eb a))))
  (Hg : lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr (fo_eb a) (Obj (fo_eb a))))
  (Hin : In (fo_fd a) (ow_fds w0)).

(** The string writer reads from the staging array at byte 48 of the
    printf buffer. Its caller gets the same source bytes back on short
    writes and errors as on a successful write. *)
Lemma file_xsputn_call : printf_xsputn_call_spec w0 registry ge F E.
Proof using Type*.
  intros fr fp bb br dq xs Φ Hbb Hal Hn Hend Hr Hy Hfr. iIntros "HF (Herr & #Hro & #Hm) Hl Hxs HK".
  iApply (wp_xsputn_tidy Hreg Hext Hfree Hfw Hov Hxs_heap fr (fo_vb a) (fo_self a) fp (fo_fd a) (fo_flags2 a) (fo_held a) dq bb br 48 (Obj bb) xs (fo_eb a) with "Hro Hm HF Herr Hl Hxs"); try first [assumption | left; reflexivity | lia].
  iNext. iIntros (r Hr') "HF Herr Hl Hxs". iApply ("HK" with "[%] HF [$Herr $Hro $Hm] Hl Hxs"). destruct Hr'; lia.
Qed.

(** The overflow wrapper returns the byte it was asked to write or
    EOF. Neither result changes which stream and errno cell the
    formatter owns. *)
Lemma file_overflow_call : printf_overflow_call_spec w0 registry ge F E.
Proof using Type*.
  intros fr fp ch Φ Hch Hfr. iIntros "HF (Herr & #Hro & #Hm) HK".
  iApply (wp_overflow_tidy Hreg Hext Hfree Hfw Hov Hov_heap fr (fo_vb a) (fo_self a) fp (fo_fd a) (fo_flags2 a) (fo_held a) ch (fo_eb a) with "Hro Hm HF Herr"); try assumption.
  iNext. iIntros (r Hr) "HF Herr". iApply ("HK" with "[%] HF [$Herr $Hro $Hm]"). destruct Hr; lia.
Qed.

Context (Hfn : ge_fn ge "_IO_new_file_xsputn" Unit_libio_fileops_os.fn__IO_new_file_xsputn).
Context `{!Defines ge "__GI___overflow" Unit_libio_genops_os.fn___GI___overflow}.
Context `{!Defines ge "__printf_buffer_to_file_switch" Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_to_file_switch}.
Context `{!Defines ge "__printf_buffer_flush_to_file" Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_flush_to_file}.

(** The file backend gets both of its stream calls from the tidy
    stream rules. It needs no separate contract for a staged write. *)
Lemma flush_to_file_tidy_has_spec :
  HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_flush_to_file") (flush_to_file_spec (file_R a)).
Proof using Type*.
  exact (flush_to_file_has_spec a Hfn file_xsputn_call file_overflow_call).
Qed.

(** In file mode the dispatcher calls the file backend. A successful
    flush returns a window with room, whether that window lies in the
    stream itself or in the staging array. *)
Lemma flush_file_tidy_has_spec `{!Defines ge "__printf_buffer_flush" Unit_stdioZ2dcommon_printf_buffer_flush_os.fn___printf_buffer_flush} :
  HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_flush") (flush_spec 4 (file_R a)).
Proof using Type*. apply flush_dispatch_has_spec; [apply flush_to_file_tidy_has_spec | assumption]. Qed.
End flush.
