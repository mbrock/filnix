(** After formatting its arguments, `c: vfprintf` flushes the file buffer
    and asks glibc for the final character count. The flush writes to the
    open descriptor of this stream. If the count does not fit in an int,
    the counting function sets the caller's errno to EOVERFLOW. *)

From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Runtime Semantics ExternalCalls.
From Glibc Require Import GlibcProgram GlibcSpec Fix OsWorld OsRegistry SysCode SysWrappers
  LibioLogic LibioSetb LibioReadCode LibioDoWriteCode LibioGenCode LibioXsputnCode LibioStreamTidy
  PrintfFileOut PrintfFlushTidy PrintfSpec PrintfBufferFileCode PrintfStateCode PrintfDone.
Import ProgramAbbreviations OsWorld.
Open Scope Z_scope.

Section calls.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge) (Hfree : free_rule w0 registry ge).
Context `{!Defines ge "__GI__IO_doallocbuf" glibc__IO_doallocbuf}.
Context `{!Defines ge "__GI__IO_setb" glibc__IO_setb}.
Context `{!Defines ge "__GI___write" glibc___libc_write}.
Context `{!Defines ge "__GI___write_nocancel" glibc___write_nocancel}.
Context `{!Defines ge "_IO_new_do_write" glibc__IO_new_do_write}.
Context (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
  (Hov : ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow)
  (Hxs : ge_fn ge "_IO_new_file_xsputn" glibc__IO_new_file_xsputn).
Context `{!Defines ge "__GI___overflow" glibc___overflow}.
Context `{!Defines ge "__printf_buffer_to_file_switch" glibc___printf_buffer_to_file_switch}.
Context `{!Defines ge "__printf_buffer_flush_to_file" glibc___printf_buffer_flush_to_file}.
Context (Hxs_heap : xsputn_heap_rule) (Hov_heap : overflow_heap_rule).

(** The second bit of the flags word selects the write wrapper. The
    linked image supplies the noncancelling wrapper, so either setting
    of that bit is supported. *)
Local Lemma file_write_ready f2 :
  Z.land f2 2 = 0 \/ Z.land f2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel).
Proof using Type*.
  destruct (Z.testbit f2 1) eqn:H; [right; split; [|exact defines] | left].
  all: change 2 with (2^1); apply Z.bits_inj; intro i; rewrite Z.land_spec, Z.pow2_bits_eqb by lia;
    rewrite ?Z.pow2_bits_eqb, ?Z.bits_0 by lia; destruct (Z.eqb_spec 1 i) as [<-|];
    [rewrite H | destruct (Z.testbit f2 i)]; reflexivity.
Qed.

Variable a : fout.
Hypothesis Hok : fo_self a = ow_self w0 /\ ow_errno w0 = Some (mkPtr (fo_eb a) (Obj (fo_eb a))) /\
  In (fo_fd a) (ow_fds w0) /\ lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr (fo_eb a) (Obj (fo_eb a))) /\
  (forall c, fo_held a = Some c -> 0 <= c /\ c+1 < 2^32).

(** Finishing the file uses the stream's flush rule and the rule for
    counting the bytes written. Neither call needs the caller to
    provide a separate proof about the printf buffer. *)
Lemma file_done_tidy_has_spec `{!Defines ge "__printf_buffer_done" glibc___printf_buffer_done}
    `{!Defines ge "__printf_buffer_to_file_done" glibc___printf_buffer_to_file_done} :
  HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_to_file_done") (file_done_spec (file_R a)).
Proof using Type*.
  destruct Hok as (_ & He & Hin & Hg & _).
  apply file_done_has_spec; first [apply flush_to_file_tidy_has_spec; first [assumption | apply file_write_ready]
    | apply buffer_done_has_spec; assumption | assumption].
Qed.
End calls.
