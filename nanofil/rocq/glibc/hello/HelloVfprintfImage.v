(** Hello prints with `c: fprintf` and `c: printf`, and both of them
    call `c: __vfprintf_internal`. The proof of that function in
    [PrintfInternal](../stdio/PrintfInternal.v) holds for any program
    that links glibc's formatter and the functions it calls. This
    module checks that the Hello image is such a program, so the
    image's formatter meets [vfprintf_spec].

    When the formatter's buffer is full, the formatter writes the
    text to the stream. The stream then stores the text in a buffer on
    the heap. The proofs of those two writes are not finished, so the
    lemma here assumes them. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics ExternalCalls Pieces Heap.
From Glibc Require Import OsWorld OsRegistry SysCode LibioLogic LibioSetb LibioReadCode LibioDoWriteCode
  LibioGenCode LibioXsputnCode LibioStreamTidy PrintfSpec PrintfBufferFileCode PrintfBufferIoCode
  PrintfStateCode StrlenLogic StrchrCode MemFwdCode FormatterCode FormatterScan FormatterLiteral PrintfPutcOneCode
  PrintfPadOneCode ItoaWordCode PrintfFileEntry PrintfFileCalls PrintfInternal HiAtexitSetb HelloGlibcLibsT.
From Glibc Require LibioCleanupExit.
From Glibc Require Import HelloImageModule HelloImageLoad HelloImageDec01 HelloImageLayout.
Import ListNotations.
Open Scope Z_scope.

(** The image defines a symbol as one of glibc's functions when the
    image's code under that symbol is the function's code. The check
    is a computation over the image. *)
Local Ltac image_defines := unfold Defines; vm_compute; reflexivity.

(** A function that glibc calls through a jump table also needs an
    address in the image. *)
Local Ltac image_fn n :=
  exists (img_addr n); split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | split; vm_compute; congruence]].

(** A call of `c: __vfprintf_internal` in the Hello image is safe
    when the caller meets the formatter's contract. The image runs
    glibc's own code for the formatter and for every function that the
    formatter calls, and the proof checks each of them by computation.
    The image also frees memory with glibc's `c: free` and leaves the
    system calls to the kernel. The lemma assumes only the two writes
    to a stream that has a buffer on the heap. *)
Lemma hello_vfprintf_image `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} w0 fr :
  hello_link (mkGenv hello_image_module img_globals fr) hello_image_objs ->
  xsputn_heap_rule (glibc_program := program_of w0 glibc_os_registry (mkGenv hello_image_module img_globals fr)) ->
  overflow_heap_rule (glibc_program := program_of w0 glibc_os_registry (mkGenv hello_image_module img_globals fr)) ->
  HasSpec glibc_os_registry (os_wi w0) (mkGenv hello_image_module img_globals fr) (TAtom "__vfprintf_internal")
    (vfprintf_spec (glibc_program := program_of w0 glibc_os_registry (mkGenv hello_image_module img_globals fr))).
Proof.
  intros Hk Hxs_heap Hov_heap.
  set (ge := mkGenv hello_image_module img_globals fr) in *.
  set (P := program_of w0 glibc_os_registry ge) in *.
  destruct (hk_frees _ _ Hk) as (Hfh & Hzf & Hzg).
  pose proof (hi_free_rule (glibc_program := P) (Hfree_fn := hk_free _ _ Hk) Hfh Hzf Hzg) as Hfree.
  assert (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write) by image_fn "_IO_new_file_write".
  assert (Hov : ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow) by image_fn "_IO_new_file_overflow".
  assert (Hxs : ge_fn ge "_IO_new_file_xsputn" glibc__IO_new_file_xsputn) by image_fn "_IO_new_file_xsputn".
  assert (Hmove : find_fn ge (TAtom "zmemmove") = None /\ lookup (TAtom "zmemmove") (ge_globals ge) = None)
    by (split; vm_compute; reflexivity).
  assert (Defines ge "__GI__IO_doallocbuf" glibc__IO_doallocbuf) by image_defines.
  assert (Defines ge "__GI__IO_setb" glibc__IO_setb) by image_defines.
  assert (Defines ge "__GI___write" glibc___libc_write) by image_defines.
  assert (Defines ge "__GI___write_nocancel" glibc___write_nocancel) by image_defines.
  assert (Defines ge "_IO_new_do_write" glibc__IO_new_do_write) by image_defines.
  assert (Defines ge "__GI___overflow" glibc___overflow) by image_defines.
  assert (Defines ge "__printf_buffer_to_file_init" glibc___printf_buffer_to_file_init) by image_defines.
  assert (Defines ge "__printf_buffer_to_file_switch" glibc___printf_buffer_to_file_switch) by image_defines.
  assert (Defines ge "__printf_buffer_flush_to_file" glibc___printf_buffer_flush_to_file) by image_defines.
  assert (Defines ge "__printf_buffer_to_file_done" glibc___printf_buffer_to_file_done) by image_defines.
  assert (Defines ge "__printf_buffer_done" glibc___printf_buffer_done) by image_defines.
  assert (Defines ge "__printf_buffer_write" glibc___printf_buffer_write) by image_defines.
  assert (Defines ge "__printf_buffer_flush" glibc___printf_buffer_flush) by image_defines.
  assert (Defines ge "__GI_memcpy" glibc_memcpy) by image_defines.
  assert (Defines ge "__GI_memset" glibc_memset) by image_defines.
  assert (Defines ge "__printf_buffer_putc_1" glibc_printf_buffer_putc_1) by image_defines.
  assert (Defines ge "__printf_buffer_pad_1" glibc_printf_buffer_pad_1) by image_defines.
  assert (Defines ge "glibc_vfprintf_internal#__printf_buffer_putc" glibc_printf_buffer_putc) by image_defines.
  assert (Defines ge "glibc_vfprintf_internal#__printf_buffer_pad" glibc_printf_buffer_pad) by image_defines.
  assert (Defines ge "glibc_vfprintf_internal#__printf_buffer_has_failed" glibc_format_failed) by image_defines.
  assert (Defines ge "glibc_vfprintf_internal#__find_specmb.gnu_inline" glibc_find_specmb) by image_defines.
  assert (Defines ge "__GI___strchrnul" glibc_strchrnul) by image_defines.
  assert (Defines ge "__GI_strlen" glibc_strlen) by image_defines.
  assert (Defines ge "_itoa_word" glibc_itoa_word) by image_defines.
  assert (Defines ge "__printf_buffer" glibc_printf_buffer) by image_defines.
  assert (Defines ge "__vfprintf_internal" glibc_vfprintf_internal) by image_defines.
  refine (vfprintf_has_spec (glibc_program := P) _ _); intros a Hok.
  - exact (file_format_tidy_has_spec (glibc_program := P) LibioCleanupExit.holds_os_glibc (hk_sys _ _ Hk) Hfree
      Hfw Hov Hxs Hxs_heap Hov_heap a Hok Hmove (hk_zmemset _ _ Hk)).
  - exact (file_done_tidy_has_spec (glibc_program := P) LibioCleanupExit.holds_os_glibc (hk_sys _ _ Hk) Hfree
      Hfw Hov Hxs Hxs_heap Hov_heap a Hok).
Qed.
