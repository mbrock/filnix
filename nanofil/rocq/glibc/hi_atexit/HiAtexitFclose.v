From Glibc Require Import Unit_io_close_nocancel_os Unit_io_write_os Unit_libio_fileops_os Unit_libio_genops_os Unit_nptl_libcZ2dcleanup_os.
From Glibc Require Import GlibcProgram.
(** Closing stdout runs glibc's `c: fclose`, which flushes the stream,
    closes its descriptor, frees its buffer and takes it out of the
    list of open streams. Its proof in LibioFclose.v assumes a triple
    for each function it calls. This file supplies those triples, so
    the triple [hi_fclose_stdout] assumes only facts about the genv:
    which functions the genv binds, and that the system calls stay
    external.

    | Callee | Its triple |
    |---|---|
    | `c: _IO_file_close_maybe_unlink` | HiAtexitCloseIt.v |
    | `c: _IO_un_link` | LibioUnlink.v | *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry
  FileInv LibioLogic SysWrappers AllocLogic LibioUnlink LibioFclose
  HiAtexitBase HiAtexitCloseIt.
From Glibc Require FileInv LibioFclose LibioLogic LibioUnlink OsWorld SysWrappers.
Import ListNotations.
Open Scope Z_scope.

(** `c: _IO_un_link`, at [HLG]. *)
(** `c: _IO_new_fclose`, at [HLG]. *)
Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).
(** The functions of the genv that the callees call. *)
Context `{Hwrite : !Defines ge "__GI___write" Unit_io_write_os.fn___GI___libc_write}
  (Hfw : ge_fn ge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write)
  `{Hfree_fn : !Defines ge "free" free_fn}
  (Hfh : frees_heap (ge_free ge))
  (Hzf : find_fn ge zgc_free_name = None)
  (Hzg : lookup zgc_free_name (ge_globals ge) = None)
  `{Hcn : !Defines ge "__GI___close_nocancel" Unit_io_close_nocancel_os.fn___GI___close_nocancel}
  (Hfc : ge_fn ge "__GI__IO_file_close" Unit_libio_fileops_os.fn___GI__IO_file_close)
  `{Hsetb : !Defines ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb}
  `{Hdwf : !Defines ge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write}
  `{Hfum : !Defines ge "__GI__IO_unsave_markers" Unit_libio_genops_os.fn___GI__IO_unsave_markers}
  `{Hpush : !Defines ge "__GI___libc_cleanup_push_defer" Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_push_defer}
  `{Hpop : !Defines ge "__GI___libc_cleanup_pop_restore" Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_pop_restore}
  `{Hunl : !Defines ge "__GI__IO_un_link" Unit_libio_genops_os.fn___GI__IO_un_link}
  `{Hdf : !Defines ge "__GI__IO_default_finish" Unit_libio_genops_os.fn___GI__IO_default_finish}
  (Hff : ge_fn ge "_IO_new_file_finish" Unit_libio_fileops_os.fn__IO_new_file_finish)
  `{Hcif : !Defines ge "_IO_file_close_maybe_unlink" Unit_libio_fileops_os.fn__IO_file_close_maybe_unlink}.


(** LibioFclose.v's [wp_glibc__IO_new_fclose_stdout] with its callees
    proved. *)
Definition hi_fclose_stdout :=
  LibioFclose.wp_glibc__IO_new_fclose_stdout Hreg Hext Hff
    (hi_close_it Hreg Hext Hfw Hfh Hzf Hzg Hfc)
    (LibioUnlink.wp_glibc__IO_un_link Hreg Hext)
    (LibioUnlink.wp_glibc__IO_un_link_unlinked).

End rules.
