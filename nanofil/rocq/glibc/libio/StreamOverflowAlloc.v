From Glibc Require Import Unit_io_fstat64_os Unit_io_write_os Unit_libio_filedoalloc_os Unit_libio_fileops_os Unit_libio_genops_os.
From Glibc Require Import Unit_misc_makedev_os Unit_termios_isatty_nostatus_os.
From Glibc Require Import GlibcProgram.
(** stdout initially has no buffer. Its first overflow allocates one,
    switches the stream to writing, and sends the requested byte. This
    file joins allocation with the proved pointer resets and send path.
    The allocator's thread cache remains available to the caller. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv
  LibioLogic SysWrappers AllocLogic LibioDoAllocBuf LibioOverflowAllocSetg LibioOverflowAlloc
  AllocCall StreamDoAlloc StreamOverflow.
Import ListNotations.
Open Scope Z_scope.

(** The buffer allocation call uses the common interpreter logic. *)
(** The new buffer's read pointers use the common interpreter logic. *)
(** The first overflow uses the common interpreter logic. *)

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hstat : ge_fn ge "__GI__IO_file_stat" Unit_libio_fileops_os.fn___GI__IO_file_stat)
  (Hfstat : Defines ge "__GI___fstat64" Unit_io_fstat64_os.fn___GI___fstat64)
  (Hmaj : Defines ge "__gnu_dev_major" Unit_misc_makedev_os.fn___gnu_dev_major)
  (Hisatty : Defines ge "__isatty_nostatus" Unit_termios_isatty_nostatus_os.fn___isatty_nostatus)
  (Hsetb : Defines ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb).
Context (Hfree_fn : Defines ge "free" free_fn) (Hfh : frees_heap (ge_free ge))
  (Hzf : find_fn ge zgc_free_name = None) (Hzg : lookup zgc_free_name (ge_globals ge) = None).
Context (Hmalloc_fn : Defines ge "malloc" malloc_fn)
  (Hmalloc2 : Defines ge "glibc_malloc#__libc_malloc2" malloc2_fn).
Existing Instances Hfstat Hmaj Hisatty Hsetb Hfree_fn Hmalloc_fn Hmalloc2.
Context (dq : dfrac) (mp tc dummy : Z) (mpr tcr dr : region).
Context (Hmp : lookup (TAtom "glibc_malloc#mp_") (ge_globals ge) = Some (mkPtr mp (Obj mp)))
  (Htc : lookup (TAtom "tcache") (ge_globals ge) = Some (mkPtr tc (Obj tc))).
Context (Hda : ge_fn ge "__GI__IO_file_doallocate" Unit_libio_filedoalloc_os.fn___GI__IO_file_doallocate)
  (Hdab : Defines ge "__GI__IO_doallocbuf" Unit_libio_genops_os.fn___GI__IO_doallocbuf)
  (Hwrite : Defines ge "__GI___write" Unit_io_write_os.fn___GI___libc_write)
  (Hfw : ge_fn ge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write)
  (Hdwf : Defines ge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write).
Existing Instances Hdab Hwrite Hdwf.

(** A stream without a buffer calls the proved buffer allocator. *)
Definition hi_doallocbuf :=
  program_call(LibioDoAllocBuf.wp_glibc__IO_doallocbuf_alloc (glibc_program := program_of w0 registry ge) Hda
    (malloc_call_state dq mp tc dummy mpr tcr dr)
    (hi_doallocate (glibc_program := program_of w0 registry ge) Hreg Hext Hstat (Hfstat := Hfstat) (Hmaj := Hmaj) (Hisatty := Hisatty) (Hsetb := Hsetb) (Hfree_fn := Hfree_fn) Hfh Hzf Hzg
       (Hmalloc_fn := Hmalloc_fn) (Hmalloc2 := Hmalloc2) dq mp tc dummy mpr tcr dr Hmp Htc)).

(** The new buffer becomes the stream's read and write area. *)
Definition hi_ovf_L33 :=
  program_call(LibioOverflowAllocSetg.wp_ovf_L33 (glibc_program := program_of w0 registry ge) (Hdabf := Hdab) (malloc_call_state dq mp tc dummy mpr tcr dr) hi_doallocbuf
    (hi_ovf_L35 w0 registry ge Hreg Hext Hwrite Hfw Hdwf)).

(** The first overflow allocates its buffer and then sends the byte. *)
Definition hi_overflow_alloc :=
  program_call(LibioOverflowAlloc.wp_glibc__IO_new_file_overflow_alloc (glibc_program := program_of w0 registry ge)
    (malloc_call_state dq mp tc dummy mpr tcr dr) hi_ovf_L33).

End rules.
