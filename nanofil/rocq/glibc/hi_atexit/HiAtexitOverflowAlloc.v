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
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode FileInv
  LibioLogic SysWrappers AllocLogic LibioDoAllocBuf LibioOverflowAllocSetg LibioOverflowAlloc
  HiAtexitBase HiAtexitSetb HiAtexitAlloc HiAtexitDoAlloc HiAtexitOverflow.
From Glibc Require LibioDoAllocBuf LibioOverflowAlloc LibioOverflowAllocSetg.
Import ListNotations.
Open Scope Z_scope.

(** The buffer allocation call uses the common interpreter logic. *)
(** The new buffer's read pointers use the common interpreter logic. *)
(** The first overflow uses the common interpreter logic. *)

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hstat : ge_fn ge "__GI__IO_file_stat" glibc__IO_file_stat)
  (Hfstat : find_fn ge (TAtom "__GI___fstat64") = Some (Defined glibc___fstat64))
  (Hmaj : find_fn ge (TAtom "__gnu_dev_major") = Some (Defined glibc___gnu_dev_major))
  (Hisatty : find_fn ge (TAtom "__isatty_nostatus") = Some (Defined glibc___isatty_nostatus))
  (Hsetb : find_fn ge (TAtom "__GI__IO_setb") = Some (Defined glibc__IO_setb)).
Context (Hfree_fn : find_fn ge (TAtom "free") = Some (Defined free_fn)) (Hfh : frees_heap (ge_free ge))
  (Hzf : find_fn ge zgc_free_name = None) (Hzg : lookup zgc_free_name (ge_globals ge) = None).
Context (Hmalloc_fn : find_fn ge (TAtom "malloc") = Some (Defined malloc_fn))
  (Hmalloc2 : find_fn ge (TAtom "malloc#__libc_malloc2") = Some (Defined malloc2_fn)).
Context (dq : dfrac) (mp tc dummy : Z) (mpr tcr dr : region).
Context (Hmp : lookup (TAtom "malloc#mp_") (ge_globals ge) = Some (mkPtr mp (Obj mp)))
  (Htc : lookup (TAtom "tcache") (ge_globals ge) = Some (mkPtr tc (Obj tc))).
Context (Hda : ge_fn ge "__GI__IO_file_doallocate" glibc__IO_file_doallocate)
  (Hdab : find_fn ge (TAtom "__GI__IO_doallocbuf") = Some (Defined glibc__IO_doallocbuf))
  (Hwrite : find_fn ge (TAtom "__GI___write") = Some (Defined glibc___libc_write))
  (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
  (Hdwf : find_fn ge (TAtom "_IO_new_do_write") = Some (Defined glibc__IO_new_do_write)).

(** A stream without a buffer calls the proved buffer allocator. *)
Definition hi_doallocbuf :=
  program_call(LibioDoAllocBuf.wp_glibc__IO_doallocbuf_alloc (glibc_program := program_of w0 registry ge) Hda
    (hi_malloc_state dq mp tc dummy mpr tcr dr)
    (hi_doallocate (glibc_program := program_of w0 registry ge) Hreg Hext Hstat (Hfstat := Hfstat) (Hmaj := Hmaj) (Hisatty := Hisatty) (Hsetb := Hsetb) (Hfree_fn := Hfree_fn) Hfh Hzf Hzg
       (Hmalloc_fn := Hmalloc_fn) (Hmalloc2 := Hmalloc2) dq mp tc dummy mpr tcr dr Hmp Htc)).

(** The new buffer becomes the stream's read and write area. *)
Definition hi_ovf_L33 :=
  program_call(LibioOverflowAllocSetg.wp_ovf_L33 (glibc_program := program_of w0 registry ge) (Hdabf := Hdab) (hi_malloc_state dq mp tc dummy mpr tcr dr) hi_doallocbuf
    (hi_ovf_L35 w0 registry ge Hreg Hext Hwrite Hfw Hdwf)).

(** The first overflow allocates its buffer and then sends the byte. *)
Definition hi_overflow_alloc :=
  program_call(LibioOverflowAlloc.wp_glibc__IO_new_file_overflow_alloc (glibc_program := program_of w0 registry ge)
    (hi_malloc_state dq mp tc dummy mpr tcr dr) hi_ovf_L33).

End rules.
