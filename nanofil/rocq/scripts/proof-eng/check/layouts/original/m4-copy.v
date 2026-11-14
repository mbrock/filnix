From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld OsRegistry SysCode FileInv LibioLogic SysWrappers
  LibioReadCode LibioDoWriteCode LibioOverflowBase PrintfStreamHeap HiAtexitBase HiAtexitPrintfOverflowHeap.
Import ListNotations.
Open Scope Z_scope.

Print Assumptions PHS.printf_copy_buffer_open.
Print Assumptions PHS.printf_copy_buffer_close.
Print Assumptions PHS.printf_heap_stream_with_forget.
Print Assumptions PHS.printf_heap_stream_with_live.
Print Assumptions PHS.printf_heap_stream_live.
Print Assumptions hi_printf_heap_file_overflow_with.
Print Assumptions hi_printf_heap_file_overflow.

Section copy_entry.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hwrite : find_fn ge (TAtom "__GI___write") = Some (Defined glibc___libc_write))
  (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
  (Hdwf : find_fn ge (TAtom "_IO_new_do_write") = Some (Defined glibc__IO_new_do_write)).
Definition copy_file_overflow :=
  hi_printf_heap_file_overflow_with w0 registry ge Hreg Hext Hwrite Hfw Hdwf PHS.printf_copy_buffer.
End copy_entry.
Print Assumptions copy_file_overflow.
Check copy_file_overflow.
