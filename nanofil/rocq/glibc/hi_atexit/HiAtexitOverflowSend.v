(** A full stdout buffer must be flushed before another byte can be
    stored. A newline also flushes a line-buffered stream. This file
    joins the proofs of those paths with the proved write function.
    Failed writes preserve the buffer's ownership and set the stream's
    error flag, so the caller can still close stdout safely. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode FileInv
  LibioLogic SysWrappers LibioOverflowBase LibioOverflowCall LibioOverflowFlush LibioOverflowPut
  LibioOverflowFull LibioOverflowSend HiAtexitBase HiAtexitDoWrite.
Import ListNotations.
Open Scope Z_scope.

(** The flush call uses the common interpreter logic. *)
Module HOC := LibioOverflowCallOn InterpRuntime HLG.
(** The newline flush uses the common interpreter logic. *)
Module HOF := LibioOverflowFlushOn InterpRuntime HLG.
(** The byte store uses the common interpreter logic. *)
Module HOP := LibioOverflowPutOn InterpRuntime HLG.
(** The full-buffer branch uses the common interpreter logic. *)
Module HOU := LibioOverflowFullOn InterpRuntime HLG.
(** The send branch uses the common interpreter logic. *)
Module HOS := LibioOverflowSendOn InterpRuntime HLG.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hwrite : find_fn ge (TAtom "__GI___write") = Some (Defined glibc___libc_write))
  (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
  (Hdwf : find_fn ge (TAtom "_IO_new_do_write") = Some (Defined glibc__IO_new_do_write)).

(** A flush of pending bytes uses the proved write from the buffer base. *)
Definition hi_ovf_do_write :=
  HOC.wp_ovf_do_write w0 registry ge
    (hi_do_write_base w0 registry ge Hreg Hext Hwrite Hfw).

(** A newline flush uses the proved write from the buffer base. *)
Definition hi_ovf_L264 :=
  HOF.wp_ovf_L264 w0 registry ge Hdwf
    (hi_do_write_base w0 registry ge Hreg Hext Hwrite Hfw).

(** Storing a byte may continue into the proved newline flush. *)
Definition hi_ovf_L198 := HOP.wp_ovf_L198 w0 registry ge hi_ovf_L264.

(** A full buffer is flushed before the byte store. *)
Definition hi_ovf_L196 := HOU.wp_ovf_L196 w0 registry ge Hdwf hi_ovf_do_write hi_ovf_L198.

(** Sending a byte handles empty, full, and partly filled buffers. *)
Definition hi_ovf_L18 :=
  HOS.wp_ovf_L18 w0 registry ge Hdwf
    (HDW.wp_glibc__IO_new_do_write_zero w0 registry ge) hi_ovf_do_write hi_ovf_L198 hi_ovf_L196.

End rules.
