(** When stdout first switches to writing, glibc resets its read and
    write pointers to the buffer's base. It then stores or flushes the
    requested byte. This file joins the pointer-reset proofs with the
    proved send path, for both a stream already writing and a stream
    that has just received its buffer. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode FileInv
  LibioLogic SysWrappers LibioOverflowBase LibioOverflowSetpEnd LibioOverflowSetpRest LibioOverflowSetp
  LibioOverflow HiAtexitBase HiAtexitOverflowSend.
Import ListNotations.
Open Scope Z_scope.

(** The final pointer resets use the common interpreter logic. *)
Module HOE := LibioOverflowSetpEndOn InterpRuntime HLG.
(** The write-pointer resets use the common interpreter logic. *)
Module HOR := LibioOverflowSetpRestOn InterpRuntime HLG.
(** The first pointer resets use the common interpreter logic. *)
Module HOSP := LibioOverflowSetpOn InterpRuntime HLG.
(** The overflow entry uses the common interpreter logic. *)
Module HOV := LibioOverflowOn InterpRuntime HLG.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hwrite : find_fn ge (TAtom "__GI___write") = Some (Defined glibc___libc_write))
  (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
  (Hdwf : find_fn ge (TAtom "_IO_new_do_write") = Some (Defined glibc__IO_new_do_write)).

(** Line-buffered streams keep the write end at the write pointer. *)
Definition hi_ovf_L162 :=
  HOE.wp_ovf_L162 w0 registry ge (hi_ovf_L18 w0 registry ge Hreg Hext Hwrite Hfw Hdwf).

(** The stream starts writing at the buffer's base. *)
Definition hi_ovf_L113_rest := HOR.wp_ovf_L113_rest w0 registry ge hi_ovf_L162.

(** The stream discards its read area before writing. *)
Definition hi_ovf_L113 := HOSP.wp_ovf_L113 w0 registry ge hi_ovf_L113_rest.

(** A stream with a new buffer switches to writing through the proved resets. *)
Definition hi_ovf_L35 :=
  HOE.wp_ovf_L35 w0 registry ge hi_ovf_L113.

(** Overflow on a stream already writing uses the proved send path. *)
Definition hi_overflow :=
  HOV.wp_glibc__IO_new_file_overflow w0 registry ge
    (hi_ovf_L18 w0 registry ge Hreg Hext Hwrite Hfw Hdwf).

End rules.
