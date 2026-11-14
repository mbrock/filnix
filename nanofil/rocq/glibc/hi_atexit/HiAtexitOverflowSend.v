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
From Glibc Require LibioDoWrite LibioOverflowCall LibioOverflowFlush LibioOverflowFull LibioOverflowPut LibioOverflowSend.
Import ListNotations.
Open Scope Z_scope.

(** The flush call uses the common interpreter logic. *)
(** The newline flush uses the common interpreter logic. *)
(** The byte store uses the common interpreter logic. *)
(** The full-buffer branch uses the common interpreter logic. *)
(** The send branch uses the common interpreter logic. *)

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hwrite : find_fn ge (TAtom "__GI___write") = Some (Defined glibc___libc_write))
  (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
  (Hdwf : find_fn ge (TAtom "_IO_new_do_write") = Some (Defined glibc__IO_new_do_write)).

(** A flush of pending bytes uses the proved write from the buffer base. *)
Definition hi_ovf_do_write :=
  LibioOverflowCall.wp_ovf_do_write w0 registry ge (fun f2 => Z.land f2 2 = 0)
    (hi_do_write_base w0 registry ge Hreg Hext Hwrite Hfw).

(** A newline flush uses the proved write from the buffer base. *)
Definition hi_ovf_L264 :=
  LibioOverflowFlush.wp_ovf_L264 w0 registry ge Hdwf (fun f2 => Z.land f2 2 = 0)
    (hi_do_write_base w0 registry ge Hreg Hext Hwrite Hfw).

(** Storing a byte may continue into the proved newline flush. *)
Definition hi_ovf_L198 := LibioOverflowPut.wp_ovf_L198 w0 registry ge (fun f2 => Z.land f2 2 = 0) hi_ovf_L264.

(** A full buffer is flushed before the byte store. *)
Definition hi_ovf_L196 := LibioOverflowFull.wp_ovf_L196 w0 registry ge Hdwf (fun f2 => Z.land f2 2 = 0) hi_ovf_do_write hi_ovf_L198.

(** Sending a byte handles empty, full, and partly filled buffers. *)
Definition hi_ovf_L18 :=
  LibioOverflowSend.wp_ovf_L18 w0 registry ge Hdwf (fun f2 => Z.land f2 2 = 0)
    (LibioDoWrite.wp_glibc__IO_new_do_write_zero w0 registry ge) hi_ovf_do_write hi_ovf_L198 hi_ovf_L196.

(* Both write branches retain flags2; the set-bit branch resolves the captured wrapper. *)
Local Definition nocancel_ready (f2 : Z) : Prop :=
  Z.land f2 2 = 0 \/
  Z.land f2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel).

(** A pending-byte flush also supports a stream that disables cancellation.
    The write returns the exact flags2 value and retains the buffer bytes on failure. *)
Definition hi_ovf_do_write_nocancel :=
  LibioOverflowCall.wp_ovf_do_write w0 registry ge nocancel_ready
    (hi_do_write_base_nocancel w0 registry ge Hreg Hext Hwrite Hfw).

(** A newline flush uses the same captured noncanceling write wrapper. *)
Definition hi_ovf_L264_nocancel :=
  LibioOverflowFlush.wp_ovf_L264 w0 registry ge Hdwf nocancel_ready
    (hi_do_write_base_nocancel w0 registry ge Hreg Hext Hwrite Hfw).

(** A byte store retains the noncanceling flush when the stream needs one. *)
Definition hi_ovf_L198_nocancel :=
  LibioOverflowPut.wp_ovf_L198 w0 registry ge nocancel_ready hi_ovf_L264_nocancel.

(** A full buffer uses the noncanceling flush before storing another byte. *)
Definition hi_ovf_L196_nocancel :=
  LibioOverflowFull.wp_ovf_L196 w0 registry ge Hdwf nocancel_ready hi_ovf_do_write_nocancel hi_ovf_L198_nocancel.

(** Sending a byte or flushing EOF permits cancellation to be disabled.
    Short writes and errors remain possible, and no path acquires or releases a stream lock. *)
Definition hi_ovf_L18_nocancel :=
  LibioOverflowSend.wp_ovf_L18 w0 registry ge Hdwf nocancel_ready
    (LibioDoWrite.wp_glibc__IO_new_do_write_zero w0 registry ge)
    hi_ovf_do_write_nocancel hi_ovf_L198_nocancel hi_ovf_L196_nocancel.

End rules.
