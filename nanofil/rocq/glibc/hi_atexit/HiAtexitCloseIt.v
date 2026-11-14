(** Before `c: fclose` drops a stream, it flushes the pending bytes and
    closes the descriptor through `c: _IO_file_close_maybe_unlink`.
    LibioCloseIt.v proves that function from triples of the four
    functions it calls, taken as assumptions. This file proves each
    assumption, so the triple [hi_close_it] assumes only facts about
    the genv.

    | Callee | Its triple |
    |---|---|
    | `c: _IO_new_do_write` | HiAtexitDoWrite.v, and LibioDoWrite.v for no bytes |
    | `c: _IO_file_close` | [hi_close], from LibioRead.v |
    | `c: _IO_setb` | HiAtexitSetb.v, with glibc's `c: free` |
    | `c: _IO_unsave_markers` | LibioGenLeaves.v | *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode LibioGenCode
  LibioUnlinkCode LibioCloseItCode FileInv LibioLogic SysWrappers AllocLogic LibioRead LibioGenLeaves
  LibioCloseIt HiAtexitBase HiAtexitDoWrite HiAtexitSetb.
From Glibc Require FileInv LibioCloseIt LibioCloseItMid LibioDoWrite LibioGenLeaves LibioLogic LibioRead OsWorld SysWrappers.
Import ListNotations.
Open Scope Z_scope.

(** `c: _IO_file_close`, at [HLG]. *)
(** `c: _IO_unsave_markers` and `c: __call_tls_dtors`, at [HLG]. *)
(** `c: _IO_file_close_maybe_unlink`, at [HLG]. *)
Import LibioRead SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
(** The functions of the genv that the callees call. *)
Context (Hwrite : find_fn ge (TAtom "__GI___write") = Some (Defined glibc___libc_write))
  (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
  (Hfree_fn : find_fn ge (TAtom "free") = Some (Defined free_fn)) (Hfh : frees_heap (ge_free ge))
  (Hzf : find_fn ge zgc_free_name = None) (Hzg : lookup zgc_free_name (ge_globals ge) = None)
  (Hcn : find_fn ge (TAtom "__GI___close_nocancel") = Some (Defined glibc___close_nocancel))
  (Hfc : ge_fn ge "__GI__IO_file_close" glibc__IO_file_close)
  (Hsetb : find_fn ge (TAtom "__GI__IO_setb") = Some (Defined glibc__IO_setb))
  (Hdwf : find_fn ge (TAtom "_IO_new_do_write") = Some (Defined glibc__IO_new_do_write))
  (Hfum : find_fn ge (TAtom "__GI__IO_unsave_markers") = Some (Defined glibc__IO_unsave_markers)).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance hi_close_it_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** LibioCloseItMid.v's [close_spec]: LibioRead.v's
    [wp_glibc__IO_file_close], ge's `c: __close_nocancel` glibc's. *)
Lemma hi_close : LibioCloseItMid.close_spec w0 registry ge.
Proof.
  intros fr fb freg fd eb Φ Hfr Hfb Hfal Hfend Hfreg He.
  exact (LibioRead.wp_glibc__IO_file_close w0 registry ge Hreg Hext fr fb freg fd eb Φ Hfr Hcn Hfb Hfal Hfend Hfreg He).
Qed.

(** LibioCloseIt.v's [wp_glibc__IO_file_close_maybe_unlink] with its
    callees proved. *)
Definition hi_close_it :=
  LibioCloseIt.wp_glibc__IO_file_close_maybe_unlink w0 registry ge Hfc Hsetb Hdwf
    (hi_do_write_mode w0 registry ge Hreg Hext Hwrite Hfw)
    (LibioDoWrite.wp_glibc__IO_new_do_write_zero w0 registry ge)
    hi_close (hi_setb w0 registry ge Hfree_fn Hfh Hzf Hzg)
    glibc__IO_unsave_markers Hfum (LibioGenLeaves.unsave_spec_holds w0 registry ge).

End rules.
