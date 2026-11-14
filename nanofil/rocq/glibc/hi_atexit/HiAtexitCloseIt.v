From Glibc Require Import GlibcProgram.
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

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).
(** The functions of the genv that the callees call. *)
Context `{Hwrite : !Defines ge "__GI___write" glibc___libc_write}
  (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
  `{Hfree_fn : !Defines ge "free" free_fn}
  (Hfh : frees_heap (ge_free ge))
  (Hzf : find_fn ge zgc_free_name = None)
  (Hzg : lookup zgc_free_name (ge_globals ge) = None)
  `{Hcn : !Defines ge "__GI___close_nocancel" glibc___close_nocancel}
  (Hfc : ge_fn ge "__GI__IO_file_close" glibc__IO_file_close)
  `{Hsetb : !Defines ge "__GI__IO_setb" glibc__IO_setb}
  `{Hdwf : !Defines ge "_IO_new_do_write" glibc__IO_new_do_write}
  `{Hfum : !Defines ge "__GI__IO_unsave_markers" glibc__IO_unsave_markers}.


(** LibioCloseItMid.v's [close_spec]: LibioRead.v's
    [wp_glibc__IO_file_close], ge's `c: __close_nocancel` glibc's. *)
Lemma hi_close : LibioCloseItMid.close_spec w0 registry ge.
Proof.
  intros fr fb freg fd eb Φ Hfr Hfb Hfal Hfend Hfreg He.
  exact (LibioRead.wp_glibc__IO_file_close Hreg Hext fr fb freg fd eb Φ Hfr Hcn Hfb Hfal Hfend Hfreg He).
Qed.

(** LibioCloseIt.v's [wp_glibc__IO_file_close_maybe_unlink] with its
    callees proved. *)
Definition hi_close_it :=
  LibioCloseIt.wp_glibc__IO_file_close_maybe_unlink Hfc
    (hi_do_write_mode Hreg Hext Hfw)
    (LibioDoWrite.wp_glibc__IO_new_do_write_zero)
    hi_close (hi_setb Hfh Hzf Hzg)
    glibc__IO_unsave_markers (LibioGenLeaves.unsave_spec_holds).

End rules.
