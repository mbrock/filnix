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
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode LibioGenCode
  LibioUnlinkCode LibioCloseItCode FileInv LibioLogic SysWrappers AllocLogic LibioUnlink LibioFclose
  HiAtexitBase HiAtexitCloseIt.
Import ListNotations.
Open Scope Z_scope.

(** `c: _IO_un_link`, at [HLG]. *)
Module HUL := LibioUnlinkOn InterpRuntime HLG.
(** `c: _IO_new_fclose`, at [HLG]. *)
Module HFC := LibioFcloseOn InterpRuntime HLG.
Import HFC.FU.FT.FN.CS.SW HFC.FU.FT.FN.CS.SW.FI.ML HFC.FU.FT.FN.CS.SW.FI.LG HFC.FU.FT.FN.CS.SW.FI.L
  HFC.FU.FT.FN.CS.SW.OW HFC.FU.FT.FN.CS.SW.FI HFC.FU.FT.FN.CS.SW.ST.

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
  (Hfum : find_fn ge (TAtom "__GI__IO_unsave_markers") = Some (Defined glibc__IO_unsave_markers))
  (Hpush : find_fn ge (TAtom "__GI___libc_cleanup_push_defer") = Some (Defined glibc___libc_cleanup_push_defer))
  (Hpop : find_fn ge (TAtom "__GI___libc_cleanup_pop_restore") = Some (Defined glibc___libc_cleanup_pop_restore))
  (Hunl : find_fn ge (TAtom "__GI__IO_un_link") = Some (Defined glibc__IO_un_link))
  (Hdf : find_fn ge (TAtom "__GI__IO_default_finish") = Some (Defined glibc__IO_default_finish))
  (Hff : ge_fn ge "_IO_new_file_finish" glibc__IO_new_file_finish)
  (Hcif : find_fn ge (TAtom "_IO_file_close_maybe_unlink") = Some (Defined glibc__IO_file_close_maybe_unlink)).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance hi_fclose_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** LibioFclose.v's [wp_glibc__IO_new_fclose_stdout] with its callees
    proved. *)
Definition hi_fclose_stdout :=
  HFC.wp_glibc__IO_new_fclose_stdout w0 registry ge Hreg Hext Hunl Hdf Hff Hcif
    (hi_close_it w0 registry ge Hreg Hext Hwrite Hfw Hfree_fn Hfh Hzf Hzg Hcn Hfc Hsetb Hdwf Hfum)
    (HUL.wp_glibc__IO_un_link w0 registry ge Hreg Hext Hpush Hpop)
    (HUL.wp_glibc__IO_un_link_unlinked w0 registry ge).

End rules.
