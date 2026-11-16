(** GNU Hello initializes its state, converts its greeting, and prints it.
    This module connects those proofs to one runtime and exposes the
    whole-program safety theorem under its original public path. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run StepRules Symbolic
  ExternalCalls LibcCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic LibcStringLogic MemLogic LibcMemLogic
  LentLogic Locale LocaleLogic Libc HelloModule HelloLeaf HelloLocale HelloConvDefs HelloConv
  HelloName HelloProgName HelloClose HelloVersion Startup Getopt GetoptLogic HelloMain.
Open Scope Z_scope.
Open Scope list_scope.

From Nanofil Require Import HelloJoinFacts HelloJoinComplete.
Include JoinDefinitions.
Module HelloJoin (R : Runtime).
Module HM. Include HelloMain R. End HM.
Module HC. Include HelloConvOn R HM.LG0. End HC.
Module HCl. Include HelloCloseOn R HM.LG0. End HCl.
Import HM.LG0 HM.LG0.L.
Local Instance join_irisGS (registry : name -> option (contract libc_world))
  (wi : mem -> libc_world -> gmap piece pval -> Prop) (ge : genv)
  {hlc Σ} `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.
Include HelloJoinComplete R.
End HelloJoin.
