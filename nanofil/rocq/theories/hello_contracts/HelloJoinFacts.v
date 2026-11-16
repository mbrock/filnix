(** Printing the greeting requires aligned storage and a call to setlocale.
    These facts describe the allocation size, greeting bytes, and calling convention without depending on a runtime. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run StepRules Symbolic
  ExternalCalls LibcCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic LibcStringLogic MemLogic LibcMemLogic
  LentLogic Locale LocaleLogic Libc HelloModule HelloLeaf HelloLocale HelloConvDefs
  HelloName HelloProgName HelloClose HelloVersion Startup Getopt GetoptLogic.
Open Scope Z_scope.
Open Scope list_scope.

Module JoinDefinitions.
(** The linked module supplies the code for xmalloc. *)
Definition xmalloc_fn : func := Eval vm_compute in hello_fn "xmalloc".

(** A block name selects the corresponding instructions from xmalloc. *)
Definition xmalloc_block (s : String.string) : block := hblk xmalloc_fn s.

(** A 16-aligned address is 4-aligned. *)
Lemma mod16_mod4 b : b mod 16 = 0 -> b mod 4 = 0.
Proof.
  intros H. apply Z.mod_divide; [lia |]. apply (Z.divide_trans 4 16 b).
  - exists 4. reflexivity.
  - apply Z.mod_divide; [lia | exact H].
Qed.

(** The traditional greeting contains the bytes of "hello, world". *)
Definition traditional_bytes : list Z := [104; 101; 108; 108; 111; 44; 32; 119; 111; 114; 108; 100].

(** setlocale returns a pointer. *)
Lemma setlocale_returns rep requests : contract_returns (libc_setlocale_contract rep requests) = RClass P.
Proof. reflexivity. Qed.

(** A locale query passes a category and a pointer, then receives a pointer result. *)
Lemma setlocale_query_abi rep requests d c v :
  contract_abi (libc_setlocale_contract rep requests) (CResult d P) [Arg W c; Arg P v].
Proof. split; [right; exists d; reflexivity | exists c, v; reflexivity]. Qed.

End JoinDefinitions.
