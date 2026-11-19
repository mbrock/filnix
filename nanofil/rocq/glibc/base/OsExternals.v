(** Programs can provide glibc's system calls and heap operations through
    the runtime. These predicates say which names the linker leaves external
    and which contracts the program registers for the OS. *)

From iris.proofmode Require Import proofmode.
From Stdlib Require Import List String.
From Nanofil Require Import Term Values Runtime Semantics ExternalCalls.
From Glibc Require Import OsWorld OsRegistry.
Import ListNotations.
Local Open Scope string_scope.

(** The wrappers call these runtime operations. *)
Definition sys_externals : list string :=
  ["zsys_write"; "zsys_fstat"; "zsys_ioctl"; "zsys_lseek"; "zsys_close"; "zsys_exit_hard";
   "zsys_exit_soft"; "zthread_self_cookie"].

(** The program leaves these names undefined as functions and global data.
    Calls therefore use the external contracts supplied by the registry. *)
Definition sys_external (ge : genv) : Prop :=
  Forall (fun s => find_fn ge (TAtom s) = None /\ lookup (TAtom s) (ge_globals ge) = None) sys_externals.

(** The registry holds the contracts of [glibc_os_registry]. *)
Definition holds_os (registry : name -> option (contract os_world)) : Prop :=
  forall n c, glibc_os_registry n = Some c -> registry n = Some c.

(** The genv ge leaves `c: malloc` and `c: free` to the model: neither
    is defined or held as data, and its free frees heap objects. *)
Definition heap_fns (ge : genv) : Prop :=
  frees_heap (ge_free ge) /\ find_fn ge (TAtom "free") = None /\ lookup (TAtom "free") (ge_globals ge) = None /\
  find_fn ge (TAtom "malloc") = None /\ lookup (TAtom "malloc") (ge_globals ge) = None.

Section lookup.
Context (registry : name -> option (contract os_world)) (ge : genv)
  (Hreg : holds_os registry) (Hext : sys_external ge).
Lemma reg_of s c : glibc_os_registry (TAtom s) = Some c -> registry (TAtom s) = Some c.
Proof using Type*. apply Hreg. Qed.
Lemma ext_fn s : In s sys_externals -> find_fn ge (TAtom s) = None.
Proof using Type*. intros Hin. exact (proj1 (proj1 (Forall_forall _ _) Hext s Hin)). Qed.
Lemma ext_data s : In s sys_externals -> lookup (TAtom s) (ge_globals ge) = None.
Proof using Type*. intros Hin. exact (proj2 (proj1 (Forall_forall _ _) Hext s Hin)). Qed.
End lookup.
