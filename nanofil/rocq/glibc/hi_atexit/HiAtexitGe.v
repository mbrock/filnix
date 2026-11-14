(** The glibc proofs assume a few facts about the genv they run in:
    that it does not define the system calls, that `c: zmemmove` is
    left to the model, and that each function a jump table names is
    laid out at its own symbol. This file proves those facts for the
    linked genv of hi_atexit.c by computation, once, so that the
    composition files can cite them.

    | Lemma | Fact |
    |---|---|
    | [hi_sys_external] | no system call is defined in the program |
    | [hi_move] | `c: zmemmove` is external |
    | [hi_ge_file_write] and the others | [ge_fn] of a function called through a jump table |
    | [hge], [hge_frees], [hge_zgc_free] | the genv with the interpreter's free | *)

From Glibc Require Import GlibcTactics LibioTactics.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics ExternalCalls.
From Glibc Require Import HiAtexitModule HiAtexitFns OsWorld OsRegistry SysWrappers LibioLogic SysCode
  LibioReadCode LibioDoWriteCode LibioGenCode LibioXsputnCode LibioUnlinkCode.
Import ListNotations.
Open Scope string_scope.

Section ge.
(** The runtime's free, which the genv carries. *)
Variable fre : word -> mem -> option (res unit * mem).

(** No system call of [sys_externals] is defined by the linked program,
    as code or as data. *)
Lemma hi_sys_external : sys_external (hi_ge fre).
Proof.
  unfold sys_external, sys_externals.
  repeat (apply Forall_cons; [split; vm_compute; reflexivity |]). apply Forall_nil.
Qed.

(** `c: zmemmove` is not defined by the linked program, as code or as
    data, and the registry holds its contract. *)
Lemma hi_move : glibc_os_registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)) /\
  find_fn (hi_ge fre) (TAtom "zmemmove") = None /\ lookup (TAtom "zmemmove") (ge_globals (hi_ge fre)) = None.
Proof. split; [reflexivity|]. vm_compute. split; reflexivity. Qed.

(** `c: _IO_new_file_write` is laid out at its own symbol. *)
Lemma hi_ge_file_write : ge_fn (hi_ge fre) "_IO_new_file_write" glibc__IO_new_file_write.
Proof. eexists. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. lia. Qed.

(** `c: _IO_new_file_xsputn` is laid out at its own symbol. *)
Lemma hi_ge_xsputn : ge_fn (hi_ge fre) "_IO_new_file_xsputn" glibc__IO_new_file_xsputn.
Proof. eexists. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. lia. Qed.

(** `c: _IO_new_file_overflow` is laid out at its own symbol. *)
Lemma hi_ge_overflow : ge_fn (hi_ge fre) "_IO_new_file_overflow" glibc__IO_new_file_overflow.
Proof. eexists. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. lia. Qed.

(** `c: _IO_file_close` is laid out at its own symbol. *)
Lemma hi_ge_file_close : ge_fn (hi_ge fre) "__GI__IO_file_close" glibc__IO_file_close.
Proof. eexists. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. lia. Qed.

(** `c: _IO_file_stat` is laid out at its own symbol. *)
Lemma hi_ge_file_stat : ge_fn (hi_ge fre) "__GI__IO_file_stat" glibc__IO_file_stat.
Proof. eexists. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. lia. Qed.

(** `c: _IO_file_doallocate` is laid out at its own symbol. *)
Lemma hi_ge_doallocate : ge_fn (hi_ge fre) "__GI__IO_file_doallocate" glibc__IO_file_doallocate.
Proof. eexists. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. lia. Qed.

(** `c: _IO_new_file_finish` is laid out at its own symbol. *)
Lemma hi_ge_file_finish : ge_fn (hi_ge fre) "_IO_new_file_finish" glibc__IO_new_file_finish.
Proof. eexists. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. lia. Qed.

End ge.

(** The linked genv with the interpreter's free: the genv of the
    theorem. *)
Definition hge : genv := hi_ge InterpRuntime.free.

(** The interpreter's free frees heap objects. *)
Lemma hge_frees : frees_heap (ge_free hge).
Proof. exact free_res_succeeds. Qed.

(** `c: zgc_free` is the model's: not defined by the linked program,
    as code or as data. *)
Lemma hge_zgc_free : find_fn hge zgc_free_name = None /\ lookup zgc_free_name (ge_globals hge) = None.
Proof. vm_compute. split; reflexivity. Qed.
