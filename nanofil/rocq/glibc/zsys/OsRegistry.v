(** When compiled userland glibc code runs on the formal machine, every
    call to a libpizlo entry point looks up its [[external call|contract]]
    in a symbol table. This module builds that table, [glibc_os_registry],
    over the shared state [os_world] from [OsWorld](OsWorld.v). It
    combines the nine system-call and thread contracts from this directory
    with the memory-copy and memory-fill contracts for `c: zmemmove` and
    `c: zmemset` from
    [ExternalCalls](../../theories/external/ExternalCalls.v). Any call to
    an unmodeled symbol, such as `c: abort`, `c: zsys_dlopen`, or
    `c: zgc_realloc`, finds no entry in [glibc_os_registry] and halts the
    labelled machine with [MissingContract].

    ## Why zmemmove and zmemset require void call sites

    In `libpas/src/libpas/filc_runtime.c`, libpizlo declares
    `c: void zmemmove(void *dst, void *src, size_t count)` and
    `c: void zmemset(void *dst, unsigned value, size_t count)` with a
    `c: void` return type. If a caller invokes either function through a
    function pointer typed as returning `c: void *`, the runtime does not
    panic; instead it leaves a null pointer with no [[capability]] in the
    return register, as verified by [zsys-mem.c](zsys-mem.c).

    In [ExternalCalls](../../theories/external/ExternalCalls.v), however,
    [memmove_contract] and [memset_contract] model the standard C
    functions `c: memmove` and `c: memset`, which return the destination
    pointer `c: dst`. Reusing those contracts directly at a result-binding
    call site of `c: zmemmove` or `c: zmemset` would falsely promise that
    the call returns `c: dst`. The combinator [void_only] below restricts
    both contracts to [CVoid] call sites that discard the return value,
    while keeping the same preconditions and memory effects. *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values Memory ExternalCalls.
From Glibc Require Import OsWorld OsWrite OsWritev OsFstat OsIoctl OsLseek OsClose OsExit OsThread.
Import ListNotations.
Open Scope string_scope.

(** Given a contract c, [void_only] produces a contract with the same
    preconditions, writable spans, effects, and postconditions, but
    restricts the ABI so that only [CVoid] call sites are accepted. *)
Definition void_only {world : Type} (c : contract world) : contract world :=
  mkContract world (contract_returns c) (fun r args => r = CVoid /\ contract_abi c r args)
    (contract_pre c) (contract_sources c) (contract_writes c) (contract_releases c)
    (contract_requests c) (contract_prefix c) (contract_post c) (contract_resource c) (contract_panics c).

(** A call site satisfies the ABI of [void_only] if and only if it
    discards the return value with [CVoid] and satisfies the underlying
    contract's ABI. *)
Lemma void_only_abi {world : Type} (c : contract world) r args :
  contract_abi (void_only c) r args <-> r = CVoid /\ contract_abi c r args.
Proof. reflexivity. Qed.

(** Every field of [void_only] except the ABI predicate is identical to
    the corresponding field of the underlying contract. *)
Lemma void_only_fields {world : Type} (c : contract world) :
  contract_returns (void_only c) = contract_returns c /\ contract_pre (void_only c) = contract_pre c /\
  contract_sources (void_only c) = contract_sources c /\ contract_writes (void_only c) = contract_writes c /\
  contract_releases (void_only c) = contract_releases c /\
  contract_requests (void_only c) = contract_requests c /\ contract_prefix (void_only c) = contract_prefix c /\
  contract_post (void_only c) = contract_post c /\ contract_resource (void_only c) = contract_resource c /\
  contract_panics (void_only c) = contract_panics c.
Proof. repeat split. Qed.

(** A call site that binds the return value of `c: zmemmove` to a
    destination register is rejected by [void_only]. *)
Example zmemmove_result_refused d args : ~ contract_abi (void_only (memmove_contract unit)) (CResult d P) args.
Proof. intros [H _]. discriminate H. Qed.

(** The association list [glibc_os_contracts] pairs each modeled libpizlo
    symbol name with its contract over [os_world]. *)
Definition glibc_os_contracts : list (string * contract os_world) := [
  ("zsys_write", os_write_contract);
  ("zsys_writev", os_writev_contract);
  ("zsys_fstat", os_fstat_contract);
  ("zsys_ioctl", os_ioctl_contract);
  ("zsys_lseek", os_lseek_contract);
  ("zsys_close", os_close_contract);
  ("zsys_exit_soft", os_exit_soft_contract);
  ("zsys_exit_hard", os_exit_hard_contract);
  ("zthread_self_cookie", os_self_contract);
  ("zmemmove", void_only (memmove_contract os_world));
  ("zmemset", void_only (memset_contract os_world))
].

(** Given a symbol name and an association list of contracts, [os_find]
    returns the first contract whose key matches the symbol, or `None` if
    the symbol is absent. *)
Fixpoint os_find (s : name) (cs : list (string * contract os_world)) : option (contract os_world) :=
  match cs with
  | [] => None
  | (k, c) :: cs' => if name_eqb s (TAtom k) then Some c else os_find s cs'
  end.

(** Looking up a symbol name in [glibc_os_contracts] with [os_find]
    defines the external-call registry [glibc_os_registry] for userland
    glibc proofs. *)
Definition glibc_os_registry (s : name) : option (contract os_world) := os_find s glibc_os_contracts.

(** Looking up any of the eleven modeled libpizlo symbols in
    [glibc_os_registry] returns its contract from this directory or from
    [ExternalCalls](../../theories/external/ExternalCalls.v). *)
Example glibc_os_registry_hits :
  glibc_os_registry (TAtom "zsys_write") = Some os_write_contract /\
  glibc_os_registry (TAtom "zsys_writev") = Some os_writev_contract /\
  glibc_os_registry (TAtom "zsys_fstat") = Some os_fstat_contract /\
  glibc_os_registry (TAtom "zsys_ioctl") = Some os_ioctl_contract /\
  glibc_os_registry (TAtom "zsys_lseek") = Some os_lseek_contract /\
  glibc_os_registry (TAtom "zsys_close") = Some os_close_contract /\
  glibc_os_registry (TAtom "zsys_exit_soft") = Some os_exit_soft_contract /\
  glibc_os_registry (TAtom "zsys_exit_hard") = Some os_exit_hard_contract /\
  glibc_os_registry (TAtom "zthread_self_cookie") = Some os_self_contract /\
  glibc_os_registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)) /\
  glibc_os_registry (TAtom "zmemset") = Some (void_only (memset_contract os_world)).
Proof. repeat split. Qed.

(** Heap deallocation functions handled by the machine's own free step,
    together with unmodeled runtime calls that verified code must never
    reach, return `None` in [glibc_os_registry]. *)
Example glibc_os_registry_misses :
  Forall (fun s => glibc_os_registry (TAtom s) = None)
    ["free"; "zgc_free"; "zgc_realloc"; "abort"; "zsys_futex_wait"; "zsys_wait4"; "zlongjmp"; "zsys_dlopen"].
Proof. repeat constructor. Qed.
