(** The registry of user glibc's calls into libpizlo over the
    [os_world] of [OsWorld](OsWorld.v): the nine OS contracts of this
    directory and ExternalCalls.v's memory contracts for libpizlo's
    `c: zmemmove` and `c: zmemset`, restricted to void call sites
    ([void_only]). Every other name, including `c: zgc_realloc`
    (ExternalCalls.v has no realloc contract at this pin), abort,
    futex, wait4, unwinding, `c: zlongjmp` and `c: dlopen`, has none, so
    the labelled machine stops a call of it with [MissingContract].

    `c: void zmemmove(void *dst, void *src, size_t count)` and `c: void
    zmemset(void *dst, unsigned value, size_t count)` return nothing
    (libpas/src/libpas/filc_runtime.c:6366, 6371). Called through a
    pointer to a function returning `c: void *`, they do not panic with
    [ReturnSize]: the result is a null pointer with no capability, as
    zsys-mem.c checks. [memmove_contract] and [memset_contract] promise
    the destination, so a site that reads a result would be told the
    wrong word. [void_only] admits only a [CVoid] site, which discards
    whatever the contract returns; any other site is a [BadABI]
    violation. The memory effect is unchanged ([void_only_fields]).
    MemLogic.v's [wp_memset] and [wp_memcpy] are stated at a
    [CResult] site of `c: memset` and `c: memcpy`; a void-site variant
    for these symbols belongs there. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values Memory ExternalCalls.
From Glibc Require Import OsWorld OsWrite OsWritev OsFstat OsIoctl OsLseek OsClose OsExit OsThread.
Import ListNotations.
Open Scope string_scope.

(** The contract c restricted to call sites that discard the result:
    every field is c's, but the ABI also asks for [CVoid]. *)
Definition void_only {world : Type} (c : contract world) : contract world :=
  mkContract world (contract_returns c) (fun r args => r = CVoid /\ contract_abi c r args)
    (contract_pre c) (contract_sources c) (contract_writes c) (contract_releases c)
    (contract_requests c) (contract_prefix c) (contract_post c) (contract_resource c) (contract_panics c).

(** [void_only] admits only a [CVoid] site, and only one c admits. *)
Lemma void_only_abi {world : Type} (c : contract world) r args :
  contract_abi (void_only c) r args <-> r = CVoid /\ contract_abi c r args.
Proof. reflexivity. Qed.

(** Every field of [void_only] c but the ABI is c's: the same
    precondition, roots, effects and postcondition. *)
Lemma void_only_fields {world : Type} (c : contract world) :
  contract_returns (void_only c) = contract_returns c /\ contract_pre (void_only c) = contract_pre c /\
  contract_sources (void_only c) = contract_sources c /\ contract_writes (void_only c) = contract_writes c /\
  contract_releases (void_only c) = contract_releases c /\
  contract_requests (void_only c) = contract_requests c /\ contract_prefix (void_only c) = contract_prefix c /\
  contract_post (void_only c) = contract_post c /\ contract_resource (void_only c) = contract_resource c /\
  contract_panics (void_only c) = contract_panics c.
Proof. repeat split. Qed.

(** A site that binds the result of `c: zmemmove` is refused. *)
Example zmemmove_result_refused d args : ~ contract_abi (void_only (memmove_contract unit)) (CResult d P) args.
Proof. intros [H _]. discriminate H. Qed.

(** The contracts, by symbol. *)
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

(** The contract of the symbol s, if it has one. *)
Fixpoint os_find (s : name) (cs : list (string * contract os_world)) : option (contract os_world) :=
  match cs with
  | [] => None
  | (k, c) :: cs' => if name_eqb s (TAtom k) then Some c else os_find s cs'
  end.

(** The registry. *)
Definition glibc_os_registry (s : name) : option (contract os_world) := os_find s glibc_os_contracts.

(** Each symbol finds its own contract: the hypotheses the rules of
    the Os*.v files take. *)
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

(** Names with no contract: the frees (the runtime's own operation),
    realloc, and the calls the proof must show are never reached. *)
Example glibc_os_registry_misses :
  Forall (fun s => glibc_os_registry (TAtom s) = None)
    ["free"; "zgc_free"; "zgc_realloc"; "abort"; "zsys_futex_wait"; "zsys_wait4"; "zlongjmp"; "zsys_dlopen"].
Proof. repeat constructor. Qed.
