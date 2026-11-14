(** String callers import this module to obtain contracts for the linked
    glibc functions. Each contract preserves the caller's memory ownership
    and records the function's result in its postcondition.

    Each function's source module proves its contract alongside its execution rules.
    Importing those modules here makes their contracts available to callers
    without requiring callers to know the order of the proofs. *)

From Glibc Require Export GlibcSpec StrlenWord StrnlenLogic StrcmpLogic
  StrncmpLogic StrchrnulLogic StrrchrLogic MemFwdLogic.
From Stdlib Require Import String.
From Nanofil Require Import Term Syntax Values Semantics ExternalCalls Runtime.
From Glibc Require Import GlibcProgram OsRegistry MemFwdCode LibioDefaultXsputnCopy.

Import ProgramAbbreviations.
Section copies.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None)
  (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None).

(** Aligned callers recover the exact copied bytes. Stream callers instead
    recover their whole buffer, including slots before an unaligned write pointer.
    One contract preserves both guarantees through separate logical inputs. *)
Definition memcpy_spec := spec_choice (MemFwdLogic.copy_spec false)
  (LibioDefaultXsputnCopy.copy_in_spec false).
Definition mempcpy_spec := spec_choice (MemFwdLogic.copy_spec true)
  (LibioDefaultXsputnCopy.copy_in_spec true).

(** The linked memcpy definition establishes both ownership alternatives. *)
#[global] Instance memcpy_has_spec n `{!Defines ge n glibc_memcpy} :
  HasSpec registry (os_wi w0) ge (TAtom n) memcpy_spec.
Proof.
  apply has_spec_choice.
  - apply MemFwdLogic.memcpy_spec_valid; try assumption; apply defines.
  - apply LibioDefaultXsputnCopy.memcpy_in_spec_valid; try assumption; apply defines.
Qed.

(** Mempcpy also requires the definition of the memcpy function it calls. *)
#[global] Instance mempcpy_has_spec n `{!Defines ge n glibc_mempcpy,
    !Defines ge "__GI_memcpy" glibc_memcpy} :
  HasSpec registry (os_wi w0) ge (TAtom n) mempcpy_spec.
Proof.
  apply has_spec_choice.
  - apply MemFwdLogic.mempcpy_spec_valid; try assumption; apply defines.
  - apply LibioDefaultXsputnCopy.mempcpy_in_spec_valid; try assumption; apply defines.
Qed.
End copies.
