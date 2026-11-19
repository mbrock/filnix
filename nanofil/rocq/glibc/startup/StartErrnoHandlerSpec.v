(** `c: __libc_start_main` registers an errno handler with the runtime,
    which calls it when a system call fails, to store the error number
    in `c: errno`. The contracts for failing system calls write the
    errno cell themselves, so a proof that calls the handler directly
    needs only what one call does. This module states that contract, and
    [StartErrnoHandler](StartErrnoHandler.v) proves it. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap fancy_updates.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic MemLogic.
From Glibc Require Import FileInv.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

Section spec.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (ge : genv).

(** Calling the errno handler with v stores the low 32 bits of v in the
    four bytes of `c: __libc_errno`. *)
Definition errno_handler_spec : fspec Σ :=
  FSpec (Z * Z * region * list Z) (fun '(v, _, _, _) => [WInt v])
    (fun '(v, eb, reg, xs) =>
       ⌜lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) /\
        eb + 4 <= r_end reg /\ length xs = 4%nat⌝ ∗ live eb reg ∗ bytes eb 0 xs)%I
    (fun '(v, eb, reg, xs) o => ⌜o = RetVoid⌝ ∗ live eb reg ∗ bytes eb 0 (le_bytes (v mod 2 ^ 32) 4))%I.

End spec.
