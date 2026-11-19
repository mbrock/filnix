(** Early initialization asks for the stack size limit through glibc's
    `c: getrlimit`, to size the stacks of new threads. That function
    passes its arguments on to the runtime's `c: zsys_getrlimit`. A
    caller needs only what one call does, so this module states that
    contract. [StartGetrlimit](StartGetrlimit.v) proves it. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap fancy_updates.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic MemLogic.
From Glibc Require Import FileInv OsBlocks OsWorld OsGetrlimit.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

Section spec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** A call of `c: getrlimit(res, b)` lends the runtime the 16 bytes at
    b and the errno cell eb, for a 32-bit resource number res. It
    returns 0 or -1, and the bytes and errno come back with any
    values. *)
Definition getrlimit_spec : fspec Σ :=
  FSpec (Z * Z * region * Z) (fun '(res, b, _, _) => [WInt res; WPtr (mkPtr b (Obj b))])
    (fun '(res, b, reg, eb) =>
       ⌜0 <= res < 2 ^ 32 /\ ow_errno w0 = Some (mkPtr eb (Obj eb)) /\ b + rlimit_size <= r_end reg⌝ ∗
       live b reg ∗ blk_any b 0 rlimit_size ∗ errno_any eb)%I
    (fun '(res, b, reg, eb) o =>
       ∃ k, ⌜o = Ret (WInt k) /\ (k = 0 \/ k = 2 ^ 32 - 1)⌝ ∗
       live b reg ∗ blk_any b 0 rlimit_size ∗ errno_any eb)%I.

End spec.
