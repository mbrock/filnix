(** `c: __libc_start_main` also registers a dlerror handler with the
    runtime, which calls it to publish a `c: dlerror` message. A proof
    that calls the handler needs only what one call does, so this module
    states that contract, and
    [StartDlerrorHandler](StartDlerrorHandler.v) proves it. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap fancy_updates.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic MemLogic.
From Glibc Require Import FileInv.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

Section spec.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (ge : genv).

(** Calling the dlerror handler with p stores p in the eight bytes of
    `c: __libc_dlerror_result_string`. *)
Definition dlerror_handler_spec : fspec Σ :=
  FSpec (ptr * Z * region * ptr) (fun '(p, _, _, _) => [WPtr p])
    (fun '(p, db, reg, x) =>
       ⌜lookup (TAtom "__libc_dlerror_result_string") (ge_globals ge) = Some (mkPtr db (Obj db)) /\
        db mod 8 = 0 /\ db + 8 <= r_end reg⌝ ∗ live db reg ∗ pcell db 0 x)%I
    (fun '(p, db, reg, x) o => ⌜o = RetVoid⌝ ∗ live db reg ∗ pcell db 0 p)%I.

End spec.
