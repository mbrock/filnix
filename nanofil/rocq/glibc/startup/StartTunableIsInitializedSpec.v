(** The allocator asks `c: __tunable_is_initialized` whether the user set
    the mmap threshold, before it chooses a default. The answer is the
    tunable's initialized byte. A caller needs only that answer, so this
    module states that contract.
    [StartTunableIsInitialized](StartTunableIsInitialized.v) proves it. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap fancy_updates.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic MemLogic.
From Glibc Require Import FileInv OsBlocks OsWorld StartTunableGetValSpec.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

Section spec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** A call of `c: __tunable_is_initialized(id)` returns 0 for a tunable
    whose initialized byte is 0, and gives its entry back unchanged. *)
Definition tunable_is_initialized_spec : fspec Σ :=
  FSpec (Z * Z * region * Z * Z) (fun '(id, _, _, _, _) => [WInt id])
    (fun '(id, tl, tlreg, ty, v) => ⌜tunable_slot_ok tl tlreg id⌝ ∗ live tl tlreg ∗ tunable_entry tl id ty v)%I
    (fun '(id, tl, tlreg, ty, v) o => ⌜o = Ret (WInt 0)⌝ ∗ live tl tlreg ∗ tunable_entry tl id ty v)%I.

End spec.
