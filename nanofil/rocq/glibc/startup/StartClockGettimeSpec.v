(** The allocator mixes the current time into a random key, which it
    reads through glibc's `c: clock_gettime`. That function passes its
    arguments on to the runtime's `c: zsys_clock_gettime`. A caller
    needs only what one call does, so this module states that contract.
    [StartClockGettime](StartClockGettime.v) proves it. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap fancy_updates.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic MemLogic.
From Glibc Require Import FileInv OsBlocks OsWorld OsClockGettime.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

Section spec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** A call of `c: clock_gettime(clk, b)` lends the runtime the 16 bytes
    at b and the errno cell eb, for a 32-bit clock id clk. It returns 0 or -1, and the bytes and
    errno come back with any values. *)
Definition clock_gettime_spec : fspec Σ :=
  FSpec (Z * Z * region * Z) (fun '(clk, b, _, _) => [WInt clk; WPtr (mkPtr b (Obj b))])
    (fun '(clk, b, reg, eb) =>
       ⌜0 <= clk < 2 ^ 32 /\ ow_errno w0 = Some (mkPtr eb (Obj eb)) /\ b + timespec_size <= r_end reg⌝ ∗
       live b reg ∗ blk_any b 0 timespec_size ∗ errno_any eb)%I
    (fun '(clk, b, reg, eb) o =>
       ∃ k, ⌜o = Ret (WInt k) /\ (k = 0 \/ k = 2 ^ 32 - 1)⌝ ∗
       live b reg ∗ blk_any b 0 timespec_size ∗ errno_any eb)%I.

End spec.
