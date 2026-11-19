(** Startup reads glibc's tunables through `c: __tunable_get_val`, and
    each caller needs only what one call does, not how the function
    branches. This module states that contract, so that a caller can
    import it without the proof. The proof lives in
    [StartTunableGetVal](StartTunableGetVal.v), and only the final
    assembly of startup imports both.

    ## One tunable's entry

    Each tunable occupies 136 bytes of a static table. Its type code sits
    at offset 48, its value at offset 88 and its initialized byte at
    offset 104. The function panics on a type code it does not know, and
    it runs a callback when the initialized byte is set. So a caller
    owns those three fields with a known type code and a zero
    initialized byte, and the call gives them back unchanged. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic StringLogic MemLogic.
From Glibc Require Import FileInv.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

Section specs.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** This assertion owns the three fields of tunable id in the table at
    tl: the type code ty, the value v and a zero initialized byte. *)
Definition tunable_entry (tl id ty v : Z) : iProp Σ :=
  bytes tl (id * 136 + 48) (le_bytes ty 4) ∗ icell tl (id * 136 + 88) v ∗ ibyte tl (id * 136 + 104) 0.

(** The table is the global that the program names
    `c: tunable_list`, and the entry for id lies inside its object. *)
Definition tunable_slot_ok (tl : Z) (tlreg : region) (id : Z) : Prop :=
  lookup (TAtom "glibc_dl_tunables#tunable_list") (ge_globals ge) = Some (mkPtr tl (Obj tl)) /\
  0 <= id < 2 ^ 32 /\ tl mod 8 = 0 /\ tl + id * 136 + 136 <= r_end tlreg.

(** Reading a size tunable, whose type code is 2, copies its eight-byte
    value v into the destination cell at dst. The callback pointer cb is
    passed but never called. *)
Definition tunable_size_spec : fspec Σ :=
  FSpec (Z * ptr * Z * region * Z * Z * region * Z)
    (fun '(id, cb, _, _, _, dst, _, _) => [WInt id; WPtr (mkPtr dst (Obj dst)); WPtr cb])
    (fun '(id, cb, tl, tlreg, v, dst, dreg, w) =>
       ⌜tunable_slot_ok tl tlreg id /\ dst mod 8 = 0 /\ dst + 8 <= r_end dreg⌝ ∗
       live tl tlreg ∗ tunable_entry tl id 2 v ∗ live dst dreg ∗ icell dst 0 w)%I
    (fun '(id, cb, tl, tlreg, v, dst, dreg, w) o =>
       ⌜o = RetVoid⌝ ∗ live tl tlreg ∗ tunable_entry tl id 2 v ∗ live dst dreg ∗ icell dst 0 (v mod 2 ^ 64))%I.

(** Reading an int tunable, whose type code is 0, copies the low four
    bytes of its value v into the four bytes at dst. *)
Definition tunable_int_spec : fspec Σ :=
  FSpec (Z * ptr * Z * region * Z * Z * region * list Z)
    (fun '(id, cb, _, _, _, dst, _, _) => [WInt id; WPtr (mkPtr dst (Obj dst)); WPtr cb])
    (fun '(id, cb, tl, tlreg, v, dst, dreg, xs) =>
       ⌜tunable_slot_ok tl tlreg id /\ dst + 4 <= r_end dreg /\ length xs = 4%nat⌝ ∗
       live tl tlreg ∗ tunable_entry tl id 0 v ∗ live dst dreg ∗ bytes dst 0 xs)%I
    (fun '(id, cb, tl, tlreg, v, dst, dreg, xs) o =>
       ⌜o = RetVoid⌝ ∗ live tl tlreg ∗ tunable_entry tl id 0 v ∗ live dst dreg ∗
       bytes dst 0 (le_bytes ((v mod 2 ^ 64) mod 2 ^ 32) 4))%I.

End specs.
