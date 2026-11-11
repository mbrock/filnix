(** This file proves the triple of `c: __overflow` (LibioGenCode.v), which glibc's
    `c: putc` and `c: _IO_default_xsputn` call when a stream has no
    room ([wp_glibc___overflow]). A stream with no orientation becomes
    narrow, its `c: _mode` set to -1, and the jump table's overflow,
    `c: _IO_new_file_overflow`, does the rest. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode LibioGenCode FileInv LibioLogic
  SysWrappers LibioOverflowBase.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioOverflowGenOn (R : Runtime) (LG0 : LogicSig R).
Module OB := LibioOverflowBaseOn R LG0.
Import OB OB.SW OB.SW.FI.ML OB.SW.FI.LG OB.SW.FI.L OB.SW.OW OB.SW.FI OB.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The genv defines `c: _IO_new_file_overflow` at the symbol the
    jump table's overflow slot holds. *)
Context (Hovf : ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow).

Local Instance overflow_gen_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** `c: __overflow(fp, ch)` on a narrow or unoriented stream sets
    `c: _mode` to -1 and returns what the jump table's overflow
    returns. *)
Lemma wp_glibc___overflow fr fb freg ch mode vb vreg Φ :
  call_frame glibc___overflow [WPtr (mkPtr fb (Obj fb)); WInt ch] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 <= ch < 2 ^ 32 ->
  (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ int_cell fb off_mode mode -∗
  pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  ▷ (∀ fr', ⌜call_frame glibc__IO_new_file_overflow [WPtr (mkPtr fb (Obj fb)); WInt ch] = Some fr'⌝ -∗
     live fb freg -∗ int_cell fb off_mode (2 ^ 32 - 1) -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
     WP (ERun fr' : sexpr) {{ o, ∃ r, ⌜o = Ret (WInt r) /\ 0 <= r < 2 ^ 32⌝ ∗ Φ (Ret (WInt r)) }}) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfb Hal Hend Hfreg Hch Hmd. injection Hfr as <-.
  iIntros "#Hvt Hl [%Hm Hmb] Hvtp HK". unfold file_size in Hend.
  iPoseProof (vtables_slot ge vb vreg slot_overflow "_IO_new_file_overflow" with "Hvt") as "#Hso"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_new_file_overflow")) vreg) as "Hfc".
  { rewrite (ge_fn_cap _ _ _ Hovf). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & Hslots)".
  unfold io_vtables_size in Hvend.
  enter. adv. load_int "Hl Hmb". st. destruct Hmd as [-> | ->]; br.
  1: adv; load_int "Hl Hmb"; st; br; adv;
    iApply (wp_raw_store_w with "Hl Hmb"); [vx | vx | reflexivity | ar | reflexivity | wi_store |];
    iNext; iIntros "Hl Hmb"; adv; assert (Hm1 : 0 <= 4294967295 < 2 ^ 32) by lia; load_int "Hl Hmb"; st.
  all: adv; iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | ar | ar | cbn; unfold vt_file in *; lia |].
  all: iNext; iIntros "Hl Hvtp #Hvl'"; st; st; st; st; st; brv true.
  all: st; st; norm.
  all: iApply (wp_check_read_dq registry (os_wi w0) ge with "Hvl'"); [reflexivity | vx | right; reflexivity | ar | ar | ar |].
  all: iNext; iIntros "_".
  all: iApply (wp_raw_load_pointer_dq with "Hvl' Hso Hfc");
    [reflexivity | vx | right; reflexivity | ar | ar | apply (ge_fn_addr _ _ _ Hovf) |].
  all: iNext; iIntros "_ _ _".
  all: iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hovf) |]; iNext.
  all: iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hovf) | apply (ge_fn_check _ _ _ Hovf) | vx |
    apply (ge_fn_find _ _ _ Hovf) | reflexivity | reflexivity |].
  all: iNext; iAssert (int_cell fb off_mode (2 ^ 32 - 1)) with "[Hmb]" as "Hmb";
    [iSplit; [iPureIntro; lia | iExact "Hmb"] |].
  all: rewrite (Z.mod_small ch (2 ^ 32)); [|lia].
  all: iApply (wp_wand with "[HK Hl Hmb Hvtp]"); [iApply ("HK" with "[] Hl Hmb Hvtp"); iPureIntro; reflexivity |].
  all: iIntros (o) "(%r & [-> %Hr] & HP)".
  all: iExists _; iSplit; [iPureIntro; reflexivity|]; iNext; cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  all: iApply wp_ret; [reflexivity | vx |]; iNext.
  all: do 2 (rewrite (Z.mod_small r (2 ^ 32)); [|lia]); iExact "HP".
Qed.

End rules.
End LibioOverflowGenOn.
