From Glibc Require Import GlibcProgram.
(** This file proves the triple of `c: __overflow` (LibioGenCode.v), which glibc's
    `c: putc` and `c: _IO_default_xsputn` call when a stream has no
    room ([wp_glibc___overflow]). A stream with no orientation becomes
    narrow, its `c: _mode` set to -1, and the jump table's overflow,
    `c: _IO_new_file_overflow`, does the rest. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode LibioGenCode FileInv LibioLogic
  SysWrappers LibioOverflowBase.
From Glibc Require FileInv LibioLogic LibioOverflowBase OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioOverflowBase SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The genv defines `c: _IO_new_file_overflow` at the symbol the
    jump table's overflow slot holds. *)
Context (Hovf : ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow).

Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Each rule application repeats the whole current frame, so a long proof
    walks the same environment and instruction list once per step. These
    tactics keep both behind local definitions: the environment is named
    after every step, the remaining instructions are a chain of definitions
    whose bodies hold one instruction each, and only the next instruction is
    shown. The block's final jump stays named until no instruction is left. The rules see the same frame up to unfolding those definitions. *)
Local Ltac chain_tail L :=
  lazymatch L with
  | _ :: ?R => first [lazymatch R with _ :: _ => chain_tail R end | let X := fresh "I" in set (X := L)]
  end.
Local Ltac tidy :=
  try lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (_ (mkFrame _ _ _ _ (Exec _ ?L _))) _) => is_var L; unfold L
  end;
  try lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (_ (mkFrame _ _ _ _ (Exec _ [] ?J))) _) => is_var J; unfold J
  end;
  repeat lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (_ (mkFrame _ _ _ _ (Exec _ (_ :: ?R) _))) _) =>
      lazymatch R with _ :: _ => chain_tail R end
  end;
  try lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (_ (mkFrame _ _ _ _ (Exec _ (_ :: _) ?J))) _) =>
      first [is_var J | let X := fresh "J" in set (X := J)]
  end;
  try lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (_ (mkFrame _ ?e _ _ _)) _) =>
      lazymatch e with put _ _ _ => let E := fresh "Env" in set (E := e) end
  end.
(** When a function calls another one, the proof uses the callee's
    specification, and every premise it gives up repeats what happens after
    the call. This tactic names that remainder and the callee's starting
    state first, and the caller unfolds the remainder when the call returns. *)
Local Ltac name_post :=
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (_ ?F) ?Q) =>
      let X := fresh "Post" in set (X := Q); let Y := fresh "Callee" in set (Y := F)
  end.
(** This tactic runs the stream's steps up to its next load, store, call
    or branch, and it applies the naming above after each step. *)
Local Ltac advt := repeat (adv1; tidy).

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
  tidy. step; tidy. advt. load_s32_group "Hl Hmb"; tidy. step; tidy. destruct Hmd as [-> | ->]; branch; tidy.
  1: advt; load_s32_group "Hl Hmb"; tidy; step; tidy; branch; tidy; advt;
    store_word "Hl Hmb" by (ar) preserving wi_store;
    iNext; iIntros "Hl Hmb"; tidy; advt; assert (Hm1 : 0 <= 4294967295 < 2 ^ 32) by lia; load_s32_group "Hl Hmb"; tidy; step; tidy.
  all: advt; iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | ar | ar | cbn; unfold vt_file in *; lia |].
  all: iNext; iIntros "Hl Hvtp #Hvl'"; tidy; step; tidy; step; tidy; step; tidy; step; tidy; step; tidy; branch_as true; tidy.
  all: step; tidy; step; norm; tidy.
  all: check_read_dq "Hvl'" by ar; tidy.
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
  all: name_post.
  all: iApply (wp_wand with "[HK Hl Hmb Hvtp]"); [iApply ("HK" with "[] Hl Hmb Hvtp"); iPureIntro; reflexivity |].
  all: iIntros (o) "(%r & [-> %Hr] & HP)"; unfold Post.
  all: iExists _; iSplit; [iPureIntro; reflexivity|]; iNext; cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  all: iApply wp_ret; [reflexivity | vx |]; iNext.
  all: do 2 (rewrite (Z.mod_small r (2 ^ 32)); [|lia]); iExact "HP".
Qed.

End rules.
