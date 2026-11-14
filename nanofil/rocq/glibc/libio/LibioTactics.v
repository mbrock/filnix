(** Stream proofs need store rules that preserve the operating system's state.
    This extension adds those rules to [GlibcTactics] without making string
    proofs load the stream invariants or the operating-system model. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  Machine Pieces Heap Language Logic MemLogic Symbolic.
From Glibc Require Import Fix FileInv LibioLogic LibioCloseSteps GlibcTactics.
Import ListNotations FileInv.ML LG0 LG0.L.
Open Scope Z_scope.

(** This tactic loads a pointer while retaining the base and loaded objects' lives. *)
Ltac load Hl Hc Hk :=
  iRevert Hk; iRevert Hc; iRevert Hl;
  lazymatch goal with |- environments.envs_entails _ (_ -∗ pcell _ _ ?pv -∗ _) =>
    eapply step_res3; [eapply wp_raw_load_pointer with (x := pv); inst;
      [reflexivity | vx | reflexivity | a2 | a2 | cbn; lia] |] end;
  iIntros Hl; iIntros Hc; iIntros Hk.

(** This tactic stores a pointer while retaining the base object's life and cell. *)
Ltac store Hl Hc :=
  rule2 Hl Hc ltac:(eapply wp_raw_store_pointer; inst;
    [vx | vx | reflexivity | a2 | a2 | wi_store]).

(** This tactic loads a signed integer from its four owned bytes. *)
Ltac load_s32 Hl Hb :=
  rule2 Hl Hb ltac:(eapply wp_raw_load_sub_bytes_dq; inst;
    [reflexivity | vx | reflexivity | apply load_sw_int; assumption | left; reflexivity | a2]).

(** This tactic stores an integer into its four owned bytes. *)
Ltac store_int Hl Hb :=
  rule2 Hl Hb ltac:(eapply wp_raw_store_w; inst;
    [vx | vx | reflexivity | a2 | reflexivity | wi_store]).

(** This tactic loads a null pointer without asking for a loaded object's life. *)
Ltac load_null Hl Hc :=
  rule2 Hl Hc ltac:(eapply wp_raw_load_null; inst;
    [reflexivity | vx | reflexivity | a2 | a2]).

(** This tactic stores a long integer into its owned cell. *)
Ltac store_long Hl Hc :=
  rule2 Hl Hc ltac:(eapply wp_raw_store; inst; [vx | vx | reflexivity | a2 | wi_store]).

(** ## Grouped ownership

    Older proofs pass several ownership names in one string rather than as separate arguments.
    These entry points preserve that convention and return the same group after the instruction. *)

(** This tactic loads an integer using a group containing its life and bytes. *)
Ltac load_s32_group H :=
  iApply (wp_raw_load_sub_bytes_dq with H);
    [reflexivity | vx | reflexivity | apply load_sw_int; assumption | left; reflexivity | ar |];
  iNext; iIntros H.

(** A caller can supply its own bounds solver when its arithmetic facts need different normalization. *)
Ltac load_s32_using bounds H :=
  iApply (wp_raw_load_sub_bytes_dq with H);
    [reflexivity | vx | reflexivity | apply load_sw_int; assumption | left; reflexivity | bounds |];
  iNext; iIntros H.

(** This tactic reads a pointer through fractional ownership of the base object. *)
Ltac load_shared H :=
  iApply (wp_raw_load_pointer_dq with H);
    [reflexivity | vx | left; reflexivity | a2 | a2 | a2 |];
  iNext; iIntros H.

(** A self-pointer rule belongs to the invariant that describes the containing object.
    The caller supplies that rule so this library need not import the invariant's proofs. *)
Ltac load_self_using rule H :=
  iApply (rule with H);
    [reflexivity | vx | reflexivity | a2 | a2 | a2 | reflexivity |];
  iNext; iIntros H.

(** This tactic loads one byte using a group containing its life and byte. *)
Ltac load_byte_group H :=
  iApply (wp_raw_load_sub_bytes_dq with H);
    [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | ar |];
  iNext; iIntros H.

(** This tactic stores an integer using a group containing its life and bytes. *)
Ltac store_int_group H :=
  iApply (wp_raw_store_w with H); [vx | vx | reflexivity | ar | reflexivity | wi_store |];
  iNext; iIntros H.

(** This tactic loads a pointer using the grouped life and cell resources. *)
Ltac load_group H :=
  iApply (wp_raw_load_pointer with H); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |];
  iNext; iIntros H.

(** This tactic stores a pointer using the grouped life and cell resources. *)
Ltac store_group H :=
  iApply (wp_raw_store_pointer with H); [vx | vx | reflexivity | ar | ar | wi_store |];
  iNext; iIntros H.

(** This tactic checks a read through a shared life token and returns that token. *)
Ltac check_shared H :=
  iApply (wp_check_read_dq with H);
    [reflexivity | vx | first [left; reflexivity | right; reflexivity] | ar | ar | ar |];
  iNext; iIntros H.

(** This tactic loads a byte whose ownership remains in the persistent context. *)
Ltac load_byte_persistent H :=
  iApply (wp_raw_load_sub_bytes_dq with H);
    [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | ar |];
  iNext; iIntros "_ _".

(** This tactic checks a read whose life token remains in the persistent context. *)
Ltac check_persistent H :=
  iApply (wp_check_read_dq with H);
    [reflexivity | vx | first [left; reflexivity | right; reflexivity] | ar | ar | ar |];
  iNext; iIntros "_".
