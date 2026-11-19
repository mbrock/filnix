(** C proofs use these tactics to load and store memory while preserving the operating
    system’s account of live objects. Each tactic returns the ownership that the next
    instruction needs. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  Machine Pieces Heap Language Logic MemLogic Symbolic.
From Glibc Require Import Fix GlibcTactics.
From Glibc Require Export OsMemLogic.
Import ListNotations Fix.ML0 LG0 LG0.L.
Open Scope Z_scope.

(** The premise of a store rule over [os_wi]: by [os_wi_store_life]. *)
Ltac wi_store :=
  let Hh := fresh "Hh" in let Hw := fresh "Hw" in
  intros ? ? ? Hh Hw; eapply os_wi_store_life; [reflexivity | | exact Hh | exact Hw];
  first [apply no_life_cell | apply no_life_byte_ps | apply no_life_pcell | apply no_life_byte].

(** Drop each wrap to 64 or 32 bits of the goal that arithmetic shows
    the identity. *)
Ltac unwrap :=
  repeat match goal with
    | |- context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2 ^ 64)); [|clear_junk; lia]
    | |- context [?x mod 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616); [|clear_junk; lia]
    | |- context [?x mod 2 ^ 32] => rewrite (Z.mod_small x (2 ^ 32)); [|clear_junk; lia]
    | |- context [?x mod 4294967296] => rewrite (Z.mod_small x 4294967296); [|clear_junk; lia]
    end.

(** An address or integer fact, by arithmetic. *)
Ltac arith := cbn [ptr_addr ptr_cap]; unfold raw_address; unwrap; clear_junk;
  first [lia | Z.div_mod_to_equations; lia].

(** An address fact using the registered field offsets, by arithmetic. *)
Ltac ar := autounfold with offs; arith.

(** Each [lookup] of the goal taken through its [put]s and, past them,
    from a hypothesis. *)
Ltac lookups :=
  repeat (rewrite Symbolic.lookup_after_put;
          match goal with |- context [?c] => lazymatch c with name_eqb _ _ =>
            let r := eval vm_compute in c in change c with r end end;
          cbn beta iota);
  repeat match goal with H : lookup ?k ?e = Some _ |- context [lookup ?k ?e] => rewrite H end.

(** This wrapper loads a narrow integer from a fractionally owned byte sequence.
    The caller's conversion proof chooses the symbolic form of the loaded value. *)
Tactic Notation "load_bytes_dq" constr(H) "decode" tactic3(decode) "by" tactic3(side) :=
  iApply (wp_raw_load_sub_bytes_dq with H);
    [memory_condition "load_bytes_dq" 1 ltac:(reflexivity) |memory_condition "load_bytes_dq" 2 ltac:(vx)
    |memory_condition "load_bytes_dq" 3 ltac:(first [reflexivity | eassumption])
    |memory_condition "load_bytes_dq" 4 decode
    |memory_condition "load_bytes_dq" 5 ltac:(first [eassumption | left; reflexivity | right; reflexivity])
    |memory_condition "load_bytes_dq" 6 side |].

(** This wrapper stores an integer's bytes while preserving the world invariant. *)
Tactic Notation "store_word" constr(H) "by" tactic3(side) "preserving" tactic3(world) :=
  iApply (wp_raw_store_w with H);
    [memory_condition "store_word" 1 ltac:(vx) |memory_condition "store_word" 2 ltac:(vx)
    |memory_condition "store_word" 3 ltac:(reflexivity)
    |memory_condition "store_word" 4 side
    |memory_condition "store_word" 5 ltac:(first [reflexivity | eassumption])
    |memory_condition "store_word" 6 world |].

(** This wrapper checks read access using fractional ownership of the object's life.
    The caller supplies bounds for the shared object. *)
Tactic Notation "check_read_dq" constr(H) "by" tactic3(side) :=
  iApply (wp_check_read_dq with H);
    [memory_condition "check_read_dq" 1 ltac:(reflexivity)
    |memory_condition "check_read_dq" 2 ltac:(first [solve [vx] | eassumption])
    |memory_condition "check_read_dq" 3 ltac:(first [eassumption | left; reflexivity | right; reflexivity])
    |memory_condition "check_read_dq" 4 side |memory_condition "check_read_dq" 5 side
    |memory_condition "check_read_dq" 6 ltac:(first [solve [apply Z.mod_1_r] | side]) |].

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

(** Write each address of the goal's environment without wraps. *)
Ltac norm := cbn [ptr_addr ptr_cap]; unwrap.

(** The term X has a variable in it. *)
Ltac has_var X := match X with context [?v] => is_var v end.

(** Compute each closed integer of the goal's words: a value glibc
    computes from constants, such as a flag test of a field known to
    be 0, becomes its numeral. *)
Ltac closed_ints :=
  repeat match goal with
    |- context [WInt ?X] =>
      tryif has_var X then fail else
      let v := eval vm_compute in X in tryif constr_eq X v then fail else change X with v
    end.
