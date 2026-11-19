(** Stream proofs use the flag masks and write results defined here.
    They use the shared OS memory tactics to step through the captured
    code and to show that stores preserve the OS world. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From iris.program_logic Require Import language weakestpre.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  Pieces Heap Language Logic StringLogic MemLogic StepRules ExternalCalls ExternalMachine.
From Nanofil Require WordBits Symbolic.
From Glibc Require Export OsTactics LibioTactics.
From Glibc Require Import OsBlocks OsWorld FileInv.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** A mask of a nonnegative integer by a 32-bit one is a 32-bit int. *)
Lemma land_lt32 a b : 0 <= a -> 0 <= b < 2 ^ 32 -> 0 <= Z.land a b < 2 ^ 32.
Proof.
  intros Ha Hb. split; [apply Z.land_nonneg; lia|].
  assert (Hl : Z.log2 b < 32).
  { destruct (Z.eq_dec b 0) as [->|Hne]; [reflexivity|]. apply Z.log2_lt_pow2; lia. }
  rewrite <- (Z.land_ones_low b 32); [|lia | exact Hl]. rewrite Z.land_assoc Z.land_ones; [|lia].
  apply Z.mod_pos_bound. lia.
Qed.

(** A test of bit k, below 24, of the 24-bit field `c: _flags2`: the
    4 bytes as loaded, sign-extended by a shift left and an arithmetic
    shift right by 8, then masked by M, 2^k, read bit k of the bytes.
    `c: _IO_ferror` tests `c: _IO_FLAGS2_NEED_LOCK` (bit 7) this way,
    `c: _IO_new_file_write` `c: _IO_FLAGS2_NOTCANCEL` (bit 1). *)
Lemma flags2_mask f2 M k : M = 2 ^ k -> 0 <= k < 24 -> 0 <= f2 < 2 ^ 32 ->
  Z.land (((sign_extension (2 ^ 32) (2 ^ 31)
              (((f2 mod 2 ^ 32 * 2 ^ ((8 mod 2 ^ 32) mod 32)) mod 2 ^ 32) mod 2 ^ 32) /
            2 ^ ((8 mod 2 ^ 32) mod 32)) mod 2 ^ 32) mod 2 ^ 32) (M mod 2 ^ 32) = Z.land f2 M.
Proof.
  intros -> Hk H. change ((8 mod 2 ^ 32) mod 32) with 8.
  rewrite (Z.mod_small (2 ^ k)); [|split; [lia | apply Z.pow_lt_mono_r; lia]].
  rewrite (Z.mod_small f2); [|lia]. rewrite !Z.mod_mod; [|lia|lia].
  apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.eq_dec i k) as [->|Hne].
  - f_equal. rewrite Z.mod_pow2_bits_low; [|lia].
    rewrite Z.div_pow2_bits; [|lia|lia]. unfold sign_extension. rewrite Z.mod_mod; [|lia].
    assert (Hl : forall l, 0 <= l < 2 ^ 32 -> Z.testbit (l - 2 ^ 32) (k + 8) = Z.testbit l (k + 8)).
    { intros l Hl. rewrite <- (Z.mod_pow2_bits_low (l - 2 ^ 32) 32 (k + 8)); [|lia].
      f_equal. rewrite Zminus_mod Z_mod_same_full Z.sub_0_r !Z.mod_mod; [|lia]. apply Z.mod_small. exact Hl. }
    assert (Hb : 0 <= (f2 * 2 ^ 8) mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
    assert (Hm : Z.testbit ((f2 * 2 ^ 8) mod 2 ^ 32) (k + 8) = Z.testbit f2 k).
    { rewrite (Z.mod_pow2_bits_low _ 32 (k + 8)); [|lia]. rewrite (Z.mul_pow2_bits f2 8 (k + 8)); [|lia].
      f_equal. lia. }
    destruct (2 ^ 31 <=? _).
    + rewrite (Hl _ Hb). exact Hm.
    + exact Hm.
  - rewrite Z.pow2_bits_false; [|lia]. rewrite !andb_false_r. reflexivity.
Qed.

(** The bitwise or of two 32-bit ints is one. *)
Lemma lor_lt32 a b : 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> 0 <= Z.lor a b < 2 ^ 32.
Proof.
  intros Ha Hb. assert (Hn : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
  split; [exact Hn|]. destruct (Z.eq_dec (Z.lor a b) 0) as [E|E]; [rewrite E; lia|].
  apply Z.log2_lt_pow2; [lia|]. rewrite Z.log2_lor; [|lia|lia].
  assert (Z.log2 a < 32) by (destruct (Z.eq_dec a 0) as [->|]; [reflexivity | apply Z.log2_lt_pow2; lia]).
  assert (Z.log2 b < 32) by (destruct (Z.eq_dec b 0) as [->|]; [reflexivity | apply Z.log2_lt_pow2; lia]).
  lia.
Qed.

(** `c: _IO_ferror`'s test of `c: _IO_FLAGS2_NEED_LOCK`: [flags2_mask]
    at bit 7. *)
Lemma flags2_bit7 f2 : 0 <= f2 < 2 ^ 32 ->
  Z.land (((sign_extension (2 ^ 32) (2 ^ 31)
              (((f2 mod 2 ^ 32 * 2 ^ ((8 mod 2 ^ 32) mod 32)) mod 2 ^ 32) mod 2 ^ 32) /
            2 ^ ((8 mod 2 ^ 32) mod 32)) mod 2 ^ 32) mod 2 ^ 32) (128 mod 2 ^ 32) = Z.land f2 128.
Proof. apply (flags2_mask f2 128 7); [reflexivity | lia]. Qed.

(** What `c: _IO_new_file_write` leaves: r of the n bytes written,
    all of them with the flags as they were, or fewer after a failed
    call, which set `c: _IO_ERR_SEEN`. *)
Definition fw_post (n fl r fl' : Z) : Prop :=
  (r = n /\ fl' = fl) \/ (0 <= r < n /\ fl' = Z.lor fl io_err_seen).

(** ## Functions of the genv *)

(** The genv ge defines the function gf as n, at the pointer its
    symbol n holds, whose capability is that function's. *)
Definition ge_fn (ge : genv) (n : string) (gf : func) : Prop :=
  exists a, lookup (TAtom n) (ge_globals ge) = Some (mkPtr a (Fn (TAtom n))) /\
            find_fn ge (TAtom n) = Some (Defined gf) /\ 0 <= a < 2 ^ 64.

(** Such a function's pointer passes `c: check_function`. *)
Lemma ge_fn_check ge n gf : ge_fn ge n gf -> function_check_res ge (sym_ptr ge n) = Some ok.
Proof.
  intros (a & Hl & _ & _). unfold sym_ptr, function_check_res. rewrite Hl. cbn. rewrite Hl. cbn.
  rewrite Z.eqb_refl. reflexivity.
Qed.

(** Its pointer's capability names it. *)
Lemma ge_fn_cap ge n gf : ge_fn ge n gf -> ptr_cap (FileInv.sym_ptr ge n) = Fn (TAtom n).
Proof. intros (a & Hl & _ & _). unfold sym_ptr. rewrite Hl. reflexivity. Qed.

(** Its pointer is a canonical address. *)
Lemma ge_fn_addr ge n gf : ge_fn ge n gf -> 0 <= ptr_addr (sym_ptr ge n) < 2 ^ 64.
Proof. intros (a & Hl & _ & Ha). unfold sym_ptr. rewrite Hl. exact Ha. Qed.

(** It is the function [find_fn] finds. *)
Lemma ge_fn_find ge n gf : ge_fn ge n gf -> find_fn ge (TAtom n) = Some (Defined gf).
Proof. intros (a & _ & Hf & _). exact Hf. Qed.
