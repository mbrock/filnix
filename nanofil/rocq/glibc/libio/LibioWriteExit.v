From Glibc Require Import GlibcProgram.
(** What the proof of `c: _IO_new_file_write` (LibioWrite.v) builds on:
    its loop's head block, the bytes a write reads, and the loop's
    exit. LibioWrite.v describes the function.

    The triple of `c: _IO_new_file_write` (LibioReadCode.v), the jump
    table's write: it hands the bytes from data to
    `c: __write(fp->_fileno, ...)` until all are written or a call
    fails, which sets `c: _IO_ERR_SEEN`, then counts what it wrote into
    `c: _total_written` and, when known, `c: _offset`.

    A write may take fewer bytes than asked, so the loop runs again on
    the rest, by Löb induction over the head of block `c: L8`
    ([wp_file_write_loop]), whose environment is the earlier one with
    the two phis `c: pr.1` (the next byte) and `c: pr.2` (the bytes
    left) put on top. The stream's `c: _flags2` has
    `c: _IO_FLAGS2_NOTCANCEL` clear, as a stream `c: fopen` did not
    open with "c" has, so the loop calls `c: __write`, the alias of
    `c: __libc_write`. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode FileInv LibioLogic
  SysWrappers.
From Glibc Require FileInv LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** Block `c: L8` of `c: _IO_new_file_write`, the loop's head. *)
Definition fw_L8 : block := Eval vm_compute in
  match find_block (TAtom "L8") (fn_blocks glibc__IO_new_file_write) with
  | Some b => b | None => mkBlock (TAtom "L8") [] [] JRetVoid end.

(** The bytes xs from offset o of the live object b, each a byte and in
    b's bounds, pass `c: filc_check_read` from any offset i among
    them for the rest ([os_readable]). *)
Lemma bytes_os_readable m b reg o xs i :
  live_at m b reg -> all_agree m (byte_ps b o xs) -> Forall (fun x => 0 <= x < 256) xs ->
  0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg -> 0 <= i <= Z.of_nat (length xs) ->
  0 <= b -> b + o + Z.of_nat (length xs) < 2 ^ 64 ->
  os_readable m (mkPtr (b + o + i) (Obj b)) (Z.of_nat (length xs) - i).
Proof.
  intros Hl Hx Hy Ho Hend Hi Hb H64. split; [lia|]. right. split; [lia|].
  split; [exists b, reg; split; [left; reflexivity | exact Hl]|]. split.
  - apply (access_read _ b reg); [left; reflexivity | exact (proj1 Hl) | cbn; lia | cbn; lia | apply Z.mod_1_r].
  - intros k Hk. cbn [ptr_addr]. destruct (lookup_lt_is_Some_2 xs (Z.to_nat (i + k)) ltac:(lia)) as [x Hxi].
    destruct (byte_ps_agree _ _ _ _ _ _ _ Hl Hx Hxi) as (Hv & _ & _).
    replace (b + o + i + k) with (b + (o + Z.of_nat (Z.to_nat (i + k)))) by lia. rewrite Hv.
    exact (Forall_lookup_1 _ _ _ _ Hy Hxi).
Qed.


Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

(** A signed 32-bit load of an owned [int_cell]'s bytes. *)


(** A call of a wrapper of SysWrappers.v from a frame, through
    [wp_call_bind]: its triple's postcondition resumes the caller. *)
Ltac resume_ret := iExists _; iSplit; [iPureIntro; reflexivity|]; iNext; cbn [fr_fn fr_env fr_locals fr_doomed fr_at].

Import ProgramAbbreviations.
Section rules_values.
Context {Σ : gFunctors}
  {gen_heapGS0 : gen_heapGS piece pval Σ}.
Existing Instance gen_heapGS0.
Lemma bytes_le_eq b o x y n : x = y -> bytes b o (le_bytes x n) -∗ bytes b o (le_bytes y n).
Proof. intros ->. auto. Qed.
Lemma live_bytes_pts b reg o xs : live b reg -∗ bytes b o xs -∗ pts ([(PLive b, VLive reg)] ++ byte_ps b o xs).
Proof. iIntros "Hl Hb". rewrite pts_app. iFrame. Qed.
Lemma pts_live_bytes b reg o xs : pts ([(PLive b, VLive reg)] ++ byte_ps b o xs) -∗ live b reg ∗ bytes b o xs.
Proof. rewrite pts_app. auto. Qed.
End rules_values.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).

Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Bytes of equal values. *)

(** The pieces a write of the bytes xs reads, as one list. *)

(** The exit of `c: _IO_new_file_write`'s loop, block `c: L10`, t of
    the n bytes left: the count written, n - t, added to
    `c: _offset` when that is known, is the result. *)
Lemma wp_file_write_exit fb freg off n t e from Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 <= t <= n -> n < 2 ^ 63 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "v4") e = Some (WInt n) ->
  lookup (TAtom "pr.2") e = Some (WInt t) ->
  live fb freg -∗ icell fb off_offset off -∗
  ▷ (∀ off', live fb freg -∗ icell fb off_offset off' -∗ Φ (Ret (WInt (n - t)))) -∗
  WP (ERun (mkFrame glibc__IO_new_file_write e [] None (Enter (TAtom "L10") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Ht Hn Hv0 Hv4 Ht'. unfold file_size in Hend. iIntros "Hl Hoff HK".
  step. step. step. norm. check "Hl".
  iApply (wp_raw_load with "Hl Hoff"); [reflexivity | vx | reflexivity | ar |]. iNext. iIntros "Hl Hoff".
  step. branch_cases.
  - step. iApply wp_ret; [reflexivity | vx |]. iNext. unwrap. iApply ("HK" with "Hl Hoff").
  - step. step. iApply (wp_raw_load with "Hl Hoff"); [reflexivity | vx | reflexivity | ar |]. iNext. iIntros "Hl Hoff".
    step. check "Hl".
    iApply (wp_raw_store with "Hl Hoff"); [vx | vx | reflexivity | ar | wi_store |]. iNext. iIntros "Hl Hoff".
    step. step. iApply wp_ret; [reflexivity | vx |]. iNext. unwrap. iApply ("HK" with "Hl Hoff").
Qed.


(** Block `c: L38` of `c: _IO_new_file_write`, after a failed call, t
    of the n bytes left: `c: _IO_ERR_SEEN` set, then the exit. *)
Lemma wp_file_write_err fb freg fl off n t e from Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 <= t <= n -> n < 2 ^ 63 ->
  0 <= fl < 2 ^ 32 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "v4") e = Some (WInt n) ->
  lookup (TAtom "pr.2") e = Some (WInt t) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (fb + off_flags2) (Obj fb))) ->
  live fb freg -∗ int_cell fb off_flags fl -∗ icell fb off_offset off -∗
  ▷ (∀ off', live fb freg -∗ int_cell fb off_flags (Z.lor fl io_err_seen) -∗ icell fb off_offset off' -∗
     Φ (Ret (WInt (n - t)))) -∗
  WP (ERun (mkFrame glibc__IO_new_file_write e [] None (Enter (TAtom "L38") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Ht Hn Hfl Hv0 Hv4 Ht' Hc0. unfold file_size in Hend. iIntros "Hl [_ Hfl] Hoff HK".
  step. check "Hl". load_s32_group "Hl Hfl". step. check "Hl".
  store_word "Hl Hfl" by (ar) preserving wi_store.
  iNext. iIntros "Hl Hfl". step.
  iApply (wp_file_write_exit with "Hl Hoff"); try wside.
  iNext. iIntros (off') "Hl Hoff".
  assert (Hor : 0 <= Z.lor fl 32 < 2 ^ 32) by (apply lor_lt32; lia).
  iApply ("HK" with "Hl [Hfl] Hoff"). iSplit; [done|]. iApply (bytes_le_eq with "Hfl"). change (32 mod 2 ^ 32) with 32.
  repeat (rewrite (Z.mod_small fl); [|lia]). apply Z.mod_small. exact Hor.
Qed.

(** Block `c: L40` of `c: _IO_new_file_write`, after a call wrote k of
    the t bytes left from p: `c: _total_written` counts them, and the
    loop's head runs again on the t - k bytes from p + k. *)
Lemma wp_file_write_next fb freg tw t k p e from Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 <= k <= t -> t < 2 ^ 63 ->
  0 <= ptr_addr p -> ptr_addr p + k < 2 ^ 64 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "v37") e = Some (WInt k) ->
  lookup (TAtom "pr.2") e = Some (WInt t) -> lookup (TAtom "pr.1") e = Some (WPtr p) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (fb + off_flags2) (Obj fb))) ->
  live fb freg -∗ icell fb off_total_written tw -∗
  ▷ (∀ e' tw', ⌜lookup (TAtom "v0") e' = lookup (TAtom "v0") e /\
                 lookup (TAtom "v4") e' = lookup (TAtom "v4") e /\
                 lookup (TAtom "pr.2") e' = Some (WInt (t - k)) /\
                 lookup (TAtom "pr.1") e' = Some (WPtr (mkPtr (ptr_addr p + k) (ptr_cap p)))⌝ -∗
       live fb freg -∗ icell fb off_total_written tw' -∗
       WP (ERun (mkFrame glibc__IO_new_file_write e' [] None (Exec (TAtom "L8") (b_insts fw_L8) (b_jump fw_L8)))
             : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc__IO_new_file_write e [] None (Enter (TAtom "L40") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Hk Ht Hp0 Hp64 Hv0 Hv37 Ht' Hp Hc0. unfold file_size in Hend. iIntros "Hl Htw HK".
  step. step. norm. check "Hl".
  iApply (wp_raw_load with "Hl Htw"); [reflexivity | vx | reflexivity | ar |]. iNext. iIntros "Hl Htw".
  step. check "Hl".
  iApply (wp_raw_store with "Hl Htw"); [vx | vx | reflexivity | ar | wi_store |]. iNext. iIntros "Hl Htw".
  step. step. step. iApply wp_enter; [reflexivity | vx | iNext].
  iApply ("HK" with "[%] Hl Htw").
  split_and!; lookups; try reflexivity;
    lazymatch goal with
    | |- Some (WPtr (mkPtr ?A _)) = Some (WPtr (mkPtr ?B _)) => replace A with B by arith
    | |- Some (WInt ?A) = Some (WInt ?B) => replace A with B by arith
    end; reflexivity.
Qed.

End rules.
