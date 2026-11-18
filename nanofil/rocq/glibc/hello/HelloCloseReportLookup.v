(** A failed close can leave any 32-bit error number. Before translating
    an error message, strerror looks for that number in glibc's table.
    A negative number bypasses the table length itself. A nonnegative
    number beyond the end, and a null slot inside the table, both leave
    strerror to format an unknown error. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic ErrlistCode StrcmpBits Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic OsWorld.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

Section lookup.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation gexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation rop b := (mkPtr b (Ro b)).

(** A caller lends a slot only for an index inside the table. The rule
    returns the pointer in that slot, which may itself be null. The
    length, table and target remain readable for later reports. *)
Lemma wp_close_get_errlist fr k lb lr tb tr mid mr Φ :
  call_frame glibc_get_errlist [WInt k] = Some fr -> 0 <= k < 2^32 ->
  lookup (TAtom "_sys_errlist_internal_len") (ge_globals ge) = Some (rop lb) ->
  lookup (TAtom "_sys_errlist_internal") (ge_globals ge) = Some (rop tb) ->
  0 < lb -> lb+8 <= r_end lr -> r_end lr <= 2^48 ->
  0 < tb -> tb mod 8 = 0 -> tb+134*8 <= r_end tr -> r_end tr <= 2^48 -> 0 <= ptr_addr mid < 2^64 ->
  liveq DfracDiscarded lb lr -∗ icellq DfracDiscarded lb 0 134 -∗ liveq DfracDiscarded tb tr -∗
  (if k <? 134 then pcellq DfracDiscarded tb (8*k) mid ∗ live_capq DfracDiscarded (ptr_cap mid) mr else True) -∗
  ▷ Φ (Ret (WPtr (if k <? 134 then mid else null))) -∗ WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hk Hlen Htable Hlb Hle Hlr Htb Hal Hte Htr Hmid. injection Hfr as <-.
  iIntros "#Hll #Hlen #Htl Hslot HK". step. step_symbolic.
  destruct (Z_lt_dec k (2^31)) as [Hpos|Hneg].
  all: branch_symbolic; change (sign_extension (2^32) (2^31) (0 mod 2^32)) with 0;
    unfold sign_extension; rewrite !(Z.mod_small k (2^32)) //.
  2: (rewrite (proj2 (Z.leb_le (2^31) k) ltac:(lia)) (proj2 (Z.leb_gt 0 (k-2^32)) ltac:(lia));
      step; branch; step; iApply wp_ret; [reflexivity|vx|]; iNext;
      rewrite (proj2 (Z.ltb_ge k 134) ltac:(lia)); iExact "HK").
  rewrite (proj2 (Z.leb_gt _ _) Hpos) (proj2 (Z.leb_le 0 k) (proj1 Hk)).
  step. step_global Hlen. check_read_dq "Hll" by a2. iNext. iIntros "_".
  iApply (wp_raw_load_read_dq with "Hll Hlen"); [reflexivity|vx|right; reflexivity|a2|].
  iNext. iIntros "_ _". do 2 step_symbolic. step. step.
  branch_symbolic. change ((134 mod 2^64) mod 2^64) with 134.
  rewrite (sext_small k ltac:(lia)) (Z.mod_small k (2^64) ltac:(lia)).
  destruct (Z.ltb_spec k 134) as [Hin|Hout].
  2: (step; iApply wp_ret; [reflexivity|vx|]; iNext; iExact "HK").
  step. step_global Htable. do 2 step_symbolic.
  change (2 ^ ((3 mod 2^32) mod 64)) with 8.
  rewrite (sext_small k ltac:(lia)) (Z.mod_small k (2^64) ltac:(lia))
    (Z.mod_small (k*8) (2^64) ltac:(lia)) (Z.mul_comm k 8).
  step. check_read_dq "Htl" by a2. iNext. iIntros "_". iDestruct "Hslot" as "[#Hcell Htarget]".
  iApply (wp_raw_load_pointer_dq with "Htl Hcell Htarget"); [reflexivity|vx|right; reflexivity|a2|a2|exact Hmid|].
  iNext. iIntros "_ _ _".
  iApply wp_ret; [reflexivity|vx|]. iNext. iExact "HK".
Qed.
End lookup.
