(** Glibc measures a string before copying it to the output buffer. This
    proof follows the string handler's nonnull, narrow path through the
    actual strlen call. It returns the length and preserves the caller's
    share of the readable string, including its terminating word.

    The proof measures the whole string without a precision limit. It
    assumes that the formatter has selected the argument and that the
    program links to this strlen implementation. Null arguments, wide
    strings, and output writes require separate proofs. *)
From Glibc Require Import Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps Fix WordString StrlenWord StrlenLogic.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L LibioLogic LibioCloseSteps.
Open Scope Z_scope.

(** Measuring the string updates the handler's temporary registers but
    leaves the caller's other registers and local allocations unchanged. *)
Definition string_length_env e p n :=
  fold_left (fun e nw => put (fst nw) (snd nw) e)
    [(TAtom "pr.84", WInt 4294967295); (TAtom "pr.63", WInt 0);
     (TAtom "pr.36", WPtr p); (TAtom "v1833", WInt (ptr_addr p));
     (TAtom "v1835", WInt 0); (TAtom "v1862", WInt 1);
     (TAtom "v1865", WInt 115); (TAtom "v1866", WInt 1);
     (TAtom "v1868", WInt 1); (TAtom "v1874", WInt 0);
     (TAtom "v1880", WInt n); (TAtom "pr.111", WInt n)] e.

Section length.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The string remains readable after its length is known. This rule
    returns the same ownership share at the block that chooses how much
    padding to write. It does not impose a width or staging-space bound. *)
Lemma wp_formatter_string_length e ls p dq s Φ :
  lookup (TAtom "v1828") e = Some (WPtr p) ->
  lookup (TAtom "pr.82") e = Some (WInt 4294967295) ->
  lookup (TAtom "pr.62") e = Some (WInt 0) ->
  lookup (TAtom "pr.97") e = Some (WInt 115) ->
  lookup (TAtom "v55") e = Some (WInt 0) ->
  0 < ptr_addr p < 2 ^ 64 ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  word_string dq p s -∗
  ▷ (word_string dq p s -∗
    WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer
      (string_length_env e p (Z.of_nat (length s))) ls None
      (Enter (TAtom "L1831") (Some (TAtom "L1871")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer e ls None
    (Enter (TAtom "L1695") (Some (TAtom "L1825")))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hp Hprec Hwide Hs Hzero Haddr Hstrlen. iIntros "Hs HK".
  iApply wp_enter; [reflexivity | vx |]. iNext.
  cbn [b_insts b_jump]. step. step. branch_as true.
  do 2 step. closed_ints. branch.
  do 3 step. closed_ints. step. step. branch.
  do 2 step. closed_ints. branch. step.
  iApply wp_call_bind; [vx | exact Hstrlen | reflexivity |]. iNext.
  iApply (wp_wand with "[Hs]").
  { iApply (wp_glibc_strlen_ws registry (os_wi w0) ge dq p s
      (fun v => ⌜v = Ret (WInt (Z.of_nat (length s)))⌝ ∗ word_string dq p s)%I with "Hs").
    iIntros "Hs". iFrame. done. }
  iIntros (v) "[-> Hs]". resume. step. step. step.
  iDestruct "Hs" as (b reg ws) "[%Hshape Hw]".
  pose proof Hshape as [Hcap Hb Ha Hstart Hfit Hspace Hlen Hwords Hbytes Hchars].
  assert (Hn : 0 <= Z.of_nat (length s) < 2 ^ 64).
  { unfold wstart in Hfit.
    pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)). lia. }
  iDestruct (word_string_intro with "Hw") as "Hs"; [exact Hshape|].
  assert (Hp0 : (ptr_addr p =? 0) = false) by (apply Z.eqb_neq; lia).
  norm. rewrite Hp0. cbn. iApply ("HK" with "Hs").
Qed.
End length.
