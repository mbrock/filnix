(** This file proves the final branch of Hello's greeting. After a
    successful conversion, Hello prints the wide greeting, releases its
    buffer and exits with status zero.

    The library proofs return the output buffer to main and leave
    stdout either narrow or wide. The exit callback handles both
    cases. *)

From Glibc Require Import HelloObjects GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import HelloBodies.
From Glibc Require Import OsBlocks OsWorld OsRegistry WordString FileInv LeavesLogic LibioLogic LibioWIdle ExitRunTail
  HelloGlibcDebts HelloGlibcMainSteps
  HelloGlibcMainVersion.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.


(** The operand module supplies the state passed into the greeting. *)
Import HelloGlibcMainVersion HelloGlibcMainSteps HelloGlibcDebts HelloGlibcDebts.FB HelloGlibcDebts.SW HelloGlibcDebts.SW.FI.ML HelloGlibcDebts.SW.FI.LG HelloGlibcDebts.SW.FI.L HelloGlibcDebts.SW.OW HelloGlibcDebts.SW.FI.

Section tail.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (priv X0 X : iProp Σ)
  (Lb : HelloLibs w0 ge o priv X0 X) (Hy : hello_layout ge o)
  (av : Z) (ar : region) (b4 b6 : Z) (pn sn : ptr).

(** Collector safepoints preserve the concrete OS interpretation. *)
Local Instance tail_stable : SafepointStable (os_wi w0) := os_wi_stable w0.
(** The program logic uses glibc's OS registry and concrete world interpretation. *)
Local Instance tail_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang glibc_os_registry ge)).
(** This notation combines the stream state and the callees' private state. *)
Local Notation io := (hello_stdio w0 ge o ∗ priv)%I.

(** A string's length is below 2^48: its words fit the address space. *)
Lemma str_len_bound dq p s : word_string dq p s ⊢ ⌜Z.of_nat (length s) < 2 ^ 48⌝.
Proof using Type.
  iIntros "(%b & %reg & %ws & %Hsh & _)". iPureIntro.
  pose proof (ss_base _ _ _ _ _ Hsh). pose proof (ss_start _ _ _ _ _ Hsh). pose proof (ss_len _ _ _ _ _ Hsh).
  pose proof (ss_fit _ _ _ _ _ Hsh). pose proof (ss_space _ _ _ _ _ Hsh). unfold wstart in *.
  pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)). change (2 ^ 48) with 281474976710656 in *.
  Z.div_mod_to_equations. lia.
Qed.

(** `xmalloc`'s zeroed object for n bytes is a wide buffer holding
    zeros. *)
Lemma obj_wbuf bd n : 0 <= n -> obj bd (wreq n) ⊢ wbuf bd n (replicate (Z.to_nat (req_extent (wreq n))) 0).
Proof using Type.
  intros Hn. rewrite (obj_zero_block bd _); [|unfold wreq, heap_req; cbn; apply Z.mul_nonneg_nonneg; [apply Z.div_pos |]; lia].
  iIntros "(Hl & Hb & Ha)". iExists _. iFrame. iPureIntro. rewrite !length_replicate. split; reflexivity.
Qed.

(** The caller resumes with a postcondition indexed by the returned 64-bit integer. *)
Lemma wp_call_long g xs P (Q : Z -> iProp Σ) f e ls lab d args rest j Ψ :
  fn_triple w0 ge g xs P (fun r => ∃ n, ⌜r = Ret (WInt n) /\ 0 <= n < 2 ^ 64⌝ ∗ Q n)%I ->
  map_option (arg_x ge e) args = Some xs ->
  P -∗ ▷ (∀ n, ⌜0 <= n < 2 ^ 64⌝ -∗ Q n -∗
            WP (ERun (mkFrame f (put d (WInt n) e) ls None (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call (CResult d L) (Global g) args :: rest) j)) : gexpr) {{ Ψ }}.
Proof using Type.
  intros Ht Hx. iIntros "HP HK". iApply (wp_call_fn with "HP"); [exact Ht | exact Hx |].
  iIntros (v) "(%n & [-> %Hn] & HQ)". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  cbn. rewrite (Z.mod_small n); [|lia]. iApply ("HK" with "[//] HQ").
Qed.

(** `L29`, entered from `iw_1.join`: `wprintf` prints the wide
    greeting in the buffer bd, `free` frees it, and `exit (0)` is
    called. The formatter leaves stdout narrow or wide, and exit's close
    callback has a contract for each orientation. *)
Lemma join_print e bd n ws Ψ :
  lookup (TAtom "v23") e = Some (WPtr (mkPtr bd (Obj bd))) -> 0 < bd -> bd mod 16 = 0 ->
  bd + req_extent (wreq n) <= 2 ^ 48 -> wide_text ws ->
  hello_ro ge o -∗ io -∗ names o -∗ X -∗ wbuf bd n ws -∗
  WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "L29") (Some (TAtom "iw_1.join")))) : gexpr) {{ Ψ }}.
Proof using Type*.
  intros H23 Hbd Hbd16 Hbde Hw. iIntros "#Hro [Hio Hpv] Hn HX Hwb".
  step. step_global (hy_lits _ _ Hy "hello#str.83" ltac:(cbn; tauto)).
  iApply (wp_call_int with "[Hio Hpv Hwb]");
    [exact (hl_wprintf _ _ _ _ _ _ Lb bd n ws Hbd Hbd16 Hbde Hw) | vx |
     iSplitR; [iExact "Hro"|]; iSplitL "Hio"; [iExact "Hio"|]; iSplitL "Hpv"; [iExact "Hpv" | iExact "Hwb"] |].
  iNext. iIntros (k _) "(Hio & Hpv & Hwb)".
  iDestruct "Hwb" as (cs) "(_ & Hl & _ & _)".
  iApply (wp_call_void w0 ge _ _ _ True%I with "Hl");
    [eapply fn_triple_mono; [exact (hl_free _ _ _ _ _ _ Lb bd (mkRegion bd (bd + req_extent (wreq n)) Heap Live) eq_refl ltac:(lia))|];
     iIntros (r) "->"; iSplit; done | vx |].
  iNext. iIntros "_".
  iDestruct "Hio" as "([Hout | Hout] & Hrest)".
  - iApply (wp_exit_call_with w0 ge o priv X0 X Lb (hello_stdio w0 ge o)
      with "Hro [Hout Hrest] Hpv Hn HX"); [exact (hl_close_stdout _ _ _ _ _ _ Lb) | vx | iFrame].
  - iApply (wp_exit_call_with w0 ge o priv X0 X Lb
      (hello_stdio_wide w0 ge o (file_wide ge (ho_vb o) (ow_self w0) (ho_out o) 1))
      with "Hro [Hout Hrest] Hpv Hn HX"); [exact (hl_close_stdout_wide _ _ _ _ _ _ Lb) | vx | iFrame].
Qed.

End tail.
