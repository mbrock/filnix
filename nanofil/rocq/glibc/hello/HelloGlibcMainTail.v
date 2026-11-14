(** This file proves the final branches of Hello's greeting.
    Conversion failure reports errno and terminates through the fatal
    error call. Success prints the wide greeting, releases its buffer
    and exits with status zero.

    Conversion, printing and error reporting remain explicit obligations.
    The allocator, errno lookup, deallocation and exit calls use their
    concrete library proofs. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  HelloModule HelloLeaf HelloMain.
From Glibc Require Import OsBlocks OsWorld OsRegistry WordString FileInv LeavesLogic LibioLogic ExitRunTail
  HelloGlibcDebts HelloGlibcMainSteps HelloGlibcMainStart HelloGlibcMainDispatch HelloGlibcMainLoop
  HelloGlibcMainVersion HelloGlibcMainHelpEnd HelloGlibcMainHelp HelloGlibcMainOperands.
From Glibc Require HelloGlibcDebts HelloGlibcMainDispatch HelloGlibcMainHelp HelloGlibcMainHelpEnd HelloGlibcMainLoop HelloGlibcMainOperands HelloGlibcMainStart HelloGlibcMainSteps HelloGlibcMainVersion LibioLogic.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.


(** The operand module supplies the state passed into the greeting. *)
Import HelloGlibcMainOperands HelloGlibcMainHelp HelloGlibcMainHelpEnd HelloGlibcMainVersion HelloGlibcMainLoop HelloGlibcMainDispatch HelloGlibcMainStart HelloGlibcMainSteps HelloGlibcDebts HelloGlibcDebts.FB HelloGlibcDebts.SW HelloGlibcDebts.SW.FI.ML HelloGlibcDebts.SW.FI.LG HelloGlibcDebts.SW.FI.L HelloGlibcDebts.SW.OW HelloGlibcDebts.SW.FI.

Section tail.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (D : HelloDebts w0 ge o) (X0 X : iProp Σ)
  (Lb : HelloLibs w0 ge o (hd_priv w0 ge o D) X0 X) (Hy : hello_layout ge o)
  (av : Z) (ar : region) (b4 b6 : Z) (pn sn : ptr).

(** Collector safepoints preserve the concrete OS interpretation. *)
Local Instance tail_stable : SafepointStable (os_wi w0) := os_wi_stable w0.
(** The program logic uses glibc's OS registry and concrete world interpretation. *)
Local Instance tail_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang glibc_os_registry ge)).
(** This notation combines the stream state and the callees' private state. *)
Local Notation io := (hello_stdio w0 ge o ∗ hd_priv w0 ge o D)%I.

(** A string's length is below 2^48: its words fit the address space. *)
Lemma str_len_bound dq p s : word_string dq p s ⊢ ⌜Z.of_nat (length s) < 2 ^ 48⌝.
Proof.
  iIntros "(%b & %reg & %ws & %Hsh & _)". iPureIntro.
  pose proof (ss_base _ _ _ _ _ Hsh). pose proof (ss_start _ _ _ _ _ Hsh). pose proof (ss_len _ _ _ _ _ Hsh).
  pose proof (ss_fit _ _ _ _ _ Hsh). pose proof (ss_space _ _ _ _ _ Hsh). unfold wstart in *.
  pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)). change (2 ^ 48) with 281474976710656 in *.
  Z.div_mod_to_equations. lia.
Qed.

(** `xmalloc`'s zeroed object for n bytes is a wide buffer holding
    zeros. *)
Lemma obj_wbuf bd n : 0 <= n -> obj bd (wreq n) ⊢ wbuf bd n (replicate (Z.to_nat (req_extent (wreq n))) 0).
Proof.
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
Proof.
  intros Ht Hx. iIntros "HP HK". iApply (wp_call_fn with "HP"); [exact Ht | exact Hx |].
  iIntros (v) "(%n & [-> %Hn] & HQ)". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  cbn. rewrite (Z.mod_small n); [|lia]. iApply ("HK" with "[//] HQ").
Qed.

(** Conversion failure passes the owned handler state to fatal error reporting.
    The existing exit triple supplies its nonreturning continuation. *)
Lemma join_fail e Ψ :
  hello_ro ge o -∗ io -∗ names o -∗ X -∗
  WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "L34") (Some (TAtom "iw_1.join")))) : gexpr) {{ Ψ }}.
Proof.
  iIntros "#Hro [Hio Hpv] Hn HX". pose proof (hy_eb_at _ _ Hy) as (He0 & Hee & Her).
  iPoseProof "Hro" as "(_ & _ & _ & _ & _ & _ & #Hel & _)".
  step.
  iApply (wp_call_ptr w0 ge _ _ _ (fun q => ⌜q = mkPtr (ho_eb o) (Obj (ho_eb o))⌝)%I with "[]");
    [eapply fn_triple_mono; [exact (hl_errno _ _ _ _ _ _ Lb)|]; iIntros (r) "->"; iExists _; iSplit; done |
     reflexivity | done |].
  iNext. iIntros (q ->).
  iApply (LibioLogic.wp_check_read_dq with "Hel"); [reflexivity | vx | left; reflexivity | arith | arith | arith |].
  iNext. iIntros "_".
  iDestruct "Hio" as "(Hfo & Hfe & Hfi & Hls & Htc & (%bs & %cs & %Hbc & Hen))".
  rewrite pts_app. iDestruct "Hen" as "[Hb Ha]". destruct Hbc as [Hb4 Hc4].
  iApply (wp_raw_load_sub_bytes_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 bs _ DfracDiscarded (DfracOwn 1)
            with "Hel Hb");
    [reflexivity | vx | exact Hb4 | reflexivity | left; reflexivity | arith |].
  iNext. iIntros "_ Hb".
  step_global (hy_lits _ _ Hy "hello#str.82" ltac:(cbn; tauto)).
  iApply (wp_call_never with "[-]");
    [eapply (hd_error_conv _ _ _ D _ X); exact (hl_exit _ _ _ _ _ _ Lb 1) | vx |].
  iSplitR; [iExact "Hro"|].
  iSplitR "Hpv Hn HX"; [|iSplitL "Hpv"; [iExact "Hpv" | iSplitL "Hn"; [iExact "Hn" | iExact "HX"]]].
  iSplitL "Hfo"; [iExact "Hfo"|]. iSplitL "Hfe"; [iExact "Hfe"|]. iSplitL "Hfi"; [iExact "Hfi"|].
  iSplitL "Hls"; [iExact "Hls"|]. iSplitL "Htc"; [iExact "Htc"|].
  iExists bs, cs. iSplit; [iPureIntro; split; assumption|]. rewrite pts_app. iSplitL "Hb"; [iExact "Hb" | iExact "Ha"].
Qed.

(** `L29`, entered from `iw_1.join`: `wprintf` prints the wide
    greeting in the buffer bd, `free` frees it, and `exit (0)` is
    called. *)
Lemma join_print e bd n ws Ψ :
  lookup (TAtom "v23") e = Some (WPtr (mkPtr bd (Obj bd))) -> 0 < bd -> wide_terminated ws ->
  hello_ro ge o -∗ io -∗ names o -∗ X -∗ wbuf bd n ws -∗
  WP (ERun (mkFrame main_fn e [] None (Enter (TAtom "L29") (Some (TAtom "iw_1.join")))) : gexpr) {{ Ψ }}.
Proof.
  intros H23 Hbd Hw. iIntros "#Hro [Hio Hpv] Hn HX Hwb".
  step. step_global (hy_lits _ _ Hy "hello#str.83" ltac:(cbn; tauto)).
  iApply (wp_call_int with "[Hio Hpv Hwb]");
    [exact (hd_wprintf _ _ _ D bd n ws Hw) | vx |
     iSplitR; [iExact "Hro"|]; iSplitL "Hio"; [iExact "Hio"|]; iSplitL "Hpv"; [iExact "Hpv" | iExact "Hwb"] |].
  iNext. iIntros (k _) "(Hio & Hpv & Hwb)".
  iDestruct "Hwb" as (cs) "(_ & Hl & _ & _)".
  iApply (wp_call_void w0 ge _ _ _ True%I with "Hl");
    [eapply fn_triple_mono; [exact (hl_free _ _ _ _ _ _ Lb bd (mkRegion bd (bd + req_extent (wreq n)) Heap Live) eq_refl ltac:(lia))|];
     iIntros (r) "->"; iSplit; done | vx |].
  iNext. iIntros "_".
  iApply (wp_exit_call w0 ge o D X0 X Lb with "Hro Hio Hpv Hn HX"). vx.
Qed.

End tail.
