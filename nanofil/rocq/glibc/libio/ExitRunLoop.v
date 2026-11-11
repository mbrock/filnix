(** The handler loop of user glibc's `__run_exit_handlers`
    (ExitRunCode.v's [glibc___run_exit_handlers]), from the block L101
    with the lock held: [exit_loop] pops the entries of `initial` one at
    a time from the top, calling each handler between the user
    resources R (S i) and R i, and ends with ExitRunTail.v's
    [exit_tail]. By induction on the entries. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules Symbolic ExternalCalls ExternalMachine Transport Pieces Heap Language Logic MemLogic.
From Glibc Require Import GlibcLogic LeavesLogic AtexitLogic OsWorld OsExit OsRegistry ExitRunCode ExitRunTail.
Open Scope Z_scope.
Open Scope list_scope.

(** The loop over the [[runtime]] R and the Logic instance LG0. *)
Module ExitRunLoopOn (R : Runtime) (LG0 : LogicSig R).
Module XT := ExitRunTailOn R LG0.
Import XT XT.L XT.LG XT.AX.ML XT.AX.LV XT.AX XT.OE.OW XT.OE.

Local Opaque glibc___run_exit_handlers.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv).
(** The Iris instance of user glibc's OS registry and world. *)
Local Instance exitloop_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang glibc_os_registry ge)).

(** The handler state after the pass that pops the entry at slot k:
    `idx` k, the entries below it, and slot k spare again. *)
Lemma exit_block_pop b reg ents :
  (List.length ents < 32)%nat ->
  live b reg ∗ pcell b 0 null ∗ icell b 8 (Z.of_nat (List.length ents)) ∗
  ([∗ list] i ↦ e ∈ ents, entry b (16 + 32 * Z.of_nat i) e) ∗ spare b (16 + 32 * Z.of_nat (List.length ents)) ∗
  ([∗ list] i ∈ seqZ (Z.of_nat (List.length ents) + 1) (32 - (Z.of_nat (List.length ents) + 1)),
     spare b (16 + 32 * i)) ⊢
  exit_block b reg ents.
Proof.
  intros Hk. rewrite /exit_block (spares_cons b (Z.of_nat (List.length ents))); [|lia].
  iIntros "($ & $ & $ & $ & $ & $)".
Qed.

(** The loop from L101, `initial` holding ents, the lock held, and R
    (|ents|) owned: each handler, from the top, runs from R (S i) to
    R i, and then the end ([exit_tail]) runs `_IO_cleanup` from R 0.
    By induction on the entries, from the top one. *)
Lemma exit_loop x ents c status e from (R : nat -> iProp Σ) Φ :
  loop_env w0 ge x -> loop_vars x status e ->
  exit_held x ents c -∗ R (List.length ents) -∗
  ([∗ list] i ↦ en ∈ ents, exit_handler w0 ge (status mod 2 ^ 32) en (R (S i)) (R i)) -∗ cleanup_rule w0 ge (R 0%nat) -∗
  WP (ERun (mkFrame glibc___run_exit_handlers e [] None (Enter (TAtom "L101") from)) : gexpr) {{ Φ }}.
Proof.
  revert e from. induction ents as [|en pre IH] using rev_ind; intros e from Henv Hvars.
  { iIntros "Hx HR _ HK". iApply (exit_tail with "Hx HR HK"); [exact Henv | exact Hvars]. }
  pose proof Henv as Henv'. destruct x as [lk lkr dn dnr cl clr fs fsr ib ibr].
  destruct Henv' as (Hlay & Hgl & Hwi & Hwdn & Hwfs & Hxf & Hxg).
  pose proof Hvars as (H0 & H2 & H4 & H6 & H90 & H96).
  destruct Hlay as (Hl0 & Hl4 & Hle & Hd0 & Hde & Hc0 & Hce & Hf0 & Hf8 & Hfe & Hi0 & Hi8 & Hie).
  destruct Hgl as (Hglk & Hgdn & Hgcl & Hgfs). destruct Hwi as (Hwlk & Hwcl & Hwib).
  cbn [xo_lock xo_lock_reg xo_done xo_done_reg xo_called xo_called_reg xo_funcs xo_funcs_reg xo_init xo_init_reg]
    in *.
  rewrite /exit_held /exit_block length_app big_sepL_snoc big_sepL_snoc.
  cbn [List.length xo_lock xo_lock_reg xo_done xo_done_reg xo_called xo_called_reg xo_funcs xo_funcs_reg xo_init
    xo_init_reg].
  rewrite Nat.add_1_r. replace (Z.of_nat (S (List.length pre))) with (Z.of_nat (List.length pre) + 1) by lia.
  remember (Z.of_nat (List.length pre)) as k eqn:Ek.
  iIntros "((%Hlen & %Hc) & Hll & Hlb & Hdl & Hdb & Hcl & Hcc & Hfl & Hfc & Hil & Hnext & Hidx & (Hents & Hen) &
            Hspares) HR (Hhs & Hh) HK".
  assert (Hk : 0 <= k < 32) by lia.
  destruct en as [[fnp argp] dsop]. rewrite /entry /slot. cbn [fst snd].
  iDestruct "Hen" as "(Hef & Hex & Hea & Hed)".
  iDestruct "Hh" as (g gf ys fr) "[%Hhd Hwp]". cbn [fst snd] in Hhd.
  destruct Hhd as (Hfg & Hfc' & Hfn & Hfa & Haa & Hacap & Hcv & Hfr).
  eapply step_wand; [eapply wp_enter; ins; [reflexivity | destruct from; reflexivity] |]; cbn [b_insts b_jump].
  st.
  rule1 "Hil" ltac:(eapply wp_check_read; ins; [reflexivity | vx | left; reflexivity | arith | arith | arith]).
  rule2 "Hil" "Hidx" ltac:(eapply wp_raw_load; ins; [reflexivity | reflexivity | reflexivity | arith]).
  st. br. st. st. st.
  rule2 "Hil" "Hidx" ltac:(eapply wp_raw_load; ins; [reflexivity | reflexivity | reflexivity | arith]).
  st. simp.
  rule1 "Hil" ltac:(eapply wp_renew; ins; [reflexivity | vx | reflexivity | reflexivity | arith | arith | arith]).
  rule2 "Hil" "Hidx" ltac:(eapply wp_raw_store; ins; [vx | reflexivity | reflexivity | arith | ign Hwib]).
  st. st. simp. st_global Hgcl.
  rule1 "Hcl" ltac:(eapply wp_check_read; ins; [reflexivity | reflexivity | left; reflexivity | arith | arith | arith]).
  rule2 "Hcl" "Hcc" ltac:(eapply wp_raw_load; ins; [reflexivity | reflexivity | reflexivity | arith]).
  rule1 "Hil" ltac:(eapply wp_check_read; ins; [reflexivity | vx | left; reflexivity | arith | arith | arith]).
  rule2 "Hil" "Hef" ltac:(eapply wp_raw_load; ins; [reflexivity | reflexivity | reflexivity | arith]).
  st. br. st. st. br. st. st. br. st. st. br. st.
  (* L256: mark the slot free, read the handler and its argument, release the lock. *)
  rule1 "Hil" ltac:(eapply wp_renew; ins; [reflexivity | vx | reflexivity | reflexivity | arith | arith | arith]).
  rule2 "Hil" "Hef" ltac:(eapply wp_raw_store; ins; [vx | reflexivity | reflexivity | arith | ign Hwib]).
  st.
  rule1 "Hil" ltac:(eapply wp_half_check_read; ins;
    [reflexivity | vx | reflexivity | left; reflexivity | arith | arith | arith | arith | arith]).
  iApply (wp_raw_load_pointer_in _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [] with "Hil Hex []");
    [reflexivity | reflexivity | left; reflexivity | arith | arith | lia | intros ? [?|?]; exfalso; congruence |
     by rewrite /pts big_sepL_nil |]. nx. iIntros "Hil Hex _".
  st.
  rule1 "Hil" ltac:(eapply wp_half_check_read; ins;
    [reflexivity | vx | reflexivity | left; reflexivity | arith | arith | arith | arith | arith]).
  iApply (wp_raw_load_pointer_in _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [] with "Hil Hea []");
    [reflexivity | reflexivity | left; reflexivity | arith | arith | lia |
     intros xb [Hx|Hx]; exfalso; destruct (Hacap xb); contradiction | by rewrite /pts big_sepL_nil |].
  nx. iIntros "Hil Hea _".
  st_global Hglk.
  rule1 "Hll" ltac:(eapply wp_check_read; ins;
    [reflexivity | reflexivity | left; reflexivity | arith | arith | arith]).
  iApply (wp_raw_load_sub_bytes_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 [1; 0; 0; 0] (WInt 1)
            (DfracOwn 1) (DfracOwn 1) with "Hll Hlb");
    [reflexivity | reflexivity | reflexivity | reflexivity | left; reflexivity | arith |]. nx. iIntros "Hll Hlb".
  st. st.
  rule1 "Hll" ltac:(eapply wp_half_check; ins;
    [reflexivity | reflexivity | reflexivity | reflexivity | arith | arith | arith | arith | arith]).
  rule2 "Hll" "Hlb" ltac:(eapply wp_raw_cas_w; ins;
    [left; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | arith | arith
     | cas_ign Hwlk]). rewrite lock_release.
  st. br. st. st. br. st.
  (* L279: the call of the handler. *)
  eapply step_wand; [eapply wp_check_function; ins; [reflexivity | exact Hfc'] |].
  iApply (wp_raw_call_bind with "[-]");
    [reflexivity | exact Hfg | exact Hfc' | vx | exact Hfn | exact Hcv | exact Hfr |].
  iNext. iApply (wp_wand with "(Hwp HR)"). iIntros (o) "[-> HR]". iExists _. iSplit; [iPureIntro; reflexivity|].
  nx. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  st_global Hglk.
  rule1 "Hll" ltac:(eapply wp_check; ins; [reflexivity | reflexivity | reflexivity | arith | arith | arith]).
  rule2 "Hll" "Hlb" ltac:(eapply wp_raw_cas_w; ins;
    [left; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | arith | arith
     | cas_ign Hwlk]). rewrite lock_take.
  st. br. st. st. br. st. st_global Hgcl.
  rule1 "Hcl" ltac:(eapply wp_check_read; ins; [reflexivity | reflexivity | left; reflexivity | arith | arith | arith]).
  rule2 "Hcl" "Hcc" ltac:(eapply wp_raw_load; ins; [reflexivity | reflexivity | reflexivity | arith]).
  st. br.
  iApply (IH with "[-HR Hhs HK] HR Hhs HK"); [exact Henv | |].
  { unfold loop_vars. cbn [xo_funcs xo_init].
    repeat split; [look H0 | look H2 | look H4 | look H6 | look H90 | look H96]. }
  rewrite /exit_held. cbn [xo_lock xo_lock_reg xo_done xo_done_reg xo_called xo_called_reg xo_funcs xo_funcs_reg xo_init
    xo_init_reg]. subst k. rewrite Z.add_simpl_r.
  iSplit; [iPureIntro; split; [lia | exact Hc]|]. iFrame "Hll Hlb Hdl Hdb Hcl Hcc Hfl Hfc".
  iApply exit_block_pop; [lia|]. iFrame "Hil Hnext Hidx Hents Hspares". iExists _, _, _, _. iFrame "Hef Hex Hea Hed".
Qed.

End rules.
End ExitRunLoopOn.
