(** This file provides the rules shared by the proofs of Hello's main
    function. Call rules resume the caller with the callee's result.
    Memory rules read the argument vector, strings and standard streams
    while preserving the ownership needed by later calls.

    The step tactics apply the existing program-logic rules for pure
    instructions, branches and returns. Each application still proves
    the rule's memory and control-flow premises. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld OsRegistry WordString FileInv LeavesLogic ExitRunTail HelloGlibcDebts.
Import ListNotations.
Open Scope Z_scope.

(** These rules and tactics share one [[runtime]] and logic instance. *)
Module HelloGlibcStepsOn (R : Runtime) (LG0 : LogicSig R).
(** The debt record supplies the call contracts and their resources. *)
Module D := HelloGlibcDebtsOn R LG0.
Import D D.FB D.SW D.SW.FI.ML D.SW.FI.LG D.SW.FI.L D.SW.OW D.SW.FI.

(** This tactic supplies the safepoint instance left by a step rule. *)
Ltac ins := lazymatch goal with |- SafepointStable _ => exact _ | _ => idtac end.

(** This tactic takes one pure step after computing its argument values. *)
Ltac st :=
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (ERun (mkFrame _ _ _ _ ?pos)) _) =>
      lazymatch pos with
      | Exec _ (Let _ _ _ _ :: _) _ =>
          eapply step_wand; [eapply wp_let; ins; [reflexivity | reflexivity | vx | intros ?; reflexivity] |]
      | Exec _ (Flight _ _ _ _ :: _) _ =>
          eapply step_wand; [eapply wp_flight; ins; [vx | reflexivity | vx] |]
      | Enter _ _ =>
          eapply step_wand; [eapply wp_enter; ins; [reflexivity | vx] |]; cbn [b_insts b_jump]
      | Exec _ nil (JGoto _) => eapply step_wand; [eapply wp_goto; ins |]; cbn [edge_label]
      end
  end.

(** This tactic copies a global pointer into the local environment. *)
Ltac st_global Hs :=
  eapply step_wand;
    [eapply wp_let; ins;
       [reflexivity | reflexivity | cbn [map2_option value_x]; rewrite Hs; reflexivity | intros ?; reflexivity] |].

(** This tactic computes a branch condition and takes the selected edge. *)
Ltac br := eapply step_wand; [eapply wp_branch; ins; vx |]; decide_branch.

(** This tactic resumes the caller with the returned value bound. *)
Ltac resume := iExists _; iSplit; [iPureIntro; reflexivity|]; iNext; cbn [fr_fn fr_env fr_locals fr_doomed fr_at].

Section steps.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs).

(** Collector safepoints preserve the concrete OS interpretation. *)
Local Instance steps_stable : SafepointStable (os_wi w0) := os_wi_stable w0.
(** The program logic uses glibc's OS registry and concrete world interpretation. *)
Local Instance steps_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang glibc_os_registry ge)).

(** A call may reuse a read-only pointer argument. *)
Global Instance arg_ro_ptr_persistent q : Persistent (arg_ro o (WPtr q)).
Proof. rewrite /arg_ro. apply _. Qed.

(** The caller keeps the bounded integer returned by this call. *)
Lemma wp_call_int g xs P Q f e ls lab d args rest j Ψ :
  fn_triple w0 ge g xs P (ret_int Q) -> map_option (arg_x ge e) args = Some xs ->
  P -∗ ▷ (∀ n, ⌜0 <= n < 2 ^ 32⌝ -∗ Q -∗ WP (ERun (mkFrame f (put d (WInt n) e) ls None (Exec lab rest j)) : gexpr)
             {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call (CResult d W) (Global g) args :: rest) j)) : gexpr) {{ Ψ }}.
Proof.
  intros Ht Hx. iIntros "HP HK". iApply (wp_call_fn with "HP"); [exact Ht | exact Hx |].
  iIntros (v) "(%n & [-> %Hn] & HQ)". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  cbn. rewrite (Z.mod_small n); [|lia]. iApply ("HK" with "[//] HQ").
Qed.

(** The caller resumes with a postcondition that depends on the returned integer. *)
Lemma wp_call_intn g xs P (Q : Z -> iProp Σ) f e ls lab d args rest j Ψ :
  fn_triple w0 ge g xs P (fun r => ∃ n, ⌜r = Ret (WInt n) /\ 0 <= n < 2 ^ 32⌝ ∗ Q n)%I ->
  map_option (arg_x ge e) args = Some xs ->
  P -∗ ▷ (∀ n, ⌜0 <= n < 2 ^ 32⌝ -∗ Q n -∗
            WP (ERun (mkFrame f (put d (WInt n) e) ls None (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call (CResult d W) (Global g) args :: rest) j)) : gexpr) {{ Ψ }}.
Proof.
  intros Ht Hx. iIntros "HP HK". iApply (wp_call_fn with "HP"); [exact Ht | exact Hx |].
  iIntros (v) "(%n & [-> %Hn] & HQ)". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  cbn. rewrite (Z.mod_small n); [|lia]. iApply ("HK" with "[//] HQ").
Qed.

(** A triple's postcondition may be weakened. *)
Lemma fn_triple_mono g xs P Q Q' :
  fn_triple w0 ge g xs P Q -> (forall r, Q r ⊢ Q' r) -> fn_triple w0 ge g xs P Q'.
Proof.
  intros (gf & Hg & Hfr & Ht) HQ. exists gf. split; [exact Hg|]. split; [exact Hfr|].
  intros fr Φ Hf. iIntros "HP HK". iApply (Ht fr Φ Hf with "HP"). iIntros (r) "HQ". iApply "HK".
  iApply (HQ with "HQ").
Qed.

(** The caller keeps the pointer returned by this call. *)
Lemma wp_call_ptr g xs Pr (Q : ptr -> iProp Σ) f e ls lab d args rest j Ψ :
  fn_triple w0 ge g xs Pr (fun r => ∃ q, ⌜r = Ret (WPtr q)⌝ ∗ Q q)%I -> map_option (arg_x ge e) args = Some xs ->
  Pr -∗ ▷ (∀ q, Q q -∗ WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call (CResult d P) (Global g) args :: rest) j)) : gexpr) {{ Ψ }}.
Proof.
  intros Ht Hx. iIntros "HP HK". iApply (wp_call_fn with "HP"); [exact Ht | exact Hx |].
  iIntros (v) "(%q & -> & HQ)". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  iApply ("HK" with "HQ").
Qed.

(** The caller resumes after a call that returns no value. *)
Lemma wp_call_void g xs P Q f e ls lab args rest j Ψ :
  fn_triple w0 ge g xs P (fun r => ⌜r = RetVoid⌝ ∗ Q)%I -> map_option (arg_x ge e) args = Some xs ->
  P -∗ ▷ (Q -∗ WP (ERun (mkFrame f e ls None (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call CVoid (Global g) args :: rest) j)) : gexpr) {{ Ψ }}.
Proof.
  intros Ht Hx. iIntros "HP HK". iApply (wp_call_fn with "HP"); [exact Ht | exact Hx |].
  iIntros (v) "[-> HQ]". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. iApply ("HK" with "HQ").
Qed.

(** A call that never returns establishes any postcondition. *)
Lemma wp_call_never g xs P r f e ls lab args rest j Ψ :
  fn_triple w0 ge g xs P (fun _ => False)%I -> map_option (arg_x ge e) args = Some xs ->
  P -∗ WP (ERun (mkFrame f e ls None (Exec lab (Call r (Global g) args :: rest) j)) : gexpr) {{ Ψ }}.
Proof.
  intros Ht Hx. iIntros "HP". iApply (wp_call_fn with "HP"); [exact Ht | exact Hx |]. iIntros (v) "[]".
Qed.

(** Eight zero bytes and an empty slot at offset 0 are a null pointer's
    cell. *)
Lemma zero_pcell b : bytes b 0 (replicate 8 0) ∗ auxes b 0 [CNone] ⊣⊢ pcell b 0 null.
Proof.
  rewrite /bytes /auxes /pcell -pts_app.
  assert (E : byte_ps b 0 (replicate 8 0) ++ aux_ps b 0 [CNone] = cell b 0 0 ++ [(PAux b 0, VAux CNone)]).
  { vm_compute. reflexivity. }
  rewrite E pts_app. cbn [ptr_addr ptr_cap null]. rewrite /pts !big_sepL_cons big_sepL_nil.
  iSplit; [iIntros "[H [A _]]"; iFrame | iIntros "[A H]"; iFrame].
Qed.

(** Reading an argument slot returns its pointer or the final null.
    All argument strings remain read-only. *)
Lemma wp_argv_load f e ls lab d c rest j av ar ps a k Ψ :
  lookup c e = Some (WPtr (mkPtr a (Obj av))) -> a = av + 8 * Z.of_nat k -> (k <= length ps)%nat ->
  argv_own av ar ps -∗ ([∗ list] q ∈ ps, str_ro q) -∗
  ▷ (argv_own av ar ps -∗ WP (ERun (mkFrame f (put d (WPtr (nth k (ps ++ [null]) null)) e) ls None
                                    (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Let d P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead])
                                             [Tmp c] :: rest) j)) : gexpr) {{ Ψ }}.
Proof.
  intros Hc -> Hk. iIntros "(%Hav & Hl & Hs) #Hps HK". destruct Hav as (Hav0 & Hav8 & H31 & Havend & Har).
  assert (Hlk : (ps ++ [null]) !! k = Some (nth k (ps ++ [null]) null)).
  { destruct (lookup_lt_is_Some_2 (ps ++ [null]) k) as [x Hx]; [rewrite length_app /=; lia|].
    rewrite (nth_lookup_Some _ _ _ _ Hx). exact Hx. }
  iDestruct (big_sepL_lookup_acc with "Hs") as "[Hq Hs]"; [exact Hlk|].
  set (q := nth k (ps ++ [null]) null) in *.
  iAssert (∃ reg', live_capq DfracDiscarded (ptr_cap q) reg' ∗ ⌜0 <= ptr_addr q < 2 ^ 64⌝)%I as (reg') "[Hk %Hq]".
  { destruct (decide (k = length ps)) as [->|Hne].
    - assert (q = null) as ->.
      { unfold q. rewrite nth_middle. reflexivity. }
      iExists (mkRegion 0 0 Heap Live). cbn. iSplit; [done | iPureIntro; lia].
    - assert (Hin : In q ps).
      { unfold q. rewrite app_nth1; [apply nth_In | ]; lia. }
      iDestruct (big_sepL_elem_of _ _ q with "Hps") as (s) "Hw"; [apply list_elem_of_In; exact Hin|].
      iDestruct "Hw" as (b reg ws) "[%Hsh [Hlv _]]".
      pose proof (Z.mod_pos_bound (ptr_addr q) 8 ltac:(lia)).
      pose proof (ss_base _ _ _ _ _ Hsh). pose proof (ss_start _ _ _ _ _ Hsh).
      pose proof (ss_fit _ _ _ _ _ Hsh). pose proof (ss_space _ _ _ _ _ Hsh). unfold wstart in *.
      iExists reg. iSplit; [|iPureIntro; lia].
      destruct (ss_cap _ _ _ _ _ Hsh) as [-> | ->]; cbn; iExact "Hlv". }
  assert (Hal : (av + 8 * Z.of_nat k) mod 8 = 0).
  { rewrite (Z.mul_comm 8) Z_mod_plus_full. exact Hav8. }
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ av ar (8 * Z.of_nat k) q reg'
            (DfracOwn 1) (DfracOwn 1) DfracDiscarded with "[Hl] [Hq] Hk");
    [reflexivity | cbn; rewrite Hc; reflexivity | left; reflexivity |
     cbn; unfold raw_address; rewrite Z.add_0_r; apply Z.mod_small; lia |
     exact Hal |
     exact Hq | iExact "Hl" | iExact "Hq" |].
  iNext. iIntros "Hl Hq _". iApply "HK". iSplit; [iPureIntro; repeat split; assumption|]. iFrame "Hl".
  iApply ("Hs" with "Hq").
Qed.

(** A literal of `main` is a read-only string. *)
Lemma lit_ro s : In s hello_lits -> hello_ro ge o ⊢ str_ro (sym_ptr ge s).
Proof.
  intros Hs. iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hl)".
  iApply (big_sepL_elem_of with "Hl"). apply list_elem_of_In. exact Hs.
Qed.

(** A read-only string's pointer has a live capability at a persistent
    share, and its address is a machine word. *)
Lemma str_ro_cap q : str_ro q ⊢ ∃ reg, live_capq DfracDiscarded (ptr_cap q) reg ∗ ⌜0 <= ptr_addr q < 2 ^ 64⌝.
Proof.
  iIntros "(%s & %b & %reg & %ws & %Hsh & Hlv & _)".
  pose proof (Z.mod_pos_bound (ptr_addr q) 8 ltac:(lia)).
  pose proof (ss_base _ _ _ _ _ Hsh). pose proof (ss_start _ _ _ _ _ Hsh).
  pose proof (ss_fit _ _ _ _ _ Hsh). pose proof (ss_space _ _ _ _ _ Hsh). unfold wstart in *.
  iExists reg. iSplit; [|iPureIntro; lia].
  destruct (ss_cap _ _ _ _ _ Hsh) as [-> | ->]; cbn; iExact "Hlv".
Qed.

(** A suffix of a read-only string is a read-only string. *)
Lemma str_ro_suffix p s (k : nat) : (k <= length s)%nat ->
  word_string DfracDiscarded p s ⊢ str_ro (ptr_add p (Z.of_nat k)).
Proof.
  intros Hk. rewrite -{1}(take_drop k s). iIntros "H". iExists (drop k s).
  iPoseProof (word_string_suffix with "H") as "H". rewrite length_take_le; [iExact "H" | exact Hk].
Qed.

(** A read-only string satisfies the output calls' argument contract. *)
Lemma str_ro_arg q : str_ro q ⊢ arg_ro o (WPtr q).
Proof.
  iIntros "(%s & Hs)". iRight. iExists q, s, O. iFrame "Hs". iPureIntro. split; [|lia].
  destruct q as [qa qc]. rewrite /ptr_add /=. f_equal. lia.
Qed.

(** Loading a string pointer preserves shared ownership of its cell
    and read-only ownership of the string. *)
Lemma wp_load_str f e ls lab d c rest j b reg x dq1 dq2 Ψ :
  lookup c e = Some (WPtr (mkPtr b (Obj b))) -> 0 <= b < 2 ^ 64 -> b mod 8 = 0 ->
  liveq dq1 b reg -∗ pcellq dq2 b 0 x -∗ str_ro x -∗
  ▷ (liveq dq1 b reg -∗ pcellq dq2 b 0 x -∗
     WP (ERun (mkFrame f (put d (WPtr x) e) ls None (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Let d P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead])
                                             [Tmp c] :: rest) j)) : gexpr) {{ Ψ }}.
Proof.
  intros Hc Hb0 Hb8. iIntros "Hl Hp Hs HK". iDestruct (str_ro_cap with "Hs") as (reg') "[Hk %Hq]".
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ b reg 0 x reg' dq1 dq2 DfracDiscarded
            with "Hl Hp Hk");
    [reflexivity | cbn; rewrite Hc; reflexivity | left; reflexivity |
     cbn; unfold raw_address; rewrite !Z.add_0_r; apply Z.mod_small; lia | rewrite Z.add_0_r; exact Hb8 | exact Hq |].
  iNext. iIntros "Hl Hp _". iApply ("HK" with "Hl Hp").
Qed.

(** Loading a standard stream reads its shared pointer cell and
    borrows the live token from the stream invariant. *)
Lemma wp_load_stream f e ls lab d c rest j sb sreg g Ψ :
  lookup c e = Some (WPtr (mkPtr sb (Obj sb))) -> 0 <= sb < 2 ^ 64 -> sb mod 8 = 0 ->
  liveq DfracDiscarded sb sreg -∗ pcellq DfracDiscarded sb 0 g -∗ file_inv (ho_vb o) (ow_self w0) g -∗
  ▷ (file_inv (ho_vb o) (ow_self w0) g -∗
     WP (ERun (mkFrame f (put d (WPtr g) e) ls None (Exec lab rest j)) : gexpr) {{ Ψ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Let d P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead])
                                             [Tmp c] :: rest) j)) : gexpr) {{ Ψ }}.
Proof.
  intros Hc Hb0 Hb8. iIntros "Hl Hp Hf HK".
  iDestruct "Hf" as "(%fb & %freg & %st & %nb & %vt & %held & %Hp & Hfl & Hrest)".
  pose proof Hp as (Hg & Hal & Hfb & Hend & Hreg & _).
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ sb sreg 0 g freg DfracDiscarded DfracDiscarded
            (DfracOwn 1) with "Hl Hp [Hfl]");
    [reflexivity | cbn; rewrite Hc; reflexivity | left; reflexivity |
     cbn; unfold raw_address; rewrite !Z.add_0_r; apply Z.mod_small; lia | rewrite Z.add_0_r; exact Hb8 |
     subst g; cbn; unfold file_size in *; lia | subst g; iExact "Hfl" |].
  iNext. iIntros "_ _ Hfl". iApply "HK". iExists fb, freg, st, nb, vt, held. iFrame. iSplit; [iPureIntro; exact Hp|].
  subst g. iExact "Hfl".
Qed.

End steps.
End HelloGlibcStepsOn.
