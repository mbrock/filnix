(** In permuting mode, after clamping its nonoption endpoints to the
    public index i, glibc's scanner either exchanges the skipped
    nonoptions with the options that followed them, or restarts the
    nonoption block at i. This file proves those blocks safe and tracks
    the endpoints they leave. *)

From Glibc Require Import GlibcSym GetoptNames OsMemLogic GetoptTactics GlibcProgram GlibcTactics OsTactics GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic FrameNotation.
From Glibc Require Import OsWorld WordString GetoptModule
    GetoptArgv GetoptExchange
  GetoptExchangeTwo GetoptIdle.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The clamp and the choice of exchange assign these names. *)
Definition clamp_names : list name := Eval vm_compute in
  scanner_writes ["L73"; "L91"; "L93"; "L104"; "L106"; "L117"; "L134"; "L135"; "L125"; "L146"]%string.

(** The skip loop over nonoptions starts here. *)
Definition getopt_blk159 : block := Eval vm_compute in x_blk "L159".
(** The test for the "--" argument starts here. *)
Definition getopt_blk119 : block := Eval vm_compute in x_blk "L119".


Import GetoptNames.fn__getopt_internal_r.

(** The scanner carries argv and its private state into the clamp. Earlier
    checks also leave pointers to the state and its opterr field. *)
Definition clamp_inputs (e : env) av b :=
  e.[‹argv›] = Some (WPtr (mkPtr av (Obj av))) /\
  e.[‹d›] = Some (WPtr (mkPtr b (Obj b))) /\
  e.[‹chk(d+4)›] = Some (WPtr (mkPtr (b + 4) (Obj b))) /\
  e.[‹chk(d)›] = Some (WPtr (mkPtr b (Obj b))).

(** Comparing the last nonoption with optind checks both field addresses.
    The ordering test and the skip loop reuse those checked pointers. *)
Definition clamp_checks (e : env) b :=
  e.[‹chk(d+48)@L73›] = Some (WPtr (mkPtr (b + 48) (Obj b))) /\
  e.[‹chk(d)@L73›] = Some (WPtr (mkPtr b (Obj b))).

Abbreviation skip_nonoptions :=
  (Exec (b_label getopt_blk159) (b_insts getopt_blk159) (b_jump getopt_blk159)).
Abbreviation test_double_dash :=
  (Exec (b_label getopt_blk119) (b_insts getopt_blk119) (b_jump getopt_blk119)).

(** The first exchange. *)
Import GetoptIdle GetoptExchangeTwo GetoptExchange Fix.ML0 Fix.LG0 Fix.LG0.L GetoptArgv.

Import ProgramAbbreviations.
Section permute.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Existing Instance program_irisGS.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance permute_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Import Fix.LG0.L.RunNotation.

(** In permuting mode the scanner may move skipped nonoptions behind
    the options after them. The branch starts with 0 <= first <= last <= i
    and reaches the skip loop with first between 0 and i. The argument
    vector it leaves is a permutation of the one it received. *)
Lemma wp_getopt_permute ks e fr f l1 i b r av ar n ps Φ :
  avoids ks (x2_outer ++ x2_edges) = true -> avoids ks clamp_names = true ->
  clamp_inputs e av b -> clamp_checks e b ->
  0 <= f <= l1 -> l1 <= i -> i <= n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 i -∗ int_cell b 40 1 -∗ int_cell b 44 f -∗ int_cell b 48 l1 -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  (∀ e' ps' f' l', ⌜Permutation ps ps' /\ keeps ks e e' /\ 0 <= f' <= i /\ clamp_checks e' b⌝ -∗
     live b r -∗ int_cell b 0 i -∗ int_cell b 40 1 -∗ int_cell b 44 f' -∗ int_cell b 48 l' -∗
     live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
     WP run{ glibc_getopt_internal_r env: e' | pc: skip_nonoptions } {{ Φ }}) -∗
  WP run{ glibc_getopt_internal_r env: e | enter: @"L117" from: fr } {{ Φ }}.
Proof using Type.
  intros Hkx Hkc (Hv2 & Hv12 & Hc0 & Hc2) (Hc23 & Hc24) Hfl Hli Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra.
  iIntros "Hl [%Hi Hib] [%Ho Hob] [%Hf Hfb] [%Hla Hlab] Ha Hc #Hs HK".
  step. sym_run "Hl Hfb Hlab". cbn [cond_bit].
  destruct (decide (f = l1 \/ l1 = i)) as [Hrs | Hx].
  + iAssert (∀ e3 fr', ⌜keeps ks e e3 /\ clamp_inputs e3 av b /\ clamp_checks e3 b⌝ -∗
      live b r -∗ int_cell b 0 i -∗ int_cell b 44 f -∗ int_cell b 48 l1 -∗
      WP run{ glibc_getopt_internal_r env: e3 | enter: @"L125" from: fr' } {{ Φ }})%I
      with "[HK Hob Ha Hc]" as "Hrestart".
    { iIntros (e3 fr' (Hk3 & (Hargv & H12' & H0' & H2'') & H23' & H24')) "Hl [%Hi3 Hib] [%Hf3 Hfb] [%Hl3 Hlab]".
      step. sym_run "Hl Hlab Hib". cbn [cond_bit].
      destruct (Z.eqb_spec l1 i) as [Eli | Eli]; close_br.
      - step. iApply ("HK" $! _ ps f l1 with "[%] Hl [Hib] [Hob] [Hfb] [Hlab] Ha Hc Hs"); [| icell | icell | icell | icell].
        split; [done|]. split; [xkeep|]. split; [lia|]. split; lk_prove.
      - step. sym_run "Hl Hib Hfb".
        store_word "Hl Hfb" by (arith) preserving wi_store.
        iNext. iIntros "Hl Hfb". step. step.
        iApply ("HK" $! _ ps i l1 with "[%] Hl [Hib] [Hob] [Hfb] [Hlab] Ha Hc Hs");
          [| icell | icell | (iApply cell_mod; [lia | iAssumption]) | icell].
        split; [done|]. split; [xkeep|]. split; [lia|]. split; lk_prove. }
    destruct (Z.eqb_spec f l1) as [Efl | Efl]; close_br.
    * step. brz. iApply ("Hrestart" with "[%] Hl [Hib] [Hfb] [Hlab]"); [| icell | icell | icell].
      split; [xkeep|]. repeat split; lk_prove.
    * assert (Eli : l1 = i) by lia. subst l1.
      step. sym_run "Hl Hlab Hib". cbn [cond_bit]. step.
      rewrite (Z.eqb_refl i). brz.
      iApply ("Hrestart" with "[%] Hl [Hib] [Hfb] [Hlab]"); [| icell | icell | icell].
      split; [xkeep|]. repeat split; lk_prove.
  + rewrite (proj2 (Z.eqb_neq f l1)); [|lia]. close_br.
    step. sym_run "Hl Hlab Hib". cbn [cond_bit]. step.
    iApply wp_branch; [vx | iNext]. rewrite (proj2 (Z.eqb_neq l1 i)); [|lia]. close_br.
    iApply (GetoptIdle.wp_x2_exchange (ks ++ [‹chk(d+48)@L73›; ‹chk(d)@L73›])%list _ _ f l1 i b r av ar n ps
      with "Hl [Hib] [Hfb] [Hlab] Ha Hc Hs [HK Hob]");
      try solve [assumption | extend_avoids | lk_prove | lia | icell].
    iIntros (e4 ps4 (Hp4 & Hk4)) "Hl Hib Hfb Hlab Ha Hc Hs4".
    apply keeps_app in Hk4 as [Hk4 Hk4']. step.
    iApply ("HK" $! _ ps4 (f + (i - l1)) i with "[%] Hl Hib [Hob] Hfb Hlab Ha Hc Hs4"); [| icell].
    split; [done|]. split; [eapply keeps_trans; [|exact Hk4]; xkeep|]. split; [lia|].
    split; (rewrite (keeps_in _ _ _ _ Hk4'); [lk_prove | cbn; tauto]).
Qed.

End permute.
