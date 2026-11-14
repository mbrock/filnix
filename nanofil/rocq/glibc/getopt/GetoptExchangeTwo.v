From Glibc Require Import GlibcProgram.
(** Glibc's scanner inlines its exchange routine twice. The outer loop
    of each copy alternates its two swap loops until one of the two
    blocks is empty. This file gives the proof script for that loop and
    proves the loop of the first copy. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString GetoptModule GetoptState GetoptBytes
  GetoptInitialize GetoptEntry GetoptArgv GetoptExchange
  GetoptSwap2Lower GetoptSwap2Upper.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptExchange GetoptInitialize GetoptState GetoptSwap2Lower GetoptSwap2Upper LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** Names that avoid a list may be extended by others that avoid it. *)
Lemma avoids_app_r ks1 ks2 W : avoids ks1 W = true -> avoids ks2 W = true -> avoids (ks1 ++ ks2) W = true.
Proof. unfold avoids. rewrite forallb_app. by intros -> ->. Qed.


(** This module proves the lower swap loop of the first copy. *)
(** This module proves the upper swap loop of the first copy. *)
Import GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

(** This tactic enters a block and evaluates its phi assignments. *)


(** This tactic proves the kept facts a swap loop's caller needs: the
    lookups at kept names, and kept lookups since the loop began. *)
Ltac x_after p1 p3 v11 av ks e :=
  iIntros (? ? ?) "Hl Hc Hs3";
  lazymatch goal with Hx : Permutation _ _ /\ _ /\ _ |- _ =>
    destruct Hx as (Hp3 & Hk3 & Hv); apply keeps_app in Hk3 as [Hk3 Hk3'];
    lazymatch type of Hk3 with keeps _ _ ?e3 =>
      eassert (L1 : lookup p1 e3 = Some _) by (rewrite (keeps_in _ _ _ _ Hk3'); [lk_prove | cbn; tauto]);
      eassert (L2 : lookup p3 e3 = Some _) by (rewrite (keeps_in _ _ _ _ Hk3'); [lk_prove | cbn; tauto]);
      eassert (L3 : lookup v11 e3 = Some _) by (rewrite (keeps_in _ _ _ _ Hk3'); [lk_prove | cbn; tauto]);
      assert (L4 : lookup (TAtom "v2") e3 = Some (WPtr (mkPtr av (Obj av))))
        by (rewrite (keeps_in _ _ _ _ Hk3'); [lk_prove | cbn; tauto]);
      assert (Hke3 : keeps ks e e3) by (eapply keeps_trans; [|exact Hk3]; xkeep)
    end
  end;
  iApply wp_enter; [reflexivity | vxn | iNext].

(** After a swap run, the outer loop continues with a shorter block.
    This tactic continues it with the new bounds bot and top. *)
Ltac x_again IH bot top :=
  lazymatch goal with Hp3 : Permutation _ ?ps3 |- _ =>
    iApply (IH (Z.to_nat (top - bot)) ltac:(lia) _ bot top ps3 eq_refl with "Hl Hc Hs3 [HK]");
    [ lk_prove | lk_prove | lk_prove | lk_prove | lia | lia | lia
    | by rewrite -(Permutation_length Hp3) | lia | lia | lia | lia
    | iIntros (? ? ?) "Hl Hc Hs4";
      match goal with Hx : Permutation _ _ /\ keeps _ _ _ |- _ =>
        destruct Hx as (Hp4 & Hk4);
        iApply ("HK" with "[%] Hl Hc Hs4");
        split; [by rewrite Hp3|]; eapply keeps_trans; [|exact Hk4]; xkeep end ]
  end.

(** This tactic proves the outer loop of either exchange, given its two
    swap-loop lemmas and the names of bot, top and mid. *)
Ltac x_outer lower upper p1 p3 v11 ks e bot mid top av ar n ps :=
  intros Hks; pose proof (avoids_app _ _ _ Hks) as [Hloop Hin];
  remember (Z.to_nat (top - bot)) as m eqn:Hms; revert e bot top ps Hms;
  induction m as [m IH] using (well_founded_induction lt_wf); intros e bot top ps Hms;
  iIntros (Hb Ht Hm Hv2 Hbm Hmt Htop Hlen Hav Hal Hend Hr) "Hl Hc #Hs HK";
  unfold_blk; cbn [b_insts b_jump];
  step; iApply wp_branch; [vx | iNext]; sx;
  destruct (Z.ltb_spec mid top) as [Hmt' | Hmt']; close_br;
  [| step; brz; iApply ("HK" with "[%] Hl Hc Hs"); split; [done|]; xkeep ];
  step; step; step; step; iApply wp_branch; [vx | iNext]; sx;
  destruct (Z.ltb_spec bot mid) as [Hbm' | Hbm']; close_br;
  [| iApply ("HK" with "[%] Hl Hc Hs"); split; [done|]; xkeep ];
  step; step; step; step;
  assert (E37 : (mid mod 2 ^ 32 - bot mod 2 ^ 32) mod 2 ^ 32 = mid - bot)
    by (rewrite (Z.mod_small mid); [|lia]; rewrite (Z.mod_small bot); [|lia]; rewrite Z.mod_small; lia);
  assert (E34 : (top mod 2 ^ 32 - mid mod 2 ^ 32) mod 2 ^ 32 = top - mid)
    by (rewrite (Z.mod_small mid); [|lia]; rewrite (Z.mod_small top); [|lia]; rewrite Z.mod_small; lia);
  rewrite E37 E34; iApply wp_branch; [vx | iNext]; sx;
  set (ks' := (ks ++ [p1; p3; v11; TAtom "v2"])%list);
  destruct (Z.ltb_spec (mid - bot) (top - mid)) as [Hlo | Hup]; close_br;
  [ iApply (lower ks' _ _ 0 bot mid top av ar n ps with "Hl Hc Hs [HK]");
    [ apply avoids_app_r; [exact Hin | vm_compute; reflexivity] | reflexivity | lk_prove | lk_prove | lk_prove | lk_prove
    | lia | lia | lia | lia | assumption | lia | lia | lia | lia
    | x_after p1 p3 v11 av ks e; x_again IH bot (top - (mid - bot)) ]
  | iApply (upper ks' _ _ 0 bot mid top av ar n ps with "Hl Hc Hs [HK]");
    [ apply avoids_app_r; [exact Hin | vm_compute; reflexivity] | reflexivity | lk_prove | lk_prove | lk_prove | lk_prove
    | lia | lia | lia | lia | assumption | lia | lia | lia | lia
    | x_after p1 p3 v11 av ks e; x_again IH (bot + (top - mid)) top ] ].

Import ProgramAbbreviations.
Section exchange.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance xchg_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The outer loop keeps 0 <= bot <= mid <= top <= n: each swap run
    shrinks the longer block by the length of the shorter one. *)
Lemma wp_x2_loop ks e bot mid top av ar n ps Φ :
  avoids ks x2_outer = true ->
  lookup (TAtom "iw_2.pr.1") e = Some (WInt bot) -> lookup (TAtom "iw_2.pr.3") e = Some (WInt top) ->
  lookup (TAtom "iw_2.v11") e = Some (WInt mid) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  0 <= bot <= mid -> mid <= top -> top <= n < 2 ^ 31 ->
  Z.of_nat (List.length ps) = n ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  (∀ e' ps', ⌜Permutation ps ps' /\ keeps ks e e'⌝ -∗
     live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "iw_2.L18") (Some (TAtom "iw_2.L23")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None
              (Exec (TAtom "iw_2.L16") (b_insts x2_blk16) (b_jump x2_blk16))) : gexpr) {{ Φ }}.
Proof. x_outer (GetoptSwap2Lower.wp_x2_lower) (GetoptSwap2Upper.wp_x2_upper)
  (TAtom "iw_2.pr.1") (TAtom "iw_2.pr.3") (TAtom "iw_2.v11") ks e bot mid top av ar n ps. Qed.

End exchange.
