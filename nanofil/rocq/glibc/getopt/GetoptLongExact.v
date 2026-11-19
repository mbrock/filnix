(** A caller of glibc's getopt_long passes a table of long options. Each
    entry is 32 bytes long and holds the option's name, whether it takes
    an argument, a flag pointer and a value, and an entry whose name is
    null ends the table. glibc's long-option parser first looks for an
    entry whose name equals the name it has measured. The caller lends the
    cells and names described by LongOptionTable. The search uses glibc's
    strncmp and strlen and stops at the first match or the null name. *)

From Glibc Require Import OsMemLogic GetoptTactics LongOption LongOptionTable Unit_string_strncmp_os
  GlibcProgram GlibcTactics OsTactics GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld WordString StrlenLogic StrlenWord
  StrncmpLogic
  GetoptModule ByteRead GetoptExchange
   GetoptReqTail GetoptLongScan.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The exact search assigns these names. *)
Definition exact_names : list name := Eval vm_compute in
  List.map TAtom ["pr.9"; "pr.2"; "chk4"; "v55"; "v56"; "v57"; "v62"; "v64"; "chk6"; "v65"; "v67"; "v68"; "chk7";
    "v73"; "v74"; "v75"; "v77"; "v82"; "v84"; "pr.11"; "pr.6"; "v89"; "v90"; "v91"]%string.

(** The search's test starts in this block. *)
Definition plo_blk50 : block := Eval vm_compute in plo_blk "L50".


(** The scan module supplies the string lemmas and the tactics. *)
Import GetoptLongScan GetoptReqTail GetoptExchange Fix.ML0 Fix.LG0 Fix.LG0.L ByteRead.
(** The strncmp module proves glibc's own strncmp. *)
(** The strlen module proves glibc's own strlen. *)

Import ProgramAbbreviations.
Section exact.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the parser's safepoints. *)
Local Instance exact_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The search stands at entry k of the table. It stops at the first
    entry whose name equals the name of length eq_len s at the cursor,
    or at the null name. A found entry j leads on with its pointer, and
    the end of the table leads on with a null pointer and the count of
    entries. The names ks keep
    their values from the caller's environment e. *)
Lemma wp_long_exact_loop ks e (k : nat) cur s lo os b r Φ :
  avoids ks exact_names = true ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined Unit_string_strncmp_os.fn___GI_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "v48") e = Some (WInt (Z.of_nat (eq_len s))) ->
  lookup (TAtom "pr.2") e = Some (WPtr (ptr_add lo (32 * Z.of_nat k))) ->
  lookup (TAtom "pr.9") e = Some (WInt (Z.of_nat k)) ->
  (k <= List.length os)%nat -> (List.length os < 2 ^ 31)%Z ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  word_string DfracDiscarded cur s -∗ opt_table lo os -∗ live b r -∗ pcell b 32 cur -∗
  ((∀ e', ⌜keeps ks e e' /\ lookup (TAtom "v90") e' = Some (WInt 0) /\
        lookup (TAtom "pr.6") e' = Some (WPtr null) /\
        lookup (TAtom "pr.9") e' = Some (WInt (Z.of_nat (List.length os)))⌝ -∗ live b r -∗ pcell b 32 cur -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L98") (Some (TAtom "L53")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e' j, ⌜keeps ks e e' /\ (j < List.length os)%nat /\ lookup (TAtom "v90") e' = Some (WInt 0) /\
        lookup (TAtom "pr.6") e' = Some (WPtr (ptr_add lo (32 * Z.of_nat j))) /\
        lookup (TAtom "pr.11") e' = Some (WInt (Z.of_nat j))⌝ -∗ live b r -∗ pcell b 32 cur -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L87") (Some (TAtom "L53")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None
              (Exec (TAtom "L50") (b_insts plo_blk50) (b_jump plo_blk50))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hks Hgn Hgl. remember (List.length os - k)%nat as m eqn:Hm. revert e k Hm.
  induction m as [m IH] using (well_founded_induction lt_wf).
  intros e k Hm H12 Hc0 H48 Hp2 Hp9 Hk Hos Hb Hal Hend Hr.
  iIntros "#Hws #Ht Hl Hcur HK".
  iDestruct "Ht" as (tb treg) "(%Ht & #Htl & #Hes & #Hnul)".
  destruct Ht as (Htc & Htb & Htlo & Hta & Hte & Htr).
  cbn [b_insts b_jump plo_blk50].
  check_read_dq "Htl" by first [rawa | al8]; iNext; iIntros "_".
  iDestruct (argv_str_cap with "Hws") as (rq) "[#Hcapq %Hq0]".
  destruct (Nat.lt_ge_cases k (List.length os)) as [Hlt | Hge].
  2: {
    assert (k = List.length os) as -> by lia.
    iApply (wp_raw_load_pointer_dq with "Htl Hnul []");
      [reflexivity | vx | exact Htc | rawa | al8 | cbn; lia | unfold live_capq; cbn; done |].
    iNext. iIntros "_ _ _". step. step. iApply wp_branch; [vx | iNext]. close_br.
    step. step. step. step. iApply wp_branch; [vx | iNext]. close_br. iDestruct "HK" as "[HK _]".
    iApply ("HK" with "[%] Hl Hcur"). split; [xkeep|]. repeat split; lk_prove. }
  destruct (lookup_lt_is_Some_2 os k Hlt) as [x Hx].
  iDestruct (big_sepL_lookup with "Hes") as "(#Hn & #Hnws & _)"; [exact Hx|].
  iDestruct (argv_str_cap with "Hnws") as (rn) "[#Hcapn %Hn0]".
  iDestruct (ws_shape with "Hnws") as %(Hchn & Hnp & Hne).
  load_pointer_dq "Htl Hn Hcapn" by first [rawa | al8].
  iNext. iIntros "_ _ _". step. step.
  rewrite (Z.mod_small (ptr_addr (lo_name x)) (2 ^ 64)); [|lia]. change (0 mod 2 ^ 64) with 0.
  rewrite (proj2 (Z.eqb_neq (ptr_addr (lo_name x)) 0)); [|lia].
  iApply wp_branch; [vx | iNext]. close_br.
  step. load_pointer_dq "Htl Hn Hcapn" by first [rawa | al8].
  iNext. iIntros "_ _ _". step. check "Hl".
  load_pointer_dq "Hl Hcur Hcapq" by StringTactics.arith.
  iNext. iIntros "Hl Hcur _".
  pose proof (eq_len_le s) as Hle. iDestruct (ws_shape with "Hws") as %(Hch & Hqp & Hqe).
  iApply (StrncmpLogic.wp_call_glibc_strncmp registry (os_wi w0) ge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z.of_nat (eq_len s)) with "Hnws Hws"); [lia | vxc (Z.of_nat (eq_len s)) | exact Hgn | reflexivity |].
  iNext. iIntros "_ _". cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. step.
  let K := lazymatch iTypeOf "HK" with Some (_, ?P) => P end in
  iAssert (∀ e2 fr2, ⌜keeps ks e e2 /\ lookup (TAtom "v12") e2 = Some (WPtr (mkPtr b (Obj b))) /\
      lookup (TAtom "chk0") e2 = Some (WPtr (mkPtr (b + 32) (Obj b))) /\
      lookup (TAtom "v48") e2 = Some (WInt (Z.of_nat (eq_len s))) /\
      lookup (TAtom "pr.2") e2 = Some (WPtr (ptr_add lo (32 * Z.of_nat k))) /\
      lookup (TAtom "pr.9") e2 = Some (WInt (Z.of_nat k))⌝ -∗ live b r -∗ pcell b 32 cur -∗ K -∗
    WP (ERun (mkFrame glibc_process_long_option e2 [] None (Enter (TAtom "L52") (Some fr2))) : gexpr) {{ Φ }})%I
    as "HL52".
  { iIntros (e2 fr2 (Hk2 & H12' & Hc0' & H48' & Hp2' & Hp9')) "Hl Hcur HK".
    step. step. step. step. iApply wp_enter; [reflexivity | reflexivity | iNext].
    match goal with |- context [put (TAtom "pr.2") (WPtr ?X) _] =>
      replace X with (ptr_add lo (32 * Z.of_nat (S k))) by
        (unfold ptr_add; cbn [ptr_addr ptr_cap]; f_equal; rewrite (Z.mod_small 32 (2 ^ 64)); [|lia];
         rewrite (Z.mod_small (ptr_addr lo + _) (2 ^ 64)); [|lia]; rewrite Z.mod_small; lia) end.
    match goal with |- context [put (TAtom "pr.9") (WInt ?X) _] =>
      replace X with (Z.of_nat (S k)) by (rewrite (Z.mod_small (Z.of_nat k) (2 ^ 32)); [|lia];
          rewrite (Z.mod_small 1 (2 ^ 32)); [|lia]; rewrite Z.mod_mod; [|lia]; rewrite Z.mod_small; lia) end.
    iApply (IH (List.length os - S k)%nat ltac:(lia) _ (S k) eq_refl with "Hws [] Hl Hcur [HK]");
      [lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lia | exact Hos | exact Hb | exact Hal | exact Hend
      | exact Hr | iExists tb, treg; iFrame "Htl Hes Hnul"; iPureIntro; repeat split; assumption |].
    iSplit.
    - iIntros (e' (Hk' & Hq1 & Hq2 & Hq3)) "Hl Hcur". iDestruct "HK" as "[HK _]". iApply ("HK" with "[%] Hl Hcur").
      split; [eapply keeps_trans; [exact Hk2|]; eapply keeps_trans; [|exact Hk']; xkeep | tauto].
    - iIntros (e' j (Hk' & Hq1 & Hq2)) "Hl Hcur". iDestruct "HK" as "[_ HK]". iApply ("HK" $! e' j with "[%] Hl Hcur").
      split; [eapply keeps_trans; [exact Hk2|]; eapply keeps_trans; [|exact Hk']; xkeep | tauto]. }
  destruct (Z.eqb _ (0 mod 2 ^ 32)) eqn:Ecmp; iApply wp_branch; [vx | iNext | vx | iNext]; close_br.
  2: { step. iApply wp_branch; [vx | iNext]. close_br.
       iApply ("HL52" with "[%] Hl Hcur HK"). split; [xkeep|]. repeat split; lk_prove. }
  step. iApply (wp_renew_read_dq with "Htl");
    [reflexivity | vx | reflexivity | exact Htc | rawa | rawa | al8 |].
  iNext. iIntros "_".
  load_pointer_dq "Htl Hn Hcapn" by first [rawa | al8].
  iNext. iIntros "_ _ _".
  iApply (StrlenWord.wp_call_glibc_strlen registry (os_wi w0) ge with "Hnws"); [vx | exact Hgl | reflexivity |].
  iNext. iIntros "_". cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. step. step. step.
  destruct (Z.eqb (Z.of_nat (eq_len s) mod 2 ^ 64) _) eqn:Elen;
    iApply wp_branch; [vx | iNext | vx | iNext]; close_br.
  2: { iApply ("HL52" with "[%] Hl Hcur HK"). split; [xkeep|]. repeat split; lk_prove. }
  iApply wp_enter; [reflexivity | cbn -[put];
    match goal with |- context [lookup (TAtom "pr.9") ?E] =>
      assert (lookup (TAtom "pr.9") E = Some (WInt (Z.of_nat k))) as Hq9 by lk_prove; rewrite Hq9 end;
    match goal with |- context [lookup (TAtom "pr.2") ?E] =>
      assert (lookup (TAtom "pr.2") E = Some (WPtr (ptr_add lo (32 * Z.of_nat k)))) as Hq2 by lk_prove; rewrite Hq2 end;
    reflexivity | iNext]; cbn [b_insts b_jump]. step. step. step.
  rewrite (Z.mod_small (ptr_addr lo + 32 * Z.of_nat k) (2 ^ 64)); [|lia].
  change ((0 mod 2 ^ 64) mod 2 ^ 64) with 0. change (0 mod 2 ^ 64) with 0.
  rewrite (proj2 (Z.eqb_neq (ptr_addr lo + 32 * Z.of_nat k) 0)); [|lia].
  iApply wp_branch; [vx | iNext]. close_br. iDestruct "HK" as "[_ HK]".
  rewrite (Z.mod_small (Z.of_nat k) (2 ^ 32)); [|lia].
  iApply ("HK" $! _ k with "[%] Hl Hcur"). split; [xkeep|]. split; [exact Hlt|]. repeat split; lk_prove.
Unshelve. exact treg. exact DfracDiscarded.
Qed.

End exact.
