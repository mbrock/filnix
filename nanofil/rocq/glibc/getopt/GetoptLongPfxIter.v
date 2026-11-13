(** When no long option has exactly the name of a word, glibc's parser
    looks through the table for options whose names start with it. This
    file proves one round of that search safe: the test of one entry.
    The parser reads the entry's name only inside the caller's table
    and only through glibc's strncmp, and it stops at the null name. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrchrCode StrchrnulLogic StrlenBits StrlenLogic StrlenLoop StrlenWord
  StrncmpCode StrcmpBits StrcmpLoop StrncmpBits StrncmpLoop StrncmpWords StrncmpLogic
  GetoptModule GetoptState GetoptBytes GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor
  GetoptDiag GetoptReqTail GetoptLongScan GetoptLongExact GetoptLongDiag GetoptLongStore GetoptLongTail GetoptLongReq GetoptLongEq GetoptLongPre GetoptLongArg GetoptLongUnrec GetoptLongMissOnly
  GetoptLongMiss GetoptLongPfxCmp GetoptLongPfxMark GetoptLongPfxAlloc GetoptLongPfxSet GetoptLongPfxStep.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The search's test of an entry starts in this block. *)
Definition plo_blk98 : block := Eval vm_compute in plo_blk "L98".
(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptLongPfxIterOn (R : Runtime) (LG0 : LogicSig R).
(** The step module supplies the step after a second match, the set, the option table and the tactics. *)
Module LPT := GetoptLongPfxStepOn R LG0.
Import LPT LPT.LPS LPT.LPS.LPA LPT.LPS.LPA.LPM LPT.LPS.LPA.LPM.LPC LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT
  LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE
  LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS
  LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT
  LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D
  LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X
  LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I
  LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S
  LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI
  LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.ML
  LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.LG
  LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.L
  LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.ST
  LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.GB
  LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.A.

Section iter.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance iter_stable : SafepointStable (os_wi w0) := LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance iter_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The search stands at entry k of the table lo. It holds the first
    match p and its index w, the flag a that says the word is ambiguous
    without a set, the flag m that says malloc made the set, and the set
    sp. At the table's null name it stops with what it holds. Otherwise
    it tests the entry and stands at the step to the next one. Every
    flag target stays the caller's, and the allocator keeps its state M. *)
Lemma wp_pfx_iter ks e (M : iProp Σ) (k : nat) p w a m sp cur s lo os F b r lonly pe Φ :
  avoids ks ploop_names = true -> avoids ks pcmp_names = true -> avoids ks pset_names = true ->
  avoids ks palloc_names = true -> avoids ks pmark_names = true ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) os -> (List.length os < 2 ^ 31)%Z -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  pfx_at e b s lonly pe (Z.of_nat (List.length os)) ->
  lookup (TAtom "pr.3") e = Some (WPtr (ptr_add lo (32 * Z.of_nat k))) ->
  lookup (TAtom "pr.13") e = Some (WInt (Z.of_nat k)) -> lookup (TAtom "pr.8") e = Some (WPtr p) ->
  lookup (TAtom "pr.42") e = Some (WInt w) -> lookup (TAtom "pr.39") e = Some (WInt a) ->
  lookup (TAtom "pr.30") e = Some (WInt m) -> lookup (TAtom "pr.21") e = Some (WPtr sp) ->
  (k <= List.length os)%nat -> pfx_first lo k p w -> (a = 0 \/ a = 1) -> (m = 0 \/ (m = 1 /\ sp <> null)) ->
  word_string DfracDiscarded cur s -∗ opt_table lo os -∗ live b r -∗ pcell b 32 cur -∗ flags_own F -∗
  amb_set (Z.of_nat (List.length os)) sp -∗ M -∗
  ((∀ e', ⌜keeps ks e e' /\ k = List.length os /\ lookup (TAtom "pr.8") e' = Some (WPtr p) /\
      lookup (TAtom "pr.42") e' = Some (WInt w) /\ lookup (TAtom "pr.39") e' = Some (WInt a) /\
      lookup (TAtom "pr.30") e' = Some (WInt m) /\ lookup (TAtom "pr.21") e' = Some (WPtr sp)⌝ -∗
     live b r -∗ pcell b 32 cur -∗ flags_own F -∗ amb_set (Z.of_nat (List.length os)) sp -∗ M -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L101") (Some (TAtom "L98")))) : gexpr)
       {{ Φ }}) ∧
   (∀ e2 p4 w40 a' m' sp', ⌜keeps ks e e2 /\ (k < List.length os)%nat /\
      pfx_at e2 b s lonly pe (Z.of_nat (List.length os)) /\
      lookup (TAtom "pr.3") e2 = Some (WPtr (ptr_add lo (32 * Z.of_nat k))) /\
      lookup (TAtom "pr.13") e2 = Some (WInt (Z.of_nat k)) /\ lookup (TAtom "pr.4") e2 = Some (WPtr p4) /\
      lookup (TAtom "pr.40") e2 = Some (WInt w40) /\ lookup (TAtom "pr.31") e2 = Some (WInt a') /\
      lookup (TAtom "pr.22") e2 = Some (WInt m') /\ lookup (TAtom "pr.14") e2 = Some (WPtr sp') /\
      pfx_first lo (S k) p4 w40 /\ (a' = 0 \/ a' = 1) /\ (m' = 0 \/ (m' = 1 /\ sp' <> null))⌝ -∗
    live b r -∗ pcell b 32 cur -∗ flags_own F -∗ amb_set (Z.of_nat (List.length os)) sp' -∗ M -∗
    WP (ERun (mkFrame glibc_process_long_option e2 [] None
      (Exec (TAtom "L108") (b_insts plo_blk108) (b_jump plo_blk108))) : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None
              (Exec (TAtom "L98") (b_insts plo_blk98) (b_jump plo_blk98))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hksc Hkss Hksa Hksm Hcut Hmal Hset Hgn Hfl Hos Hpe Hb Hal Hend Hr.
  intros Hat H3 H13 H8 H42 H39 H30 H21 Hk Hf Ha Hm.
  assert (Hw32 : 0 <= w < 2 ^ 32) by (destruct Hf as [(_ & ->) | (j & Hj & _ & ->)]; lia).
  iIntros "#Hws #Ht Hl Hcur HF Hs HM HK".
  iPoseProof "Ht" as "Ht0".
  iDestruct "Ht" as (tb treg) "(%Ht & #Htl & #Hes & #Hnul)".
  destruct Ht as (Htc & Htb & Htlo & Hta & Hte & Htr).
  pose proof Hat as (H12 & Hc0 & H48 & H10 & H14 & H90 & H9).
  cbn [b_insts b_jump plo_blk98].
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Htl");
    [reflexivity | vx | exact Htc | rawa | rawa | al8 |]; iNext; iIntros "_".
  iDestruct (argv_str_cap with "Hws") as (rq) "[#Hcapq %Hq0]".
  destruct (Nat.lt_ge_cases k (List.length os)) as [Hlt | Hge].
  2: {
    assert (k = List.length os) as -> by lia.
    iApply (wp_raw_load_pointer_dq with "Htl Hnul []");
      [reflexivity | vx | exact Htc | rawa | al8 | cbn; lia | unfold live_capq; cbn; done |].
    iNext. iIntros "_ _ _". st. st. iApply wp_branch; [vx | iNext]. close_br.
    iDestruct "HK" as "[HK _]". iApply ("HK" with "[%] Hl Hcur HF Hs HM"). split; [xkeep|]. repeat split; lk_prove. }
  destruct (lookup_lt_is_Some_2 os k Hlt) as [y Hy].
  iDestruct (big_sepL_lookup with "Hes") as "(#Hn & #Hnws & _)"; [exact Hy|].
  iDestruct (argv_str_cap with "Hnws") as (rn) "[#Hcapn %Hn0]".
  iDestruct (ws_shape with "Hnws") as %(Hchn & Hnp & Hne).
  iApply (wp_raw_load_pointer_dq with "Htl Hn Hcapn");
    [reflexivity | vx | exact Htc | rawa | al8 | exact Hn0 |].
  iNext. iIntros "_ _ _". st. st.
  rewrite (Z.mod_small (ptr_addr (lo_name y)) (2 ^ 64)); [|lia]. change (0 mod 2 ^ 64) with 0.
  rewrite (proj2 (Z.eqb_neq (ptr_addr (lo_name y)) 0)); [|lia].
  iApply wp_branch; [vx | iNext]. close_br.
  en. iApply (wp_raw_load_pointer_dq with "Htl Hn Hcapn");
    [reflexivity | vx | exact Htc | rawa | al8 | exact Hn0 |].
  iNext. iIntros "_ _ _". st. chk "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hcur Hcapq"); [reflexivity | vx | left; reflexivity | arith | arith | lia |].
  iNext. iIntros "Hl Hcur _".
  pose proof (eq_len_le s) as Hle. iDestruct (ws_shape with "Hws") as %(Hch & Hqp & Hqe).
  iApply (SN.wp_call_glibc_strncmp registry (os_wi w0) ge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z.of_nat (eq_len s))
    with "Hnws Hws"); [lia | vxc (Z.of_nat (eq_len s)) | exact Hgn | reflexivity |].
  iNext. iIntros "_ _". cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. st.
  iDestruct "HK" as "[_ HK]".
  destruct (Z.eqb _ (0 mod 2 ^ 32)) eqn:Ecmp; iApply wp_branch; [vx | iNext | vx | iNext]; close_br.
  2: { st. ploop_small. pcmp_fold "L108" plo_blk108. iApply ("HK" with "[%] Hl Hcur HF Hs HM").
       split; [xkeep|]. split; [exact Hlt|]. split; [unfold pfx_at; repeat split; lk_prove|].
       repeat split; try lk_prove; first [apply pfx_first_S; exact Hf | assumption]. }
  iApply (wp_pfx_step w0 registry ge ks _ M k lo os F b s lonly pe p w a m sp with "Ht0 HF Hs HM");
    [exact Hks | exact Hksc | exact Hkss | exact Hksa | exact Hksm | exact Hcut | exact Hmal | exact Hset | exact Hfl
    | exact Hos | exact Hpe | unfold pfx_at; repeat split; lk_prove | lk_prove | lk_prove | lk_prove | lk_prove
    | lk_prove | lk_prove | lk_prove | lk_prove | exact Hf | exact Hlt | exact Ha | exact Hm |].
  iIntros (e2 p4 w40 a' m' sp' (Hk2 & Hrest)) "HF Hs HM".
  iApply ("HK" $! e2 p4 w40 a' m' sp' with "[%] Hl Hcur HF Hs HM").
  split; [eapply keeps_trans; [|exact Hk2]; xkeep | split; [exact Hlt | exact Hrest]].
Unshelve. all: first [exact treg | exact DfracDiscarded | idtac].
Qed.

End iter.
End GetoptLongPfxIterOn.
