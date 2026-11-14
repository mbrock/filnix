(** glibc's scanner turns "-W foo" or "-Wfoo" into a call of its
    long-option parser on the word after the W. One file proves the
    scanner safe up to that call, and another proves the call and the
    session that it leaves. This file joins them, so a caller that
    reaches the W option receives either the parser's answer with a
    session at the new index or the missing-argument path. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
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
  GetoptLongMiss GetoptLongPfxCmp GetoptLongPfxMark GetoptLongPfxAlloc GetoptLongPfxSet GetoptLongPfxStep GetoptLongPfxIter GetoptLongPfxLoop GetoptLongPfxEnd GetoptLongAmbTail GetoptLongAmbPrint GetoptLongAmbItem GetoptLongAmbList
  GetoptLongAmbHead GetoptLongAmbPoss GetoptLongAmbRep GetoptLongPfxPath GetoptLongFind GetoptLongBody GetoptLongJoinMiss GetoptLongJoinFound GetoptLongJoin GetoptLongCall GetoptLongOnly GetoptDispatch GetoptLongSession GetoptWTail GetoptWOpt GetoptLongW.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptLongAmbTail GetoptLongBody GetoptLongCall GetoptLongDiag GetoptLongExact GetoptLongPfxAlloc GetoptLongSession GetoptLongStore GetoptLongW GetoptState GetoptWOpt LibioLogic OsWorld.
From Glibc Require Import Fix.

Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The W call reads these names, which keep their values from the scanner's entry to the W option. *)
Definition wos_keys : list name := Eval vm_compute in
  List.map TAtom ["v0"; "v2"; "pr.1"; "v6"; "v8"; "v12"; "pr.3"]%string.

(** A pointer moved twice moves by the sum. *)
Lemma wos_ptr_add p x y : ptr_add (ptr_add p x) y = ptr_add p (x + y).
Proof. destruct p. unfold ptr_add. cbn. f_equal. lia. Qed.

(** A pointer moved by zero stays. *)
Lemma wos_ptr_add_0 p : ptr_add p 0 = p.
Proof. destruct p. unfold ptr_add. cbn. f_equal. lia. Qed.

(** A byte after a dropped prefix is the byte at the summed index. *)
Lemma wos_nth_drop (l : list Z) k m : nth m (drop k l) 0 = nth (k + m) l 0.
Proof. revert l. induction k as [|k IH]; intros [|x l]; cbn; try reflexivity; try (destruct m; reflexivity); apply IH. Qed.

(** These controls show which way the word "-Wfoo" and the word "-W"
    go when the W sits at byte 1. In "-Wfoo" a byte follows the W, so
    the rest of the cluster becomes the long option at the same index. *)
Lemma wos_ctl_cluster : (1 < List.length [45; 87; 102; 111; 111])%nat /\
  sbyte [45; 87; 102; 111; 111] 1 = 87 /\ sbyte [45; 87; 102; 111; 111] 2 <> 0.
Proof. unfold sbyte. cbn. repeat split; lia. Qed.

(** In "-W" the terminator follows the W, so the next word becomes the long option. *)
Lemma wos_ctl_next : (1 < List.length [45; 87])%nat /\ sbyte [45; 87] 1 = 87 /\ sbyte [45; 87] 2 = 0.
Proof. unfold sbyte. cbn. repeat split; lia. Qed.

(** A cursor at the terminator of "-W" fails the condition that a W sits there. *)
Lemma wos_ctl_end : ~ (2 < List.length [45; 87])%nat.
Proof. cbn. lia. Qed.


(** The W option module proves the scanner up to the call. *)
(** The W call module proves the call and restores the session. *)
Import GetoptLongW GetoptLongCall GetoptLongSession GetoptLongBody GetoptLongAmbTail GetoptLongPfxAlloc GetoptLongStore GetoptLongDiag GetoptLongExact GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

(** A key in the list keeps its value through the W option. *)
Ltac wos_lk Hk :=
  lazymatch goal with |- lookup ?k ?e' = _ =>
    rewrite (keeps_in wos_keys k _ e' Hk);
    [|unfold wos_keys; cbn [In]; repeat first [left; reflexivity | right]] end.

(** This tactic proves a pure premise and leaves the proof-mode goal alone. *)
Ltac wos_side :=
  lazymatch goal with
  | |- environments.envs_entails _ _ => fail
  | |- avoids _ _ = true => vm_compute; reflexivity
  | _ => first [assumption | lia | (hnf; apply Forall_forall; intros; reflexivity)]
  end.

Section wos.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance wos_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance wos_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The W option and the call describe the same cells through two copies of their modules, and this tactic converts between the copies. *)
Ltac wos_conv b r j av ar ps c :=
  iAssert (pcell b 32 c) with "[Hcur]" as "Hcur"; [iExact "Hcur"|];
  iAssert (live b r) with "[Hl]" as "Hl"; [iExact "Hl"|];
  iAssert (int_cell b 0 j) with "[Hib]" as "Hib"; [iExact "Hib"|];
  iAssert (live av ar) with "[Ha]" as "Ha"; [iExact "Ha"|];
  iAssert (argv_cells av ps) with "[Hcl]" as "Hcl"; [iExact "Hcl"|].

(** The scanner read the W at the cursor cur, which lies k0 bytes into
    the word q at index i, so the rest of the cluster t starts with the
    W. If the cluster goes on, its rest becomes the long option at the
    same index. Otherwise the next word does, which may be empty, and
    the index moves past the cluster. Either way the caller receives
    the parser's answer with a session at the new index. With no word
    left, the caller receives the missing-argument path with every
    field that it lent. *)
Lemma wp_getopt_wopt_session e fr i n c pe po so oo a b r av ar ps (G : iProp Σ) T fp dom se sereg mid
    (M : iProp Σ) f138 f139 f140 f141 lmid mid3 mid4 lo os F pfx pxs q sq k0 li er ord fst lst Φ :
  GetoptDiag.getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "v455") e = Some (WInt c) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) -> lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "v6") e = Some (WPtr lo) -> lookup (TAtom "v8") e = Some (WPtr li) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk19") e = Some (WPtr po) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk137") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) os -> (List.length os < 2 ^ 31)%Z ->
  ps !! Z.to_nat i = Some q -> (k0 < List.length sq)%nat -> sbyte sq k0 <> 0 ->
  0 <= i < n -> n < 2 ^ 31 - 1 -> Z.of_nat (List.length ps) = n ->
  0 <= c < 2 ^ 32 -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (n + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  0 <= ord <= 2 -> 0 <= fst <= lst -> lst <= i ->
  opt_table lo os -∗ word_string DfracDiscarded q sq -∗ word_string DfracDiscarded po so -∗
  word_string DfracDiscarded pfx pxs -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 (if sbyte sq (S k0) =? 0 then i + 1 else i) -∗ int_cell b 4 er -∗ int_cell b 8 oo -∗
  pcell b 16 a -∗ int_cell b 24 1 -∗ pcell b 32 (ptr_add q (Z.of_nat (S k0))) -∗
  int_cell b 40 ord -∗ int_cell b 44 fst -∗ int_cell b 48 lst -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
  ((∀ x (j' : Z), ⌜((sbyte sq (S k0) <> 0 /\ (i <= j' <= i + 1 \/ (j' = i + 2 /\ i + 1 < n))) \/
        (sbyte sq (S k0) = 0 /\ i + 1 < n /\ (i + 1 <= j' <= i + 2 \/ (j' = i + 3 /\ i + 2 < n))))%Z⌝ -∗
      GetoptState.getopt_session b r av ar ps j' -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ Φ (Ret (WInt x))) ∧
   (∀ e', ⌜keeps wos_keys e e' /\ sbyte sq (S k0) = 0 /\ (i + 1)%Z = n /\
        lookup (TAtom "v575") e' = Some (WInt (if sbyte so 0 =? 58 then 58 else 63))⌝ -∗
      live b r -∗ int_cell b 0 n -∗ int_cell b 8 c -∗ pcell b 16 a -∗ pcell b 32 (ptr_add q (Z.of_nat (S k0))) -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ int_cell b 4 er -∗ int_cell b 24 1 -∗ int_cell b 40 ord -∗
      int_cell b 44 fst -∗ int_cell b 48 lst -∗ flags_own F -∗ M -∗ longind_own li -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Exec (TAtom "L570") [] (b_jump getopt_blk570))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L508") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hrule Hse Hmid H0 H2 H12 H455 Hpo Hpe H6 H8 Hc0 Hc1 Hc2 Hc19 Hc20 H137 Hgp Hstr Hcut Hmal Hset Hlrule
    Hfree Hgn Hgl Hg Hgc H138 H139 H140 H141 Hlmid Hmid3 Hmid4 Hfl Hos Hq Hk0 Hsk Hi Hn Hlen Hc Hper
    Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser Hord Hfst Hlst.
  iIntros "#Ht #Hwq #Hpo #Hpfx #Hsl #Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl #Hs HG HF HM Hli HK".
  assert (Hlk : Z.of_nat (List.length (take k0 sq)) = Z.of_nat k0) by (rewrite length_take_le; lia).
  iAssert (word_string DfracDiscarded (ptr_add q (Z.of_nat k0)) (drop k0 sq)) as "#Hwc".
  { rewrite -Hlk. iApply word_string_suffix. by rewrite take_drop. }
  assert (Ht0 : sbyte (drop k0 sq) 0 = sbyte sq k0).
  { unfold sbyte. rewrite -drop_app_le; [|lia]. rewrite wos_nth_drop. by rewrite Nat.add_0_r. }
  assert (Ht1 : sbyte (drop k0 sq) 1 = sbyte sq (S k0)).
  { unfold sbyte. rewrite -drop_app_le; [|lia]. rewrite wos_nth_drop. by rewrite Nat.add_1_r. }
  assert (Hc1' : ptr_add (ptr_add q (Z.of_nat k0)) 1 = ptr_add q (Z.of_nat (S k0))) by (rewrite wos_ptr_add; f_equal; lia).
  rewrite -Hc1' -Ht1.
  iApply (GetoptWOpt.wp_getopt_wopt w0 registry ge wos_keys e e fr i n c pe (ptr_add q (Z.of_nat k0)) (drop k0 sq) po so a oo b r
    av ar ps G T fp dom se sereg mid with "Hwc Hpo Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl Hs HG [-]"); try wos_side.
  iSplit; [|iSplit].
  - iIntros (e' [Hk Hs1]) "Hl Hib Hoob Hab Hcur Ha Hcl HG". rewrite Hc1'.
    wos_conv b r i av ar ps (ptr_add q (Z.of_nat (S k0))). iDestruct "HK" as "[HK _]".
    assert (Hk1 : (S k0 <= List.length sq)%nat).
    { destruct (decide (S k0 < List.length sq)%nat); [lia|]. exfalso. apply Hs1. rewrite Ht1.
      unfold sbyte. rewrite app_nth2; [|lia]. by destruct (S k0 - List.length sq)%nat as [|[|]] eqn:?; cbn; try lia. }
    iApply (GetoptLongW.wp_getopt_w_session w0 registry ge e' G T fp dom M se sereg f138 f139 f140 f141 lmid mid3 mid4 av ar ps
      lo os F pfx pxs po so q sq (S k0) n pe i oo null b r li er ord fst lst
      with "Ht Hwq Hpo Hpfx Hsl Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl Hs HG HF HM Hli");
      try (wos_lk Hk; assumption); try wos_side.
    iIntros (x j' Hj') "Hss Ha Hcl HG HF HM Hli". iApply ("HK" $! x j' with "[%] Hss Ha Hcl HG HF HM Hli").
    left. split; [first [exact Hs1 | rewrite -Ht1; exact Hs1] | exact Hj'].
  - iIntros (e' (Hk & Hs1 & Hin)) "Hl Hib Hoob Hab Hcur Ha Hcl HG".
    destruct (lookup_lt_is_Some_2 ps (Z.to_nat (i + 1))) as [q2 Hq2]; [lia|].
    assert (Hn2 : nth (Z.to_nat (i + 1)) ps null = q2) by (by rewrite (nth_lookup_Some _ _ _ _ Hq2)).
    iDestruct (big_sepL_lookup with "Hs") as (s2) "#Hw2"; [exact Hq2|].
    rewrite Hn2. iAssert (pcell b 32 (ptr_add q2 (Z.of_nat 0))) with "[Hcur]" as "Hcur".
    { cbn [Z.of_nat]. rewrite wos_ptr_add_0. iExact "Hcur". }
    wos_conv b r (i + 1) av ar ps (ptr_add q2 (Z.of_nat 0)). iDestruct "HK" as "[HK _]".
    iApply (GetoptLongW.wp_getopt_w_session w0 registry ge e' G T fp dom M se sereg f138 f139 f140 f141 lmid mid3 mid4 av ar ps
      lo os F pfx pxs po so q2 s2 0 n pe (i + 1) oo null b r li er ord fst lst
      with "Ht Hw2 Hpo Hpfx Hsl Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl Hs HG HF HM Hli");
      try (wos_lk Hk; assumption); try wos_side.
    iIntros (x j' Hj') "Hss Ha Hcl HG HF HM Hli". iApply ("HK" $! x j' with "[%] Hss Ha Hcl HG HF HM Hli").
    right. split; [first [exact Hs1 | rewrite -Ht1; exact Hs1]|]. split; [exact Hin | lia].
  - iIntros (e' (Hk & Hs1 & Hin & H575)) "Hl Hib Hoob Hab Hcur Ha Hcl HG". rewrite Hc1'.
    wos_conv b r n av ar ps (ptr_add q (Z.of_nat (S k0))). iDestruct "HK" as "[_ HK]".
    iApply ("HK" $! e' with "[%] Hl Hib Hoob Hab Hcur Ha Hcl HG Her Hini Hor Hfi Hla HF HM Hli").
    split; [exact Hk|]. split; [first [exact Hs1 | rewrite -Ht1; exact Hs1]|]. split; [exact Hin | exact H575].
Qed.

End wos.
