From Glibc Require Import GlibcProgram.
(** "-W foo" or "-Wfoo" stands for "--foo" when the option string holds
    "W;". glibc's scanner stores the word after the W as its private
    cursor and then calls the long-option parser with long-only mode
    off and returns the parser's answer. The next call of getopt relies
    on the private object that this call leaves behind. This file joins
    the call with the restoration of the session, so the caller receives
    the answer together with a session at the new index. *)

From Glibc Require Import GlibcTactics LibioTactics.
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
  GetoptLongAmbHead GetoptLongAmbPoss GetoptLongAmbRep GetoptLongPfxPath GetoptLongFind GetoptLongBody GetoptLongJoinMiss GetoptLongJoinFound GetoptLongJoin GetoptLongCall GetoptLongOnly GetoptDispatch GetoptLongSession GetoptWTail.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptExchange GetoptInitialize GetoptLongAmbTail GetoptLongBody GetoptLongCall GetoptLongDiag GetoptLongExact GetoptLongJoinMiss GetoptLongPfxAlloc GetoptLongSession GetoptLongStore GetoptState LibioLogic OsWorld StrlenLoop.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** A lookup in a list finds the same element as [nth_error]. *)
Lemma w_nth_error (l : list ptr) k x : l !! k = Some x -> nth_error l k = Some x.
Proof. revert k. induction l as [|y l IH]; intros [|k] H; cbn in *; try discriminate; auto. Qed.

(** The W option passes the word at index j with the cursor k bytes
    into it, and these controls show the three shapes that the session
    lemma below must accept. After "-W" the next word may be empty, and
    the cursor then sits at its terminator. *)
Lemma w_ctl_empty : (0 <= List.length ([] : list Z))%nat /\ drop 0 ([] : list Z) = [].
Proof. split; [lia | reflexivity]. Qed.

(** In "-Wfoo" the cursor sits two bytes in, so the long option is "foo". *)
Lemma w_ctl_cluster : (2 <= List.length [45; 87; 102; 111; 111])%nat /\
  take 2 [45; 87; 102; 111; 111] = [45; 87] /\ drop 2 [45; 87; 102; 111; 111] = [102; 111; 111].
Proof. cbn. repeat split; lia || reflexivity. Qed.

(** A cursor past the terminator of "-Wfoo" fails the bound on k. *)
Lemma w_ctl_past : ~ (6 <= List.length [45; 87; 102; 111; 111])%nat.
Proof. cbn. lia. Qed.


(** The call module supplies the rule for a call of the parser. *)
(** The session module restores the session after a return. *)
Import GetoptLongCall GetoptLongSession GetoptLongBody GetoptLongAmbTail GetoptLongPfxAlloc GetoptLongStore GetoptLongDiag GetoptLongExact GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

(** This tactic evaluates arguments through assignments and drops their wraps to 32 bits. *)
Ltac w_vx :=
  cbn -[put];
  repeat match goal with
    |- context [lookup ?k ?E] =>
      let H := fresh "Hlk" in assert (H : lookup k E = _) by lk_prove; rewrite H; clear H
    end;
  StrlenLoop.unwrap; reflexivity.

(** A call needs facts about its arguments, such as their values and ranges, and this tactic proves them. *)
Ltac w_side :=
  lazymatch goal with
  | |- environments.envs_entails _ _ => fail
  | _ => first [assumption | lia | vx | w_vx]
  end.

Import ProgramAbbreviations.
Section wsite.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance w_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The W option reaches the call with the cursor cur in the word q at
    index i. getopt returns the parser's answer x, and the caller
    receives x with the parser's return state. Long-only mode is off,
    so the parser never reads the first byte of q, and q may be empty. *)
Lemma wp_getopt_long_w e (G : iProp Σ) T fp dom (M : iProp Σ) se sereg
    f138 f139 f140 f141 mid mid3 mid4 av ar ps lo os F pfx pxs po so q sq cur s n pe i oo a b r li Φ :
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some mid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) os -> (List.length os < 2 ^ 31)%Z ->
  0 <= pe < 2 ^ 32 -> ps !! Z.to_nat i = Some q ->
  0 <= i < n -> n < 2 ^ 31 - 1 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo os -∗ word_string DfracDiscarded q sq -∗ word_string DfracDiscarded po so -∗
  word_string DfracDiscarded pfx pxs -∗ word_string DfracDiscarded cur s -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo -∗ pcell b 16 a -∗ pcell b 32 cur -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
  (∀ x, GetoptLongJoinMiss.plo_res b r av ar ps li F G M i n cur s a os x -∗ Φ (Ret (WInt x))) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Exec (TAtom "L533") w_call w_jump)) : gexpr) {{ Φ }}.
Proof.
  intros Hgp H0 H2 H1 H6 H8 H12 H3 Hstr Hcut Hmal Hset Hrule Hfree Hgn Hgl Hg Hgc Hse H138 H139 H140 H141 Hmid Hmid3
    Hmid4 Hfl Hos Hpe Hq Hi Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser.
  iIntros "#Ht #Hwq #Hpo #Hpfx #Hws #Hsl #Hsc Hl Hib Hoob Hab Hcur Ha Hcl #Hs HG HF HM Hli HK".
  unfold w_call, w_jump. step.
  iApply (GetoptLongCall.wp_call_glibc_process_long_option _ _ _ _ _ _ _ _ _ G T fp dom M se sereg f138 f139 f140
    f141 mid mid3 mid4 av ar ps lo os F pfx pxs po so q sq cur s n 0 pe i oo a b r li
    with "Ht Hwq Hpo Hpfx Hws Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl Hs HG HF HM Hli");
    try w_side.
  iNext. iIntros (x) "Hres". iExists _. iSplit; [done|]. iNext.
  iDestruct "Hres" as (i' oo' a' c') "(Hl & Hib & Hoob & Hab & Hcur & Ha & Hcl & HG & HF & HM & Hli & %Hp)".
  destruct Hp as (Hi' & Hc' & Ha' & Hxr & Hxf).
  iApply (wp_ret registry (os_wi w0) ge _ _ _ _ _ (WInt x)); [reflexivity | w_vx |]. iNext.
  iApply "HK". iApply (GetoptLongJoinMiss.plo_res_intro with "Hl Hib Hoob Hab Hcur Ha Hcl HG HF HM Hli"); assumption.
Qed.

(** A caller of getopt needs the next call to be safe as well, so the
    call for the W option must leave a session behind. The W option
    passes the word q at index j with the cursor k bytes into it: the
    rest of the cluster when the cluster goes on, or the whole next
    word, which may be empty. The other private fields keep the values
    they had, and the nonoption interval ends at or before j. getopt
    returns the parser's answer, and the caller receives it with a
    session at the new index and everything else it lent the parser. *)
Lemma wp_getopt_w_session e (G : iProp Σ) T fp dom (M : iProp Σ) se sereg
    f138 f139 f140 f141 mid mid3 mid4 av ar ps lo os F pfx pxs po so q sq k n pe j oo a b r li er ord fst lst Φ :
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some mid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) os -> (List.length os < 2 ^ 31)%Z ->
  0 <= pe < 2 ^ 32 -> ps !! Z.to_nat j = Some q -> (k <= List.length sq)%nat ->
  0 <= j < n -> n < 2 ^ 31 - 1 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (n + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  0 <= ord <= 2 -> 0 <= fst <= lst -> lst <= j ->
  opt_table lo os -∗ word_string DfracDiscarded q sq -∗ word_string DfracDiscarded po so -∗
  word_string DfracDiscarded pfx pxs -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 j -∗ int_cell b 4 er -∗ int_cell b 8 oo -∗ pcell b 16 a -∗ int_cell b 24 1 -∗
  pcell b 32 (ptr_add q (Z.of_nat k)) -∗ int_cell b 40 ord -∗ int_cell b 44 fst -∗ int_cell b 48 lst -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
  (∀ x j', ⌜(j <= j' <= j + 1 \/ (j' = j + 2 /\ j + 1 < n))%Z⌝ -∗ GetoptState.getopt_session b r av ar ps j' -∗
     live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ Φ (Ret (WInt x))) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Exec (TAtom "L533") w_call w_jump)) : gexpr) {{ Φ }}.
Proof.
  intros Hgp H0 H2 H1 H6 H8 H12 H3 Hstr Hcut Hmal Hset Hrule Hfree Hgn Hgl Hg Hgc Hse H138 H139 H140 H141 Hmid Hmid3
    Hmid4 Hfl Hos Hpe Hq Hk Hi Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser Hord Hfst Hlst.
  iIntros "#Ht #Hwq #Hpo #Hpfx #Hsl #Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl #Hs HG HF HM Hli HK".
  assert (Hlk : Z.of_nat (List.length (take k sq)) = Z.of_nat k) by (rewrite length_take_le; lia).
  iAssert (word_string DfracDiscarded (ptr_add q (Z.of_nat k)) (drop k sq)) as "#Hws".
  { rewrite -Hlk. iApply word_string_suffix. by rewrite take_drop. }
  iApply (wp_getopt_long_w e G T fp dom M se sereg f138 f139 f140 f141 mid mid3 mid4 av ar ps lo
    os F pfx pxs po so q sq (ptr_add q (Z.of_nat k)) (drop k sq) n pe j oo a b r li
    with "Ht Hwq Hpo Hpfx Hws Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl Hs HG HF HM Hli"); try (assumption || lia).
  iIntros (x) "Hres".
  iDestruct "Hres" as (j' oo' a' c') "(Hl & Hib & Hoob & Hab & Hcur & Ha & Hcl & HG & HF & HM & Hli & %Hp)".
  destruct Hp as (Hj' & Hc' & _ & _ & _).
  iApply ("HK" $! x j' with "[%] [-Ha Hcl HG HF HM Hli] Ha Hcl HG HF HM Hli"); [exact Hj'|].
  set (s0 := mkGetoptState j er oo a 1 (ptr_add q (Z.of_nat k)) ord fst lst).
  iApply (GetoptLongSession.long_session b r av ar ps s0 j' oo' a' c' (drop k sq)
    with "[] Hws Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla");
    try (unfold getopt_bounds; cbn; lia); try (cbn; lia); try reflexivity; try exact Hc'.
  unfold GetoptState.getopt_cursor. unfold s0. cbn [gs_next gs_last gs_ind]. destruct (drop k sq) as [|t0 t] eqn:Ht0.
  - iRight. iLeft. iExact "Hws".
  - iRight. iRight. iExists q, (take k sq), (drop k sq). iSplit; [iPureIntro|].
    + rewrite Ht0. split; [lia|]. split; [by apply w_nth_error|]. split; [discriminate|].
      split; [by rewrite Hlk|lia].
    + by rewrite take_drop.
Qed.

End wsite.
