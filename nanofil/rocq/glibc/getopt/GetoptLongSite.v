From Glibc Require Import GlibcProgram.
(** In long-only mode glibc's getopt also hands a word with one dash
    to its long-option parser. When the parser answers -1, getopt treats
    the word as a cluster of short options instead. This file proves
    that call safe, and it states the condition on the option table
    that makes the fallback safe. *)

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
  GetoptLongAmbHead GetoptLongAmbPoss GetoptLongAmbRep GetoptLongPfxPath GetoptLongFind GetoptLongBody GetoptLongJoinMiss GetoptLongJoinFound GetoptLongJoin GetoptLongCall GetoptLongOnly GetoptDispatch.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptExchange GetoptInitialize GetoptLongAmbTail GetoptLongBody GetoptLongCall GetoptLongDiag GetoptLongExact GetoptLongJoinMiss GetoptLongPfxAlloc GetoptLongStore GetoptState LibioLogic OsWorld StrlenLoop.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** ## The table condition for long-only mode

    In long-only mode getopt reads the answer -1 as "this word was not a
    long option" and parses the word again as short options. An entry
    without a flag whose value is -1 also answers -1, but only after the
    parser has consumed the word and cleared the cursor. getopt would
    then build a cursor from the next word, which may be the null
    sentinel or an empty word. The condition below rules such entries
    out. *)

(** No entry of the table answers -1 through its value. *)
Definition no_neg1_val (os : list lopt) : Prop :=
  Forall (fun y => lo_flag y <> null \/ (lo_val y mod 2 ^ 32 <> 4294967295)%Z) os.

(** The parser's return state carries this fact about the answer -1. *)
Definition neg1_fact (os : list lopt) (x i i' : Z) (cur c' : ptr) : Prop :=
  x = 4294967295 -> (c' = cur /\ i' = i) \/
    exists y, y ∈ os /\ lo_flag y = null /\ (lo_val y mod 2 ^ 32 = 4294967295)%Z.

(** Under the table condition, the answer -1 leaves the cursor and the index where they were. *)
Lemma neg1_fallback os x i i' cur c' :
  no_neg1_val os -> neg1_fact os x i i' cur c' -> x = 4294967295 -> c' = cur /\ i' = i.
Proof.
  intros Hos Hf Hx. destruct (Hf Hx) as [H | (y & Hy & Hfl & Hv)]; [exact H|].
  unfold no_neg1_val in Hos. rewrite Forall_forall in Hos. destruct (Hos y Hy); contradiction.
Qed.

(** These controls show that the fact separates the three kinds of
    answer. The cursor at address 100 stands for any nonnull cursor. *)
Definition ctl_cur : ptr := mkPtr 100 (Obj 64).

(** An answer of -1 that leaves the word unconsumed satisfies the fact for every table. *)
Lemma neg1_ctl_fallback os i : neg1_fact os 4294967295 i i ctl_cur ctl_cur.
Proof. intros _. left. split; reflexivity. Qed.

(** An entry without a flag and with the value -1 lets a consumed word
    answer -1, and that table fails the condition. *)
Lemma neg1_ctl_consumed i :
  neg1_fact [mkLopt null [] 0 null 4294967295] 4294967295 i (i + 1) ctl_cur null /\
  ~ no_neg1_val [mkLopt null [] 0 null 4294967295].
Proof.
  split.
  - intros _. right. eexists. split; [left|]. split; reflexivity.
  - intros H. inversion H as [|? ? [Hf | Hv]]; subst; [apply Hf; reflexivity | apply Hv; reflexivity].
Qed.

(** Under the condition, a consumed word cannot answer -1, while an
    ordinary value such as 'h' satisfies the fact trivially. *)
Lemma neg1_ctl_ordinary os i :
  no_neg1_val os -> ~ neg1_fact os 4294967295 i (i + 1) ctl_cur null /\ neg1_fact os 104 i (i + 1) ctl_cur null.
Proof.
  intros Hos. split.
  - intros Hf. destruct (neg1_fallback _ _ _ _ _ _ Hos Hf eq_refl) as [Hc _]. discriminate Hc.
  - intros Hx. discriminate Hx.
Qed.


(** The call module supplies the rule for a call of the parser. *)
Import GetoptLongCall GetoptLongBody GetoptLongAmbTail GetoptLongPfxAlloc GetoptLongStore GetoptLongDiag GetoptLongExact GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

(** This tactic evaluates arguments through assignments and drops their wraps to 32 bits. *)
Ltac site_vx :=
  cbn -[put];
  repeat match goal with
    |- context [lookup ?k ?E] =>
      let H := fresh "Hlk" in assert (H : lookup k E = _) by lk_prove; rewrite H; clear H
    end;
  StrlenLoop.unwrap; reflexivity.

(** A call needs facts about its arguments, such as their values and ranges, and this tactic proves them. *)
Ltac site_side :=
  lazymatch goal with
  | |- environments.envs_entails _ _ => fail
  | _ => first [assumption | lia | vx | site_vx]
  end.

Import ProgramAbbreviations.
Section site.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance site_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** In long-only mode a word at index i with one dash reaches the call
    with the cursor cur past the dash. An answer other than -1 is
    getopt's answer. Under the table condition, the answer -1 leaves
    the index and the cursor where they were, and getopt goes on to the
    short options with the parser's resources. *)
Lemma wp_getopt_long_only_call e (G : iProp Σ) T fp dom (M : iProp Σ) se sereg
    f138 f139 f140 f141 mid mid3 mid4 av ar ps lo os F pfx pxs po so q sq cur s n lonly pe i oo a b r li Φ :
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) -> lookup (TAtom "v10") e = Some (WInt lonly) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "glibc_getopt#str.147") (ge_globals ge) = Some pfx -> no_neg1_val os ->
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
  0 <= pe < 2 ^ 32 -> 0 <= lonly < 2 ^ 32 ->
  ps !! Z.to_nat i = Some q -> sbyte sq 0 <> 0 ->
  0 <= i < n -> n < 2 ^ 31 - 1 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo os -∗ word_string DfracDiscarded q sq -∗ word_string DfracDiscarded po so -∗
  word_string DfracDiscarded pfx pxs -∗ word_string DfracDiscarded cur s -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo -∗ pcell b 16 a -∗ pcell b 32 cur -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
  ((∀ x, ⌜x <> 4294967295⌝ -∗ GetoptLongJoinMiss.plo_res b r av ar ps li F G M i n cur s a os x -∗ Φ (Ret (WInt x))) ∧
   (∀ e' oo' a', ⌜lookup (TAtom "v2") e' = Some (WPtr (mkPtr av (Obj av))) /\
       lookup (TAtom "v12") e' = Some (WPtr (mkPtr b (Obj b))) /\ lookup (TAtom "chk2") e' = lookup (TAtom "chk2") e /\
       lookup (TAtom "chk20") e' = lookup (TAtom "chk20") e /\
       lookup (TAtom "pr.1") e' = lookup (TAtom "pr.1") e /\ lookup (TAtom "v80") e' = lookup (TAtom "v80") e⌝ -∗
     live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 cur -∗
     live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L338") (Some (TAtom "L376")))) : gexpr)
       {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Exec (TAtom "L376") long_only_call long_only_jump)) : gexpr)
    {{ Φ }}.
Proof.
  intros Hgp H0 H2 H1 H6 H8 H10 H12 H3 Hstr Hneg Hcut Hmal Hset Hrule Hfree Hgn Hgl Hg Hgc Hse H138 H139 H140 H141 Hmid Hmid3
    Hmid4 Hfl Hos Hpe Hlo Hq Hq0 Hi Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser.
  iIntros "#Ht #Hwq #Hpo #Hpfx #Hws #Hsl #Hsc Hl Hib Hoob Hab Hcur Ha Hcl #Hs HG HF HM Hli HK".
  unfold long_only_call, long_only_jump. step.
  iApply (GetoptLongCall.wp_call_glibc_process_long_option _ _ _ _ _ _ _ _ _ G T fp dom M se sereg f138 f139 f140 f141 mid mid3 mid4 av ar ps lo os F pfx pxs po so q sq cur s n lonly pe i oo a b r li with "Ht Hwq Hpo Hpfx Hws Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl Hs HG HF HM Hli");
    try site_side.
  iNext. iIntros (x) "Hres". iExists _. iSplit; [done|]. iNext.
  iDestruct "Hres" as (i' oo' a' c') "(Hl & Hib & Hoob & Hab & Hcur & Ha & Hcl & HG & HF & HM & Hli & %Hp)".
  destruct Hp as (Hi' & Hc' & Ha' & Hxr & Hxf). cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  step. iApply wp_branch; [vx | iNext]. StrlenLoop.unwrap.
  destruct (Z.eqb_spec x 4294967295) as [Ex | Ex]; cbn [negb];
    lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
      let c' := eval vm_compute in c in change c with c' end; cbn [edge_label].
  - destruct (neg1_fallback os x i i' cur c' Hneg Hxf Ex) as [-> ->]. iDestruct "HK" as "[_ HK]".
    iApply ("HK" with "[%] Hl Hib Hoob Hab Hcur Ha Hcl HG HF HM Hli").
    repeat split; repeat (eapply lookup_put_miss; [vm_compute; reflexivity|]); first [eassumption | reflexivity].
  - iDestruct "HK" as "[HK _]". step. iApply (wp_ret registry (os_wi w0) ge _ _ _ _ _ (WInt x)); [reflexivity | site_vx |]. iNext.
    iApply ("HK" with "[%]"); [exact Ex|].
    iApply (GetoptLongJoinMiss.plo_res_intro with "Hl Hib Hoob Hab Hcur Ha Hcl HG HF HM Hli"); assumption.
Qed.

End site.
