From Glibc Require Import GlibcProgram.
(** glibc's getopt decides how to parse an argument that starts with a
    dash. A word with two dashes goes to the long-option parser, and in
    long-only mode a word with one dash may go there too; every other
    option is a cluster of short options. This file joins that choice
    with the call for a word with two dashes, so the caller of the
    choice receives either a session after that call or the state for
    one of the other two ways. *)

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
  GetoptLongAmbHead GetoptLongAmbPoss GetoptLongAmbRep GetoptLongPfxPath GetoptLongFind GetoptLongBody GetoptLongJoinMiss GetoptLongJoinFound GetoptLongJoin GetoptLongCall GetoptLongOnly GetoptDispatch GetoptLongSession GetoptLongDash.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDispatch GetoptExchange GetoptInitialize GetoptLongAmbTail GetoptLongBody GetoptLongCall GetoptLongDash GetoptLongDiag GetoptLongExact GetoptLongPfxAlloc GetoptLongStore GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


(** The dispatch module proves the choice between short and long options. *)
(** The two-dash module proves the call for a word with two dashes and restores the session. *)
Import GetoptLongDash GetoptLongCall GetoptLongBody GetoptLongAmbTail GetoptLongPfxAlloc GetoptLongStore GetoptLongDiag GetoptLongExact GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

(** The two-dash call and the short options read these names, which keep their values through the choice. *)
Definition choice_keys : list name := Eval vm_compute in
  List.map TAtom ["v0"; "v2"; "pr.1"; "v6"; "v8"; "v10"; "v12"; "pr.3"; "v80"; "chk2"; "chk20"]%string.

(** This tactic takes a parameter's value through the choice. *)
Ltac choice_lk Hk :=
  lazymatch goal with |- lookup ?k ?e' = _ =>
    rewrite (keeps_in choice_keys k _ e' Hk);
    [assumption | unfold choice_keys; cbn [In]; repeat first [left; reflexivity | right]] end.

(** This tactic proves a pure premise of the choice and leaves the proof-mode goal alone. *)
Ltac choice_side :=
  lazymatch goal with
  | |- environments.envs_entails _ _ => fail
  | |- avoids _ _ = true => vm_compute; reflexivity
  | _ => first [assumption | lia]
  end.

Import ProgramAbbreviations.
Section choice.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance choice_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The choice and the two-dash call describe the same cells through two copies of their modules, and this tactic converts between the copies. *)
Ltac choice_conv b r i av ar ps c :=
  iAssert (pcell b 32 c) with "[Hcur]" as "Hcur"; [iExact "Hcur"|];
  iAssert (live b r) with "[Hl]" as "Hl"; [iExact "Hl"|];
  iAssert (int_cell b 0 i) with "[Hib]" as "Hib"; [iExact "Hib"|];
  iAssert (live av ar) with "[Ha]" as "Ha"; [iExact "Ha"|];
  iAssert (argv_cells av ps) with "[Hcl]" as "Hcl"; [iExact "Hcl"|].

(** The caller of the choice needs to know where each kind of word
    leads. Here the word q at index i starts with a dash and has a
    second character. A word with two dashes goes through the
    long-option parser, and the caller gets the answer with a session
    at the new index. A cluster of short options, or a word for the
    long-only call, comes back to the caller with the cursor one byte
    in. The caller then also gets back the resources that the parser
    would have used. *)
Lemma wp_getopt_long_choice e (G : iProp Σ) T fp dom (M : iProp Σ) se sereg
    f138 f139 f140 f141 mid mid3 mid4 av ar ps lo os F pfx pxs po so q sq n lonly pe i oo a b r li er ord fst lst c Φ :
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) -> lookup (TAtom "v10") e = Some (WInt lonly) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some pfx ->
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
  ps !! Z.to_nat i = Some q -> sbyte sq 0 = 45 -> sbyte sq 1 <> 0 ->
  0 <= i < n -> n < 2 ^ 31 - 1 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (n + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  0 <= ord <= 2 -> 0 <= fst <= lst -> lst <= i ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk100") e = Some (WPtr (mkPtr b (Obj b))) ->
  opt_table lo os -∗ word_string DfracDiscarded q sq -∗ word_string DfracDiscarded po so -∗
  word_string DfracDiscarded pfx pxs -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 i -∗ int_cell b 4 er -∗ int_cell b 8 oo -∗ pcell b 16 a -∗ int_cell b 24 1 -∗
  pcell b 32 c -∗ int_cell b 40 ord -∗ int_cell b 44 fst -∗ int_cell b 48 lst -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
  ((∀ e', ⌜keeps choice_keys e e'⌝ -∗
      live b r -∗ int_cell b 0 i -∗ pcell b 32 (ptr_add q 1) -∗ live av ar -∗ argv_cells av ps -∗
      int_cell b 4 er -∗ int_cell b 8 oo -∗ pcell b 16 a -∗ int_cell b 24 1 -∗ int_cell b 40 ord -∗
      int_cell b 44 fst -∗ int_cell b 48 lst -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L75") (Some (TAtom "L338")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps choice_keys e e' /\ lonly mod 2 ^ 32 <> 0 /\ sbyte sq 1 <> 45⌝ -∗
      live b r -∗ int_cell b 0 i -∗ pcell b 32 (ptr_add q 1) -∗ live av ar -∗ argv_cells av ps -∗
      int_cell b 4 er -∗ int_cell b 8 oo -∗ pcell b 16 a -∗ int_cell b 24 1 -∗ int_cell b 40 ord -∗
      int_cell b 44 fst -∗ int_cell b 48 lst -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Exec (TAtom "L376") long_only_call long_only_jump))
            : gexpr) {{ Φ }}) ∧
   (∀ x i', ⌜(i <= i' <= i + 1 \/ (i' = i + 2 /\ i + 1 < n))%Z⌝ -∗ GetoptState.getopt_session b r av ar ps i' -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ Φ (Ret (WInt x)))) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L291") (Some (TAtom "L303")))) : gexpr)
    {{ Φ }}.
Proof.
  intros Hgp H0 H2 H1 H6 H8 H10 H12 H3 Hstr Hcut Hmal Hset Hrule Hfree Hgn Hgl Hg Hgc Hse H138 H139 H140 H141 Hmid Hmid3
    Hmid4 Hfl Hos Hpe Hlo Hq Hq0 Hq1 Hi Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser Hord Hfst Hlst
    Hc2 Hc20 Hc100.
  iIntros "#Ht #Hwq #Hpo #Hpfx #Hsl #Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl #Hs HG HF HM Hli HK".
  assert (Hnq : nth (Z.to_nat i) ps null = q) by (by rewrite (nth_lookup_Some _ _ _ _ Hq)).
  iAssert (word_string DfracDiscarded (nth (Z.to_nat i) ps null) sq) as "#Hwn"; [by rewrite Hnq|].
  iApply (GetoptDispatch.wp_getopt_choice choice_keys e i n c lo lonly po so b r av ar ps sq
    with "Hwn Hpo Hl Hib Hcur Ha Hcl Hs [-]");
    try choice_side.
  iSplit; [|iSplit].
  - iIntros (e' Hk) "Hl Hib Hcur Ha Hcl". rewrite Hnq.
    choice_conv b r i av ar ps (ptr_add q 1). iDestruct "HK" as "[HK _]".
    iApply ("HK" $! e' with "[%] Hl Hib Hcur Ha Hcl Her Hoob Hab Hini Hor Hfi Hla HG HF HM Hli"). exact Hk.
  - iIntros (e' (Hk & H45)) "Hl Hib Hcur Ha Hcl". rewrite Hnq.
    choice_conv b r i av ar ps (ptr_add q 2). iDestruct "HK" as "[_ [_ HK]]".
    iApply (GetoptLongDash.wp_getopt_dash_session e' G T fp dom M se sereg f138 f139 f140 f141 mid mid3 mid4 av ar ps
      lo os F pfx pxs po so q sq n lonly pe i oo a b r li er ord fst lst
      with "Ht Hwq Hpo Hpfx Hsl Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl Hs HG HF HM Hli HK");
      first [choice_lk Hk | assumption].
  - iIntros (e' Hk) "Hl Hib Hcur Ha Hcl". rewrite Hnq.
    choice_conv b r i av ar ps (ptr_add q 1). iDestruct "HK" as "[_ [HK _]]".
    iApply ("HK" $! e' with "[%] Hl Hib Hcur Ha Hcl Her Hoob Hab Hini Hor Hfi Hla HG HF HM Hli"). exact Hk.
Qed.

End choice.
