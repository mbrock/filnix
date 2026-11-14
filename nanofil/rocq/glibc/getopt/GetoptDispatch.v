(** An argument that starts with a dash and has a second character is
    an option. glibc's scanner first decides how to parse it. With a long
    option table, an argument that starts with two dashes is a long
    option. In long-only mode, an argument with a single dash is also
    tried as a long option, unless it is a single character that the
    short option string names. Every other option is a cluster of short
    options. Each choice stores the private cursor, which points into the
    argument just after its dashes. This file proves the choice safe. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrchrCode StrchrnulLogic GetoptModule GetoptState GetoptBytes
  GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor GetoptLongOnly.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptCursor GetoptExchange GetoptInitialize GetoptLongOnly GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The choice assigns these names before the long-only test. *)
Definition choice_names : list name :=
  List.map TAtom ["v340"; "v341"; "v347"; "v348"; "v349"; "v350"; "chk117"; "v351"; "v352"; "chk118"; "v353";
    "v354"; "v356"; "v359"; "v360"; "v361"; "v362"; "chk120"; "v363"; "v364"; "chk121"]%string
  ++ short_names ++ long_only_names.

(** A long option starting with two dashes calls the long-option parser here. *)
Definition long_call : list inst := Eval vm_compute in skipn 10 (b_insts (x_blk "L342")).
(** The jump after that call returns its result. *)
Definition long_jump : jump := Eval vm_compute in b_jump (x_blk "L342").


(** The long-only module proves the long-only test and both cursor stores. *)
Import GetoptLongOnly GetoptCursor GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

(** This tactic enters a block and evaluates its phi assignments. *)


(** This tactic loads an owned private integer field as a signed 32-bit value. *)


Section dispatch.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance dispatch_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance dispatch_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** This tactic checks and loads byte k, which lies inside the shared string s at q, as a signed byte. *)
Ltac rdin q s k :=
  let bb := fresh "bb" in let breg := fresh "breg" in let Hbb := fresh "Hbb" in
  let Hcap := fresh "Hcap" in
  iDestruct (ws_byte q s k with "Hws") as (bb breg) "(%Hbb & #Hbl & #Hbt)"; [lia|];
  destruct Hbb as (Hcap & ? & ? & ? & ?);
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hbl");
    [reflexivity | vx | exact Hcap | arith | cbn [ptr_addr]; unfold raw_address; rewrite Z.mod_small; lia | arith |];
  iNext; iIntros "_";
  iApply (wp_raw_load_sub_bytes_dq with "Hbl Hbt");
    [reflexivity | vx | reflexivity | apply extended_chr | exact Hcap | arith |];
  iNext; iIntros "_ _"; iClear "Hbl Hbt".

(** The choice runs when argument i, below the argument count n, is an
    option. That argument is a shared string s that starts with a dash
    and has a second character. The caller supplies the short option
    string po and the facts that the linked names __GI_strchr and
    __GI___strchrnul are glibc's functions. A cluster of short options
    reaches the cluster loop with the cursor one byte into the argument.
    With a long option table lo, two dashes reach the long-option parser
    with the cursor two bytes in. In long-only mode, a single dash may
    also reach that parser, with the cursor one byte in. *)
Lemma wp_getopt_choice ks e i n c lo lonly po so b r av ar ps s Φ :
  avoids ks choice_names = true ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v10") e = Some (WInt lonly) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk100") e = Some (WPtr (mkPtr b (Obj b))) ->
  0 <= i < n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  sbyte s 0 = 45 -> sbyte s 1 <> 0 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  word_string DfracDiscarded (nth (Z.to_nat i) ps null) s -∗ word_string DfracDiscarded po so -∗
  live b r -∗ int_cell b 0 i -∗ pcell b 32 c -∗ live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  ((∀ e', ⌜keeps ks e e'⌝ -∗
      live b r -∗ int_cell b 0 i -∗ pcell b 32 (ptr_add (nth (Z.to_nat i) ps null) 1) -∗
      live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L75") (Some (TAtom "L338")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ sbyte s 1 = 45⌝ -∗
      live b r -∗ int_cell b 0 i -∗ pcell b 32 (ptr_add (nth (Z.to_nat i) ps null) 2) -∗
      live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Exec (TAtom "L342") long_call long_jump)) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ lonly mod 2 ^ 32 <> 0 /\ sbyte s 1 <> 45⌝ -∗
      live b r -∗ int_cell b 0 i -∗ pcell b 32 (ptr_add (nth (Z.to_nat i) ps null) 1) -∗
      live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Exec (TAtom "L376") long_only_call long_only_jump))
            : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L291") (Some (TAtom "L303")))) : gexpr)
    {{ Φ }}.
Proof.
  intros Hks Hg Hgn Hv2 Hv6 Hv10 Hv12 Hpo Hc2 Hc20 Hc100 Hi Hn Hlen Hs0 Hs1 Hb Hal Hend Hr Hav Hala Hda Hra.
  iIntros "#Hws #Hpo Hl [%Hi0 Hib] Hcur Ha Hc #Hs HK".
  pose proof (avoids_app _ _ _ Hks) as [_ Hks']. apply avoids_app in Hks' as [Hksh Hklo].
  set (j := Z.to_nat i). assert (Hj : Z.of_nat j = i) by (unfold j; lia).
  destruct (lookup_lt_is_Some_2 ps j) as [q Hq]; [lia|].
  assert (Hnq : nth j ps null = q) by (by rewrite (nth_lookup_Some _ _ _ _ Hq)).
  fold j. rewrite Hnq.
  iDestruct (argv_str_cap with "Hws") as (rq) "[#Hcapq %Hq0]".
  iDestruct (ws_shape with "Hws") as %(Hch & Hqp & Hqe).
  pose proof (sbyte_in_len s 1 Hs1) as Hl1.
  iAssert ((∀ e2 fr, ⌜keeps ks e e2 /\ lookup (TAtom "v2") e2 = Some (WPtr (mkPtr av (Obj av))) /\
      lookup (TAtom "v12") e2 = Some (WPtr (mkPtr b (Obj b))) /\
      lookup (TAtom "chk2") e2 = Some (WPtr (mkPtr b (Obj b))) /\
      lookup (TAtom "chk20") e2 = Some (WPtr (mkPtr (b + 32) (Obj b)))⌝ -∗
    live b r -∗ int_cell b 0 i -∗ pcell b 32 c -∗ live av ar -∗ argv_cells av ps -∗
    WP (ERun (mkFrame glibc_getopt_internal_r e2 [] None (Enter (TAtom "L338") (Some fr))) : gexpr) {{ Φ }}) ∧
    ((∀ e', ⌜keeps ks e e' /\ sbyte s 1 = 45⌝ -∗
      live b r -∗ int_cell b 0 i -∗ pcell b 32 (ptr_add q 2) -∗ live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Exec (TAtom "L342") long_call long_jump)) : gexpr)
        {{ Φ }}) ∧
     (∀ e', ⌜keeps ks e e' /\ lonly mod 2 ^ 32 <> 0 /\ sbyte s 1 <> 45⌝ -∗
      live b r -∗ int_cell b 0 i -∗ pcell b 32 (ptr_add q 1) -∗ live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Exec (TAtom "L376") long_only_call long_only_jump))
            : gexpr) {{ Φ }})))%I
    with "[HK]" as "HL".
  { iSplit; [|iDestruct "HK" as "(_ & HK)"; iExact "HK"].
    iIntros (e2 fr (Hk & H2 & H12 & H2' & H20)) "Hl Hi Hcur Ha Hc".
    iApply (wp_getopt_short_cursor w0 registry ge ks e2 fr i n c b r av ar ps with "Hl Hi Hcur Ha Hc Hs [HK]");
      [ exact Hksh | exact H2 | exact H12 | exact H2' | exact H20 | lia | lia | exact Hlen
      | lia | lia | lia | lia | lia | lia | lia | lia |].
    iIntros (e' Hk') "Hl Hi Hcur Ha Hc". iDestruct "HK" as "[HK _]". fold j. rewrite Hnq.
    iApply ("HK" with "[%] Hl Hi Hcur Ha Hc"). eapply keeps_trans; [exact Hk | exact Hk']. }
  step. step. step. destruct (ptr_addr lo mod 2 ^ 64 =? 0 mod 2 ^ 64);
    iApply wp_branch; [vx | iNext | vx | iNext]; close_br.
  1:{ iDestruct "HL" as "[HL338 _]". iApply ("HL338" with "[%] Hl [Hib] Hcur Ha Hc"); [split; [xkeep|]; repeat split; lk_prove | by iSplit]. }
  step. load_s32_using ltac:(arith) "Hl Hib". step. step. step. idx i. check "Ha".
  iDestruct (big_sepL_lookup_acc with "Hc") as "[Hcj Hc]"; [exact Hq|].
  iApply (wp_raw_load_pointer_dq with "Ha Hcj Hcapq"); [reflexivity | vx | left; reflexivity | arith | arith | lia |].
  iNext. iIntros "Ha Hcj _". iSpecialize ("Hc" with "Hcj"). step. norm.
  rdin q s 1%nat. step.
  pose proof (sbyte_range s 1 Hch) as Hs1r. rewrite chr_cmp; [|lia|lia].
  iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec (sbyte s 1) 45) as [E45 | E45]; close_br.
  - step. step. load_s32_using ltac:(arith) "Hl Hib". step. step. step. idx i. check "Ha".
    iDestruct (big_sepL_lookup_acc with "Hc") as "[Hcj Hc]"; [exact Hq|].
    iApply (wp_raw_load_pointer_dq with "Ha Hcj Hcapq");
      [reflexivity | vx | left; reflexivity | arith | arith | lia |].
    iNext. iIntros "Ha Hcj _". iSpecialize ("Hc" with "Hcj"). step. check "Hl".
    iApply (wp_raw_store_pointer with "Hl Hcur"); [vx | vx | reflexivity | arith | arith | wi_store |].
    iNext. iIntros "Hl Hcur".
    assert (Ha2 : (ptr_addr q mod 2 ^ 64 + 2 mod 2 ^ 64) mod 2 ^ 64 = ptr_addr q + 2)
      by (rewrite !(Z.mod_small _ (2 ^ 64)); lia).
    rewrite Ha2. iDestruct "HL" as "(_ & HK & _)".
    iApply ("HK" with "[%] Hl [Hib] Hcur Ha Hc"); [split; [xkeep | exact E45] | by iSplit].
  - iApply (wp_getopt_long_only w0 registry ge (ks ++ List.map TAtom ["v2"; "v12"; "chk2"; "chk20"]%string) _ i n c lonly po so b r av ar ps s
              with "[Hws] Hpo Hl [Hib] Hcur Ha Hc Hs [HL]");
      [ unfold avoids; rewrite forallb_app; apply andb_true_intro; split; [exact Hklo | vm_compute; reflexivity] | exact Hg | exact Hgn | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove
      | lk_prove | lia | lia | exact Hlen | exact Hs0 | exact Hs1 | exact E45
      | lia | lia | lia | lia | lia | lia | lia | lia | fold j; by rewrite Hnq | by iSplit |].
    iSplit.
    + iIntros (e' fr Hk') "Hl Hi Hcur Ha Hc". iDestruct "HL" as "[HL338 _]".
      apply keeps_app in Hk' as [Hk' Hk2].
      iApply ("HL338" with "[%] Hl Hi Hcur Ha Hc"). split; [eapply keeps_trans; [|exact Hk']; xkeep|].
      repeat split; (rewrite (keeps_in _ _ _ _ Hk2); [lk_prove | cbn; tauto]).
    + iIntros (e' (Hk' & El)) "Hl Hi Hcur Ha Hc". iDestruct "HL" as "(_ & _ & HK)".
      apply keeps_app in Hk' as [Hk' _]. fold j. rewrite Hnq.
      iApply ("HK" with "[%] Hl Hi Hcur Ha Hc"). split; [eapply keeps_trans; [|exact Hk']; xkeep | split; [exact El | exact E45]].
Qed.

End dispatch.
