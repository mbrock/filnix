(** Before it looks for an option, glibc's permuting scanner tidies the
    argument vector. It clamps the ends of the pending nonoption block to
    the public index, moves pending nonoptions behind the options that
    follow them, skips the nonoptions at the index, and handles "--".
    This file joins the proofs of those steps into one lemma for the
    whole path, from the clamp to the end-of-scan test. *)

From Glibc Require Import GetoptTactics GetoptNames CStruct OsMemLogic Unit_string_strcmp_os GlibcProgram GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic FrameNotation.
From Glibc Require Import OsWorld WordString
  GetoptModule GetoptArgv GetoptExchange
  GetoptExchangeTwo GetoptIdle GetoptIdleThree GetoptPermute GetoptClamp
  GetoptSkip GetoptDash GetoptDashTest.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import GetoptNames.fn__getopt_internal_r.

(** The path assigns these names, and the caller's kept names avoid them. *)
Definition idle_names : list name :=
  (x2_outer ++ x2_edges) ++ clamp_names ++ skip_names ++ (x3_outer ++ x3_edges) ++ dash_names ++ dash_test_names.

(** These names hold what the steps after the clamp read. *)
Definition clamp_keys : list name := [‹argc›; ‹argv›; ‹d›; ‹chk(d+4)›; ‹chk(d)›].

Import GetoptExchange Fix.ML0 Fix.LG0 Fix.LG0.L GetoptArgv.

Import ProgramAbbreviations.
Section path.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Existing Instance program_irisGS.
Import Fix.LG0.L.RunNotation.

Local Abbreviation end_of_scan :=
  (Exec (b_label getopt_blk203) (b_insts getopt_blk203) (b_jump getopt_blk203)).

(** Whatever the arguments are, the path must not read or write outside
    the argument vector. This lemma proves the path safe and says where
    its positions end up. The pending nonoptions still lie between first
    and last, last is at most the new index, and the index has not moved
    back or past the argument count. The vector holds the same arguments
    in another order. *)
Lemma wp_getopt_idle ks e fr0 n i o f l b r av ar ps pdd sdd Φ :
  avoids ks idle_names = true ->
  find_fn ge (TAtom "__GI_strcmp") = Some (Defined Unit_string_strcmp_os.fn___GI_strcmp) ->
  lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some pdd ->
  e.[‹argc›] = Some (WInt n) -> clamp_inputs e av b ->
  0 <= f <= l -> l <= n -> f <= i -> i <= n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ clamp_fields b i o f l -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ word_string DfracDiscarded pdd sdd -∗
  (∀ e' ps' i' f' l', ⌜Permutation ps ps' /\ keeps ks e e' /\ 0 <= f' <= l' /\ l' <= i' <= n /\ i <= i' /\
       e'.[‹chk(d+48)@L73›] = Some (WPtr (mkPtr (b + 48) (Obj b)))⌝ -∗
     live b r -∗ clamp_fields b i' o f' l' -∗
     live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
     WP run{ glibc_getopt_internal_r env: e' | pc: end_of_scan } {{ Φ }}) -∗
  WP run{ glibc_getopt_internal_r env: e | enter: @"L73" from: fr0 } {{ Φ }}.
Proof using Type.
  intros Hks Hg Hdd Hargc Hinputs Hfl Hln Hfi Hin Hlen Hb Hal Hend Hr Hav Hala Hda Hra.
  pose proof Hinputs as (Hargv & Hdata & Hopterr & Hindex).
  unfold idle_names in Hks.
  apply avoids_app in Hks as [Hkx2 Hks]. apply avoids_app in Hks as [Hkc Hks].
  apply avoids_app in Hks as [Hksk Hks]. apply avoids_app in Hks as [Hkx3 Hks].
  apply avoids_app in Hks as [Hkd Hkt].
  iIntros "Hl Hfields Ha Hc #Hs #Hdd HK".
  (* Both scanner modes reach the same test for "--". *)
  iAssert (∀ at_test args index first last,
    ⌜Permutation ps args /\ keeps (ks ++ clamp_keys) e at_test /\
      at_test.[‹chk(d+48)@L73›] = Some (WPtr (mkPtr (b + 48) (Obj b))) /\
      0 <= first <= last /\ last <= index <= n /\ i <= index⌝ -∗
    live b r -∗ clamp_fields b index o first last -∗ live av ar -∗ argv_cells av args -∗ argv_strs args -∗
    WP run{ glibc_getopt_internal_r env: at_test | pc: test_double_dash } {{ Φ }})%I
    with "[HK]" as "Hdash".
  { iIntros (at_test args index first last (Hp & Hkept & Hlast & Hfl' & Hli & Hi)) "Hl Hfields Ha Hc #Hs'".
    apply keeps_app in Hkept as [Hk Hregs].
    struct_open "Hfields" as "(Hi & Ho & Hf & Hlast & _)".
    iApply (wp_getopt_dash_end (ks ++ [‹chk(d+48)@L73›]) at_test index n first last b r av ar args pdd sdd
      with "Hl Hi Hf Hlast Ha Hc Hs' Hdd [Ho HK]");
      try solve [assumption | extend_avoids | kept_lookup | rewrite <-(Permutation_length Hp); assumption | lia].
    iIntros (e' args' index' first' last' (Hp' & Hk' & Hord)) "Hl Hi Hf Hlast Ha Hc Hs''".
    apply keeps_app in Hk' as [Hk' Hchecked].
    iApply ("HK" with "[%] Hl [Hi Ho Hf Hlast] Ha Hc Hs''"); [|struct_close].
    split; [etransitivity; eassumption|]. split; [eapply keeps_trans; eassumption|].
    repeat split; first [lia | kept_lookup]. }
  iApply (wp_getopt_clamp (ks ++ clamp_keys) e fr0 n i o f l b r av ar ps
    with "Hl Hfields Ha Hc Hs [Hdash]");
    try solve [assumption | extend_avoids | lia].
  iSplit.
  - iIntros (e1 args first last (Hp & Hk & _ & Hfirst & Hlast & _)) "Hl Hfields Ha Hc #Hs'".
    struct_open "Hfields" as "(Hi & Ho & Hf & Hla & _)".
    pose proof (keeps_app _ _ _ _ Hk) as [_ Hregs].
    iApply (wp_getopt_skip ((ks ++ clamp_keys) ++ [‹chk(d+48)@L73›]) e1 i n last b r av ar args
      with "Hl Hi Hla Ha Hc Hs' [Ho Hf Hdash]");
      try solve [assumption | extend_avoids | kept_lookup | rewrite <-(Permutation_length Hp); assumption | lia].
    iIntros (e2 index (Hk' & Hi)) "Hl Hi Hlast Ha Hc Hs''". apply keeps_app in Hk' as [Hk' Hchecked].
    iApply ("Hdash" with "[%] Hl [Hi Ho Hf Hlast] Ha Hc Hs''"); [|struct_close].
    split; [assumption|]. split; [eapply keeps_trans; eassumption|]. repeat split; first [lia | kept_lookup].
  - iIntros (e1 last (Hk & _ & Hlast & Hchecked & _)) "Hl Hfields Ha Hc Hs'".
    iApply ("Hdash" with "[%] Hl Hfields Ha Hc Hs'"). repeat split; first [assumption | reflexivity | lia].
Qed.

End path.
