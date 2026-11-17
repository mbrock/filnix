From Glibc Require Import GlibcProgram.
(** After the cache search misses, glibc's `c: __dcigettext` looks for
    the directory of the message domain and the name of the message
    category. This module proves that part of the C-locale route, from
    the search of the domain bindings to the point where the inlined
    `c: guess_category_value` has chosen the locale name.

    A program that never calls bindtextdomain has an empty list of domain
    bindings, so the lookup uses the default directory. Next it needs the
    name of the message category, which it finds through a table of
    indexes into a table of names. It then asks again for the current
    locale name. Because that name is "C", it does not consult the
    environment. The proof continues from the chosen name in another
    module. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks FileInv LibioLogic WordString GetoptBytes DcigettextCode DcigettextPreRules.
From Glibc Require MemchrLast.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Import FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance dci_dom_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).

(** An unsigned byte load of x returns x itself. *)
Lemma extended_ub x : 0 <= x < 256 -> extended Ub W (of_bytes [x]) = Some (WInt x).
Proof using Type*.
  intros Hx. unfold extended, of_bytes. cbn. rewrite Z.add_0_r.
  rewrite !Z.mod_small; try lia. reflexivity.
Qed.

(** These tactics read the two bytes of the locale name "C". The first
    checks and loads byte 0, and the second loads the terminator through
    the pointer advanced by one. *)
Ltac rd_c0 :=
  let bb := fresh "bb" in let breg := fresh "breg" in let Hbb := fresh "Hbb" in
  iDestruct (ws_byte _ [67] 0 with "Hcv") as (bb breg) "(%Hbb & #Hbl & #Hbt)"; [cbn; lia|];
  destruct Hbb as (Hcap & Hb0' & Hbq & Hbe & Hbr);
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hbl");
    [reflexivity | vx | exact Hcap | ar | ar | ar |]; iNext; iIntros "_";
  iApply (wp_raw_load_sub_bytes_dq with "Hbl Hbt");
    [reflexivity | vx | reflexivity | apply extended_chr | exact Hcap | ar |];
  iNext; iIntros "_ _".
Ltac ra := unfold raw_address; cbn [ptr_addr length Z.of_nat Pos.of_succ_nat] in *;
  first [apply Z.mod_1_r | rewrite ?Z.add_0_r; rewrite Z.mod_small; lia].
Ltac rd_c1 :=
  let bb := fresh "bb" in let breg := fresh "breg" in let Hbb := fresh "Hbb" in
  iDestruct (ws_byte _ [67] 1 with "Hcv") as (bb breg) "(%Hbb & #Hbl1 & #Hbt1)"; [cbn; lia|];
  destruct Hbb as (Hcap1 & Hb01 & Hbq1 & Hbe1 & Hbr1);
  iApply (MemchrLast.wp_half_check_read_dq registry (os_wi w0) ge with "Hbl1");
    [reflexivity | vx | reflexivity | exact Hcap1 | ra | ra | lia | lia | ra |]; iNext; iIntros "_";
  iApply (wp_raw_load_sub_bytes_dq with "Hbl1 Hbt1");
    [reflexivity | vx | reflexivity | apply extended_chr | exact Hcap1 | ra |];
  iNext; iIntros "_ _".

(** ## From the binding search to the locale name *)

(** Before it can name a catalog file, the lookup must find the domain's
    directory and the category's name. The caller lends a share of the
    empty list head and of the index byte k. The locale query returns the
    name cv, which reads "C". The lookup leaves with that name chosen and
    with a pointer to entry k of the table of category names. *)
Lemma wp_dci_dom e xs rl sb dom msgid cv s db dqb dbreg dd nb nc ib ic dqi ireg k C Φ :
  dci_pre_env e xs rl sb dom msgid cv s -> dci_locale_rule 5 C cv ->
  lookup (TAtom "_nl_domain_bindings") (ge_globals ge) = Some (mkPtr db (Obj db)) ->
  0 < db -> db mod 8 = 0 -> db + 8 <= r_end dbreg -> r_end dbreg <= 2 ^ 48 ->
  lookup (TAtom "__GI__nl_default_dirname") (ge_globals ge) = Some dd ->
  lookup (TAtom "_nl_category_names") (ge_globals ge) = Some (mkPtr nb nc) ->
  lookup (TAtom "_nl_category_name_idxs") (ge_globals ge) = Some (mkPtr ib ic) ->
  (ic = Obj ib \/ ic = Ro ib) -> 0 < ib -> ib + 6 <= r_end ireg -> r_end ireg <= 2 ^ 48 ->
  0 <= k < 256 -> 0 <= nb -> nb + k < 2 ^ 48 ->
  liveq dqb db dbreg -∗ pcellq dqb db 0 null -∗ liveq dqi ib ireg -∗ bytesq dqi ib 5 [k] -∗
  word_string DfracDiscarded cv [67] -∗ C -∗
  ▷ (∀ e', ⌜dci_pre_env e' xs rl sb dom msgid cv s /\ lookup (TAtom "iw_3.v7") e' = Some (WPtr cv) /\
         lookup (TAtom "iw_2.v9") e' = Some (WPtr (mkPtr (nb + k) nc))⌝ -∗
      liveq dqb db dbreg -∗ pcellq dqb db 0 null -∗ liveq dqi ib ireg -∗ bytesq dqi ib 5 [k] -∗ C -∗
      WP (ERun (mkFrame glibc_dcigettext e' [] None (Enter (TAtom "iw_3.join") (Some (TAtom "iw_3.L16")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_dcigettext e [] None (Enter (TAtom "L102") (Some (TAtom "L108")))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Henv Hloc Hdb Hdb0 Hdb8 Hdbend Hdbr Hdd Hcn Hci Hic Hib0 Hibend Hibr Hk Hnb Hnbk.
  pose proof Henv as (Hv17 & Hc0 & Hv21 & Hv23 & Hpr1 & Hv2 & Hv6 & Hv10 & Hv32 & Hv69 & Hv90).
  iIntros "Hnl Hnc Hil Hib #Hcv HC HK".
  step. step_global Hdb. check_shared "Hnl".
  iApply (wp_raw_load_pointer_dq with "Hnl Hnc [//]");
    [reflexivity | vx | left; reflexivity | ar | ar | cbn; lia |].
  iNext. iIntros "Hnl Hnc _".
  repeat (first [step | branch]).
  assert (Ei : (ptr_addr (mkPtr ib ic) mod 2 ^ 64 + sign_extension (2 ^ 32) (2 ^ 31) (5 mod 2 ^ 32) mod 2 ^ 64 mod 2 ^ 64)
    mod 2 ^ 64 = ib + 5).
  { change (sign_extension (2 ^ 32) (2 ^ 31) (5 mod 2 ^ 32) mod 2 ^ 64 mod 2 ^ 64) with 5. cbn [ptr_addr].
    rewrite (Z.mod_small ib); [|lia]. rewrite !Z.mod_small; lia. }
  rewrite Ei.
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hil"); [reflexivity | vx | exact Hic | ar | ar | ar |].
  iNext. iIntros "Hil".
  iApply (wp_raw_load_sub_bytes_dq with "Hil Hib");
    [reflexivity | vx | reflexivity | apply extended_ub; exact Hk | exact Hic | ar |].
  iNext. iIntros "Hil Hib".
  step. step.
  iApply (Hloc with "HC"); [vx |]. iNext. iIntros "HC".
  rd_c0. change (chr_w (sbyte [67] 0)) with 67.
  step. branch. step. step.
  assert (Ec1 : (ptr_addr cv mod 2 ^ 64 + 1 mod 2 ^ 64) mod 2 ^ 64 = ptr_addr cv + 1).
  { cbn [length Z.of_nat] in Hbe. rewrite (Z.mod_small (ptr_addr cv)); [|lia]. apply Z.mod_small. lia. }
  rewrite Ec1. rd_c1. change (chr_w (sbyte [67] 1)) with 0.
  step. branch. step. branch.
  assert (Ecat : (ptr_addr (mkPtr nb nc) mod 2 ^ 64 + k mod 2 ^ 32 mod 2 ^ 32 mod 2 ^ 64 mod 2 ^ 64) mod 2 ^ 64 = nb + k).
  { cbn [ptr_addr]. rewrite !(Z.mod_small k); try lia. rewrite (Z.mod_small nb); [|lia]. apply Z.mod_small. lia. }
  rewrite Ecat. change (ptr_cap (mkPtr nb nc)) with nc.
  iApply ("HK" with "[%] Hnl Hnc Hil Hib HC").
  { unfold dci_pre_env. split_and!; lk_prove. }
  Unshelve. all: first [exact dbreg | exact dqb].
Qed.
End rules.
