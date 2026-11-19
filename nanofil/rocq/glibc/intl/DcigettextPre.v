From Glibc Require Import Unit_intl_dcigettext_os.
From Glibc Require Import GlibcProgram.
(** This module proves the prefix of glibc's `c: __dcigettext` up to the
    search of the domain bindings, for the call that getopt's diagnostics
    make: a nonnull message, a nonnull domain, category 5 (LC_MESSAGES)
    and no plural. The prefix allocates three objects, stores null into
    the directory slot and checks the arguments. It saves errno, takes the
    setlocale and state read locks and fills the search key. It then asks
    for the current locale name and searches the cache under the tree lock.

    The prefix calls five functions that this file does not prove: the
    two lock operations, the locale query, the cache search and the
    release of the cache lock. Their behavior is a premise of the caller,
    and the premise for the cache search says that the search finds
    nothing. At the end, the caller gets back everything that the prefix
    allocated, with errno unchanged. *)
From Glibc Require Import GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic VariadicLogic.
From Glibc Require Import OsWorld OsBlocks OsMemLogic DcigettextExit DcigettextPreRules.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Import Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld OsMemLogic DcigettextPreRules.DciVL.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance dci_pre_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).

(** ## The prefix up to the binding search *)

(** This lemma runs the prefix for one diagnostic message. The caller
    lends what the five calls use, together with errno's bytes. When the
    prefix reaches the binding search, the caller holds the two read locks
    and has released the cache lock. The search key holds the domain, the
    category, the locale name and the message id, and errno still holds
    its original bytes. *)
Lemma wp_dci_pre e dom msgid lk1 lk2 L1 L1' L2 L2' bs C cv lkt T T' T'' rt tc K Φ :
  dci_locale_rule 5 C cv ->
  lookup (TAtom "glibc_dcigettext#tree_lock") (ge_globals ge) = Some lkt ->
  lookup (TAtom "glibc_dcigettext#root") (ge_globals ge) = Some rt ->
  lookup (TAtom "glibc_dcigettext#transcmp") (ge_globals ge) = Some tc ->
  dci_rdlock_rule lkt T T' -> dci_unlock_rule lkt T' T'' ->
  (forall sb, dci_tfind_miss_rule (mkPtr sb (Obj sb)) rt tc K) ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "_nl_state_lock") (ge_globals ge) = Some lk1 ->
  lookup (TAtom "__libc_setlocale_lock") (ge_globals ge) = Some lk2 ->
  dci_rdlock_rule lk1 L1 L1' -> dci_rdlock_rule lk2 L2 L2' ->
  lookup (TAtom "v0") e = Some (WPtr dom) -> lookup (TAtom "v2") e = Some (WPtr msgid) ->
  lookup (TAtom "v6") e = Some (WInt 0) -> lookup (TAtom "v10") e = Some (WInt 5) ->
  0 < ptr_addr msgid < 2 ^ 64 -> 0 < ptr_addr dom < 2 ^ 64 ->
  L1 -∗ L2 -∗ errno_own eb bs -∗ C -∗ T -∗ K -∗
  ▷ (∀ (e' : env) (xs : Z) (xreg : region) (rl sb : Z) (sreg : region), ⌜dci_pre_env e' xs rl sb dom msgid cv (dci_w bs) /\
       (0 < xs /\ xs mod 16 = 0 /\ r_end xreg = xs + 16 /\ xs + 16 <= 2 ^ 48)%Z /\ r_kind xreg = Heap /\
       (0 < sb /\ sb mod 16 = 0 /\ r_end sreg = sb + 64 /\ sb + 64 <= 2 ^ 48)%Z⌝ -∗
     live xs xreg -∗ pcell xs 0 null -∗ obj rl (heap_req 8 8) -∗
     live sb sreg -∗ pcell sb 0 dom -∗ bytes sb 8 (le_bytes 5 4) -∗ pcell sb 16 cv -∗ pcell sb 32 null -∗
     pcell sb 56 msgid -∗ errno_own eb bs -∗ L1' -∗ L2' -∗ C -∗ T'' -∗ K -∗
     WP (ERun (mkFrame Unit_intl_dcigettext_os.fn___dcigettext e' [] None (Enter (TAtom "L102") (Some (TAtom "L108")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame Unit_intl_dcigettext_os.fn___dcigettext e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hloc Hlkt Hrt Htc Hrt1 Hut Htf Hge Hlk1 Hlk2 Hr1 Hr2 Hv0 Hv2 Hv6 Hv10 Hm Hd.
  iIntros "HL1 HL2 Herr HC HT HK HΦ".
  step.
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (xs [Hxs [Hxsal Hxsend]]) "Hxo".
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (rl [Hrl [Hrlal Hrlend]]) "Hro".
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (sb [Hsb [Hsbal Hsbend]]) "Hso".
  change (req_align (heap_req 8 8)) with 16 in Hxsal. change (req_extent (heap_req 8 8)) with 16 in Hxsend.
  change (req_align (heap_req 8 64)) with 16 in Hsbal. change (req_extent (heap_req 8 64)) with 64 in Hsbend.
  iDestruct (obj_zero_block with "Hxo") as "(Hxl & Hxb & Hxa)"; [vm_compute; discriminate|].
  change (req_extent (heap_req 8 8)) with 16 in *. change (req_kind (heap_req 8 8)) with Heap.
  iDestruct (zero_cell_prefix xs 0 8 with "Hxb Hxa") as "(Hxc & _ & _)".
  iDestruct (dci_search_split with "Hso") as "(Hsl & Hs0 & Hs8 & Hs16 & Hs32 & Hs56)".
  set (xreg := mkRegion xs (xs + 16) Heap Live) in *. set (sreg := mkRegion sb (sb + 64) Heap Live) in *.
  assert (Hxre : r_end xreg = xs + 16) by reflexivity.
  assert (Hxs8 : xs mod 8 = 0) by (Z.div_mod_to_equations; lia). assert (Hsb8 : sb mod 8 = 0) by (Z.div_mod_to_equations; lia). assert (Hsre : r_end sreg = sb + 64) by reflexivity.
  check "Hxl". store "Hxl" "Hxc". step. step. step.
  assert (Hnn : ((if ptr_addr msgid mod 2 ^ 64 =? (0 mod 2 ^ 64) mod 2 ^ 64 then 1 else 0) mod 2 ^ 32 =? 0) = true).
  { change ((0 mod 2 ^ 64) mod 2 ^ 64) with 0. rewrite (Z.mod_small (ptr_addr msgid)); [|lia].
    destruct (Z.eqb_spec (ptr_addr msgid) 0); [lia | reflexivity]. }
  branch_symbolic. rewrite Hnn. cbn [edge_label].
  do 12 (first [step | branch]). branch.
  step. step_global Hge. iApply (wp_dci_errno_check eb Herr); [vx |]. iNext.
  iDestruct "Herr" as (cs [Hbs Hcs]) "Hp". rewrite pts_app. iDestruct "Hp" as "[Heb Hea]".
  iApply (wp_dci_errno_load eb Herr with "Heb"); [vx | exact Hbs |]. iNext. iIntros "Heb".
  step_global Hlk2. iApply (Hr2 with "HL2"); [vx |]. iNext. iIntros (r2) "HL2".
  step_global Hlk1. iApply (Hr1 with "HL1"); [vx |]. iNext. iIntros (r1) "HL1".
  step. step.
  assert (Hdn : ((if ptr_addr dom mod 2 ^ 64 =? (0 mod 2 ^ 64) mod 2 ^ 64 then 1 else 0) mod 2 ^ 32 =? 0) = true).
  { change ((0 mod 2 ^ 64) mod 2 ^ 64) with 0. rewrite (Z.mod_small (ptr_addr dom)); [|lia].
    destruct (Z.eqb_spec (ptr_addr dom) 0); [lia | reflexivity]. }
  branch_symbolic. rewrite Hdn. cbn [edge_label].
  step. step. check "Hsl". store "Hsl" "Hs32".
  step. check "Hsl". store "Hsl" "Hs56".
  check "Hsl". store "Hsl" "Hs0".
  step. check "Hsl". store_int "Hsl" "Hs8".
  iApply (Hloc with "HC"); [vx |]. iNext. iIntros "HC".
  step. check "Hsl". store "Hsl" "Hs16".
  step_global Hlkt. iApply (Hrt1 with "HT"); [vx |]. iNext. iIntros (r3) "HT".
  step_global Hrt. step_global Htc. iApply (Htf with "HK"); [vx |]. iNext. iIntros "HK".
  step_global Hlkt. iApply (Hut with "HT"); [vx |]. iNext. iIntros (r4) "HT".
  step. step. branch. step. branch.
  iApply ("HΦ" with "[%] Hxl Hxc Hro Hsl Hs0 Hs8 Hs16 Hs32 Hs56 [Heb Hea] HL1 HL2 HC HT HK").
  { unfold dci_pre_env. split_and!; try lk_prove; try lia; try reflexivity. }
  iExists cs. rewrite pts_app. iFrame. done.
Qed.
End rules.
