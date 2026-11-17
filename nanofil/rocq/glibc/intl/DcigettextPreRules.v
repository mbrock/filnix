From Glibc Require Import GlibcProgram.
(** The first blocks of glibc's `c: __dcigettext` prepare a translation
    lookup before they know the locale. They save errno, take the setlocale
    and state read locks, fill a 64-byte search key, ask for the current
    locale name and search the translation cache. This module states what
    those blocks need from the functions they call, and it proves the
    memory facts that the prefix proof in DcigettextPre.v uses.

    The callees are not captured, so each one is a rule that a caller
    supplies. The rules for the read locks and the cache search name the
    resources that the lock or the cache gives back. The rule for the
    locale name returns one fixed name, so a caller decides the locale
    when it supplies the rule. None of these rules is proved here. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic VariadicLogic.
From Glibc Require Import OsWorld OsBlocks FileInv LibioLogic DcigettextCode DcigettextExit.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Module DciVL := VariadicLogicOn R LG0.
Import FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic DciVL.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance dci_pre_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).

(** ## Saving errno *)

(** A signed four-byte load of errno's bytes xs yields this 32-bit word. *)
Definition dci_w (xs : list Z) : Z :=
  match xs with
  | [a; b; c; d] => extension Sw (((d * 256 + c) * 256 + b) * 256 + a) mod 2 ^ 32
  | _ => 0
  end.

(** The saved word is a 32-bit value, which the restore at exit needs. *)
Lemma dci_w_range xs : 0 <= dci_w xs < 2 ^ 32.
Proof using Type*.
  unfold dci_w. destruct xs as [|a [|b [|c [|d [|u xs]]]]]; try (cbn; lia).
  apply Z.mod_pos_bound. lia.
Qed.

(** The lookup reads errno once at entry. The load needs only the
    caller's ownership of the four bytes and keeps them unchanged. *)
Lemma wp_dci_errno_load f e ls l dst v rest j bs Φ :
  value_x ge e A v = Some (WPtr (mkPtr eb (Obj eb))) -> length bs = 4%nat ->
  bytes eb 0 bs -∗
  ▷ (bytes eb 0 bs -∗ WP (ERun (mkFrame f (put dst (WInt (dci_w bs)) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let dst W (RawLoad (LdNarrow Sw) 0) [v] :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hv Hlen. iIntros "Hb HK".
  iApply (wp_read_with registry (os_wi w0) ge (bytes eb 0 bs)
    (fun m => dci_errno_mem eb m ∧ all_agree m (byte_ps eb 0 bs)) _ _ [] with "Hb HK").
  - iIntros (σ) "Hσ Hb". iDestruct (dci_errno_mem_facts eb Herr with "Hσ") as %Hmem.
    iDestruct (pts_facts with "Hσ Hb") as %[Hbs _]. iPureIntro. auto.
  - intros m fuel [(reg & Hl & Hbase & Hend & He) Hbs].
    destruct bs as [|a [|b [|c [|d [|u bs]]]]]; try discriminate Hlen.
    pose proof (byte_ps_agree _ _ _ _ _ 0%nat a Hl Hbs eq_refl) as (E0 & _).
    pose proof (byte_ps_agree _ _ _ _ _ 1%nat b Hl Hbs eq_refl) as (E1 & _).
    pose proof (byte_ps_agree _ _ _ _ _ 2%nat c Hl Hbs eq_refl) as (E2 & _).
    pose proof (byte_ps_agree _ _ _ _ _ 3%nat d Hl Hbs eq_refl) as (E3 & _).
    apply rule_let with (classes := [A]) (xs := [WPtr (mkPtr eb (Obj eb))]);
      [reflexivity | reflexivity | cbn; rewrite Hv; reflexivity |].
    assert (Ha : raw_address eb 0 = eb) by (unfold raw_address; rewrite Z.add_0_r; apply Z.mod_small; lia).
    assert (Haccess : access_res m eb (Obj eb) 4 Read 1 = Some ok).
    { apply (access_obj _ _ reg); [exact (proj1 Hl)|lia|lia|apply Z.mod_1_r]. }
    cbn - [access_res raw_address load_bytes extension]. rewrite Ha.
    unfold int_load_res. cbn - [access_res load_bytes extension]. rewrite Haccess.
    change (Some (OpRes (RVal (WInt (extension Sw
      (((m_bytes m (eb + 3) * 256 + m_bytes m (eb + 2)) * 256 +
        m_bytes m (eb + 1)) * 256 + m_bytes m (eb + 0)) mod 2 ^ 32))) m) =
      Some (OpRes (RVal (WInt (dci_w [a; b; c; d]))) m)).
    cbn [Z.of_nat Z.add] in E0, E1, E2, E3.
    rewrite E0 E1 E2 E3. reflexivity.
Qed.

(** The word keeps errno's byte order: the low byte comes first, and a
    word with every bit set stays 2^32 - 1. *)
Example dci_w_controls : dci_w [1; 0; 0; 0] = 1 /\ dci_w [0; 1; 0; 0] = 256 /\
  dci_w [255; 255; 255; 255] = 2 ^ 32 - 1 /\ dci_w [1; 0; 0] = 0.
Proof using Type*. repeat split. Qed.

(** ## The callees of the prefix *)

(** The lookup holds read locks so that another thread cannot change the
    locale while it works. Because the lock code is not captured, a caller
    states what taking a lock does: the call takes U, gives back U' and
    returns an integer that the lookup ignores. *)
Definition dci_rdlock_rule (lk : ptr) (U U' : iProp Σ) : Prop :=
  forall f e ls l d args rest j Φ, map_option (arg_x ge e) args = Some [WPtr lk] ->
    ⊢ U -∗ ▷ (∀ x, U' -∗ WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
      WP (ERun (mkFrame f e ls None
        (Exec l (Call (CResult d W) (Global (TAtom "__GI___pthread_rwlock_rdlock")) args :: rest) j)) : gexpr) {{ Φ }}.

(** The lookup asks __current_locale_name for the name of category cat.
    This rule returns the fixed pointer cv and keeps the caller's
    resource C, so the caller states the current locale by choosing cv. *)
Definition dci_locale_rule (cat : Z) (C : iProp Σ) (cv : ptr) : Prop :=
  forall f e ls l d args rest j Φ, map_option (arg_x ge e) args = Some [WInt cat] ->
    ⊢ C -∗ ▷ (C -∗ WP (ERun (mkFrame f (put d (WPtr cv) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
      WP (ERun (mkFrame f e ls None
        (Exec l (Call (CResult d P) (Global (TAtom "__current_locale_name")) args :: rest) j)) : gexpr) {{ Φ }}.

(** The cache search __GI___tfind receives the search key, the cache root
    and the comparison function. This rule describes a miss: it returns
    null and gives back the cache resource K. The rule lends no part of
    the key, so it suits a search that does not compare keys, such as a
    search of an empty cache. A cache that holds entries needs a rule
    that also lends the key's fields. *)
Definition dci_tfind_miss_rule (key root cmp : ptr) (K : iProp Σ) : Prop :=
  forall f e ls l d args rest j Φ, map_option (arg_x ge e) args = Some [WPtr key; WPtr root; WPtr cmp] ->
    ⊢ K -∗ ▷ (K -∗ WP (ERun (mkFrame f (put d (WPtr null) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
      WP (ERun (mkFrame f e ls None
        (Exec l (Call (CResult d P) (Global (TAtom "__GI___tfind")) args :: rest) j)) : gexpr) {{ Φ }}.

(** ## The search key *)

(** The key is a fresh 64-byte object. The prefix writes the domain at
    offset 0, the category at offset 8, the locale name at offset 16, a
    null domain at offset 32 and the message id at offset 56. A fresh
    object holds zeros, so it splits into those five cells, each null or
    zero. *)
Lemma dci_search_split sb :
  obj sb (heap_req 8 64) ⊢ live sb (mkRegion sb (sb + 64) Heap Live) ∗ pcell sb 0 null ∗ bytes sb 8 [0; 0; 0; 0] ∗
    pcell sb 16 null ∗ pcell sb 32 null ∗ pcell sb 56 null.
Proof using Type.
  rewrite obj_zero_block; [|vm_compute; discriminate].
  change (req_extent (heap_req 8 64)) with 64. change (req_kind (heap_req 8 64)) with Heap.
  change (replicate (Z.to_nat 64) 0) with (replicate 8 0 ++ replicate 4 0 ++ replicate 4 0 ++ replicate 8 0 ++
    replicate 8 0 ++ replicate 8 0 ++ replicate 16 0 ++ replicate 8 0)%list.
  change (replicate (Z.to_nat 64) CNone) with (replicate 8 CNone ++ replicate 8 CNone ++ replicate 8 CNone ++
    replicate 8 CNone ++ replicate 8 CNone ++ replicate 16 CNone ++ replicate 8 CNone)%list.
  rewrite !bytes_app !auxes_app. cbn [length Z.of_nat replicate Pos.of_succ_nat].
  iIntros "(Hl & (B0 & B8 & B12 & B16 & B24 & B32 & B40 & B56) & (A0 & A8 & A16 & A24 & A32 & A40 & A56))".
  iFrame "Hl B8".
  iSplitL "B0 A0"; [iApply (zero_cell with "B0 A0")|].
  iSplitL "B16 A16"; [iApply (zero_cell with "[B16] [A16]"); [iExact "B16" | iExact "A16"]|].
  iSplitL "B32 A32"; [iApply (zero_cell with "[B32] [A32]"); [iExact "B32" | iExact "A32"]|].
  iApply (zero_cell with "[B56] [A56]"); [iExact "B56" | iExact "A56"].
Qed.

(** The later blocks read values that the prefix computed, so its end
    state must say where they are. This predicate lists them: the
    directory slot xs, the result-length slot rl and the key sb, then the
    domain, the message id, the plural flag and the category. It also
    lists the null address, the saved errno word s and the locale name cv. *)
Definition dci_pre_env (e : env) (xs rl sb : Z) (dom msgid cv : ptr) (s : Z) : Prop :=
  lookup (TAtom "v17") e = Some (WPtr (mkPtr xs (Obj xs))) /\ lookup (TAtom "chk0") e = Some (WPtr (mkPtr xs (Obj xs))) /\
  lookup (TAtom "v21") e = Some (WPtr (mkPtr rl (Obj rl))) /\ lookup (TAtom "v23") e = Some (WPtr (mkPtr sb (Obj sb))) /\
  lookup (TAtom "pr.1") e = Some (WPtr dom) /\ lookup (TAtom "v2") e = Some (WPtr msgid) /\
  lookup (TAtom "v6") e = Some (WInt 0) /\ lookup (TAtom "v10") e = Some (WInt 5) /\
  lookup (TAtom "v32") e = Some (WInt 0) /\ lookup (TAtom "v69") e = Some (WInt s) /\
  lookup (TAtom "v90") e = Some (WPtr cv).

End rules.
