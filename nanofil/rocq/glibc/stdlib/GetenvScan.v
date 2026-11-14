(** A static environment is a finite array of readable strings followed by
    a null pointer. Owning that array lets getenv advance after a mismatch
    without assuming that the rest of the scan succeeds. The counter's read
    share remains owned throughout, so the final counter check cannot retry.
    This proof does not cover concurrent environment writers. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  Machine Pieces Heap Language Logic ExternalCalls StepRules Symbolic.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics WordString
  GetoptBytes GetenvCode GetenvEntry GetenvName GetenvCompare StrncmpCode.
Import ListNotations LG0 LG0.L ProgramAbbreviations GetoptBytes GetoptBytes.ML.
Open Scope Z_scope.
Open Scope list_scope.

(** Each entry records its pointer, readable text, and the region whose
    lifetime is borrowed when the atomic pointer load reads its [[capability]]. *)
Record getenv_entry := EnvEntry {
  entry_ptr : ptr;
  entry_text : list Z;
  entry_region : region
}.

(** The scan returns the first matching value pointer, or null when it
    reaches the sentinel. This computation does not exclude names containing
    equals signs; it uses the captured comparison tests unchanged. *)
Fixpoint getenv_scan_result (s : list Z) (entries : list getenv_entry) : ptr :=
  match entries with
  | [] => null
  | x :: xs => if getenv_entry_matches s (entry_text x)
      then ptr_add (entry_ptr x) (Z.of_nat (length s) + 1)
      else getenv_scan_result s xs
  end.

Section resources.
Context `{!gen_heapGS piece pval Σ}.

(** The array owns one pointer cell per entry and a final null cell.
    The target lifetime shares stay separate from the array lifetime. *)
Fixpoint getenv_cells dq dqt b o (entries : list getenv_entry) : iProp Σ :=
  match entries with
  | [] => pcellq dq b o null
  | x :: xs => pcellq dq b o (entry_ptr x) ∗
      live_capq dqt (ptr_cap (entry_ptr x)) (entry_region x) ∗
      word_string DfracDiscarded (entry_ptr x) (entry_text x) ∗
      getenv_cells dq dqt b (o + 8) xs
  end%I.

(** The array's bounds cover every pointer slot, including the sentinel. *)
Definition getenv_vector dq dqt b reg o entries : iProp Σ :=
  ⌜0 < b /\ 0 <= o /\ b + o + 8 * (Z.of_nat (length entries) + 1) <= r_end reg /\
    r_end reg <= 2 ^ 48 /\ (b + o) mod 8 = 0⌝ ∗
  liveq dq b reg ∗ getenv_cells dq dqt b o entries.

(** A found value remains a readable string, including an empty value.
    A missing variable is represented by the null pointer instead. *)
Definition getenv_value r : iProp Σ :=
  ⌜r = null⌝ ∨ ∃ value, word_string DfracDiscarded r value.

(** Reading a matched suffix does not consume the original entry's string
    permission. The returned value begins immediately after its equals sign. *)
Lemma getenv_cells_value p s dq dqt b o entries : s <> [] ->
  word_string DfracDiscarded p s -∗ getenv_cells dq dqt b o entries -∗
  getenv_cells dq dqt b o entries ∗ getenv_value (getenv_scan_result s entries).
Proof.
  intros Hne. revert o. induction entries as [|x xs IH]; intros o;
    iIntros "#Hname Hcells"; cbn [getenv_cells getenv_scan_result].
  - iFrame. iLeft. done.
  - iDestruct "Hcells" as "(Hcell & Htarget & #Htext & Htail)".
    destruct (getenv_entry_matches s (entry_text x)) eqn:Hmatch.
    + iDestruct (ws_shape with "Hname") as %(Hs & _).
      iDestruct (ws_shape with "Htext") as %(Ht & _).
      destruct (proj1 (getenv_entry_matches_iff s (entry_text x) Hs Ht Hne) Hmatch)
        as [value Hvalue].
      iFrame "Hcell Htarget Htail Htext". iRight. iExists value.
      iEval (rewrite Hvalue) in "Htext".
      replace (s ++ 61 :: value) with ((s ++ [61]) ++ value) by (rewrite <- app_assoc; reflexivity).
      iPoseProof (word_string_suffix DfracDiscarded (entry_ptr x) (s ++ [61]) value with "Htext") as "Hv".
      rewrite length_app Nat2Z.inj_add. cbn. iExact "Hv".
    + iDestruct (IH (o + 8) with "Hname Htail") as "[Htail Hv]".
      iFrame "Hcell Htarget Htext Htail Hv".
Qed.
End resources.

Section scan.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance getenv_scan_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Before comparing a string, getenv reads its pointer from the current
    array slot. The first iteration uses the environment pointer; later
    iterations use the cursor advanced by the preceding comparison. *)
Lemma getenv_scan_load e (first : bool) p cursor n old q b reg o qr dq dqt (G : iProp Σ) Φ :
  lookup (TAtom "v0") e = Some (WPtr p) ->
  lookup (TAtom (if first then "v10" else "v81")) e = Some (WPtr cursor) ->
  lookup (TAtom "v29") e = Some (WInt n) ->
  lookup (TAtom "v7") e = Some (WInt old) ->
  lookup (TAtom "v16") e = Some (WInt 0) ->
  cursor = mkPtr (b + o) (Obj b) ->
  0 < b -> 0 <= o -> b + o + 8 <= r_end reg -> r_end reg <= 2 ^ 48 ->
  (b + o) mod 8 = 0 -> 0 <= ptr_addr q < 2 ^ 64 ->
  liveq dq b reg -∗ pcellq dq b o q -∗ live_capq dqt (ptr_cap q) qr -∗ G -∗
  (∀ e', ⌜getenv_scan_bindings e' p cursor n old /\ lookup (TAtom "v38") e' = Some (WPtr q)⌝ -∗
    liveq dq b reg -∗ pcellq dq b o q -∗ live_capq dqt (ptr_cap q) qr -∗ G -∗
    WP (ERun (mkFrame glibc_getenv e' [] None
      (Enter (TAtom (if ptr_addr q =? 0 then "L35" else "L41")) (Some (TAtom "L32"))))
      : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getenv e [] None
    (Enter (TAtom "L32") (Some (TAtom (if first then "L13" else "L34"))))) : gexpr) {{ Φ }}.
Proof.
  intros Hp Hcursor Hn Hold Hz -> Hb Ho Hend Hspace Hal Hq.
  iIntros "Hl Hcell Htarget HG HK".
  destruct first; step;
    check_read_dq "Hl" by (unfold raw_address; cbn; rewrite Z.add_0_r;
      rewrite (Z.mod_small (b + o) (2 ^ 64)); [first [lia |exact Hal] |lia]);
    iNext; iIntros "Hl";
    (iApply (getenv_atomic_load with "Hl Hcell Htarget");
      [reflexivity |vx |left; reflexivity |
       unfold raw_address; cbn; rewrite Z.add_0_r Z.mod_small; lia |exact Hal |exact Hq |]).
  all: iNext; iIntros "Hl Hcell Htarget"; step; step;
    rewrite (Z.mod_small (ptr_addr q) (2 ^ 64) Hq) Zmod_0_l;
    destruct (ptr_addr q =? 0); branch;
    iApply ("HK" with "[] Hl Hcell Htarget HG"); iPureIntro;
    unfold getenv_scan_bindings; repeat split; vx.
Qed.

(** A failed comparison moves to the following array slot. A null pointer
    marks the end and causes getenv to reread the counter before returning.
    The caller keeps all memory permissions across these iterations. *)
Lemma getenv_scan e (first : bool) p s entries b reg o dq dqt bc rc dc counter (E : iProp Σ) Φ
    `{!Defines ge "__GI_strncmp" glibc_strncmp} :
  s <> [] ->
  lookup (TAtom "v0") e = Some (WPtr p) ->
  lookup (TAtom (if first then "v10" else "v81")) e = Some (WPtr (mkPtr (b + o) (Obj b))) ->
  lookup (TAtom "v29") e = Some (WInt (Z.of_nat (length s))) ->
  lookup (TAtom "v7") e = Some (WInt (counter mod 2 ^ 64)) ->
  lookup (TAtom "v16") e = Some (WInt 0) ->
  lookup (TAtom "__environ_counter") (ge_globals ge) = Some (mkPtr bc (Obj bc)) ->
  0 < bc -> bc + 8 <= r_end rc -> r_end rc <= 2 ^ 48 ->
  word_string DfracDiscarded p s -∗ getenv_vector dq dqt b reg o entries -∗
  liveq dc bc rc -∗ icellq dc bc 0 counter -∗ E -∗
  (getenv_vector dq dqt b reg o entries -∗ liveq dc bc rc -∗ icellq dc bc 0 counter -∗ E -∗
    Φ (Ret (WPtr (getenv_scan_result s entries)))) -∗
  WP (ERun (mkFrame glibc_getenv e [] None
    (Enter (TAtom "L32") (Some (TAtom (if first then "L13" else "L34"))))) : gexpr) {{ Φ }}.
Proof.
  revert e first o E. induction entries as [|x xs IH];
    intros e first o E Hne Hp Hcur Hn Hold Hz Hcounter Hbc Hrc Hrcmax;
    iIntros "#Hname (%Hbounds & Hl & Hcells) Hcl Hcc HE HK";
    destruct Hbounds as (Hb & Ho & Hend & Hspace & Hal).
  - cbn [getenv_cells].
    iAssert (live_capq dqt (ptr_cap null) reg) with "[]" as "Hnil"; [done|].
    iCombine "Hcl Hcc HE" as "HG".
    iApply (getenv_scan_load with "Hl Hcells Hnil HG"); try eassumption;
      try reflexivity; try (cbn in *; lia).
    iIntros (e') "%Henv Hl Hcell _ (Hcl & Hcc & HE)".
    destruct Henv as [(Hp' & Hcur' & Hn' & Hold' & Hz') Hq'].
    cbn. iCombine "Hl Hcell HE" as "HG".
    iApply (getenv_counter_check with "Hcl Hcc HG"); try eassumption.
    iIntros "Hcl Hcc (Hl & Hcell & HE)".
    rewrite Z.mod_mod; [|lia]. rewrite Z.eqb_refl.
    iApply ("HK" with "[Hl Hcell] Hcl Hcc HE").
    unfold getenv_vector. cbn [getenv_cells]. iFrame. done.
  - cbn [getenv_cells]. iDestruct "Hcells" as "(Hcell & Htarget & #Htext & Htail)".
    iDestruct (ws_shape with "Htext") as %(Hchars & Hqpos & Hqend).
    iCombine "Htail Hcl Hcc HE" as "HG".
    iApply (getenv_scan_load with "Hl Hcell Htarget HG"); try eassumption;
      try reflexivity; try (cbn in *; lia).
    iIntros (e') "%Henv Hl Hcell Htarget (Htail & Hcl & Hcc & HE)".
    destruct Henv as [Hbind Hq].
    rewrite (proj2 (Z.eqb_neq (ptr_addr (entry_ptr x)) 0) ltac:(lia)).
    iCombine "Hl Hcell Htarget Htail Hcl Hcc HE" as "HG".
    iApply (getenv_compare_entry with "Hname Htext HG"); try eassumption; [cbn; lia|].
    cbn [getenv_scan_result]. destruct (getenv_entry_matches s (entry_text x)) eqn:Hmatch.
    + iIntros "(Hl & Hcell & Htarget & Htail & Hcl & Hcc & HE)".
      iApply ("HK" with "[Hl Hcell Htarget Htail] Hcl Hcc HE").
      unfold getenv_vector. cbn [getenv_cells]. iFrame "Hl Hcell Htarget Htail Htext". done.
    + iIntros (e'') "%Hnext (Hl & Hcell & Htarget & Htail & Hcl & Hcc & HE)".
      destruct Hnext as [(Hp'' & Hcur'' & Hn'' & Hold'' & Hz'') Hnext].
      iCombine "Hcell Htarget HE" as "HE".
      iApply (IH e'' false (o + 8) with "Hname [Hl Htail] Hcl Hcc HE"); try eassumption.
      * cbn. rewrite Hnext. unfold ptr_add. cbn.
        replace (b + o + 8) with (b + (o + 8)) by lia. reflexivity.
      * unfold getenv_vector. iFrame. iPureIntro. cbn in Hend.
        repeat split; try lia.
        replace (b + (o + 8)) with (b + o + 1 * 8) by lia.
        rewrite (Z.mod_add (b + o) 1 8 ltac:(lia)). exact Hal.
      * iIntros "(%Hbounds & Hl & Htail) Hcl Hcc (Hcell & Htarget & HE)".
        iApply ("HK" with "[Hl Hcell Htarget Htail] Hcl Hcc HE").
        unfold getenv_vector. cbn [getenv_cells]. iFrame "Hl Hcell Htarget Htail Htext". done.
Qed.
End scan.
