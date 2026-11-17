(** A program's `c: getenv` scans the environment array that the runtime
    passed to `c: __libc_start_main`. Its proof in
    [GetenvCall](../stdlib/GetenvCall.v) asks for two resources: the
    globals `c: __environ` and `c: __environ_counter`, and the array with
    a read-only string for each entry. This module builds both from what
    a run owns once the constructors have run, for any image.

    ## Why the strings become read-only

    Nothing in the program writes an environment string, so the proof
    freezes each one. A frozen string also holds a copyable share of its
    object's life, and the scan needs exactly such a share. The globals
    and the array stay owned, and a caller may split them between
    several readers, such as getopt's and setlocale's calls of
    `c: getenv`. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic MemLogic.
From Glibc Require Import FileInv WordString StartState StartOwn StartJoin GetenvScan GetenvEntry GetenvStatic.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** Every call of `c: getenv` needs two facts about the image. The two
    globals exist, and each one fits in its region. *)
Definition getenv_image_ok (ge : genv) (bc : Z) (rc : region) (be : Z) (re : region) : Prop :=
  lookup (TAtom "__environ_counter") (ge_globals ge) = Some (mkPtr bc (Obj bc)) /\
  lookup (TAtom "__environ") (ge_globals ge) = Some (mkPtr be (Obj be)) /\
  0 < bc /\ bc + 8 <= r_end rc /\ r_end rc <= 2 ^ 48 /\
  0 < be /\ be + 8 <= r_end re /\ r_end re <= 2 ^ 48 /\ be mod 8 = 0.

(** A lookup in a list finds what [nth_error] finds. *)
Lemma lookup_nth_error_eq {A} (l : list A) k x : l !! k = Some x -> nth_error l k = Some x.
Proof. revert k. induction l as [|y l IH]; intros [|k] H; cbn in *; try discriminate; auto. Qed.

(** These are the entries that `c: getenv` scans for an environment
    array env of the start state. Each entry's pointer is the base of
    its own string, and its region is the one memory records for it. *)
Definition env_entry (m : mem) (q : Z * list Z) : getenv_entry := EnvEntry (mkPtr q.1 (Obj q.1)) q.2 (reg_of m q.1).
Definition env_entries (m : mem) (env : Z * list (Z * list Z)) : list getenv_entry := map (env_entry m) env.2.

(** The entries hold the array's strings. *)
Lemma env_entries_text m env : map entry_text (env_entries m env) = map snd env.2.
Proof. rewrite /env_entries map_map. reflexivity. Qed.

Section own.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** A start string can be frozen. Then it is a read-only string, and
    it also holds a copyable share of its object's life in the region
    that memory records. *)
Lemma start_str_ro m q : c_string m q.1 q.2 ->
  live q.1 (reg_of m q.1) -∗ bytes q.1 0 (str_bytes q.2) ==∗
  word_string DfracDiscarded (mkPtr q.1 (Obj q.1)) q.2 ∗ liveq DfracDiscarded q.1 (reg_of m q.1).
Proof using Type.
  intros Hc. iIntros "L B". iDestruct (str_wwin m q Hc with "L B") as (ws Hs) "[L W]".
  iMod (ptsq_persist with "L") as "#L". iMod (ptsq_persist with "W") as "#W". iModIntro.
  iSplit; [|iExact "L"]. iExists q.1, (reg_of m q.1), ws. iSplit; [done|]. rewrite /wwin. iFrame "L W".
Qed.

(** The scan reads one cell for each slot of the array. Those cells come
    from the slots at offsets o, o + 8 and onward, the null slot, and a
    frozen string with its life for each slot. *)
Lemma env_cells_own m b o (ss : list (Z * list Z)) :
  ([∗ list] i ↦ q ∈ ss, pcell b (o + 8 * Z.of_nat i) (mkPtr q.1 (Obj q.1))) -∗
  pcell b (o + 8 * Z.of_nat (length ss)) null -∗
  ([∗ list] q ∈ ss, word_string DfracDiscarded (mkPtr q.1 (Obj q.1)) q.2 ∗ liveq DfracDiscarded q.1 (reg_of m q.1)) -∗
  getenv_cells (DfracOwn 1) DfracDiscarded b o (map (env_entry m) ss).
Proof using Type.
  revert o. induction ss as [|q ss IH]; intros o; cbn [big_opL length List.map].
  - iIntros "_ Hn _". cbn [getenv_cells]. rewrite /pcellq -pts_ptsq.
    by replace (o + 8 * Z.of_nat 0) with o by lia.
  - iIntros "[Hq Hs] Hn [[#Hw #Hl] Hws]". replace (o + 8 * Z.of_nat 0) with o by lia.
    iDestruct (IH (o + 8) with "[Hs] [Hn] Hws") as "Hc".
    { iApply (big_sepL_impl with "Hs"). iIntros "!>" (k x _) "H".
      by replace (o + 8 * Z.of_nat (S k)) with (o + 8 + 8 * Z.of_nat k) by lia. }
    { by replace (o + 8 * Z.of_nat (S (length ss))) with (o + 8 + 8 * Z.of_nat (length ss)) by lia. }
    cbn [getenv_cells env_entry entry_ptr entry_text entry_region ptr_cap live_capq].
    iSplitL "Hq"; [rewrite /LG0.pcellq; iExact "Hq"|]. iSplitR; [iExact "Hl"|]. iSplitR; [iExact "Hw"|iExact "Hc"].
Qed.

(** Each call of `c: getenv` reads two globals and the environment
    array. Once the constructors have run, a run owns all of them:
    `c: __environ` points at the array, and the array holds its strings.
    So the run can own what the scan reads. The counter starts at zero,
    and the entries are the strings of the start state. *)
Lemma getenv_own m (env : Z * list (Z * list Z)) bc rc be re :
  string_array m env.1 env.2 ->
  live bc rc -∗ icell bc 0 0 -∗ live be re -∗ pcell be 0 (mkPtr env.1 (Obj env.1)) -∗
  live env.1 (reg_of m env.1) -∗
  ([∗ list] i ↦ q ∈ env.2, pcell env.1 (8 * Z.of_nat i) (mkPtr q.1 (Obj q.1))) -∗
  pcell env.1 (8 * Z.of_nat (length env.2)) null -∗
  ([∗ list] q ∈ env.2, live q.1 (reg_of m q.1) ∗ bytes q.1 0 (str_bytes q.2)) ==∗
  getenv_globals (DfracOwn 1) bc rc be re 0 (mkPtr env.1 (Obj env.1)) ∗
  getenv_storage (DfracOwn 1) DfracDiscarded (mkPtr env.1 (Obj env.1)) (env_entries m env).
Proof using Type.
  destruct env as [b ss]. rewrite /env_entries. cbn [fst snd]. intros (Hh & Hs & _).
  pose proof Hh as (reg & [Er _] & _ & H0 & Ha & He & Hr).
  assert (Rg : reg_of m b = reg) by (unfold reg_of; rewrite Er; reflexivity).
  iIntros "Lc Hc Le He La Hsl Hn Hstr".
  iAssert (|==> [∗ list] q ∈ ss, word_string DfracDiscarded (mkPtr q.1 (Obj q.1)) q.2 ∗
    liveq DfracDiscarded q.1 (reg_of m q.1))%I with "[Hstr]" as ">Hw".
  { iApply big_sepL_bupd. iApply (big_sepL_impl with "Hstr"). iIntros "!>" (k q Hk) "[L B]".
    destruct q as [sb s]. destruct (Hs k sb s (lookup_nth_error_eq _ _ _ Hk)) as [_ Hc].
    iApply (start_str_ro m (sb, s) Hc with "L B"). }
  iDestruct (env_cells_own m b 0 ss with "[Hsl] [Hn] Hw") as "Hcells".
  { iApply (big_sepL_impl with "Hsl"). iIntros "!>" (k x _) "H". by rewrite Z.add_0_l. }
  { by rewrite Z.add_0_l. }
  rewrite Rg. iModIntro. rewrite /getenv_globals /liveq /icellq /pcellq -!pts_ptsq. iFrame "Lc Hc Le He". iRight.
  iExists b, reg, 0. iSplit; [iPureIntro; by rewrite Z.add_0_r|]. rewrite /getenv_vector.
  assert (Le : length (map (env_entry m) ss) = length ss) by apply length_map.
  assert (Hd : 8 * (Z.of_nat (length ss) + 1) <= (8 * (Z.of_nat (length ss) + 1) + 15) / 16 * 16)
    by (Z.div_mod_to_equations; lia).
  assert (H8 : b mod 8 = 0).
  { apply Z.mod_divide; [lia|]. destruct (proj1 (Z.mod_divide b 16 ltac:(lia)) Ha) as [k ->]. exists (2 * k). lia. }
  iSplit; [iPureIntro; rewrite Le Z.add_0_r; split_and!; lia|].
  rewrite /liveq -pts_ptsq. iSplitL "La"; [iExact "La"|iExact "Hcells"].
Qed.

(** A full share of any pieces is two halves. *)
Lemma ptsq_half ps : ptsq (DfracOwn 1) ps ⊣⊢ ptsq (DfracOwn (1/2)) ps ∗ ptsq (DfracOwn (1/2)) ps.
Proof using Type. rewrite -ptsq_split Qp.half_half. done. Qed.

(** A discarded share of an object's life can be copied. *)
Lemma live_capq_dup c reg :
  live_capq DfracDiscarded c reg ⊢ live_capq DfracDiscarded c reg ∗ live_capq DfracDiscarded c reg.
Proof using Type. destruct c; cbn [live_capq]; try (iIntros "_"; done). all: iIntros "#H"; iFrame "H". Qed.

(** The cells of the scan split into two halves that read the same
    entries. *)
Lemma getenv_cells_half b o es :
  getenv_cells (DfracOwn 1) DfracDiscarded b o es ⊢
  getenv_cells (DfracOwn (1/2)) DfracDiscarded b o es ∗ getenv_cells (DfracOwn (1/2)) DfracDiscarded b o es.
Proof using Type.
  revert o. induction es as [|e es IH]; intros o; cbn [getenv_cells].
  - rewrite /pcellq ptsq_half. done.
  - iIntros "(Hp & Hl & #Hw & Hc)". iDestruct (IH with "Hc") as "[H1 H2]".
    iDestruct (live_capq_dup with "Hl") as "[Hl1 Hl2]".
    rewrite /pcellq ptsq_half. iDestruct "Hp" as "[P1 P2]".
    iSplitL "P1 Hl1 H1"; iFrame "Hw"; iFrame.
Qed.

(** Two readers can each hold half of what `c: getenv` reads, because the
    scan only reads it and gives it back unchanged. *)
Lemma getenv_half bc rc be re c ep es :
  getenv_globals (DfracOwn 1) bc rc be re c ep ∗ getenv_storage (DfracOwn 1) DfracDiscarded ep es ⊢
  (getenv_globals (DfracOwn (1/2)) bc rc be re c ep ∗ getenv_storage (DfracOwn (1/2)) DfracDiscarded ep es) ∗
  (getenv_globals (DfracOwn (1/2)) bc rc be re c ep ∗ getenv_storage (DfracOwn (1/2)) DfracDiscarded ep es).
Proof using Type.
  rewrite /getenv_globals /liveq /icellq /pcellq !ptsq_half.
  iIntros "[((L1 & L2) & (C1 & C2) & (E1 & E2) & (P1 & P2)) HS]".
  iDestruct "HS" as "[#HS | (%b & %reg & %o & %Hep & (%Hv & La & Hc))]".
  - iSplitL "L1 C1 E1 P1"; iFrame; by iLeft.
  - rewrite /liveq ptsq_half. iDestruct "La" as "[A1 A2]".
    iDestruct (getenv_cells_half with "Hc") as "[H1 H2]".
    iSplitL "L1 C1 E1 P1 A1 H1"; iFrame; iRight; iExists b, reg, o; iFrame; iSplit; done.
Qed.

End own.
