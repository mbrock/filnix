From Glibc Require Import GlibcProgram.
(** The getopt wrapper copies the public optind and opterr into the
    private object before it calls the parser. A session describes the
    object as the previous call left it, so it no longer fits once the
    copy has happened: a caller may reset optind to 0, and fresh storage
    then holds the public index but no set-up flag. This file states what
    the parser's first blocks need right after the copy, builds that from
    a session or from fresh storage, and runs the first blocks from it. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString GetoptModule GetoptState GetoptBytes
  GetoptInitialize GetoptColon GetoptEntry GetoptLongSession GetoptEntryBridge.
From Glibc Require FileInv GetoptEntry GetoptEntryBridge GetoptInitialize GetoptLongSession GetoptState OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** ## The private object after the copy

    The wrapper writes only the index and error fields, so the copy
    leaves every other field of the object as it was. The controls below
    show the two cases that a session cannot describe after the copy,
    and the first blocks' answer in each case. *)

(** The copy puts the public index and error flag into the first two fields. *)
Definition getopt_copy_in (s : getopt_state) (j err : Z) : getopt_state :=
  mkGetoptState j err (gs_opt s) (gs_arg s) (gs_initialized s) (gs_next s)
    (gs_order s) (gs_first s) (gs_last s).

(** Suppose a caller resets optind to 0 after the scan has passed a
    nonoption at index 1. The copied object has no limits at index 0,
    because its first nonoption lies at 1, yet it must start over, and
    the first blocks set it up with limits at index 1. *)
Lemma entry_pre_ctl_reset : let s := getopt_copy_in (mkGetoptState 3 1 0 null 1 null 1 1 2) 0 1 in
  ~ getopt_bounds 5 0 s /\ needs_init s /\ init_state s 0 = mkGetoptState 1 1 0 null 1 null 0 1 1 /\
  getopt_bounds 5 1 (init_state s 0).
Proof. cbn. unfold getopt_bounds, needs_init. cbn. split; [lia | split; [left; reflexivity | split; [reflexivity | lia]]]. Qed.

(** Fresh storage that receives the public index 4 is not the zero
    object, and the first blocks start it at 4 rather than at 1. *)
Lemma entry_pre_ctl_fresh : let s := getopt_copy_in getopt_zero 4 1 in
  s <> getopt_zero /\ needs_init s /\ gs_ind (init_state s 0) = 4 /\ gs_first (init_state s 0) = 4.
Proof. cbn. unfold needs_init. cbn. split; [discriminate | split; [right; reflexivity | split; reflexivity]]. Qed.

(** A resumed call with the same index keeps its limits, because the
    limits do not mention the index or error fields. *)
Lemma entry_pre_ctl_resume : let s := mkGetoptState 3 1 0 null 1 null 1 1 2 in
  getopt_bounds 5 3 (getopt_copy_in s 3 0) /\ ~ needs_init (getopt_copy_in s 3 0).
Proof. cbn. unfold getopt_bounds, needs_init. cbn. lia. Qed.

(** The session module supplies the state and the cursor relation. *)
Import GetoptEntryBridge GetoptLongSession GetoptState FileInv FileInv.ML FileInv.LG FileInv.L.

Section entry_pre.
Context `{!gen_heapGS piece pval Σ}.

(** The cursor relation holds only shared strings and pure facts, so it may be used twice. *)
Local Instance ep_cursor_persistent ps i s : Persistent (getopt_cursor ps i s).
Proof. unfold getopt_cursor. apply _. Qed.

(** ## What the first blocks need after the copy

    The parser's first blocks start over when the index is 0 or the
    object is not set up, and then they ignore the saved position except
    to read it. Otherwise they resume, and a resumed call needs the
    limits at the copied index and a saved position inside that word.
    The precondition below says exactly that, and nothing about the
    limits of an object that is about to start over. *)

(** After the copy, the object holds the public index j. Either it will
    start over, with a null or readable saved position, or it is set up
    with limits at j and a saved position that belongs to word j. *)
Definition getopt_entry_pre (b : Z) (r : region) (av : Z) (ar : region)
    (ps : list ptr) (j : Z) : iProp Σ :=
  ⌜0 < av /\ av mod 8 = 0 /\ av + 8 * (Z.of_nat (length ps) + 1) <= r_end ar /\ r_end ar <= 2 ^ 48 /\
    1 <= Z.of_nat (length ps) < 2 ^ 31 /\ 0 <= j <= Z.of_nat (length ps)⌝ ∗
  ∃ s, getopt_state_own b r s ∗ ⌜gs_ind s = j⌝ ∗
    ((⌜needs_init s⌝ ∗ (⌜gs_next s = null⌝ ∨ ∃ tail, word_string DfracDiscarded (gs_next s) tail)) ∨
     (⌜gs_initialized s = 1 /\ 0 <= gs_order s <= 2 /\ getopt_bounds (Z.of_nat (length ps)) j s⌝ ∗
      getopt_cursor ps j s)).

(** ## Building the precondition

    A program that calls getopt never touches the private object; only
    the wrapper writes its index and error fields. The lemmas below
    follow that split. The wrapper borrows those two fields for the copy,
    and the rest of the object stays with the program. Once the copy is
    done, the program can show that the parser may start. *)

(** A session at index i admits the public index i or 0. A set-up object
    cannot move to another nonzero index, because its saved position
    belongs to word i and would be read as part of a different word. *)
Lemma session_entry_pre b r av ar ps i j err :
  j = i \/ j = 0 ->
  getopt_session b r av ar ps i ⊢ ∃ i0 e0, live b r ∗ int_cell b 0 i0 ∗ int_cell b 4 e0 ∗
    (live b r -∗ int_cell b 0 j -∗ int_cell b 4 err -∗ getopt_entry_pre b r av ar ps j).
Proof.
  intros Hj. iIntros "[%Hav (%s & (%Hb & Hl & Hi & He & Ho & Ha & Hn & Hx & Hr & Hf & Hla) & %Hbd & Hk)]".
  iExists (gs_ind s), (gs_err s). iFrame "Hl Hi He". iIntros "Hl Hi He".
  iSplit; [iPureIntro; unfold getopt_bounds in Hbd; destruct Hj; subst; lia|].
  iExists (getopt_copy_in s j err). iSplitL "Hl Hi He Ho Ha Hn Hx Hr Hf Hla"; [|iSplit; [done|]].
  { unfold getopt_state_own, getopt_copy_in; cbn [gs_ind gs_err gs_opt gs_arg gs_initialized gs_next
      gs_order gs_first gs_last]. iFrame. done. }
  iDestruct "Hk" as "[[%Hz %Hi1] | [(%Hin & %Hind & %Hor) #Hcu]]".
  - subst s. iLeft. iSplit; [iPureIntro; right; reflexivity | by iLeft].
  - destruct Hj as [-> | ->].
    + iRight. unfold getopt_bounds in *. unfold getopt_cursor. cbn [getopt_copy_in gs_next gs_last
        gs_first gs_initialized gs_order]. iSplit; [iPureIntro; lia | iExact "Hcu"].
    + iLeft. iSplit; [iPureIntro; left; reflexivity|]. cbn [getopt_copy_in gs_next].
      iDestruct (getopt_cursor_read with "Hcu") as "[%Hn0 | (%t & Ht & _)]"; [by iLeft|].
      iRight. by iExists t.
Qed.

(** Fresh storage holds zeroes before the first copy. It admits any
    public index within the argument count, and the first blocks will
    set it up at that index. *)
Lemma zero_entry_pre b r av ar ps j err :
  0 < av -> av mod 8 = 0 -> av + 8 * (Z.of_nat (length ps) + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  1 <= Z.of_nat (length ps) < 2 ^ 31 -> 0 <= j <= Z.of_nat (length ps) ->
  getopt_state_own b r getopt_zero ⊢ live b r ∗ int_cell b 0 0 ∗ int_cell b 4 0 ∗
    (live b r -∗ int_cell b 0 j -∗ int_cell b 4 err -∗ getopt_entry_pre b r av ar ps j).
Proof.
  intros Hav Hal Hfit Har Hn Hj. iIntros "(%Hb & Hl & Hi & He & Ho & Ha & Hn & Hx & Hr & Hf & Hla)".
  iFrame "Hl Hi He". iIntros "Hl Hi He". iSplit; [iPureIntro; lia|].
  iExists (getopt_copy_in getopt_zero j err). iSplitL; [|iSplit; [done|]].
  { unfold getopt_state_own, getopt_copy_in; cbn [gs_ind gs_err gs_opt gs_arg gs_initialized gs_next
      gs_order gs_first gs_last getopt_zero]. iFrame. done. }
  iLeft. iSplit; [iPureIntro; right; reflexivity | by iLeft].
Qed.

(** When the call goes on to look for the next argument, the object is
    set up, its limits hold at its new index, and the saved position is
    null or at the end of a string. The new index is 1 if the copied
    index was 0, and the copied index otherwise. This holds whether the
    call started over or resumed. *)
Lemma entry_pre_select b r (ps : list ptr) j s s' (tail : list Z) :
  1 <= Z.of_nat (length ps) < 2 ^ 31 -> 0 <= j <= Z.of_nat (length ps) -> gs_ind s = j ->
  (needs_init s \/ gs_initialized s = 1 /\ 0 <= gs_order s <= 2 /\ getopt_bounds (Z.of_nat (length ps)) j s) ->
  entry_state s s' -> gs_next s' = null \/ tail = [] ->
  (⌜gs_next s = null⌝ ∨ word_string DfracDiscarded (gs_next s) tail) -∗ getopt_state_own b r s' -∗
  ⌜0 < b /\ b mod 8 = 0 /\ b + 56 <= r_end r /\ r_end r <= 2 ^ 48 /\ gs_initialized s' = 1 /\
    0 <= gs_order s' <= 2 /\ getopt_bounds (Z.of_nat (length ps)) (gs_ind s') s' /\ gs_arg s' = null /\
    gs_ind s' = (if j =? 0 then 1 else j)⌝ ∗
  live b r ∗ int_cell b 0 (gs_ind s') ∗ int_cell b 4 (gs_err s') ∗ int_cell b 8 (gs_opt s') ∗
  pcell b 16 (gs_arg s') ∗ int_cell b 24 (gs_initialized s') ∗ pcell b 32 (gs_next s') ∗
  int_cell b 40 (gs_order s') ∗ int_cell b 44 (gs_first s') ∗ int_cell b 48 (gs_last s') ∗
  (⌜gs_next s' = null⌝ ∨ word_string DfracDiscarded (gs_next s') []).
Proof.
  intros Hn Hj Hi Hk Hst Hnt. iIntros "#Hc (%Hb & Hl & Hi & He & Ho & Ha & Hn & Hx & Hr & Hf & Hla)". iFrame.
  subst j. destruct Hst as [(Hni & o & Ho & ->) | (Hni & ->)].
  - iSplit; [|by iLeft]. iPureIntro. unfold init_state, getopt_bounds.
    destruct (Z.eqb_spec (gs_ind s) 0); cbn; repeat split; try reflexivity; lia.
  - destruct Hk as [Hk | (Hin & Hor & Hbd)]; [contradiction|]. iSplit.
    + iPureIntro. unfold needs_init in Hni. unfold getopt_bounds in *. unfold clear_arg; cbn.
      destruct (Z.eqb_spec (gs_ind s) 0); [lia|]. repeat split; try reflexivity; lia.
    + cbn. destruct Hnt as [Hn0 | ->]; [by iLeft|]. iDestruct "Hc" as "[%Hn0 | Hw]"; [by iLeft | by iRight].
Qed.

End entry_pre.

Import ProgramAbbreviations.
Section entry_pre_wp.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance epw_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The cursor relation holds only shared strings and pure facts, so it may be used twice. *)
Local Instance epw_cursor_persistent ps i s : Persistent (getopt_cursor ps i s).
Proof. unfold getopt_cursor. apply _. Qed.

(** ## The first blocks after the copy

    After the copy, the wrapper calls the parser, whose first blocks
    either start over or resume. The rule below proves those blocks safe
    in both cases. It gives the program the same facts as the rule for a
    resumed session, except one about the object before the call, which
    is false when the program reset optind to 0. *)

(** The call ends in one of two places. If it goes on to find the next
    argument, the program gets the fields of the object, which is now set
    up, and its limits at the new index. If it goes on with a group of
    short options, it kept the copied index, and the program learns where
    the saved position lies in the current word. A call that starts over
    reads the environment, so the program supplies a rule for that. *)
Lemma wp_getopt_entry_pre e n av ar p os lo li lonly pc penv b r ps j (G : iProp Σ) Φ :
  GetoptInitialize.getenv_rule w0 registry ge G -> lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v4") e = Some (WPtr p) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) -> lookup (TAtom "v10") e = Some (WInt lonly) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "v14") e = Some (WInt pc) ->
  Z.of_nat (length ps) = n ->
  getopt_entry_pre b r av ar ps j -∗ word_string DfracDiscarded p os -∗ G -∗
  ((∀ e' s s', ⌜entry_state s s' /\
        entry_env e' n (mkPtr av (Obj av)) (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b (print_errors os (gs_err s)) /\
        gs_ind s = j /\ gs_initialized s' = 1 /\ 0 <= gs_order s' <= 2 /\ getopt_bounds n (gs_ind s') s' /\
        gs_arg s' = null /\ gs_ind s' = (if j =? 0 then 1 else j) /\
        0 < b /\ b mod 8 = 0 /\ b + 56 <= r_end r /\ r_end r <= 2 ^ 48 /\
        0 < av /\ av mod 8 = 0 /\ av + 8 * (n + 1) <= r_end ar /\ r_end ar <= 2 ^ 48⌝ -∗
      live b r -∗ int_cell b 0 (gs_ind s') -∗ int_cell b 4 (gs_err s') -∗ int_cell b 8 (gs_opt s') -∗
      pcell b 16 (gs_arg s') -∗ int_cell b 24 (gs_initialized s') -∗ pcell b 32 (gs_next s') -∗
      int_cell b 40 (gs_order s') -∗ int_cell b 44 (gs_first s') -∗ int_cell b 48 (gs_last s') -∗
      (⌜gs_next s' = null⌝ ∨ word_string DfracDiscarded (gs_next s') []) -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L73") (Some (TAtom "L83")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e' s q sq k0, ⌜entry_env e' n (mkPtr av (Obj av)) (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b
          (print_errors os (gs_err s)) /\
        ~ needs_init s /\ gs_ind s = j /\ gs_initialized s = 1 /\ 0 <= gs_order s <= 2 /\ getopt_bounds n j s /\
        0 <= j < n /\ ps !! Z.to_nat j = Some q /\ (k0 < length sq)%nat /\ sbyte sq k0 <> 0 /\
        gs_next s = ptr_add q (Z.of_nat k0) /\ gs_last s <= j /\
        0 < b /\ b mod 8 = 0 /\ b + 56 <= r_end r /\ r_end r <= 2 ^ 48 /\
        0 < av /\ av mod 8 = 0 /\ av + 8 * (n + 1) <= r_end ar /\ r_end ar <= 2 ^ 48⌝ -∗
      word_string DfracDiscarded q sq -∗ word_string DfracDiscarded (gs_next s) (drop k0 sq) -∗
      live b r -∗ int_cell b 0 j -∗ int_cell b 4 (gs_err s) -∗ int_cell b 8 (gs_opt s) -∗ pcell b 16 null -∗
      int_cell b 24 1 -∗ pcell b 32 (gs_next s) -∗ int_cell b 40 (gs_order s) -∗ int_cell b 44 (gs_first s) -∗
      int_cell b 48 (gs_last s) -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L75") (Some (TAtom "L83")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None
              (Exec (TAtom "start") (b_insts getopt_blk_start) (b_jump getopt_blk_start))) : gexpr) {{ Φ }}.
Proof.
  intros Hget Hpenv H0 H2 H4 H6 H8 H10 H12 H14 Hlen. subst n.
  iIntros "[%Hp (%s & Hs & %Hj & #Hk)] #Hos HG HK".
  destruct Hp as (Hav & Hal & Hfit & Har & Hn & Hjn).
  iAssert (∃ tail, ⌜gs_next s = null⌝ ∨ word_string DfracDiscarded (gs_next s) tail)%I as (tail) "#Hc".
  { iDestruct "Hk" as "[[_ [%Hn0 | (%t & Ht)]] | [_ Hcu]]"; [iExists []; by iLeft | iExists t; by iRight|].
    iDestruct (getopt_cursor_read with "Hcu") as "[%Hn0 | (%t & Ht & _)]"; [iExists []; by iLeft | iExists t; by iRight]. }
  iAssert ⌜needs_init s \/ gs_initialized s = 1 /\ 0 <= gs_order s <= 2 /\
    getopt_bounds (Z.of_nat (length ps)) j s⌝%I as %Hkp.
  { iDestruct "Hk" as "[[%H _] | [%H _]]"; iPureIntro; [left | right]; exact H. }
  iApply (GetoptEntry.wp_getopt_entry e (Z.of_nat (length ps)) (mkPtr av (Obj av)) p os lo li lonly pc penv
    b r s tail G with "Hs Hos Hc HG"); try (assumption || lia).
  iSplit.
  - iIntros (e' s' (Hst & Henv & Hnt)) "Hs' HG".
    iDestruct (entry_pre_select b r ps j s s' tail with "Hc Hs'") as
      "(%Hq & Hl & Hi & He & Ho & Ha & Hn & Hx & Hr & Hf & Hla & Hcur)"; try assumption.
    iDestruct "HK" as "[HK _]".
    iApply ("HK" $! e' s s' with "[%] Hl Hi He Ho Ha Hn Hx Hr Hf Hla Hcur HG").
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat (split; [first [assumption | lia] |]). first [assumption | lia].
  - iIntros (e' s' (Hst & Henv & Hni & Hnn & Htn)) "Hs' HG".
    iDestruct "Hk" as "[[%Hni' _] | [%Hin #Hcu]]"; [by exfalso|].
    iDestruct "Hc" as "[%Hn0 | #Hw]".
    { exfalso. destruct Hst as [(Hn' & _) | (_ & ->)]; [contradiction|]. apply Hnn. exact Hn0. }
    destruct Hin as (Hin & Hor & Hbd).
    iDestruct (entry_cluster b r ps j s s' tail with "[] Hw Hs'") as (q sq k0)
      "(%Hq & Hwq & Hwd & Hl & Hi & He & Ho & Ha & Hn & Hx & Hr & Hf & Hla)"; try assumption.
    { iRight. iFrame "Hcu". iPureIntro. auto. }
    iDestruct "HK" as "[_ HK]".
    iApply ("HK" $! e' s q sq k0 with "[%] Hwq Hwd Hl Hi He Ho Ha Hn Hx Hr Hf Hla HG").
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat (split; [first [assumption | lia] |]). first [assumption | lia].
Qed.

End entry_pre_wp.
