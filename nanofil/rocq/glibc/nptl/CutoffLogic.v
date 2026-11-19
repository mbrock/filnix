From Glibc Require Import Unit_nptl_alloca_cutoff_os.
From Glibc Require Import GlibcProgram.
(** Before glibc puts a buffer on the stack with alloca, it asks
    `c: __libc_alloca_cutoff(size)` whether the request is small enough.
    The getopt parser asks this question when it collects the candidates
    for an ambiguous long option. This module proves a call rule for the
    real function, captured in [CutoffCode](CutoffCode.v), and states
    exactly which memory the call reads.

    ## What the function reads

    The pinned source in nptl/alloca_cutoff.c compares the request with
    a quarter of the calling thread's `c: stackblock_size`, capped at
    64 KiB.

    ```c
    return size <= (MIN (__MAX_ALLOCA_CUTOFF,
                         THREAD_GETMEM (THREAD_SELF, stackblock_size) / 4
                         ?: __MAX_ALLOCA_CUTOFF * 4));
    ```

    A caller needs to know what memory the answer depends on. The
    compiled code asks the runtime which thread is running, then reads
    one eight-byte field of that thread's descriptor. When the quarter
    is at most 64 KiB, it asks and reads a second time. So the caller
    must hold a share of the descriptor's lifetime and a share of that
    field, and both reads then see the same value. Under Fil-C the
    macro `c: THREAD_SELF` is `c: zthread_self_cookie()`, and the field
    sits at offset 1720 of `c: struct pthread`. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic.
From Glibc Require Import OsWorld OsThread WordString FileInv LayoutTables CutoffLayout.
From Glibc Require OsThread WordString FileInv.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Import OsWorld OsWorld.L OsWorld.LG.

(** ## The answer

    The function's result depends only on the request and the field's
    value. These definitions state that answer in Gallina. *)

(** This is the byte offset of `c: stackblock_size` in `c: struct pthread`. *)
Definition off_stackblock_size : Z :=
  ltac:(layout_constant (CutoffLayout.field_offset "struct pthread" "stackblock_size")).

(** The limit is a quarter of the field's unsigned value, or 256 KiB when
    that quarter is zero, capped at 64 KiB. *)
Definition cutoff_limit (sz : Z) : Z :=
  let q := sz mod 2 ^ 64 / 4 in Z.min 65536 (if q =? 0 then 262144 else q).

(** The function returns 1 when the unsigned request fits under the limit
    and 0 otherwise. *)
Definition cutoff_bit (n sz : Z) : Z := if n mod 2 ^ 64 <=? cutoff_limit sz then 1 else 0.

(** ## A check that finds its own bound

    A check needs the accessed bytes to lie inside the object's region.
    When the caller owns shares of the object's lifetime and of the
    eight bytes being read, memory already guarantees that, so the
    caller does not have to state the region's end. *)
Section cell_check.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
Local Instance cell_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A read check of at most eight bytes at an owned cell succeeds, using
    shares of the lifetime and the cell instead of a stated bound. *)
Lemma wp_check_read_cell_dq f e ls l d lo hi al args rest j classes p b reg o v dq1 dq2 Φ :
  op_arg_classes (Check lo hi Read al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b -> raw_address (ptr_addr p) lo = b + o -> hi - lo <= 8 ->
  (b + o) mod al = 0 ->
  liveq dq1 b reg -∗ icellq dq2 b o v -∗
  ▷ (liveq dq1 b reg -∗ icellq dq2 b o v -∗ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (Check lo hi Read al) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using SafepointStable0.
  intros Hc Hx Hp Ha Hw Hal. iIntros "Hl Hc HK".
  iApply (wp_read_with registry wi ge (liveq dq1 b reg ∗ icellq dq2 b o v)
            (fun m => live_at m b reg /\ all_agree m (cell b o v)) _ _ [] with "[$Hl $Hc] [HK]").
  - iIntros (σ) "Hσ [Hl Hc]".
    iDestruct (ptsq_facts with "Hσ Hl") as %([Hlv _] & _).
    iDestruct (ptsq_facts with "Hσ Hc") as %(Hcl & _). iPureIntro. auto.
  - intros m fuel (Hlv & Hcl). destruct (cell_bounds _ _ _ _ _ Hlv Hcl) as [Ho He].
    apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
    apply op_check. rewrite Ha. apply (access_read _ b reg); [exact Hp | exact (proj1 Hlv) | lia | lia | exact Hal].
  - iNext. iIntros "[Hl Hc]". iApply ("HK" with "Hl Hc").
Qed.

End cell_check.

Import ProgramAbbreviations.
Section rule.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The thread's descriptor comes from the runtime's registered
    `c: zthread_self_cookie`, which the linked program must not define. *)
Context (Hself : registry (TAtom "zthread_self_cookie") = Some os_self_contract)
  (Hself_fn : find_fn ge (TAtom "zthread_self_cookie") = None)
  (Hself_sym : Term.lookup (TAtom "zthread_self_cookie") (ge_globals ge) = None).
(** The OS interpretation survives the runtime's safepoints. *)
Local Instance cutoff_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation cexpr := (language.expr (nanofil_lang registry ge)).

(** ## The call rule

    The rule takes any shares of the lifetime and the field and gives
    them back. A caller can therefore lend the whole lifetime for the
    call, or keep a read-only share for good. *)

(** Running the function on request n returns [cutoff_bit] n sz, where
    sz is the value of the calling thread's `c: stackblock_size`. The
    region's end follows from the shares, so only the address must fit. *)
Lemma wp_glibc_alloca_cutoff_cell fr n dq1 dq2 tb treg sz Φ :
  call_frame Unit_nptl_alloca_cutoff_os.fn___GI___libc_alloca_cutoff [WInt n] = Some fr ->
  ow_self w0 = mkPtr tb (Obj tb) -> 0 < tb -> tb + off_stackblock_size + 8 <= 2 ^ 64 ->
  liveq dq1 tb treg -∗ icellq dq2 tb off_stackblock_size sz -∗
  ▷ (liveq dq1 tb treg -∗ icellq dq2 tb off_stackblock_size sz -∗ Φ (Ret (WInt (cutoff_bit n sz)))) -∗
  WP (ERun fr : cexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hown Htb Hend. injection Hfr as <-. unfold off_stackblock_size in *. cbn in Hend.
  iIntros "Hl Hc HK".
  assert (Eq : forall x, x mod 2 ^ 64 mod 2 ^ 64 / 2 ^ ((2 mod 2 ^ 32) mod 64) = x mod 2 ^ 64 / 4).
  { intros x. rewrite Z.mod_mod; [reflexivity | lia]. }
  set (q := sz mod 2 ^ 64 / 4).
  assert (Hqm : q mod 2 ^ 64 = q).
  { unfold q. pose proof (Z.mod_pos_bound sz (2 ^ 64) ltac:(lia)). apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (Eqq : q = sz mod 2 ^ 64 / 4) by reflexivity. clearbody q.
  step.
  iApply OsThread.wp_zthread_self_cookie; [exact Hself | exact Hself_fn | exact Hself_sym | rewrite Hown; cbn; lia |].
  iNext. rewrite Hown. step.
  rule2 "Hl" "Hc" ltac:(eapply wp_check_read_cell_dq; inst;
    [reflexivity | vx | left; reflexivity | a2 | lia | a2]).
  rule2 "Hl" "Hc" ltac:(eapply wp_raw_load_read_dq; inst; [reflexivity | vx | left; reflexivity | a2]).
  step. step. rewrite !Eq -Eqq.
  rewrite Hqm.
  destruct (Z.eqb_spec q 0) as [Hq|Hq].
  - rewrite Hq. branch. step. step. step. step. branch. step. step.
    iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    replace ((if n mod 2 ^ 64 <=? (65536 mod 2 ^ 64) mod 2 ^ 64 then 1 else 0) mod 2 ^ 32) with (cutoff_bit n sz).
    + iApply ("HK" with "Hl Hc").
    + unfold cutoff_bit, cutoff_limit. cbv zeta. rewrite -Eqq Hq.
      change ((65536 mod 2 ^ 64) mod 2 ^ 64) with 65536. change (Z.min 65536 (if 0 =? 0 then 262144 else 0)) with 65536.
      destruct (_ <=? _); reflexivity.
  - rewrite (proj2 (Z.eqb_neq q (0 mod 2 ^ 64)) ltac:(change (0 mod 2 ^ 64) with 0; exact Hq)). branch. step. step.
    rewrite Hqm Hqm. change (65536 mod 2 ^ 64) with 65536.
    destruct (Z.ltb_spec 65536 q) as [Hb|Hb].
    + branch. step. step.
      iApply wp_ret; [reflexivity | reflexivity |]. iNext.
      replace ((if n mod 2 ^ 64 <=? (65536 mod 2 ^ 64) mod 2 ^ 64 then 1 else 0) mod 2 ^ 32) with (cutoff_bit n sz).
      * iApply ("HK" with "Hl Hc").
      * unfold cutoff_bit, cutoff_limit. cbv zeta. rewrite -Eqq (proj2 (Z.eqb_neq q 0) Hq) Z.min_l; [|lia].
        change ((65536 mod 2 ^ 64) mod 2 ^ 64) with 65536. destruct (_ <=? _); reflexivity.
    + branch. step.
      iApply OsThread.wp_zthread_self_cookie; [exact Hself | exact Hself_fn | exact Hself_sym | rewrite Hown; cbn; lia |].
      iNext. rewrite Hown. step.
      rule2 "Hl" "Hc" ltac:(eapply wp_check_read_cell_dq; inst;
        [reflexivity | vx | left; reflexivity | a2 | lia | a2]).
      rule2 "Hl" "Hc" ltac:(eapply wp_raw_load_read_dq; inst; [reflexivity | vx | left; reflexivity | a2]).
      step. step. rewrite !Eq -Eqq Hqm.
      rewrite (proj2 (Z.eqb_neq q (0 mod 2 ^ 64)) ltac:(change (0 mod 2 ^ 64) with 0; exact Hq)). branch. step. step.
      iApply wp_ret; [reflexivity | reflexivity |]. iNext.
      rewrite Hqm Hqm.
      replace ((if n mod 2 ^ 64 <=? q then 1 else 0) mod 2 ^ 32) with (cutoff_bit n sz).
      * iApply ("HK" with "Hl Hc").
      * unfold cutoff_bit, cutoff_limit. cbv zeta. rewrite -Eqq (proj2 (Z.eqb_neq q 0) Hq) Z.min_r; [|lia].
        destruct (_ <=? _); reflexivity.
Qed.

(** The same holds when the caller also states the region's end. *)
Lemma wp_glibc_alloca_cutoff fr n dq1 dq2 tb treg sz Φ :
  call_frame Unit_nptl_alloca_cutoff_os.fn___GI___libc_alloca_cutoff [WInt n] = Some fr ->
  ow_self w0 = mkPtr tb (Obj tb) -> 0 < tb -> tb + off_stackblock_size + 8 <= r_end treg -> r_end treg <= 2 ^ 63 ->
  liveq dq1 tb treg -∗ icellq dq2 tb off_stackblock_size sz -∗
  ▷ (liveq dq1 tb treg -∗ icellq dq2 tb off_stackblock_size sz -∗ Φ (Ret (WInt (cutoff_bit n sz)))) -∗
  WP (ERun fr : cexpr) {{ Φ }}.
Proof using Type*. intros Hfr Hown Htb Hend Hreg. apply wp_glibc_alloca_cutoff_cell; [exact Hfr | exact Hown | exact Htb | lia]. Qed.

(** A call site that binds the result to d continues with that answer. *)
Lemma wp_call_alloca_cutoff f e ls l d args rest j n dq1 dq2 tb treg sz Φ :
  find_fn ge (TAtom "__GI___libc_alloca_cutoff") = Some (Defined Unit_nptl_alloca_cutoff_os.fn___GI___libc_alloca_cutoff) ->
  map_option (arg_x ge e) args = Some [WInt n] ->
  ow_self w0 = mkPtr tb (Obj tb) -> 0 < tb -> tb + off_stackblock_size + 8 <= r_end treg -> r_end treg <= 2 ^ 63 ->
  liveq dq1 tb treg -∗ icellq dq2 tb off_stackblock_size sz -∗
  ▷ (liveq dq1 tb treg -∗ icellq dq2 tb off_stackblock_size sz -∗
     WP (ERun (mkFrame f (put d (WInt (cutoff_bit n sz)) e) ls None (Exec l rest j)) : cexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d W) (Global (TAtom "__GI___libc_alloca_cutoff")) args :: rest) j)) : cexpr) {{ Φ }}.
Proof using Type*.
  intros Hg Hx Hown Htb Hend Hreg. iIntros "Hl Hc HK".
  iApply wp_call_bind; [exact Hx | exact Hg | reflexivity |]. iNext.
  iApply (wp_glibc_alloca_cutoff with "Hl Hc"); [reflexivity | exact Hown | exact Htb | exact Hend | exact Hreg |].
  iNext. iIntros "Hl Hc". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  rewrite (Z.mod_small (cutoff_bit n sz)); [iApply ("HK" with "Hl Hc") | unfold cutoff_bit; destruct (_ <=? _); lia].
Qed.

(** ## A read-only share

    The parser's current rule for the cutoff takes no resource at all,
    yet the function reads the thread's memory. A read-only share of
    the descriptor's lifetime and field is the smallest resource that
    serves every call, because it can be copied. *)

(** [thread_stack_ro] holds read-only shares of the calling thread's
    descriptor lifetime and its `c: stackblock_size`. *)
Definition thread_stack_ro : iProp Σ :=
  ∃ tb treg sz, ⌜ow_self w0 = mkPtr tb (Obj tb) /\ 0 < tb /\ tb + off_stackblock_size + 8 <= r_end treg /\
                 r_end treg <= 2 ^ 63⌝ ∗
    liveq DfracDiscarded tb treg ∗ icellq DfracDiscarded tb off_stackblock_size sz.

(** The read-only share can be copied freely. *)
Global Instance thread_stack_ro_persistent : Persistent thread_stack_ro.
Proof using Type. rewrite /thread_stack_ro /liveq /icellq /ptsq. apply _. Qed.

(** With the read-only share, the call returns a 32-bit answer for any
    request, which is the form the parser's rule asks for. *)
Lemma wp_call_alloca_cutoff_ro f e ls l d args rest j n Φ :
  find_fn ge (TAtom "__GI___libc_alloca_cutoff") = Some (Defined Unit_nptl_alloca_cutoff_os.fn___GI___libc_alloca_cutoff) ->
  map_option (arg_x ge e) args = Some [WInt n] ->
  thread_stack_ro -∗
  ▷ (∀ x, ⌜0 <= x < 2 ^ 32⌝ -∗ WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : cexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d W) (Global (TAtom "__GI___libc_alloca_cutoff")) args :: rest) j)) : cexpr) {{ Φ }}.
Proof using Type*.
  intros Hg Hx. iIntros "(%tb & %treg & %sz & %Ht & Hl & Hc) HK". destruct Ht as (Hown & Htb & Hend & Hreg).
  iApply (wp_call_alloca_cutoff with "Hl Hc"); [exact Hg | exact Hx | exact Hown | exact Htb | exact Hend | exact Hreg |].
  iNext. iIntros "_ _". iApply "HK". iPureIntro. unfold cutoff_bit. destruct (_ <=? _); lia.
Qed.

(** ## Who can own the share

    Before this rule can serve the parser, someone must own the share.
    When Hello closes its streams, glibc writes to the same thread
    descriptor, so Hello owns that descriptor's whole lifetime. Nobody
    can keep a read-only share of a lifetime that someone else owns
    whole. The next section lends that whole lifetime for one call
    instead. *)

(** The read-only share contradicts the whole lifetime that the stream cleanup owns. *)
Lemma tcb_cleanup_thread_stack_ro : tcb_cleanup_inv (ow_self w0) ∗ thread_stack_ro ⊢ False.
Proof using Type.
  iIntros "[(%tb & %treg & %jb & %Ht & Hl & _) (%tb' & %treg' & %sz & %Ht' & Hq & _)]".
  destruct Ht as (Hs & _). destruct Ht' as (Hs' & _). rewrite Hs in Hs'. injection Hs' as <-.
  rewrite /live /liveq /pts /ptsq /=. iDestruct "Hl" as "[Hl _]". iDestruct "Hq" as "[Hq _]".
  iDestruct (pointsto_valid_2 with "Hl Hq") as %[Hv _].
  apply dfrac_valid_own_discarded in Hv. exfalso. exact (irreflexivity _ _ Hv).
Qed.

(** ## Borrowing the cleanup lifetime

    The parser should be able to ask for the cutoff without taking
    anything away from Hello's streams. Hello already owns the whole
    lifetime of the thread descriptor, so a call can borrow it and give
    it back unchanged. The only new memory the call needs is a share of
    the eight bytes that hold the stack size, and that share contains no
    lifetime. The fields that the stream cleanup writes keep their
    values. *)

(** The cutoff reads the thread's stack size, so the caller lends a
    share of those eight bytes, which hold sz. *)
Definition stack_size_cell (self : ptr) (dq : dfrac) (sz : Z) : iProp Σ :=
  ∃ tb, ⌜self = mkPtr tb (Obj tb)⌝ ∗ icellq dq tb off_stackblock_size sz.

(** The cutoff only reads the stack size, so the eight bytes that hold
    it can be frozen when Hello's main starts. After that nobody can
    change them, and every call to the cutoff can copy the frozen share.
    The lemma does not say where the bytes come from. The caller must
    find them in the starting memory. *)
Lemma stack_size_own tb sz : ow_self w0 = mkPtr tb (Obj tb) ->
  pts (cell tb off_stackblock_size sz) ==∗ □ stack_size_cell (ow_self w0) DfracDiscarded sz.
Proof using Type.
  intros Hs. iIntros "H". rewrite pts_ptsq. iMod (ptsq_persist with "H") as "#H".
  iModIntro. iModIntro. iExists tb. iSplit; [done | iExact "H"].
Qed.

(** A call borrows the cleanup lifetime and the stack-size bytes and
    returns both, binding d to the function's answer. *)
Lemma wp_call_alloca_cutoff_tcb f e ls l d args rest j n dq sz Φ :
  find_fn ge (TAtom "__GI___libc_alloca_cutoff") = Some (Defined Unit_nptl_alloca_cutoff_os.fn___GI___libc_alloca_cutoff) ->
  map_option (arg_x ge e) args = Some [WInt n] ->
  tcb_cleanup_inv (ow_self w0) -∗ stack_size_cell (ow_self w0) dq sz -∗
  ▷ (tcb_cleanup_inv (ow_self w0) -∗ stack_size_cell (ow_self w0) dq sz -∗
     WP (ERun (mkFrame f (put d (WInt (cutoff_bit n sz)) e) ls None (Exec l rest j)) : cexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d W) (Global (TAtom "__GI___libc_alloca_cutoff")) args :: rest) j)) : cexpr) {{ Φ }}.
Proof using Type*.
  intros Hg Hx. iIntros "(%tb & %treg & %jb & %Ht & Hl & Hcl & Hjb & Hch) (%tb' & %Hs' & Hc) HK".
  pose proof Ht as (Hs & Htb & _ & Hend & Hreg). rewrite Hs in Hs'. injection Hs' as <-.
  iApply wp_call_bind; [exact Hx | exact Hg | reflexivity |]. iNext.
  iApply (wp_glibc_alloca_cutoff_cell _ n (DfracOwn 1) dq tb treg sz with "Hl Hc");
    [reflexivity | exact Hs | exact Htb | unfold off_cancelhandling, off_stackblock_size in *; cbn in *; lia |].
  iNext. iIntros "Hl Hc". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  rewrite (Z.mod_small (cutoff_bit n sz)); [|unfold cutoff_bit; destruct (_ <=? _); lia].
  iApply ("HK" with "[Hl Hcl Hjb Hch] [Hc]").
  - iExists tb, treg, jb. iSplit; [iPureIntro; exact Ht|]. iFrame.
  - iExists tb. iSplit; [iPureIntro; exact Hs | iExact "Hc"].
Qed.

(** The loan joins Hello's cleanup ownership with a share of the stack
    size bytes, whatever value they hold. *)
Definition cutoff_loan (dq : dfrac) : iProp Σ :=
  tcb_cleanup_inv (ow_self w0) ∗ ∃ sz, stack_size_cell (ow_self w0) dq sz.

(** With the loan, the call returns the loan and a 32-bit answer for any
    request, which is the form the parser's rule asks for. *)
Lemma wp_call_alloca_cutoff_loan f e ls l d args rest j n dq Φ :
  find_fn ge (TAtom "__GI___libc_alloca_cutoff") = Some (Defined Unit_nptl_alloca_cutoff_os.fn___GI___libc_alloca_cutoff) ->
  map_option (arg_x ge e) args = Some [WInt n] ->
  cutoff_loan dq -∗
  ▷ (cutoff_loan dq -∗ ∀ x, ⌜0 <= x < 2 ^ 32⌝ -∗
     WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : cexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d W) (Global (TAtom "__GI___libc_alloca_cutoff")) args :: rest) j)) : cexpr) {{ Φ }}.
Proof using Type*.
  intros Hg Hx. iIntros "(Ht & %sz & Hc) HK".
  iApply (wp_call_alloca_cutoff_tcb with "Ht Hc"); [exact Hg | exact Hx |].
  iNext. iIntros "Ht Hc". iApply ("HK" with "[Ht Hc]"); [iFrame "Ht"; iExists sz; iExact "Hc"|].
  iPureIntro. unfold cutoff_bit. destruct (_ <=? _); lia.
Qed.

End rule.
