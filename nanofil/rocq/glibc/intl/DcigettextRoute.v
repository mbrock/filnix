From Glibc Require Import GlibcProgram.
(** GNU Hello translates getopt's messages through glibc's
    `c: __dcigettext`. In the C locale that function returns the message
    it was given, and this module proves the whole of that route, from the
    entry of the function to its return. It joins the proofs of the
    separate blocks: the prefix in DcigettextPre.v, the binding search in
    DcigettextDom.v, the allocation of the file name in DcigettextJoin.v,
    the copies in DcigettextCopy.v and the locale test in DcigettextC.v.
    When an allocation fails, the route ends through DcigettextFail.v
    and returns the same message.

    Some functions on the route are not proved here, so their behavior
    must be stated by the caller. They are the rwlock operations, the
    locale query, the cache search, malloc and stpcpy, and each premise
    names the resources that the call takes and gives back. The caller
    also states that the program runs in the C locale, that it is not
    privileged and that no domain was bound. These are conditions on the
    caller's state, not facts that this module proves about startup. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv LibioLogic LibioSetb WordString StrlenLogic StrlenWord.
From Glibc Require Import MemFwdCode GetoptLongPfxAlloc DcigettextCode DcigettextFree DcigettextExit DcigettextPreRules.
From Glibc Require Import DcigettextPre DcigettextDom DcigettextJoin DcigettextCopy DcigettextC.
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
Local Instance dci_route_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).

(** ## What the caller states

    A caller must say how the unproved functions behave, where the route's
    globals are and which memory it may read. Each of these needs a
    definition below, so that the statement of the route stays short. The
    callee resources themselves are lent separately. *)

(** Taking or releasing a lock changes what the caller holds, so each
    lock has a resource for every state it passes through. The prefix
    takes each read lock and the exit releases it, so L1 becomes L1' and
    then L1'', and likewise for L2. The tree lock goes from T to T''
    around a cache search that misses. *)
Definition dci_callees (lk1 lk2 lkt rt tc : ptr) (L1 L1' L1'' L2 L2' L2'' T T' T'' K C M : iProp Σ) (cv : ptr) : Prop :=
  registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)) /\
  find_fn ge (TAtom "zmemmove") = None /\ lookup (TAtom "zmemmove") (ge_globals ge) = None /\
  dci_stpcpy_rule /\ heap_fns ge /\ getopt_malloc_rule w0 registry ge M /\ dci_locale_rule 5 C cv /\
  dci_rdlock_rule lkt T T' /\ dci_unlock_rule lkt T' T'' /\
  (forall sb, dci_tfind_miss_rule (mkPtr sb (Obj sb)) rt tc K) /\
  dci_rdlock_rule lk1 L1 L1' /\ dci_rdlock_rule lk2 L2 L2' /\
  dci_unlock_rule lk1 L1' L1'' /\ dci_unlock_rule lk2 L2' L2''.

(** This predicate collects every callee rule except the one for
    stpcpy, because the proof of the captured stpcpy replaces that one. *)
Definition dci_others (lk1 lk2 lkt rt tc : ptr) (L1 L1' L1'' L2 L2' L2'' T T' T'' K C M : iProp Σ) (cv : ptr) : Prop :=
  registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)) /\
  find_fn ge (TAtom "zmemmove") = None /\ lookup (TAtom "zmemmove") (ge_globals ge) = None /\
  heap_fns ge /\ getopt_malloc_rule w0 registry ge M /\ dci_locale_rule 5 C cv /\
  dci_rdlock_rule lkt T T' /\ dci_unlock_rule lkt T' T'' /\
  (forall sb, dci_tfind_miss_rule (mkPtr sb (Obj sb)) rt tc K) /\
  dci_rdlock_rule lk1 L1 L1' /\ dci_rdlock_rule lk2 L2 L2' /\
  dci_unlock_rule lk1 L1' L1'' /\ dci_unlock_rule lk2 L2' L2''.

(** The real stpcpy needs its buffer to hold valid bytes before each
    call, so this predicate pairs the other callee rules with that
    stpcpy rule. *)
Definition dci_callees_r (lk1 lk2 lkt rt tc : ptr) (L1 L1' L1'' L2 L2' L2'' T T' T'' K C M : iProp Σ) (cv : ptr) : Prop :=
  dci_stpcpy_rule_r /\ dci_others lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv.

(** The old callee rules give the new ones. *)
Lemma dci_callees_r_of lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv :
  dci_callees lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_callees_r lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv.
Proof using Type.
  intros (H1 & H2 & H3 & Hcpy & H) . split; [exact (dci_stpcpy_rule_r_of Hcpy) | unfold dci_others; tauto].
Qed.

(** Hello uses glibc's own free, so the route cannot assume that the
    machine frees memory itself. This predicate therefore asks for a rule
    that says what one call to free does. Every other callee rule stays
    as it was. *)
Definition dci_others_f (lk1 lk2 lkt rt tc : ptr) (L1 L1' L1'' L2 L2' L2'' T T' T'' K C M : iProp Σ) (cv : ptr) : Prop :=
  registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)) /\
  find_fn ge (TAtom "zmemmove") = None /\ lookup (TAtom "zmemmove") (ge_globals ge) = None /\
  dci_free_rule /\ getopt_malloc_rule w0 registry ge M /\ dci_locale_rule 5 C cv /\
  dci_rdlock_rule lkt T T' /\ dci_unlock_rule lkt T' T'' /\
  (forall sb, dci_tfind_miss_rule (mkPtr sb (Obj sb)) rt tc K) /\
  dci_rdlock_rule lk1 L1 L1' /\ dci_rdlock_rule lk2 L2 L2' /\
  dci_unlock_rule lk1 L1' L1'' /\ dci_unlock_rule lk2 L2' L2''.

(** The route also calls stpcpy, so this predicate adds the stpcpy rule
    to the rules above. *)
Definition dci_callees_f (lk1 lk2 lkt rt tc : ptr) (L1 L1' L1'' L2 L2' L2'' T T' T'' K C M : iProp Σ) (cv : ptr) : Prop :=
  dci_stpcpy_rule_r /\ dci_others_f lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv.

(** A program without its own free still meets the new rule, because
    the machine's free does what the rule says. So the older predicate
    gives the new one. *)
Lemma dci_others_f_of lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv :
  dci_others lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_others_f lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv.
Proof using Type.
  intros (H1 & H2 & H3 & H4 & H). split_and!; try tauto. exact (dci_free_rule_heap H4).
Qed.

(** The same conversion works when the stpcpy rule comes along with the
    other rules. *)
Lemma dci_callees_f_of lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv :
  dci_callees_r lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_callees_f lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv.
Proof using Type. intros [Hs Ho]. split; [exact Hs | exact (dci_others_f_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ho)]. Qed.

(** These are the globals. The binding list head lives at db, entry 5 of
    the category index lives at ib + 5, and the privilege flag lives at
    sec. *)
Definition dci_globals (lk1 lk2 lkt rt tc dd : ptr) (db nb : Z) (nc : cap) (ib : Z) (ic : cap)
    (p276 p277 : ptr) (sec : Z) : Prop :=
  lookup (TAtom "glibc_dcigettext#tree_lock") (ge_globals ge) = Some lkt /\
  lookup (TAtom "glibc_dcigettext#root") (ge_globals ge) = Some rt /\
  lookup (TAtom "glibc_dcigettext#transcmp") (ge_globals ge) = Some tc /\
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) /\
  lookup (TAtom "_nl_state_lock") (ge_globals ge) = Some lk1 /\
  lookup (TAtom "__libc_setlocale_lock") (ge_globals ge) = Some lk2 /\
  lookup (TAtom "_nl_domain_bindings") (ge_globals ge) = Some (mkPtr db (Obj db)) /\
  lookup (TAtom "__GI__nl_default_dirname") (ge_globals ge) = Some dd /\
  lookup (TAtom "_nl_category_names") (ge_globals ge) = Some (mkPtr nb nc) /\
  lookup (TAtom "_nl_category_name_idxs") (ge_globals ge) = Some (mkPtr ib ic) /\
  lookup (TAtom "glibc_dcigettext#str.276") (ge_globals ge) = Some p276 /\
  lookup (TAtom "glibc_dcigettext#str.277") (ge_globals ge) = Some p277 /\
  lookup (TAtom "__libc_enable_secure") (ge_globals ge) = Some (mkPtr sec (Obj sec)).

(** Every read of that memory must stay in bounds. This predicate bounds
    the regions dbreg, ireg and secreg, the index byte k and the place of
    category name k. *)
Definition dci_bounds (db : Z) (dbreg : region) (nb ib : Z) (ic : cap) (ireg : region) (k sec : Z) (secreg : region) :
    Prop :=
  (0 < db /\ db mod 8 = 0 /\ db + 8 <= r_end dbreg /\ r_end dbreg <= 2 ^ 48) /\
  (ic = Obj ib \/ ic = Ro ib) /\ (0 < ib /\ ib + 6 <= r_end ireg /\ r_end ireg <= 2 ^ 48) /\
  (0 <= k < 256 /\ 0 <= nb /\ nb + k < 2 ^ 48) /\
  (0 < sec /\ sec mod 4 = 0 /\ sec + 4 <= r_end secreg /\ r_end secreg <= 2 ^ 48).

(** The route reads some memory and changes none of it, so the caller
    lends it for one call and gets it back unchanged. That memory holds
    the domain string, category name k and the locale name "C". It also
    holds the two literals of the file name, the null head of the binding
    list, index byte k and the privilege flag, which reads 0. *)
Definition dci_reads (dom : ptr) (ds : list Z) (dqd : dfrac) (nb : Z) (nc : cap) (k : Z) (cat : list Z) (dqc : dfrac)
    (cv p276 p277 : ptr) (db : Z) (dqb : dfrac) (dbreg : region) (ib : Z) (dqi : dfrac) (ireg : region)
    (sec : Z) (dqs : dfrac) (secreg : region) : iProp Σ :=
  word_string dqd dom ds ∗ word_string dqc (mkPtr (nb + k) nc) cat ∗
  word_string DfracDiscarded cv [67] ∗ word_string DfracDiscarded p276 [47] ∗
  word_string DfracDiscarded p277 [46; 109; 111] ∗
  liveq dqb db dbreg ∗ pcellq dqb db 0 null ∗ liveq dqi ib ireg ∗ bytesq dqi ib 5 [k] ∗
  liveq dqs sec secreg ∗ int_cellq dqs sec 0 0.

(** ## The C-locale route *)

(** The route starts with the domain dom, a nonnull message id, category
    5 and no plural. It returns the message id on every path. The caller
    gets back the memory it lent, the callee resources in their final
    states, and errno holding the 32-bit value that it held at entry. *)
Lemma wp_dci_route_f e dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    msgid lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy} :
  dci_callees_f lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  lookup (TAtom "v0") e = Some (WPtr dom) -> lookup (TAtom "v2") e = Some (WPtr msgid) ->
  lookup (TAtom "v6") e = Some (WInt 0) -> lookup (TAtom "v10") e = Some (WInt 5) -> 0 < ptr_addr msgid < 2 ^ 64 ->
  dci_reads dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg -∗
  L1 -∗ L2 -∗ T -∗ K -∗ C -∗ M -∗ errno_own eb bs -∗
  ▷ (dci_reads dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg -∗
     L1'' -∗ L2'' -∗ T'' -∗ K -∗ C -∗ M -∗ errno_own eb (le_bytes (dci_w bs) 4) -∗ Φ (Ret (WPtr msgid))) -∗
  WP (ERun (mkFrame glibc_dcigettext e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros (Hcpy & Hmv & Hmvf & Hmvs & Hheap & Hmal & Hloc & Hrt1 & Hut & Htf & Hr1 & Hr2 & Hu1 & Hu2)
    (Hlkt & Hrt & Htc & Hge & Hlk1 & Hlk2 & Hdb & Hdd & Hcn & Hci & H276 & H277 & Hsec)
    ((Hdb0 & Hdb8 & Hdbend & Hdbr) & Hic & (Hib0 & Hibend & Hibr) & (Hk & Hnb & Hnbk) & (Hsec0 & Hsec4 & Hsecend & Hsecr))
    Hv0 Hv2 Hv6 Hv10 Hm.
  iIntros "(Hdom & Hcat & #Hcv & #H276 & #H277 & Hnl & Hnc & Hil & Hib & Hsecl & Hsecb) HL1 HL2 HT HK HC HM Herr HΦ".
  iDestruct (dci_ws_bounds with "Hdom") as "[%Hdomb Hdom]".
  iApply (wp_dci_pre eb Herr e dom msgid lk1 lk2 L1 L1' L2 L2' bs C cv lkt T T' T'' rt tc K
    with "HL1 HL2 Herr HC HT HK"); try first [assumption | lia].
  iNext. iIntros (e1 xs xreg rl sb sreg (Henv1 & (Hxs0 & Hxs16 & Hxre & Hxsb) & Hxk & Hsb))
    "Hxl Hxc _ _ _ _ _ _ _ Herr HL1 HL2 HC HT HK".
  assert (Hxs8 : xs mod 8 = 0) by (Z.div_mod_to_equations; lia).
  pose proof (dci_w_range bs) as Hs.
  iApply (wp_dci_dom with "Hnl Hnc Hil Hib Hcv HC"); try first [eassumption | lia].
  iNext. iIntros (e2 (Henv2 & Hv7 & Hv9)) "Hnl Hnc Hil Hib HC".
  iApply (wp_dci_join_fr eb Herr _ xs xreg _ _ _ _ _ _ _ _ _ _ _ _ _ L1' L1'' L2' L2'' with "Hcat Hdom HM Hxl Hxc HL1 HL2 Herr");
    try first [eassumption | lia].
  iNext. iSplit.
  { iIntros "_ _ HL1 HL2 Herr Hcat Hdom HM".
    iApply ("HΦ" with "[$Hdom $Hcat $Hcv $H276 $H277 $Hnl $Hnc $Hil $Hib $Hsecl $Hsecb] HL1 HL2 HT HK HC HM Herr"). }
  iIntros (e3 xd (Henv3 & Hv224 & Hv9' & Hv226 & Hv232 & Hxd0 & Hxd16 & Hxdend)) "Ho Hcat Hdom HM Hxl Hxc HL1 HL2 Herr".
  iApply (wp_dci_copy_r_fr eb Herr _ xs xreg _ _ _ _ _ _ _ _ _ _ _ xd p276 p277 _ _ L1' L1'' L2' L2''
    with "Ho Hcat Hdom Hcv H276 H277 HM Hxl Hxc HL1 HL2 Herr"); try first [eassumption | lia].
  iNext. iSplit.
  { iIntros "_ _ HL1 HL2 Herr Hcat Hdom HM".
    iApply ("HΦ" with "[$Hdom $Hcat $Hcv $H276 $H277 $Hnl $Hnc $Hil $Hib $Hsecl $Hsecb] HL1 HL2 HT HK HC HM Herr"). }
  iIntros (e4 sl (Henv4 & Hv224' & Hv232' & Hv254 & Hsl0 & Hslend))
    "Hdl Hsl Hb0 Hb1 Hcat Hdom HM Hxl Hxc HL1 HL2 Herr".
  assert (0 <= req_extent (heap_req 16 (Z.of_nat (length cat + length ds) + 5))) by (cbn; Z.div_mod_to_equations; lia).
  pose proof Henv4 as (Hv17 & Hc0 & _ & _ & _ & Hv2' & Hv6' & _ & _ & Hv69 & _).
  iApply (wp_dci_c_locale_fr eb Herr e4 cv sl _ 0 0 sec secreg dqs xs xreg xd _ (dci_w bs) msgid lk1 lk2 L1' L1'' L2' L2''
    with "Hcv Hsecl Hsecb Hsl Hb0 Hb1 Hxl Hxc Hdl HL1 HL2 Herr"); try first [eassumption | reflexivity | cbn [r_end]; lia].
  iNext. iIntros "_ _ Hsecl Hsecb HL1 HL2 Herr".
  iApply ("HΦ" with "[$Hdom $Hcat $Hcv $H276 $H277 $Hnl $Hnc $Hil $Hib $Hsecl $Hsecb] HL1 HL2 HT HK HC HM Herr").
Qed.

(** This corollary keeps the statement that assumed the model's heap functions. *)
Lemma wp_dci_route_r e dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    msgid lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy} :
  dci_callees_r lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  lookup (TAtom "v0") e = Some (WPtr dom) -> lookup (TAtom "v2") e = Some (WPtr msgid) ->
  lookup (TAtom "v6") e = Some (WInt 0) -> lookup (TAtom "v10") e = Some (WInt 5) -> 0 < ptr_addr msgid < 2 ^ 64 ->
  dci_reads dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg -∗
  L1 -∗ L2 -∗ T -∗ K -∗ C -∗ M -∗ errno_own eb bs -∗
  ▷ (dci_reads dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg -∗
     L1'' -∗ L2'' -∗ T'' -∗ K -∗ C -∗ M -∗ errno_own eb (le_bytes (dci_w bs) 4) -∗ Φ (Ret (WPtr msgid))) -∗
  WP (ERun (mkFrame glibc_dcigettext e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof using Type*. intros Hc. eapply wp_dci_route_f; first [exact (dci_callees_f_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc) | exact _]. Qed.

(** This corollary keeps the statement of the route that assumed the old
    stpcpy rule. *)
Lemma wp_dci_route e dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    msgid lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy} :
  dci_callees lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  lookup (TAtom "v0") e = Some (WPtr dom) -> lookup (TAtom "v2") e = Some (WPtr msgid) ->
  lookup (TAtom "v6") e = Some (WInt 0) -> lookup (TAtom "v10") e = Some (WInt 5) -> 0 < ptr_addr msgid < 2 ^ 64 ->
  dci_reads dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg -∗
  L1 -∗ L2 -∗ T -∗ K -∗ C -∗ M -∗ errno_own eb bs -∗
  ▷ (dci_reads dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg -∗
     L1'' -∗ L2'' -∗ T'' -∗ K -∗ C -∗ M -∗ errno_own eb (le_bytes (dci_w bs) 4) -∗ Φ (Ret (WPtr msgid))) -∗
  WP (ERun (mkFrame glibc_dcigettext e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof using Type*. intros Hc. pose proof (dci_callees_r_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc) as Hr. eapply wp_dci_route_r; first [exact Hr | exact _]. Qed.
End rules.
