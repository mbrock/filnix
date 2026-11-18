(** When getopt reports a bad option, gettext translates the message
    and glibc prints it to stderr. GNU Hello's proof assumes two rules
    for these reports, one for short options and one for long options.
    Each rule names a resource G that the caller holds between reports.
    This module proves both rules for each state of the G that Hello
    holds after startup, from the objects that
    [HelloStartGetopt](HelloStartGetopt.v) gives.
    [HelloStartHdRules](HelloStartHdRules.v) then hides the state. The
    proof of glibc's formatter is not finished yet, so this module
    assumes its contract for now. *)

From Glibc Require Import GlibcTactics GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Run Semantics Pieces Heap Logic MemLogic StringLogic ExternalCalls.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv WordString GlibcSpec PrintfSpec GetoptDiag GetoptLongDiag
  DcgettextLocale HelloGlibcDebts HelloGetoptDiagGettext HelloGetoptDiagLock HelloGetoptDiagMsgs HelloGettextLocaleConst
  HelloGettextDomain HelloImageModule HelloImageLoad HelloImageEarly HelloImageKept HelloImageLayout HelloStartFacts
  HelloGetoptFormats HelloGetoptDiagImage HelloStartGetopt HelloGettextLink HiAtexitAlloc HelloGlibcMainAlloc
  AllocRo LibioFputsSpec.
From Glibc Require LibioCleanupExit.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** ## A value that the caller does not know

    Startup sets a flag for a privileged process, and the caller does
    not know its value. So G must hide that value. When both rules hold
    for every value with a property P, they also hold for a G that hides
    the value and keeps only P. The message T then hides it too. *)

Section hide.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w : os_world) (r : name -> option (contract os_world)) (ge : genv).

Lemma getopt_diag_rule_ex {A} (P : A -> Prop) (G : A -> iProp Σ) (T : A -> ptr -> ptr -> iProp Σ) fp dom x0 :
  P x0 -> (forall v, P v -> getopt_diag_rule w r ge (G v) (T v) fp dom) ->
  getopt_diag_rule w r ge (∃ v, ⌜P v⌝ ∗ G v) (fun mid q => ∃ v, ⌜P v⌝ ∗ T v mid q)%I fp dom.
Proof using Type.
  intros H0 H. destruct (H x0 H0) as (Hd & Hf & _). refine (conj Hd (conj Hf (conj _ (conj _ _)))).
  - iIntros "(%v & %Hv & HG)". destruct (H v Hv) as (_ & _ & Hc & _). iDestruct (Hc with "HG") as (dq reg) "[Hl Hb]".
    iExists dq, reg. iFrame "Hl". iIntros "Hl". iExists v. iSplit; [done|]. iApply ("Hb" with "Hl").
  - intros f e ls l d args rest j mid Φ Hm Hx. iIntros "(%v & %Hv & HG) HK". destruct (H v Hv) as (_ & _ & _ & Ht & _).
    iApply (Ht with "HG"); [exact Hm | exact Hx |]. iNext. iIntros (q) "HT". iApply "HK". iExists v. iSplit; [done|]. iExact "HT".
  - intros f e ls l d args rest j mid q a0 s0 c Φ Hm Hc Hx. iIntros "(%v & %Hv & HT) Ha HK".
    destruct (H v Hv) as (_ & _ & _ & _ & Hp).
    iApply (Hp with "HT Ha"); [exact Hm | exact Hc | exact Hx |]. iNext. iIntros (x) "HG". iApply "HK". iExists v.
    iSplit; [done|]. iExact "HG".
Qed.

Lemma getopt_ldiag_rule_ex {A} (P : A -> Prop) (G : A -> iProp Σ) (T : A -> ptr -> ptr -> iProp Σ) fp dom x0 :
  P x0 -> (forall v, P v -> getopt_ldiag_rule w r ge (G v) (T v) fp dom) ->
  getopt_ldiag_rule w r ge (∃ v, ⌜P v⌝ ∗ G v) (fun mid q => ∃ v, ⌜P v⌝ ∗ T v mid q)%I fp dom.
Proof using Type.
  intros H0 H. destruct (H x0 H0) as (Hd & Hf & _). refine (conj Hd (conj Hf (conj _ (conj _ (conj _ (conj _ _)))))).
  - iIntros "(%v & %Hv & HG)". destruct (H v Hv) as (_ & _ & Hc & _). iDestruct (Hc with "HG") as (dq reg) "[Hl Hb]".
    iExists dq, reg. iFrame "Hl". iIntros "Hl". iExists v. iSplit; [done|]. iApply ("Hb" with "Hl").
  - intros f e ls l d args rest j mid Φ Hm Hx. iIntros "(%v & %Hv & HG) HK". destruct (H v Hv) as (_ & _ & _ & Ht & _).
    iApply (Ht with "HG"); [exact Hm | exact Hx |]. iNext. iIntros (q) "HT". iApply "HK". iExists v. iSplit; [done|]. iExact "HT".
  - intros f e ls l d args rest j mid q a0 s0 pfx sp nm sn Φ Hm Hx. iIntros "(%v & %Hv & HT) Ha Hp Hn HK".
    destruct (H v Hv) as (_ & _ & _ & _ & Hp & _).
    iApply (Hp with "HT Ha Hp Hn"); [exact Hm | exact Hx |]. iNext. iIntros (x) "HG". iApply "HK". iExists v.
    iSplit; [done|]. iExact "HG".
  - intros f e ls l d args rest j fmt pfx sp nm sn Φ Hl Hx. iIntros "(%v & %Hv & HG) Hp Hn HK".
    destruct (H v Hv) as (_ & _ & _ & _ & _ & Hp & _).
    iApply (Hp with "HG Hp Hn"); [exact Hl | exact Hx |]. iNext. iIntros (x) "HG". iApply "HK". iExists v.
    iSplit; [done|]. iExact "HG".
  - intros f e ls l d args rest j fmt Φ Hl Hx. iIntros "(%v & %Hv & HG) HK".
    destruct (H v Hv) as (_ & _ & _ & _ & _ & _ & Hp).
    iApply (Hp with "HG"); [exact Hl | exact Hx |]. iNext. iIntros (x) "HG". iApply "HK". iExists v.
    iSplit; [done|]. iExact "HG".
Qed.

(** A caller often holds more than the report needs, and it lends that
    part too. The extra part N waits beside the message between the two
    calls and comes back with G. *)
Lemma getopt_diag_rule_sep_l (N G : iProp Σ) T fp dom :
  getopt_diag_rule w r ge G T fp dom -> getopt_diag_rule w r ge (N ∗ G) (fun mid q => N ∗ T mid q)%I fp dom.
Proof using Type.
  intros (Hd & Hf & Hcap & Hgt & Hfx). refine (conj Hd (conj Hf (conj _ (conj _ _)))).
  - iIntros "[HN HG]". iDestruct (Hcap with "HG") as (dq reg) "[Hc Hb]".
    iExists dq, reg. iFrame "Hc". iIntros "Hc". iFrame "HN". iApply ("Hb" with "Hc").
  - intros f e ls l d args rest j mid Φ Hm Hx. iIntros "[HN HG] HK".
    iApply (Hgt with "HG"); [exact Hm | exact Hx |]. iNext. iIntros (q) "HT". iApply ("HK" with "[$HN $HT]").
  - intros f e ls l d args rest j mid q a0 s0 c Φ Hm Hc Hx. iIntros "[HN HT] Hs HK".
    iApply (Hfx with "HT Hs"); [exact Hm | exact Hc | exact Hx |]. iNext. iIntros (x) "HG".
    iApply ("HK" with "[$HN $HG]").
Qed.

Lemma getopt_ldiag_rule_sep_l (N G : iProp Σ) T fp dom :
  getopt_ldiag_rule w r ge G T fp dom -> getopt_ldiag_rule w r ge (N ∗ G) (fun mid q => N ∗ T mid q)%I fp dom.
Proof using Type.
  intros (Hd & Hf & Hcap & Hgt & Hfx & H140 & H141).
  refine (conj Hd (conj Hf (conj _ (conj _ (conj _ (conj _ _)))))).
  - iIntros "[HN HG]". iDestruct (Hcap with "HG") as (dq reg) "[Hc Hb]".
    iExists dq, reg. iFrame "Hc". iIntros "Hc". iFrame "HN". iApply ("Hb" with "Hc").
  - intros f e ls l d args rest j mid Φ Hm Hx. iIntros "[HN HG] HK".
    iApply (Hgt with "HG"); [exact Hm | exact Hx |]. iNext. iIntros (q) "HT". iApply ("HK" with "[$HN $HT]").
  - intros f e ls l d args rest j mid q a0 s0 pfx sp nm sn Φ Hm Hx. iIntros "[HN HT] Ha Hp Hn HK".
    iApply (Hfx with "HT Ha Hp Hn"); [exact Hm | exact Hx |]. iNext. iIntros (x) "HG".
    iApply ("HK" with "[$HN $HG]").
  - intros f e ls l d args rest j fmt pfx sp nm sn Φ Hm Hx. iIntros "[HN HG] Hp Hn HK".
    iApply (H140 with "HG Hp Hn"); [exact Hm | exact Hx |]. iNext. iIntros (x) "HG".
    iApply ("HK" with "[$HN $HG]").
  - intros f e ls l d args rest j fmt Φ Hm Hx. iIntros "[HN HG] HK".
    iApply (H141 with "HG"); [exact Hm | exact Hx |]. iNext. iIntros (x) "HG".
    iApply ("HK" with "[$HN $HG]").
Qed.

End hide.

(** ## The formats in the image *)

(** The image places getopt's nine messages at the objects that
    [HelloImageKept](HelloImageKept.v) lists. *)
Lemma hello_msg_at : dgx_msg_at img_globals hello_msg_bases.
Proof.
  destruct hello_image_kept as (g & m & E & Hat & _). destruct (hello_loaded_tables g m E) as [<- _]. exact Hat.
Qed.

(** The nine formats that the formatter bridge names are the nine
    messages, in the same order. *)
Lemma getopt_fmt_texts : getopt_fmt_names = dgx_msg_names /\ map getopt_fmt getopt_fmt_names = dgx_msg_texts.
Proof. split; vm_compute; reflexivity. Qed.

Section lends.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Import ProgramAbbreviations.

(** The read-only half of Hello's private state lends each format, as
    the formatter bridge asks. It never runs out. *)
Lemma hello_getopt_ws n mid : ge_globals ge = img_globals ->
  In n getopt_fmt_names -> lookup (TAtom n) (ge_globals ge) = Some mid ->
  hello_getopt_ro ⊢ ∃ dq, word_string dq mid (getopt_fmt n) ∗ printf_ro ∗
    (word_string dq mid (getopt_fmt n) -∗ hello_getopt_ro).
Proof using Type.
  intros Hg Hin Hl. rewrite Hg in Hl. destruct getopt_fmt_texts as [En Et].
  rewrite En in Hin. apply list_elem_of_In, list_elem_of_lookup_1 in Hin as (k & Hk).
  pose proof hello_msg_at as Hat. destruct (Forall2_lookup_l _ _ _ _ _ Hat Hk) as ([b reg] & Hb & Hl').
  rewrite Hl in Hl'. injection Hl' as ->.
  assert (Ht : dgx_msg_texts !! k = Some (getopt_fmt n)).
  { rewrite <- Et, En. change (map getopt_fmt dgx_msg_names) with (getopt_fmt <$> dgx_msg_names).
    rewrite list_lookup_fmap Hk. reflexivity. }
  iIntros "#Hro". iPoseProof "Hro" as "(Hm & _ & _ & _ & _ & _ & _ & _ & _ & Hpr)".
  rewrite /dgx_msgs. iDestruct (big_sepL2_lookup with "Hm") as "#Hw"; [exact Hb | exact Ht|].
  iExists DfracDiscarded. iSplitR; [iExact "Hw"|]. iSplitR; [iExact "Hpr"|]. iIntros "_". iExact "Hro".
Qed.

End lends.

(** ## The cache's allocator state

    A translation reads whether the allocator is idle. Hello's
    read-only objects already record that fact, so G can copy it from
    them. *)

Section cache.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

Lemma hello_gettext_cache_of_ro ge (o : hello_objs) : hello_ro ge o ⊢ hello_gettext_cache o.
Proof using Type.
  rewrite /hello_ro /hello_gettext_cache /hi_malloc_state.
  iIntros "(_ & _ & _ & _ & _ & _ & _ & H & _)". iExact "H".
Qed.

End cache.

(** ## The two rules for Hello *)

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w : os_world) (fr : word -> mem -> option (res unit * mem)) (Hfr : frees_heap fr).

(** This is the linked Hello program in world w. *)
Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
#[local] Instance hello_rules_program : GlibcProgram Σ := program_of w glibc_os_registry hge.

(** errno lives where the image puts `c: __libc_errno`. *)
Local Abbreviation eb := (img_a "__libc_errno").
Context (Herr : ow_errno w = Some (mkPtr eb (Obj eb))).

(** Nobody has proved glibc's formatter or the C locale after startup
    yet. Until then, the formatter's contract and the place of the
    locale's cells are hypotheses. *)
Context `{Hvf : !HasSpec glibc_os_registry (os_wi w) hge (TAtom "__vfprintf_internal") vfprintf_spec}.
Context (gb go : Z) (greg : region) (dqg : dfrac) (lp : ptr) (lb : Z) (lreg : region) (dql dqn dqt : dfrac)
  (treg : region) (cv : ptr) (Hloc : locale_cells gb go greg lp lb lreg).

(** The thread's object lies at tb. Each lock reads a share of the
    thread's id, and the translation reads a share of the privilege
    flag. *)
Context (i1 i2 i3 : dfrac) (tb : Z) (dqs : dfrac).

(** Hello reports to stderr. Between reports, F keeps the read-only
    objects that the reports read. These are Hello's own constants, the
    stream jump tables and the allocator's idle state. Lm lends the nine
    messages. *)
Local Abbreviation ob := hello_image_objs.
Definition hello_dg_F : iProp Σ := hello_getopt_ro ∗ fputs_ro (ho_vb ob) ∗ malloc_ro.
Definition hello_dg_Lm : iProp Σ := dgx_msgs hello_msg_bases.
Definition hello_dg_Q : Z -> Z -> iProp Σ := getopt_q eb hello_dg_F.

(** This is G for one value v of the privilege flag and one thread id
    tid. *)
Definition hello_dg_G (v tid : Z) : iProp Σ :=
  dlk_G eb hello_dom libc_domain_text DfracDiscarded (ptr_addr hello_nb) (ptr_cap hello_nb) lc_messages_off lc_messages
    DfracDiscarded cv hello_p276 hello_p277 hello_db.1 (DfracOwn 1) hello_db.2 hello_ib.1 DfracDiscarded hello_ib.2
    hello_sec.1 dqs hello_sec.2 ob (DfracOwn 1) hello_root.1 0 hello_root.2 gb go greg dqg lp lb lreg dql dqn dqt treg
    hello_lk1.1 hello_lk1.2 i1 hello_lk2.1 hello_lk2.2 i2 hello_lkt.1 hello_lkt.2 i3 tb tid (ho_vb ob) (ho_sb ob)
    (ho_sreg ob) (ho_err ob) hello_dg_F hello_dg_Lm v.

Definition hello_dg_T (v tid : Z) (mid q : ptr) : iProp Σ :=
  dlk_T eb hello_dom libc_domain_text DfracDiscarded (ptr_addr hello_nb) (ptr_cap hello_nb) lc_messages_off lc_messages
    DfracDiscarded cv hello_p276 hello_p277 hello_db.1 (DfracOwn 1) hello_db.2 hello_ib.1 DfracDiscarded hello_ib.2
    hello_sec.1 dqs hello_sec.2 ob (DfracOwn 1) hello_root.1 0 hello_root.2 gb go greg dqg lp lb lreg dql dqn dqt treg
    hello_lk1.1 hello_lk1.2 i1 hello_lk2.1 hello_lk2.2 i2 hello_lkt.1 hello_lkt.2 i3 tb tid (ho_vb ob) (ho_sb ob)
    (ho_sreg ob) (ho_err ob) hello_dg_F hello_dg_Lm v mid q.

(** Every image fact that the diagnostic rules need holds for Hello. *)
Lemma hello_dg_premises v : 0 <= v < 2 ^ 32 ->
  dlk_premises eb hello_dom (ptr_addr hello_nb) (ptr_cap hello_nb) lc_messages_off hello_p276 hello_p277
    hello_db.1 hello_db.2 hello_ib.1 (Ro hello_ib.1) hello_ib.2 hello_sec.1 hello_sec.2 hello_tc hello_dd ob
    hello_root.1 0 hello_root.2 gb go greg lp lb lreg (lock_ptr hello_lk1) hello_lk1.1 hello_lk1.2
    (lock_ptr hello_lk2) hello_lk2.1 hello_lk2.2 (lock_ptr hello_lkt) hello_lkt.1 hello_lkt.2 (ho_err ob)
    hello_dg_F hello_dg_Q v.
Proof using Hfr Hloc.
  intros Hv. assert (Hk : 0 <= lc_messages_off < 256) by (vm_compute; split; congruence).
  assert (Hf : 0 <= ptr_addr (ho_err ob) < 2 ^ 64) by (vm_compute; split; congruence).
  destruct (hello_dlk_image w fr lc_messages_off (ho_err ob) Hk Hf)
    as (A2 & A3 & A4 & P1 & P2 & P3 & Rt & Dg & Db & Fx & Dm & Fp).
  unfold dlk_premises. split_and!; try assumption; try tauto; try lia.
  - exact (hello_link_all fr Hfr).
  - intros x m. rewrite /hello_dg_Q /getopt_q. iIntros "($ & $ & $)".
Qed.

(** F lends each format with the formatter's read-only data, as the
    formatter bridge asks. *)
Lemma hello_dg_ws n mid : In n getopt_fmt_names -> lookup (TAtom n) (ge_globals hge) = Some mid ->
  hello_dg_F ⊢ ∃ dq, word_string dq mid (getopt_fmt n) ∗ printf_ro ∗ fputs_ro (ho_vb ob) ∗ malloc_ro ∗
    (word_string dq mid (getopt_fmt n) -∗ hello_dg_F).
Proof using Type.
  intros Hin Hl. rewrite /hello_dg_F. iIntros "(Hg & #Hf & #Hm)".
  iDestruct (hello_getopt_ws (glibc_program := hello_rules_program) n mid eq_refl Hin Hl with "Hg") as (dq) "(Hw & #Hp & Hb)".
  iExists dq. iSplitL "Hw"; [iExact "Hw"|]. iSplitR; [iExact "Hp"|]. iSplitR; [iExact "Hf"|].
  iSplitR; [iExact "Hm"|]. iIntros "Hw". iSplitL; [iApply ("Hb" with "Hw")|]. iSplit; [iExact "Hf" | iExact "Hm"].
Qed.

Lemma hello_dg_HQ x m : m = 0 \/ m = 2 ^ 32 - 1 -> errno_any eb ∗ hello_dg_F ⊢ hello_dg_Q x m.
Proof using Type. exact (getopt_q_tidy eb hello_dg_F x m). Qed.

(** The messages lie at positive addresses below 2^64. *)
Lemma hello_dg_msgs_pos mid : diag_msg hge mid \/ ldiag_msg hge mid \/
  lookup (TAtom "glibc_getopt#str.140") img_globals = Some mid \/
  lookup (TAtom "glibc_getopt#str.141") img_globals = Some mid -> 0 < ptr_addr mid < 2 ^ 64.
Proof using Type.
  unfold diag_msg, ldiag_msg. cbn [ge_globals]. rewrite !List.Exists_cons List.Exists_nil.
  intros H; repeat destruct H as [H|H]; try contradiction; vm_compute in H; injection H as <-; vm_compute; split; congruence.
Qed.

(** The rule for short options holds for G and T, for each value v of
    the flag and each thread id. *)
Lemma hello_dg_diag v tid : 0 <= v < 2 ^ 32 ->
  getopt_diag_rule w glibc_os_registry hge (hello_dg_G v tid) (hello_dg_T v tid) (ho_err ob) hello_dom.
Proof using Hfr Herr Hvf Hloc.
  intros Hv.
  eapply (hello_getopt_diag_rule_lock (glibc_program := hello_rules_program) eb Herr LibioCleanupExit.holds_os_glibc) with (Q := hello_dg_Q)
    (ic := Ro hello_ib.1) (tc := hello_tc) (dd := hello_dd) (lk1 := lock_ptr hello_lk1)
    (lk2 := lock_ptr hello_lk2) (lkt := lock_ptr hello_lkt).
  - exact (hello_dg_premises v Hv).
  - intros mid Hm. apply hello_dg_msgs_pos. left. exact Hm.
  - apply dgx_msgs_lends_diag. exact hello_msg_at.
  - intros mid a0 s0 c Hm Hc. eapply getopt_diag_formats; [exact Herr | vm_compute; reflexivity | exact hello_dg_HQ | | exact Hm | exact Hc].
    intros n m Hin Hl. exact (hello_dg_ws n m Hin Hl).
Qed.

(** The rule for long options holds in the same way. *)
Lemma hello_dg_ldiag v tid : 0 <= v < 2 ^ 32 ->
  getopt_ldiag_rule w glibc_os_registry hge (hello_dg_G v tid) (hello_dg_T v tid) (ho_err ob) hello_dom.
Proof using Hfr Herr Hvf Hloc.
  intros Hv.
  eapply (hello_getopt_ldiag_rule_lock (glibc_program := hello_rules_program) eb Herr LibioCleanupExit.holds_os_glibc)
    with (Q := hello_dg_Q) (ic := Ro hello_ib.1) (tc := hello_tc) (dd := hello_dd) (lk1 := lock_ptr hello_lk1)
    (lk2 := lock_ptr hello_lk2) (lkt := lock_ptr hello_lkt).
  - exact (hello_dg_premises v Hv).
  - intros mid Hm. apply hello_dg_msgs_pos. right. left. exact Hm.
  - apply dgx_msgs_lends_ldiag; [exact hello_msg_at | vm_compute; reflexivity | vm_compute; reflexivity].
  - vm_compute; reflexivity.
  - vm_compute; split; congruence.
  - vm_compute; reflexivity.
  - vm_compute; split; congruence.
  - intros mid a0 s0 pfx sp nm sn Hm. eapply getopt_ldiag_formats; [exact Herr | vm_compute; reflexivity | exact hello_dg_HQ | | exact Hm].
    intros n m Hin Hl. exact (hello_dg_ws n m Hin Hl).
  - intros pfx sp nm sn. eapply getopt_f140_format; [exact Herr | vm_compute; reflexivity | exact hello_dg_HQ | |].
    + intros n m Hin Hl. exact (hello_dg_ws n m Hin Hl).
    + vm_compute; reflexivity.
  - eapply getopt_f141_format; [exact Herr | vm_compute; reflexivity | exact hello_dg_HQ | |].
    + intros n m Hin Hl. exact (hello_dg_ws n m Hin Hl).
    + vm_compute; reflexivity.
Qed.

(** Between reports, G lends the thread's cleanup state and takes it
    back in any region. *)
Lemma hello_dg_lend v tid :
  hello_dg_G v tid ⊢ tcb_cleanup_inv (ow_self w) ∗ (tcb_cleanup_inv (ow_self w) -∗ hello_dg_G v tid).
Proof using Type.
  iIntros "HG". iDestruct (dlk_lend (glibc_program := hello_rules_program) with "HG") as "[Hc Hb]".
  iFrame "Hc". iExact "Hb".
Qed.

End rules.
