From Glibc Require Import GlibcProgram.
(** A diagnostic takes three read locks while it translates a message.
    Each lock word holds a reader count, a writer, a shared flag and
    other flags, and earlier calls such as setlocale may leave them in
    any state that is ready for a new reader. The rules of
    [HelloGetoptDiagTcb](HelloGetoptDiagTcb.v) fix these words as
    parameters, so a caller would have to know them in advance.

    This module lets the caller hold the locks in whatever state they
    are in, as long as each one is idle. A lock is idle when no reader
    holds it, no flag is set and this thread is not its writer. Its
    word may still be the 1 that setlocale's unlock leaves, because the
    lock's resource counts readers rather than fixing the word. Setlocale
    needs exactly this state to take the lock for writing, and a
    translation brings each lock back to it. G carries these facts with
    the lock states. A translation reads the current states, runs the
    earlier proof for them, and puts back the states that the locks
    return. Where each lock lies stays fixed, and errno and the thread's
    bookkeeping are lent as before.

    This module only packages resources. It does not show that
    setlocale or startup leaves the locks idle. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv LibioLogic StrlenLogic MemFwdCode WordString SysWrappers.
From Glibc Require Import AllocLogic HiAtexitAlloc HiAtexitModule HelloGlibcDebts HelloGlibcLibsT.
From Glibc Require Import StpcpyCode TfindCode TfindEmpty LocalenameCode LocalenameLogic RdlockCode RwunlockCode StrchrCode.
From Glibc Require Import PrintfStreamInv FxprintfCode FxprintfStream FxprintfCall.
From Glibc Require Import GetoptDiag GetoptLongDiag GetoptDiagFx.
From Glibc Require Import DcgettextCode DcigettextCode DcigettextPreRules DcigettextRoute DcigettextSecure.
From Glibc Require Import DcgettextC DcgettextLocale DcgettextRwlock DcgettextReal DcgettextRealV HelloGettextLink.
From Glibc Require Import HelloGetoptDiagGettext HelloGetoptDiagTcb.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import PrintfStreamInv SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

(** A lock's state is its reader count, its writer, its shared flag and
    its other flags. *)
Record dlk_state : Type := mkDlk { dl_r : Z; dl_cw : Z; dl_sh : Z; dl_fl : Z }.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).
Context (Hreg : holds_os registry).

(** A translation reads the globals and cells that
    [HelloGetoptDiagTcb](HelloGetoptDiagTcb.v) lists. Here the three
    locks keep their places and their shares of the thread's id, but
    not their states. *)
Context (dom : ptr) (ds : list Z) (dqd : dfrac) (nb : Z) (nc : cap) (k : Z) (cat : list Z) (dqc : dfrac)
  (cv p276 p277 : ptr) (db : Z) (dqb : dfrac) (dbreg : region) (ib : Z) (ic : cap) (dqi : dfrac) (ireg : region)
  (sec : Z) (dqs : dfrac) (secreg : region) (tc dd : ptr) (ob : hello_objs)
  (dqr : dfrac) (rb ro : Z) (rreg : region) (gb go : Z) (greg : region) (dqg : dfrac) (lp : ptr) (lb : Z) (lreg : region)
  (dql dqn dqt : dfrac) (treg : region)
  (lk1 : ptr) (a1 : Z) (ar1 : region) (i1 : dfrac) (lk2 : ptr) (a2 : Z) (ar2 : region) (i2 : dfrac)
  (lkt : ptr) (a3 : Z) (ar3 : region) (i3 : dfrac) (tb : Z) (tid : Z).

(** The print writes to the stream fp, as before. *)
Context (vb sb : Z) (sreg : region) (fp f140 f141 : ptr) (F : iProp Σ) (Q : Z -> Z -> iProp Σ) (Lm : iProp Σ).

(** ## Where a lock lies and when it is ready *)

(** A lock object must lie inside its region, aligned. These facts do
    not change between reports. *)
Definition dlk_place (lk : ptr) (a : Z) (ar : region) : Prop :=
  lk = mkPtr a (Obj a) /\ 0 < a /\ a mod 8 = 0 /\ a + 56 <= r_end ar /\ r_end ar <= 2 ^ 63.

(** A lock is idle when no reader holds it, no flag is set and this
    thread is not its writer. Such a lock is ready for a reader, and
    setlocale can also take it for writing. *)
Definition dlk_ready (s : dlk_state) : Prop :=
  dl_r s = 0 /\ dl_fl s = 0 /\ dl_cw s <> tid.

(** The earlier rules asked for a lock ready for a reader. An idle lock
    in its place meets them. *)
Lemma dlk_lock_of lk a ar s : dlk_place lk a ar -> dlk_ready s -> dtx_lock tid lk a ar (dl_r s) (dl_cw s).
Proof using Q eb. unfold dtx_lock, dlk_place, dlk_ready. intros (? & ? & ? & ? & ?) (-> & _ & Hcw). cbn. split_and!; first [assumption | lia | reflexivity]. Qed.

(** ## The resources between reports *)

(** This is the earlier G for the three lock states s1, s2 and s3. *)
Definition dlk_G0 (s1 s2 s3 : dlk_state) (v : Z) : iProp Σ :=
  dtx_G eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg ob dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    a1 ar1 (dl_r s1) (dl_cw s1) (dl_sh s1) (dl_fl s1) i1 a2 ar2 (dl_r s2) (dl_cw s2) (dl_sh s2) (dl_fl s2) i2 a3 ar3 (dl_r s3) (dl_cw s3) (dl_sh s3) (dl_fl s3) i3
    tb tid vb sb sreg fp F Lm v.

(** A caller cannot know the lock words in advance, so G hides them.
    It only promises that each word is ready for a reader. After a
    translation, T also records that the result is the message. *)
Definition dlk_G (v : Z) : iProp Σ :=
  ∃ s1 s2 s3, ⌜dlk_ready s1 /\ dlk_ready s2 /\ dlk_ready s3⌝ ∗ dlk_G0 s1 s2 s3 v.
Definition dlk_T (v : Z) (mid q : ptr) : iProp Σ := ⌜q = mid⌝ ∗ dlk_G v.

(** Any ready states can enter G. *)
Lemma dlk_pack s1 s2 s3 v : dlk_ready s1 -> dlk_ready s2 -> dlk_ready s3 -> dlk_G0 s1 s2 s3 v ⊢ dlk_G v.
Proof using Q. intros H1 H2 H3. iIntros "H". iExists s1, s2, s3. iSplit; [iPureIntro; tauto | iExact "H"]. Qed.

(** Whatever G holds, its lock states are ready. *)
Lemma dlk_ready_of v : dlk_G v ⊢ ∃ s1 s2 s3, ⌜dlk_ready s1 /\ dlk_ready s2 /\ dlk_ready s3⌝.
Proof using Type. iIntros "(%s1 & %s2 & %s3 & %Hr & _)". iExists s1, s2, s3. done. Qed.

(** The caller can still lend the thread's bookkeeping between
    reports. G gives it away whole and accepts it back in any
    region. *)
Lemma dlk_lend v : dlk_G v ⊢ tcb_cleanup_inv (ow_self w0) ∗ (tcb_cleanup_inv (ow_self w0) -∗ dlk_G v).
Proof using Type.
  iIntros "(%s1 & %s2 & %s3 & %Hr & H)". unfold dlk_G0.
  iDestruct (dtx_lend eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg ob dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    a1 ar1 (dl_r s1) (dl_cw s1) (dl_sh s1) (dl_fl s1) i1 a2 ar2 (dl_r s2) (dl_cw s2) (dl_sh s2) (dl_fl s2) i2 a3 ar3 (dl_r s3) (dl_cw s3) (dl_sh s3) (dl_fl s3) i3
    tb tid vb sb sreg fp F Lm v with "H") as "[$ Hb]".
  iIntros "Ht". iExists s1, s2, s3. iSplit; [done|]. unfold dlk_G0. iApply ("Hb" with "Ht").
Qed.

(** Errno can change between reports, and G takes any bytes back. *)
Lemma dlk_errno v : dlk_G v ⊢ ∃ bs, errno_own eb bs ∗ (∀ bs', errno_own eb bs' -∗ dlk_G v).
Proof using Type.
  iIntros "(%s1 & %s2 & %s3 & %Hr & H)". unfold dlk_G0.
  iDestruct (dtx_errno eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg ob dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    a1 ar1 (dl_r s1) (dl_cw s1) (dl_sh s1) (dl_fl s1) i1 a2 ar2 (dl_r s2) (dl_cw s2) (dl_sh s2) (dl_fl s2) i2 a3 ar3 (dl_r s3) (dl_cw s3) (dl_sh s3) (dl_fl s3) i3
    tb tid vb sb sreg fp F Lm v with "H") as (bs) "[He Hb]".
  iExists bs. iFrame "He". iIntros (bs') "He". iExists s1, s2, s3. iSplit; [done|]. unfold dlk_G0.
  iApply ("Hb" with "He").
Qed.

(** A report reads the stream's lifetime, and G lends a share of it. *)
Lemma dlk_cap v : ⊢ dlk_G v -∗ ∃ dq reg, live_capq dq (ptr_cap fp) reg ∗ (live_capq dq (ptr_cap fp) reg -∗ dlk_G v).
Proof using Type.
  iIntros "(%s1 & %s2 & %s3 & %Hr & H)". unfold dlk_G0.
  iDestruct (dtx_cap eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg ob dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    a1 ar1 (dl_r s1) (dl_cw s1) (dl_sh s1) (dl_fl s1) i1 a2 ar2 (dl_r s2) (dl_cw s2) (dl_sh s2) (dl_fl s2) i2 a3 ar3 (dl_r s3) (dl_cw s3) (dl_sh s3) (dl_fl s3) i3
    tb tid vb sb sreg fp F Lm v with "H") as (dq reg) "[Hc Hb]".
  iExists dq, reg. iFrame "Hc". iIntros "Hc". iExists s1, s2, s3. iSplit; [done|]. unfold dlk_G0.
  iApply ("Hb" with "Hc").
Qed.

(** G lends the locale cells that Hello's own query reads. *)
Lemma dlk_locale v :
  dlk_G v ⊢ word_string DfracDiscarded cv [67] ∗ locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg ∗
    (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg -∗ dlk_G v).
Proof using Type.
  iIntros "(%s1 & %s2 & %s3 & %Hr & H)". unfold dlk_G0.
  iDestruct (dtx_locale eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg ob dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    a1 ar1 (dl_r s1) (dl_cw s1) (dl_sh s1) (dl_fl s1) i1 a2 ar2 (dl_r s2) (dl_cw s2) (dl_sh s2) (dl_fl s2) i2 a3 ar3 (dl_r s3) (dl_cw s3) (dl_sh s3) (dl_fl s3) i3
    tb tid vb sb sreg fp F Lm v with "H") as "(#Hcv & HC & Hb)".
  iSplitR; [iExact "Hcv"|]. iSplitL "HC"; [iExact "HC"|].
  iIntros "HC". iExists s1, s2, s3. iSplit; [done|]. unfold dlk_G0. iApply ("Hb" with "HC").
Qed.

(** ## The facts each report needs *)

(** A report needs the same program and global cells as before. Only
    where each lock lies is fixed now, because G carries the facts about
    each lock's current state. *)
Definition dlk_premises (v : Z) : Prop :=
  hello_link ge ob /\ hello_gettext_link ge /\
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) /\
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) /\
  dlk_place lk1 a1 ar1 /\ dlk_place lk2 a2 ar2 /\ dlk_place lkt a3 ar3 /\
  locale_cells gb go greg lp lb lreg /\
  (0 < rb /\ 0 <= ro /\ (rb + ro) mod 8 = 0 /\ rb + ro + 8 <= r_end rreg /\ r_end rreg <= 2 ^ 48) /\
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec /\
  dci_bounds db dbreg nb ib ic ireg k sec secreg /\ 0 <= v < 2 ^ 32 /\
  find_fn ge (TAtom "__fxprintf_nocancel") = Some (Defined glibc_fxprintf_nocancel) /\
  lookup (TAtom "__GI__libc_intl_domainname") (ge_globals ge) = Some dom /\ 0 <= ptr_addr fp < 2 ^ 64 /\
  dgx_qe eb F Q.

(** Each report checks that every lock is in its place and ready for a
    reader. The caller states the places, and G states that the current
    words are ready. *)
Lemma dlk_premises_at v s1 s2 s3 :
  dlk_premises v -> dlk_ready s1 -> dlk_ready s2 -> dlk_ready s3 ->
  dtx_premises eb dom nb nc k p276 p277 db dbreg ib ic ireg sec secreg tc dd ob rb ro rreg gb go greg lp lb lreg
    lk1 a1 ar1 (dl_r s1) (dl_cw s1) lk2 a2 ar2 (dl_r s2) (dl_cw s2) lkt a3 ar3 (dl_r s3) (dl_cw s3) tid fp F Q v.
Proof using Type.
  intros (A1 & A2 & A3 & A4 & P1 & P2 & P3 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16) R1 R2 R3.
  pose proof (dlk_lock_of lk1 a1 ar1 s1 P1 R1) as L1.
  pose proof (dlk_lock_of lk2 a2 ar2 s2 P2 R2) as L2.
  pose proof (dlk_lock_of lkt a3 ar3 s3 P3 R3) as L3.
  exact (conj A1 (conj A2 (conj A3 (conj A4 (conj L1 (conj L2 (conj L3 (conj A8 (conj A9 (conj A10 (conj A11
    (conj A12 (conj A13 (conj A14 (conj A15 A16))))))))))))))).
Qed.

(** ## One report *)

(** Translating a message must leave the caller ready to report again.
    The proof runs the earlier translation for the lock words that G
    holds, and those words come back unchanged and still ready. *)
Lemma dlk_translate v (Mm : ptr -> Prop) f e ls l d args rest j mid Φ :
  dlk_premises v -> (forall m, Mm m -> 0 < ptr_addr m < 2 ^ 64) -> Mm mid ->
  map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] ->
  ⊢ dlk_G v -∗ ▷ (∀ q, dlk_T v mid q -∗ WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame f e ls None
      (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Herr Hreg.
  intros Hp Hm Hmid Hargs. iIntros "(%s1 & %s2 & %s3 & %Hr & H) HK".
  destruct Hr as (R1 & R2 & R3). pose proof (dlk_premises_at v s1 s2 s3 Hp R1 R2 R3) as Hq. unfold dlk_G0.
  iApply (dtx_translate eb Herr Hreg dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg tc dd ob dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    lk1 a1 ar1 (dl_r s1) (dl_cw s1) (dl_sh s1) (dl_fl s1) i1 lk2 a2 ar2 (dl_r s2) (dl_cw s2) (dl_sh s2) (dl_fl s2) i2 lkt a3 ar3 (dl_r s3) (dl_cw s3) (dl_sh s3) (dl_fl s3) i3
    tb tid vb sb sreg fp F Q Lm v
    Mm f e ls l d args rest j mid Φ Hq Hm Hmid Hargs with "H").
  iNext. iIntros (q) "HT". iDestruct "HT" as "[%Hq' H]". iApply "HK". iSplit; [done|].
  iExists s1, s2, s3. iSplit; [iPureIntro; tauto|]. unfold dlk_G0. iExact "H".
Qed.

(** A print lends errno to the formatter, and the caller gets G back
    with the same lock states. *)
Lemma dlk_print v fmt ys X f e ls l d args rest j Φ :
  dlk_premises v -> 0 <= ptr_addr fmt < 2 ^ 64 -> forallb snapshot_word ys = true ->
  (Lm ⊢ ∃ dq reg, live_capq dq (ptr_cap fmt) reg ∗ (live_capq dq (ptr_cap fmt) reg -∗ Lm)) ->
  fx_format vb fp fmt ys ((errno_any eb ∗ F) ∗ X) Q ->
  map_option (arg_x ge e) args = Some (WPtr fp :: WPtr fmt :: ys) ->
  ⊢ dlk_G v -∗ X -∗ ▷ (∀ x, dlk_G v -∗ WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame f e ls None
      (Exec l (Call (CResult d W) (Global (TAtom "__fxprintf_nocancel")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Hreg.
  intros Hp Hfr Hys Hlm Hfm Hargs. iIntros "(%s1 & %s2 & %s3 & %Hr & H) HX HK".
  destruct Hr as (R1 & R2 & R3). pose proof (dlk_premises_at v s1 s2 s3 Hp R1 R2 R3) as Hq. unfold dlk_G0.
  iApply (dtx_print eb Hreg dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg tc dd ob dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    lk1 a1 ar1 (dl_r s1) (dl_cw s1) (dl_sh s1) (dl_fl s1) i1 lk2 a2 ar2 (dl_r s2) (dl_cw s2) (dl_sh s2) (dl_fl s2) i2 lkt a3 ar3 (dl_r s3) (dl_cw s3) (dl_sh s3) (dl_fl s3) i3
    tb tid vb sb sreg fp F Q Lm v
    fmt ys X f e ls l d args rest j Φ Hq Hfr Hys Hlm Hfm Hargs with "H HX").
  iNext. iIntros (x) "H". iApply "HK". iExists s1, s2, s3. iSplit; [iPureIntro; tauto|]. unfold dlk_G0. iExact "H".
Qed.

(** ## The two rules *)

(** This is the short-option rule over the G that owns the lock
    states. *)
Lemma hello_getopt_diag_rule_lock v :
  dlk_premises v -> (forall mid, diag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) -> dgx_lends Lm (diag_msg ge) ->
  (forall mid a0 s0 c, diag_msg ge mid -> 0 <= c < 2 ^ 32 ->
     fx_format vb fp mid [WPtr a0; WInt c] ((errno_any eb ∗ F) ∗ word_string DfracDiscarded a0 s0) Q) ->
  getopt_diag_rule w0 registry ge (dlk_G v) (dlk_T v) fp dom.
Proof.
  intros Hp Hm Hlm Hfm. pose proof Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd & Hf & _).
  refine (conj Hd (conj Hf (conj (dlk_cap v) (conj _ _)))).
  - intros f e ls l d args rest j mid Φ Hmid Hargs. exact (dlk_translate v _ f e ls l d args rest j mid Φ Hp Hm Hmid Hargs).
  - intros f e ls l d args rest j mid q a0 s0 c Φ Hmid Hc Hargs. iIntros "[%Hq HG] Ha HK". subst q.
    pose proof (Hm mid Hmid).
    iApply (dlk_print v mid [WPtr a0; WInt c] (word_string DfracDiscarded a0 s0) with "HG Ha HK");
      first [exact Hp | lia | reflexivity | exact (Hlm mid Hmid) | exact (Hfm mid a0 s0 c Hmid Hc) | exact Hargs].
Qed.

(** This is the long-option rule over the same G. *)
Lemma hello_getopt_ldiag_rule_lock v :
  dlk_premises v -> (forall mid, ldiag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  dgx_lends Lm (fun p => ldiag_msg ge p \/ p = f140 \/ p = f141) ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 -> 0 <= ptr_addr f140 < 2 ^ 64 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 -> 0 <= ptr_addr f141 < 2 ^ 64 ->
  (forall mid a0 s0 pfx sp nm sn, ldiag_msg ge mid ->
     fx_format vb fp mid [WPtr a0; WPtr pfx; WPtr nm]
       ((errno_any eb ∗ F) ∗ (word_string DfracDiscarded a0 s0 ∗ word_string DfracDiscarded pfx sp ∗
         word_string DfracDiscarded nm sn)) Q) ->
  (forall pfx sp nm sn, fx_format vb fp f140 [WPtr pfx; WPtr nm]
     ((errno_any eb ∗ F) ∗ (word_string DfracDiscarded pfx sp ∗ word_string DfracDiscarded nm sn)) Q) ->
  fx_format vb fp f141 [] ((errno_any eb ∗ F) ∗ True) Q ->
  getopt_ldiag_rule w0 registry ge (dlk_G v) (dlk_T v) fp dom.
Proof.
  intros Hp Hm Hlm H140 Hr140 H141 Hr141 Hfm Hfm140 Hfm141.
  pose proof Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd & Hf & _).
  refine (conj Hd (conj Hf (conj (dlk_cap v) (conj _ (conj _ (conj _ _)))))).
  - intros f e ls l d args rest j mid Φ Hmid Hargs. exact (dlk_translate v _ f e ls l d args rest j mid Φ Hp Hm Hmid Hargs).
  - intros f e ls l d args rest j mid q a0 s0 pfx sp nm sn Φ Hmid Hargs. iIntros "[%Hq HG] Ha Hp Hn HK". subst q.
    pose proof (Hm mid Hmid).
    iApply (dlk_print v mid [WPtr a0; WPtr pfx; WPtr nm]
      (word_string DfracDiscarded a0 s0 ∗ word_string DfracDiscarded pfx sp ∗ word_string DfracDiscarded nm sn)%I
      with "HG [$Ha $Hp $Hn] HK"); first [exact Hp | lia | reflexivity |
      exact (Hlm mid (or_introl Hmid)) | exact (Hfm mid a0 s0 pfx sp nm sn Hmid) | exact Hargs].
  - intros f e ls l d args rest j fmt pfx sp nm sn Φ Hfmt Hargs. rewrite H140 in Hfmt. injection Hfmt as <-.
    iIntros "HG Hp Hn HK".
    iApply (dlk_print v f140 [WPtr pfx; WPtr nm] (word_string DfracDiscarded pfx sp ∗ word_string DfracDiscarded nm sn)%I
      with "HG [$Hp $Hn] HK"); first [exact Hp | exact Hr140 | reflexivity |
      exact (Hlm f140 (or_intror (or_introl eq_refl))) | exact (Hfm140 pfx sp nm sn) | exact Hargs].
  - intros f e ls l d args rest j fmt Φ Hfmt Hargs. rewrite H141 in Hfmt. injection Hfmt as <-.
    iIntros "HG HK".
    iApply (dlk_print v f141 [] True%I with "HG [//] HK"); first [exact Hp | exact Hr141 | reflexivity |
      exact (Hlm f141 (or_intror (or_intror eq_refl))) | exact Hfm141 | exact Hargs].
Qed.

(** ## Controls *)

(** These are two different idle states. The first lock is free, and
    the second names another thread as its last writer and has its
    shared flag set. *)
Definition dlk_free : dlk_state := mkDlk 0 (tid + 1) 0 0.
Definition dlk_busy : dlk_state := mkDlk 0 (tid + 7) 3 0.

(** Both states are ready and differ, and G accepts either of them in
    any of the three locks. *)
Example dlk_state_controls v :
  dlk_ready dlk_free /\ dlk_ready dlk_busy /\ dlk_free <> dlk_busy /\
  (dlk_G0 dlk_free dlk_free dlk_free v ⊢ dlk_G v) /\ (dlk_G0 dlk_busy dlk_free dlk_busy v ⊢ dlk_G v).
Proof.
  assert (Hf : dlk_ready dlk_free) by (unfold dlk_ready, dlk_free; cbn; split_and!; lia).
  assert (Hb : dlk_ready dlk_busy) by (unfold dlk_ready, dlk_busy; cbn; split_and!; lia).
  split_and!; [exact Hf | exact Hb | unfold dlk_free, dlk_busy; intros H; discriminate H |
    apply dlk_pack; assumption | apply dlk_pack; assumption].
Qed.

(** A lock that is not idle cannot enter G. Each state below breaks one
    fact: a reader holds the lock, a flag is set, or this thread is the
    writer. *)
Example dlk_bad_controls sh :
  ~ dlk_ready (mkDlk 8 (tid + 1) sh 0) /\ ~ dlk_ready (mkDlk 0 (tid + 1) sh 1) /\ ~ dlk_ready (mkDlk 0 tid sh 0).
Proof using Type. unfold dlk_ready; cbn. split_and!; intros (H1 & H2 & H3); lia. Qed.

(** A caller may report twice, and between the reports getenv may
    borrow the bookkeeping. Each report may change errno. This example
    starts from the busy and free words and gets G back after each
    step. *)
Example dlk_repeat_controls v :
  dlk_G0 dlk_busy dlk_free dlk_busy v ⊢ ∃ bs, errno_own eb bs ∗ (errno_own eb [9; 0; 0; 0] -∗
    tcb_cleanup_inv (ow_self w0) ∗ (tcb_cleanup_inv (ow_self w0) -∗
      ∃ bs2, errno_own eb bs2 ∗ (errno_own eb [0; 0; 0; 0] -∗
        tcb_cleanup_inv (ow_self w0) ∗ (tcb_cleanup_inv (ow_self w0) -∗ dlk_G v)))).
Proof.
  iIntros "H0". iDestruct (proj2 (proj2 (proj2 (proj2 (dlk_state_controls v)))) with "H0") as "HG".
  iDestruct (dlk_errno with "HG") as (bs) "[He Hb]". iExists bs. iFrame "He". iIntros "He".
  iDestruct ("Hb" with "He") as "HG". iDestruct (dlk_lend with "HG") as "[$ Hb]". iIntros "Ht".
  iDestruct ("Hb" with "Ht") as "HG". iDestruct (dlk_errno with "HG") as (bs2) "[He Hb]". iExists bs2.
  iFrame "He". iIntros "He". iDestruct ("Hb" with "He") as "HG". iApply (dlk_lend with "HG").
Qed.
End rules.
