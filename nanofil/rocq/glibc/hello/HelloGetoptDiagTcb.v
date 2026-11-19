From Glibc Require Import Unit_stdioZ2dcommon_fxprintf_os Unit_string_strchr_os Unit_string_strchrnul_os.
From Glibc Require Import GlibcProgram.
(** A program that reports an option error may call getenv and glibc's
    allocation cutoff between two reports. Both calls need the thread's
    cancellation bookkeeping, which owns the whole thread object. A
    report also reads the thread object, because its locks check the
    thread's id. So the rules of
    [HelloGetoptDiagGettext](HelloGetoptDiagGettext.v), which keep part
    of the thread object, cannot be used beside getenv or the cutoff.

    This module builds the two diagnostic rules again so that the
    caller holds the thread object only once. While a message is
    translated, the right to the object is split three ways for the
    three locks. When the translation returns, the parts join again.
    Between reports, the caller can lend the whole bookkeeping to getenv
    or the cutoff. Errno goes to the formatter as before, and the
    caller still supplies the thread's id. *)
From Glibc Require Import GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv LibioLogic StrlenLogic WordString SysWrappers.
From Glibc Require Import AllocLogic AllocCall HelloGlibcDebts HelloGlibcLibsT.
From Glibc Require Import LocalenameLogic.
From Glibc Require Import GetoptDiag GetoptLongDiag GetoptDiagFx.
From Glibc Require Import DcigettextRoute.
From Glibc Require Import DcgettextLocale DcgettextRwlock DcgettextRealV HelloGettextLink.
From Glibc Require Import HelloGetoptDiagGettext.
From Glibc Require Import RdlockLogic.
From Glibc Require Import SysLayout.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import SysWrappers Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).
Context (Hreg : holds_os registry).

(** A translation reads the globals, locks and cells that
    [HelloGetoptDiagGettext](HelloGetoptDiagGettext.v) lists. The thread
    object stays at tb, but the region it lies in may change. *)
Context (dom : ptr) (ds : list Z) (dqd : dfrac) (nb : Z) (nc : cap) (k : Z) (cat : list Z) (dqc : dfrac)
  (cv p276 p277 : ptr) (db : Z) (dqb : dfrac) (dbreg : region) (ib : Z) (ic : cap) (dqi : dfrac) (ireg : region)
  (sec : Z) (dqs : dfrac) (secreg : region) (tc dd : ptr) (ob : hello_objs)
  (dqr : dfrac) (rb ro : Z) (rreg : region) (gb go : Z) (greg : region) (dqg : dfrac) (lp : ptr) (lb : Z) (lreg : region)
  (dql dqn dqt : dfrac) (treg : region)
  (lk1 : ptr) (a1 : Z) (ar1 : region) (r1 cw1 sh1 fl1 : Z) (i1 : dfrac)
  (lk2 : ptr) (a2 : Z) (ar2 : region) (r2 cw2 sh2 fl2 : Z) (i2 : dfrac)
  (lkt : ptr) (a3 : Z) (ar3 : region) (r3 cw3 sh3 fl3 : Z) (i3 : dfrac) (tb : Z) (tid : Z).

(** The print writes to the stream fp, as before. *)
Context (vb sb : Z) (sreg : region) (fp f140 f141 : ptr) (F : iProp Σ) (Q : Z -> Z -> iProp Σ) (Lm : iProp Σ).

(** The first lock holds half of the thread's lifetime, and each of the
    other two holds a quarter. *)
Local Notation qh := (DfracOwn (1 / 2)%Qp).
Local Notation qq := (DfracOwn (1 / 2 / 2)%Qp).

(** ## The thread's lifetime *)

(** The three shares make up the whole lifetime. *)
Lemma dtx_live_split b reg : live b reg ⊣⊢ liveq qh b reg ∗ liveq qq b reg ∗ liveq qq b reg.
Proof using Type.
  rewrite /live /liveq pts_ptsq -(ptsq_split (1 / 2 / 2) (1 / 2 / 2)) Qp.div_2 -ptsq_split Qp.div_2. reflexivity.
Qed.

(** Each lock owns its part of the thread object in the old G. *)
Definition dtx_G0 (tbreg : region) (v : Z) : iProp Σ :=
  dgx_G eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg ob dqr rb ro rreg
    gb go greg dqg lp lb lreg dql dqn dqt treg a1 ar1 r1 cw1 sh1 fl1 qh i1 a2 ar2 r2 cw2 sh2 fl2 qq i2
    a3 ar3 r3 cw3 sh3 fl3 qq i3 tb tbreg tid vb sb sreg fp F Lm v.

(** This is the old T in the same instance. *)
Definition dtx_T0 (tbreg : region) (v : Z) (mid q : ptr) : iProp Σ :=
  dgx_T eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg ob dqr rb ro rreg
    gb go greg dqg lp lb lreg dql dqn dqt treg a1 ar1 r1 cw1 sh1 fl1 qh i1 a2 ar2 r2 cw2 sh2 fl2 qq i2
    a3 ar3 r3 cw3 sh3 fl3 qq i3 tb tbreg tid vb sb sreg fp F Lm v mid q.

(** Lending the thread object must not lose the rest of a report's
    resources. The three parts come out of the locks and join into the
    whole object, and the rest accepts the object back in any
    region. *)
Lemma dtx_shares tbreg v : dtx_G0 tbreg v ⊢ live tb tbreg ∗ (∀ tbreg', live tb tbreg' -∗ dtx_G0 tbreg' v).
Proof using Type.
  unfold dtx_G0, dgx_G, dgx_before, dcg_before_v, rw_held.
  iIntros "((%bs & H1 & (Hk1 & Hl1 & Hi1) & (Hk2 & Hl2 & Hi2) & (Hk3 & Hl3 & Hi3) & H5 & H6 & H7 & He) & HS & HL)".
  iSplitL "Hl1 Hl2 Hl3"; [iApply dtx_live_split; iFrame "Hl1 Hl2 Hl3"|].
  iIntros (tbreg') "Hl". iDestruct (dtx_live_split with "Hl") as "(Hl1 & Hl2 & Hl3)".
  iSplitR "HS HL"; [|iSplitL "HS"; [iExact "HS" | iExact "HL"]]. iExists bs.
  iSplitL "H1"; [iExact "H1"|]. iSplitL "Hk1 Hl1 Hi1"; [iFrame "Hk1 Hl1 Hi1"|].
  iSplitL "Hk2 Hl2 Hi2"; [iFrame "Hk2 Hl2 Hi2"|]. iSplitL "Hk3 Hl3 Hi3"; [iFrame "Hk3 Hl3 Hi3"|].
  iSplitL "H5"; [iExact "H5"|]. iSplitL "H6"; [iExact "H6"|]. iSplitL "H7"; [iExact "H7"|]. iExact "He".
Qed.

(** ## The resources between reports *)

(** The thread's bookkeeping states where the thread object lies and
    that it is large enough. This predicate states the same facts for a
    region tbreg. *)
Definition dtx_tcb_at (tbreg : region) : Prop :=
  ow_self w0 = mkPtr tb (Obj tb) /\ 0 < tb /\ tb mod 8 = 0 /\ tb + off_cancelhandling + 4 <= r_end tbreg /\
  r_end tbreg <= 2 ^ 63.

(** The caller must be able to lend all of the thread's bookkeeping
    between reports. So G keeps that bookkeeping in one piece, and T
    keeps the same resources together with the returned message. *)
Definition dtx_G (v : Z) : iProp Σ :=
  ∃ tbreg jb, ⌜dtx_tcb_at tbreg⌝ ∗ pcell tb off_cleanup null ∗ pcell tb off_cleanup_jmp jb ∗
    int_cell tb off_cancelhandling 0 ∗ dtx_G0 tbreg v.
Definition dtx_T (v : Z) (mid q : ptr) : iProp Σ := ⌜q = mid⌝ ∗ dtx_G v.

(** Between reports, G lends the whole cleanup state. The callee may
    hand it back in any region, and G takes that region. *)
Lemma dtx_lend v : dtx_G v ⊢ tcb_cleanup_inv (ow_self w0) ∗ (tcb_cleanup_inv (ow_self w0) -∗ dtx_G v).
Proof using Type.
  iIntros "(%tbreg & %jb & %Hc & Hcl & Hj & Hx & H0)". iDestruct (dtx_shares with "H0") as "[Hl Hb]".
  pose proof Hc as (Hs & _).
  iSplitL "Hl Hcl Hj Hx"; [iExists tb, tbreg, jb; iSplit; [iPureIntro; exact Hc | iFrame "Hl Hcl Hj Hx"]|].
  iIntros "(%tb' & %tbreg' & %jb' & %Hc' & Hl & Hcl & Hj & Hx)".
  destruct Hc' as (Hs' & Hc'). rewrite Hs in Hs'. injection Hs' as <-.
  iExists tbreg', jb'. iSplit; [iPureIntro; exact (conj Hs Hc')|]. iFrame "Hcl Hj Hx". iApply ("Hb" with "Hl").
Qed.

(** Errno can change between reports, and G takes any bytes back. *)
Lemma dtx_errno v : dtx_G v ⊢ ∃ bs, errno_own eb bs ∗ (∀ bs', errno_own eb bs' -∗ dtx_G v).
Proof using Type.
  unfold dtx_G, dtx_G0, dgx_G. iIntros "(%tbreg & %jb & %Hc & Hcl & Hj & Hx & (%bs & HB) & HS & HL)".
  iDestruct (dgx_errno with "HB") as "[He HB]". iExists bs. iFrame "He". iIntros (bs') "He".
  iExists tbreg, jb. iSplit; [done|]. iFrame "Hcl Hj Hx HS HL". iExists bs'. iApply ("HB" with "He").
Qed.

(** ## The facts each report needs *)

(** A lock object must be in bounds, its reader count must have room,
    and the thread must not hold it for writing. Unlike [rw_ready], this
    says nothing about the thread object. *)
Definition dtx_lock (lk : ptr) (a : Z) (ar : region) (r cw : Z) : Prop :=
  lk = mkPtr a (Obj a) /\ 0 < a /\ a mod 8 = 0 /\ a + 56 <= r_end ar /\ r_end ar <= 2 ^ 63 /\
  0 <= r /\ r mod 8 = 0 /\ r + 8 < 2 ^ 31 /\ cw <> tid.

(** A report needs the same program and global cells as before. The
    caller no longer has to bound the thread object, because the
    bookkeeping that G holds already does. *)
Definition dtx_premises (v : Z) : Prop :=
  hello_link ge ob /\ hello_gettext_link ge /\
  find_fn ge (TAtom "__GI_strchr") = Some (Defined Unit_string_strchr_os.fn___GI_strchr) /\
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined Unit_string_strchrnul_os.fn___GI___strchrnul) /\
  dtx_lock lk1 a1 ar1 r1 cw1 /\ dtx_lock lk2 a2 ar2 r2 cw2 /\ dtx_lock lkt a3 ar3 r3 cw3 /\
  locale_cells gb go greg lp lb lreg /\
  (0 < rb /\ 0 <= ro /\ (rb + ro) mod 8 = 0 /\ rb + ro + 8 <= r_end rreg /\ r_end rreg <= 2 ^ 48) /\
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec /\
  dci_bounds db dbreg nb ib ic ireg k sec secreg /\ 0 <= v < 2 ^ 32 /\
  find_fn ge (TAtom "__fxprintf_nocancel") = Some (Defined Unit_stdioZ2dcommon_fxprintf_os.fn___fxprintf_nocancel) /\
  lookup (TAtom "__GI__libc_intl_domainname") (ge_globals ge) = Some dom /\ 0 <= ptr_addr fp < 2 ^ 64 /\
  dgx_qe eb F Q.

(** Each read lock looks at the thread's id, which lies at offset 720,
    so the thread object must be at least 724 bytes long. The
    bookkeeping already promises more than 792 bytes, so the caller
    does not need to promise anything new. *)
Lemma dtx_premises_at v tbreg :
  dtx_premises v -> dtx_tcb_at tbreg ->
  dgx_premises_e eb dom nb nc k p276 p277 db dbreg ib ic ireg sec secreg tc dd ob rb ro rreg gb go greg lp lb lreg
    lk1 a1 ar1 r1 cw1 lk2 a2 ar2 r2 cw2 lkt a3 ar3 r3 cw3 tb tbreg tid fp F Q v.
Proof using Type.
  intros (A1 & A2 & A3 & A4 & L1 & L2 & L3 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16)
    (Hs & Htb & _ & Hend & Hr).
  assert (Hoff : off_cancelhandling = 792) by reflexivity. rewrite Hoff in Hend.
  assert (Hrw : forall lk a ar r cw, dtx_lock lk a ar r cw -> rw_ready lk a ar tb tbreg r cw tid).
  { intros lk a ar r cw (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). unfold rw_ready, rw_place.
    split_and!; first [assumption | lia]. }
  assert (Hsr : ptr_addr (ow_self w0) = tb) by (rewrite Hs; reflexivity).
  refine (conj A1 (conj A2 (conj A3 (conj A4 (conj (Hrw _ _ _ _ _ L1) (conj (Hrw _ _ _ _ _ L2)
    (conj (Hrw _ _ _ _ _ L3) (conj A8 (conj A9 (conj A10 (conj A11 (conj A12 (conj A13
    (conj _ (conj _ (conj A14 (conj A15 A16))))))))))))))))); lia.
Qed.

(** ## One report *)

(** A report reads the stream's lifetime, and G lends a share of it. *)
Lemma dtx_cap v : ⊢ dtx_G v -∗ ∃ dq reg, live_capq dq (ptr_cap fp) reg ∗ (live_capq dq (ptr_cap fp) reg -∗ dtx_G v).
Proof using Type.
  unfold dtx_G, dtx_G0. iIntros "(%tbreg & %jb & %Hc & Hcl & Hj & Hx & H0)".
  iDestruct (dgx_cap with "H0") as (dq reg) "[Hc0 Hb]". iExists dq, reg. iFrame "Hc0". iIntros "Hc0".
  iExists tbreg, jb. iSplit; [done|]. iFrame "Hcl Hj Hx". iApply ("Hb" with "Hc0").
Qed.

(** G lends the locale cells that Hello's own query reads. *)
Lemma dtx_locale v :
  dtx_G v ⊢ word_string DfracDiscarded cv [67] ∗ locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg ∗
    (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg -∗ dtx_G v).
Proof using Type.
  unfold dtx_G, dtx_G0. iIntros "(%tbreg & %jb & %Hc & Hcl & Hj & Hx & H0)".
  iDestruct (dgx_locale with "H0") as "(#Hcv & HC & Hb)". iSplitR; [iExact "Hcv"|]. iSplitL "HC"; [iExact "HC"|].
  iIntros "HC". iExists tbreg, jb. iSplit; [done|]. iFrame "Hcl Hj Hx". iApply ("Hb" with "HC").
Qed.

(** The old T gives back the message and the old G. *)
Lemma dtx_T0_G tbreg v mid q : dtx_T0 tbreg v mid q ⊢ ⌜q = mid⌝ ∗ dtx_G0 tbreg v.
Proof using Type.
  unfold dtx_T0, dtx_G0, dgx_T, dgx_G. iIntros "((%bs & HA) & HS & HL)".
  iDestruct (dgx_cycle with "HA") as "[%Hq HB]". iSplit; [done|].
  iSplitL "HB"; [iExists _; iExact "HB"|]. iSplitL "HS"; [iExact "HS" | iExact "HL"].
Qed.

(** A translation runs on the old G for the current region. Its locks
    use their parts of the thread object and hand them back with the
    message. *)
Lemma dtx_translate v (Mm : ptr -> Prop) f e ls l d args rest j mid Φ :
  dtx_premises v -> (forall m, Mm m -> 0 < ptr_addr m < 2 ^ 64) -> Mm mid ->
  map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] ->
  ⊢ dtx_G v -∗ ▷ (∀ q, dtx_T v mid q -∗ WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame f e ls None
      (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Herr Hreg.
  intros Hp Hm Hmid Hargs. iIntros "(%tbreg & %jb & %Hc & Hcl & Hj & Hx & H0) HK".
  pose proof (dtx_premises_at v tbreg Hp Hc) as Ho. apply dgx_premises_of_e in Ho.
  unfold dtx_G0.
  iApply (dgx_translate eb Herr Hreg dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    tc dd ob dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg lk1 a1 ar1 r1 cw1 sh1 fl1 qh i1
    lk2 a2 ar2 r2 cw2 sh2 fl2 qq i2 lkt a3 ar3 r3 cw3 sh3 fl3 qq i3 tb tbreg tid vb sb sreg fp F Q Lm v Mm
    f e ls l d args rest j mid Φ Ho Hm Hmid Hargs with "H0").
  iNext. iIntros (q) "HT". iDestruct (dtx_T0_G tbreg v mid q with "HT") as "[%Hq H0]".
  iApply "HK". iSplit; [done|]. iExists tbreg, jb. iSplit; [done|]. iFrame "Hcl Hj Hx". iExact "H0".
Qed.

(** Printing a message must leave the caller ready for the next report.
    The formatter borrows errno, and the caller gets G back. *)
Lemma dtx_print v fmt ys X f e ls l d args rest j Φ :
  dtx_premises v -> 0 <= ptr_addr fmt < 2 ^ 64 -> forallb snapshot_word ys = true ->
  (Lm ⊢ ∃ dq reg, live_capq dq (ptr_cap fmt) reg ∗ (live_capq dq (ptr_cap fmt) reg -∗ Lm)) ->
  fx_format vb fp fmt ys ((errno_any eb ∗ F) ∗ X) Q ->
  map_option (arg_x ge e) args = Some (WPtr fp :: WPtr fmt :: ys) ->
  ⊢ dtx_G v -∗ X -∗ ▷ (∀ x, dtx_G v -∗ WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame f e ls None
      (Exec l (Call (CResult d W) (Global (TAtom "__fxprintf_nocancel")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Hreg.
  intros Hp Hfr Hys Hlm Hfm Hargs. iIntros "(%tbreg & %jb & %Hc & Hcl & Hj & Hx & H0) HX HK".
  pose proof (dtx_premises_at v tbreg Hp Hc) as Hpe. unfold dtx_G0.
  iApply (dgx_print_g_e eb Hreg dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    tc dd ob dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg lk1 a1 ar1 r1 cw1 sh1 fl1 qh i1
    lk2 a2 ar2 r2 cw2 sh2 fl2 qq i2 lkt a3 ar3 r3 cw3 sh3 fl3 qq i3 tb tbreg tid vb sb sreg fp F Q Lm v
    fmt ys X f e ls l d args rest j Φ Hpe Hfr Hys Hlm Hfm Hargs with "H0 HX [Hcl Hj Hx HK]").
  iNext. iIntros (x) "H0". iApply "HK". iExists tbreg, jb. iSplit; [done|]. iFrame "Hcl Hj Hx". iExact "H0".
Qed.

(** ## The two rules *)

(** This is the short-option rule over the G that owns the cleanup
    fields. *)
Lemma hello_getopt_diag_rule_tcb v :
  dtx_premises v -> (forall mid, diag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) -> dgx_lends Lm (diag_msg ge) ->
  (forall mid a0 s0 c, diag_msg ge mid -> 0 <= c < 2 ^ 32 ->
     fx_format vb fp mid [WPtr a0; WInt c] ((errno_any eb ∗ F) ∗ word_string DfracDiscarded a0 s0) Q) ->
  getopt_diag_rule w0 registry ge (dtx_G v) (dtx_T v) fp dom.
Proof using Herr Hreg.
  intros Hp Hm Hlm Hfm. pose proof Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd & Hf & _).
  refine (conj Hd (conj Hf (conj (dtx_cap v) (conj _ _)))).
  - intros f e ls l d args rest j mid Φ Hmid Hargs. exact (dtx_translate v _ f e ls l d args rest j mid Φ Hp Hm Hmid Hargs).
  - intros f e ls l d args rest j mid q a0 s0 c Φ Hmid Hc Hargs. iIntros "[%Hq HG] Ha HK". subst q.
    pose proof (Hm mid Hmid).
    iApply (dtx_print v mid [WPtr a0; WInt c] (word_string DfracDiscarded a0 s0) with "HG Ha HK");
      first [exact Hp | lia | reflexivity | exact (Hlm mid Hmid) | exact (Hfm mid a0 s0 c Hmid Hc) | exact Hargs].
Qed.

(** This is the long-option rule over the same G. *)
Lemma hello_getopt_ldiag_rule_tcb v :
  dtx_premises v -> (forall mid, ldiag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
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
  getopt_ldiag_rule w0 registry ge (dtx_G v) (dtx_T v) fp dom.
Proof using Herr Hreg.
  intros Hp Hm Hlm H140 Hr140 H141 Hr141 Hfm Hfm140 Hfm141.
  pose proof Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd & Hf & _).
  refine (conj Hd (conj Hf (conj (dtx_cap v) (conj _ (conj _ (conj _ _)))))).
  - intros f e ls l d args rest j mid Φ Hmid Hargs. exact (dtx_translate v _ f e ls l d args rest j mid Φ Hp Hm Hmid Hargs).
  - intros f e ls l d args rest j mid q a0 s0 pfx sp nm sn Φ Hmid Hargs. iIntros "[%Hq HG] Ha Hp Hn HK". subst q.
    pose proof (Hm mid Hmid).
    iApply (dtx_print v mid [WPtr a0; WPtr pfx; WPtr nm]
      (word_string DfracDiscarded a0 s0 ∗ word_string DfracDiscarded pfx sp ∗ word_string DfracDiscarded nm sn)%I
      with "HG [$Ha $Hp $Hn] HK"); first [exact Hp | lia | reflexivity |
      exact (Hlm mid (or_introl Hmid)) | exact (Hfm mid a0 s0 pfx sp nm sn Hmid) | exact Hargs].
  - intros f e ls l d args rest j fmt pfx sp nm sn Φ Hfmt Hargs. rewrite H140 in Hfmt. injection Hfmt as <-.
    iIntros "HG Hp Hn HK".
    iApply (dtx_print v f140 [WPtr pfx; WPtr nm] (word_string DfracDiscarded pfx sp ∗ word_string DfracDiscarded nm sn)%I
      with "HG [$Hp $Hn] HK"); first [exact Hp | exact Hr140 | reflexivity |
      exact (Hlm f140 (or_intror (or_introl eq_refl))) | exact (Hfm140 pfx sp nm sn) | exact Hargs].
  - intros f e ls l d args rest j fmt Φ Hfmt Hargs. rewrite H141 in Hfmt. injection Hfmt as <-.
    iIntros "HG HK".
    iApply (dtx_print v f141 [] True%I with "HG [//] HK"); first [exact Hp | exact Hr141 | reflexivity |
      exact (Hlm f141 (or_intror (or_intror eq_refl))) | exact Hfm141 | exact Hargs].
Qed.

(** ## Controls *)

(** These numbers come from the layout captured from glibc's headers.
    They show that the bound that the bookkeeping states covers the id
    that the locks read. *)
Example dtx_layout_controls :
  SysLayout.field_offset "struct pthread"%string "tid"%string = Some 720 /\ off_cancelhandling = 792 /\
  (forall reg, tb + off_cancelhandling + 4 <= r_end reg -> tb + 720 + 4 <= r_end reg).
Proof using Type.
  split; [vm_compute; reflexivity|]. assert (Hoff : off_cancelhandling = 792) by reflexivity.
  split; [exact Hoff|]. intros reg H. rewrite Hoff in H. lia.
Qed.

(** Two reports in a row may each change errno, and the callers in
    between may each borrow the cleanup state. Here the first formatter
    writes 9 and the second writes 0, and G comes back each time. *)
Example dtx_repeat_controls v :
  dtx_G v ⊢ ∃ bs, errno_own eb bs ∗ (errno_own eb [9; 0; 0; 0] -∗
    tcb_cleanup_inv (ow_self w0) ∗ (tcb_cleanup_inv (ow_self w0) -∗
      ∃ bs2, errno_own eb bs2 ∗ (errno_own eb [0; 0; 0; 0] -∗
        tcb_cleanup_inv (ow_self w0) ∗ (tcb_cleanup_inv (ow_self w0) -∗ dtx_G v)))).
Proof using Type.
  iIntros "HG". iDestruct (dtx_errno with "HG") as (bs) "[He Hb]". iExists bs. iFrame "He". iIntros "He".
  iDestruct ("Hb" with "He") as "HG". iDestruct (dtx_lend with "HG") as "[$ Hb]". iIntros "Ht".
  iDestruct ("Hb" with "Ht") as "HG". iDestruct (dtx_errno with "HG") as (bs2) "[He Hb]". iExists bs2.
  iFrame "He". iIntros "He". iDestruct ("Hb" with "He") as "HG". iApply (dtx_lend with "HG").
Qed.

(** A caller cannot keep the old G and also lend the bookkeeping. The
    old G keeps part of the right to the thread object in its first
    lock, whatever part the caller chose, and the bookkeeping claims the
    whole object. No state holds both. *)
Example dtx_frame_refused tbreg' q1' q2' q3' v :
  ow_self w0 = mkPtr tb (Obj tb) ->
  dgx_G eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg ob dqr rb ro rreg
    gb go greg dqg lp lb lreg dql dqn dqt treg a1 ar1 r1 cw1 sh1 fl1 q1' i1 a2 ar2 r2 cw2 sh2 fl2 q2' i2
    a3 ar3 r3 cw3 sh3 fl3 q3' i3 tb tbreg' tid vb sb sreg fp F Lm v ∗ tcb_cleanup_inv (ow_self w0) ⊢ False.
Proof using Type.
  intros Hs. unfold dgx_G, dgx_before, dcg_before_v, rw_held.
  iIntros "[((%bs & _ & (_ & Hl1 & _) & _) & _) Ht]".
  iDestruct "Ht" as (tb2 treg2 jb) "(%Hc & Hl & _)". destruct Hc as (Hs' & _). rewrite Hs in Hs'. injection Hs' as <-.
  rewrite /live /liveq /pts /ptsq /=. iDestruct "Hl" as "[Hl _]". iDestruct "Hl1" as "[Hl1 _]".
  iDestruct (pointsto_valid_2 with "Hl Hl1") as %[Hv _].
  apply dfrac_valid_own_l in Hv. exfalso. exact (irreflexivity _ _ Hv).
Qed.
End rules.
