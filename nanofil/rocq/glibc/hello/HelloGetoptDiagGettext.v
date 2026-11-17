From Glibc Require Import GlibcProgram.
(** Hello's getopt proofs take two diagnostic rules as premises. Each
    rule says what happens when getopt translates a message and then
    prints it to stderr. This module builds both rules from proofs of
    the real code. The translation runs glibc's dcgettext in the C locale,
    with any 32-bit value of the privilege flag. The print runs glibc's
    `c: __fxprintf_nocancel`, and only the formatter behind it stays a
    premise.

    A rule must hand its resources back after every report, so that
    getopt can report again. The translation returns everything it
    borrowed, but errno may then hold a different value, so the rules
    keep errno's bytes unknown. The formatter may leave stderr in any
    mode. The next report needs a stream that is not wide, so the caller
    states that the formatter returns such a mode, and the rules keep the
    mode that it returns.

    The rules cover only the two premises of getopt. How Hello's startup
    gives these resources, what the formatter does, the environment and
    the link of the whole program are left to the caller. *)
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
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import PrintfStreamInv SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).
Context (Hreg : holds_os registry).

(** The translation reads these globals and borrows these locks, the
    cache root, the locale cells and the allocator's cache. *)
Context (dom : ptr) (ds : list Z) (dqd : dfrac) (nb : Z) (nc : cap) (k : Z) (cat : list Z) (dqc : dfrac)
  (cv p276 p277 : ptr) (db : Z) (dqb : dfrac) (dbreg : region) (ib : Z) (ic : cap) (dqi : dfrac) (ireg : region)
  (sec : Z) (dqs : dfrac) (secreg : region) (tc dd : ptr) (ob : hello_objs)
  (dqr : dfrac) (rb ro : Z) (rreg : region) (gb go : Z) (greg : region) (dqg : dfrac) (lp : ptr) (lb : Z) (lreg : region)
  (dql dqn dqt : dfrac) (treg : region)
  (lk1 : ptr) (a1 : Z) (ar1 : region) (r1 cw1 sh1 fl1 : Z) (q1 i1 : dfrac)
  (lk2 : ptr) (a2 : Z) (ar2 : region) (r2 cw2 sh2 fl2 : Z) (q2 i2 : dfrac)
  (lkt : ptr) (a3 : Z) (ar3 : region) (r3 cw3 sh3 fl3 : Z) (q3 i3 : dfrac) (tb : Z) (tbreg : region) (tid : Z).

(** The print writes to the stream fp. The formatter borrows F and
    returns Q, and Lm lends the lifetimes of the format strings. *)
Context (vb sb : Z) (sreg : region) (fp f140 f141 : ptr) (F : iProp Σ) (Q : Z -> Z -> iProp Σ) (Lm : iProp Σ).

(** ## The resources between reports *)

(** Before a translation the caller holds these resources, with errno's
    bytes bs. *)
Definition dgx_before (v : Z) (bs : list Z) : iProp Σ :=
  dcg_before_v eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v
    (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
    (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
    (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hello_gettext_cache ob) bs.

(** When the translation of mid returns q, the caller holds these
    resources. *)
Definition dgx_after (v : Z) (bs : list Z) (mid q : ptr) : iProp Σ :=
  dcg_after_v eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v
    (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
    (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
    (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hello_gettext_cache ob) bs mid q.

(** A print writes to stderr, so the caller lends the stream. Its mode
    must be 0 or narrow, its lock count must have room for one more
    holder, and the formatter's resource F comes with it. *)
Definition dgx_stream : iProp Σ :=
  single_ro ge sb sreg ∗ ∃ mode flags2 held,
    ⌜(mode = 0 \/ mode = 2 ^ 32 - 1) /\ (forall c, held = Some c -> 0 <= c /\ c + 1 < 2 ^ 32)⌝ ∗
    printf_stream vb (ow_self w0) fp mode flags2 held ∗ fx_owner (ow_self w0) held ∗ F.

(** These are the rules' G and T. *)
Definition dgx_G (v : Z) : iProp Σ := (∃ bs, dgx_before v bs) ∗ dgx_stream ∗ Lm.
Definition dgx_T (v : Z) (mid q : ptr) : iProp Σ := (∃ bs, dgx_after v bs mid q) ∗ dgx_stream ∗ Lm.

(** The translation gives back every resource it borrowed, and the
    message as its result. Only errno's bytes change. *)
Lemma dgx_cycle v bs mid q : dgx_after v bs mid q ⊢ ⌜q = mid⌝ ∗ dgx_before v (le_bytes (dci_w bs) 4).
Proof using Type. unfold dgx_after, dgx_before, dcg_after_v, dcg_before_v. iIntros "[%Hq H]". iSplit; [done | iExact "H"]. Qed.

(** Lm lends a lifetime share of each format string that P allows. *)
Definition dgx_lends (P : ptr -> Prop) : Prop :=
  forall fmt, P fmt -> Lm ⊢ ∃ dq reg, live_capq dq (ptr_cap fmt) reg ∗ (live_capq dq (ptr_cap fmt) reg -∗ Lm).

(** A report reads the stream's lifetime, and G lends a share of it. *)
Lemma dgx_cap v : ⊢ dgx_G v -∗ ∃ dq reg, live_capq dq (ptr_cap fp) reg ∗ (live_capq dq (ptr_cap fp) reg -∗ dgx_G v).
Proof using Type.
  unfold dgx_G, dgx_stream.
  iIntros "(HB & (#Hs & %mode & %flags2 & %held & %Hp & Hst & Ho & HF) & HL)".
  iDestruct "Hst" as (fb freg st nb' vt) "(%Hq & Hl & Hrest)".
  assert (Hc : ptr_cap fp = Obj fb) by (destruct Hq as [-> _]; reflexivity).
  iExists (DfracOwn 1), freg. rewrite Hc. iSplitL "Hl"; [iExact "Hl"|]. iIntros "Hl".
  iFrame "HB HL". iSplitR; [iExact "Hs"|]. iExists mode, flags2, held. iSplit; [done|]. iFrame "Ho HF".
  iExists fb, freg, st, nb', vt. iFrame "Hl Hrest". done.
Qed.

(** A print takes the stream from K ∗ dgx_stream ∗ Lm and gives it back
    with the mode that the formatter leaves. The formatter's Q must say
    that this mode is not wide and must return F. *)
Lemma dgx_loan K Kb fmt :
  0 <= ptr_addr fmt < 2 ^ 64 ->
  (Lm ⊢ ∃ dq reg, live_capq dq (ptr_cap fmt) reg ∗ (live_capq dq (ptr_cap fmt) reg -∗ Lm)) ->
  (forall x m, Q x m ⊢ ⌜m = 0 \/ m = 2 ^ 32 - 1⌝ ∗ F) -> (K ⊢ Kb) ->
  fx_loan (K ∗ dgx_stream ∗ Lm) vb sb sreg fp fmt F Q (Kb ∗ dgx_stream ∗ Lm).
Proof using Type.
  intros Hfr Hl Hcy Hk. unfold fx_loan, dgx_stream.
  iIntros "(HK & (#Hs & %mode & %flags2 & %held & %Hp & Hst & Ho & HF) & HL)".
  iDestruct (Hl with "HL") as (dq reg) "[Hc HL]".
  iExists mode, flags2, held, dq, reg. iSplit; [iPureIntro; tauto|]. iSplitR; [iExact "Hs"|]. iFrame "Hst Ho Hc HF".
  iIntros (x mode') "Hst Ho Hc HQ". iDestruct (Hcy x mode' with "HQ") as "[%Hm HF]".
  iSplitL "HK"; [iApply (Hk with "HK")|]. iSplitR "Hc HL"; [|iApply ("HL" with "Hc")].
  iSplitR; [iExact "Hs"|]. iExists mode', flags2, held. iFrame "Hst Ho HF". iPureIntro. tauto.
Qed.

(** A diagnostic can run only when the program contains the code that
    it calls and its global cells are ready. Both rules assume the same
    facts about this. The program links Hello, gettext, strchr and the
    print wrapper. The three locks are free, and the locale and cache
    cells hold their values. The formatter also returns a stream that is
    not wide. *)
Definition dgx_premises (v : Z) : Prop :=
  hello_link ge ob /\ hello_gettext_link ge /\
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) /\
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) /\
  rw_ready lk1 a1 ar1 tb tbreg r1 cw1 tid /\ rw_ready lk2 a2 ar2 tb tbreg r2 cw2 tid /\ rw_ready lkt a3 ar3 tb tbreg r3 cw3 tid /\
  locale_cells gb go greg lp lb lreg /\
  (0 < rb /\ 0 <= ro /\ (rb + ro) mod 8 = 0 /\ rb + ro + 8 <= r_end rreg /\ r_end rreg <= 2 ^ 48) /\
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec /\
  dci_bounds db dbreg nb ib ic ireg k sec secreg /\ 0 <= v < 2 ^ 32 /\
  find_fn ge (TAtom "__fxprintf_nocancel") = Some (Defined glibc_fxprintf_nocancel) /\
  ptr_addr (ow_self w0) <> 0 /\ 0 <= ptr_addr (ow_self w0) < 2 ^ 64 /\
  lookup (TAtom "__GI__libc_intl_domainname") (ge_globals ge) = Some dom /\ 0 <= ptr_addr fp < 2 ^ 64 /\
  (forall x m, Q x m ⊢ ⌜m = 0 \/ m = 2 ^ 32 - 1⌝ ∗ F).

(** Translating one message takes G and gives T. *)
Lemma dgx_translate v (M : ptr -> Prop) f e ls l d args rest j mid Φ :
  dgx_premises v -> (forall m, M m -> 0 < ptr_addr m < 2 ^ 64) -> M mid ->
  map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] ->
  ⊢ dgx_G v -∗ ▷ (∀ q, dgx_T v mid q -∗ WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame f e ls None
      (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Herr Hreg.
  intros (Hk & Hg & Hchr & Hchrn & H1 & H2 & H3 & Hl & (Hrb & Hro & Hal & Hend & Hrr) & Hglo & Hbnd & Hv & _) Hm Hmid Hargs.
  pose proof (hello_heap_glibc ob Hk Hg) as Hh.
  pose proof (hk_gi_strlen _ _ Hk). pose proof (hk_free _ _ Hk).
  pose proof (hk_malloc _ _ Hk). pose proof (hk_malloc2 _ _ Hk).
  destruct Hg as [? ? ? ? ? ? ? ? ? _].
  assert (Hlinks : v = 0 \/ dci_strchr_links) by (right; split; assumption).
  unfold dgx_G, dgx_T, dgx_before, dgx_after. iIntros "((%bs & HB) & HS & HL) HK".
  iApply (wp_dcgettext_c_real_v eb Herr Hreg (hk_sys _ _ Hk) with "HB");
    try first [exact Hh | exact Hlinks | exact (Hm mid Hmid) | eassumption | exact _].
  iNext. iIntros (q) "HA". iApply "HK". iFrame "HS HL". iExists bs. iExact "HA".
Qed.

(** Printing a translated message takes T and gives G back. The
    arguments after the message are the strings and integers that X
    describes. *)
Lemma dgx_print_t v mid q ys X f e ls l d args rest j Φ :
  dgx_premises v -> 0 <= ptr_addr mid < 2 ^ 64 -> forallb snapshot_word ys = true ->
  (Lm ⊢ ∃ dq reg, live_capq dq (ptr_cap mid) reg ∗ (live_capq dq (ptr_cap mid) reg -∗ Lm)) ->
  fx_format vb fp mid ys (F ∗ X) Q ->
  map_option (arg_x ge e) args = Some (WPtr fp :: WPtr q :: ys) ->
  ⊢ dgx_T v mid q -∗ X -∗ ▷ (∀ x, dgx_G v -∗ WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame f e ls None
      (Exec l (Call (CResult d W) (Global (TAtom "__fxprintf_nocancel")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Hreg.
  intros Hp Hmr Hys Hlm Hfm Hargs. pose proof Hp as (Hk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfn & Hself & Hselfr & _ & _ & Hcy).
  iIntros "((%bs & HA) & HS & HL) HX HK". iDestruct (dgx_cycle with "HA") as "[%Hq HB]". subst q.
  iApply (wp_call_fx_loan Hreg (hk_sys _ _ Hk) (dgx_before v (le_bytes (dci_w bs) 4) ∗ dgx_stream ∗ Lm) (dgx_G v)
    vb sb sreg fp mid ys F X Q with "[$HB $HS $HL] HX [HK]");
    [exact Hfn | exact Hself | exact Hselfr | exact Hargs | exact Hys | | exact Hfm |].
  - apply dgx_loan; [exact Hmr | exact Hlm | exact Hcy | iIntros "H"; iExists _; iExact "H"].
  - iNext. iIntros (x) "HG". iApply ("HK" $! (x mod 2 ^ 32) with "HG").
Qed.

(** Printing a fixed format that getopt does not translate takes G and
    gives G back. *)
Lemma dgx_print_g v fmt ys X f e ls l d args rest j Φ :
  dgx_premises v -> 0 <= ptr_addr fmt < 2 ^ 64 -> forallb snapshot_word ys = true ->
  (Lm ⊢ ∃ dq reg, live_capq dq (ptr_cap fmt) reg ∗ (live_capq dq (ptr_cap fmt) reg -∗ Lm)) ->
  fx_format vb fp fmt ys (F ∗ X) Q ->
  map_option (arg_x ge e) args = Some (WPtr fp :: WPtr fmt :: ys) ->
  ⊢ dgx_G v -∗ X -∗ ▷ (∀ x, dgx_G v -∗ WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame f e ls None
      (Exec l (Call (CResult d W) (Global (TAtom "__fxprintf_nocancel")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Hreg.
  intros Hp Hmr Hys Hlm Hfm Hargs. pose proof Hp as (Hk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfn & Hself & Hselfr & _ & _ & Hcy).
  iIntros "HG HX HK".
  iApply (wp_call_fx_loan Hreg (hk_sys _ _ Hk) (dgx_G v) (dgx_G v) vb sb sreg fp fmt ys F X Q with "HG HX [HK]");
    [exact Hfn | exact Hself | exact Hselfr | exact Hargs | exact Hys | | exact Hfm |].
  - apply dgx_loan; [exact Hmr | exact Hlm | exact Hcy | done].
  - iNext. iIntros (x) "HG". iApply ("HK" $! (x mod 2 ^ 32) with "HG").
Qed.

(** ## The two rules *)

(** This lemma builds the rule for short options. Besides the shared
    premises, the caller lends the lifetimes of the two messages and
    states what the formatter does with each of them. *)
Lemma hello_getopt_diag_rule_gettext v :
  dgx_premises v -> (forall mid, diag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) -> dgx_lends (diag_msg ge) ->
  (forall mid a0 s0 c, diag_msg ge mid -> 0 <= c < 2 ^ 32 ->
     fx_format vb fp mid [WPtr a0; WInt c] (F ∗ word_string DfracDiscarded a0 s0) Q) ->
  getopt_diag_rule w0 registry ge (dgx_G v) (dgx_T v) fp dom.
Proof.
  intros Hp Hm Hlm Hfm. pose proof Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd & Hf & _).
  refine (conj Hd (conj Hf (conj (dgx_cap v) (conj _ _)))).
  - intros f e ls l d args rest j mid Φ Hmid Hargs. exact (dgx_translate v _ f e ls l d args rest j mid Φ Hp Hm Hmid Hargs).
  - intros f e ls l d args rest j mid q a0 s0 c Φ Hmid Hc Hargs.
    pose proof (Hm mid Hmid). eapply (dgx_print_t v mid q [WPtr a0; WInt c]); first [exact Hp | lia | reflexivity | exact (Hlm mid Hmid) |
      exact (Hfm mid a0 s0 c Hmid Hc) | exact Hargs].
Qed.

(** This lemma builds the rule for long options. The caller also lends
    the lifetimes of the two formats that getopt prints untranslated,
    and states what the formatter does with each kind of print. *)
Lemma hello_getopt_ldiag_rule_gettext v :
  dgx_premises v -> (forall mid, ldiag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  dgx_lends (fun p => ldiag_msg ge p \/ p = f140 \/ p = f141) ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 -> 0 <= ptr_addr f140 < 2 ^ 64 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 -> 0 <= ptr_addr f141 < 2 ^ 64 ->
  (forall mid a0 s0 pfx sp nm sn, ldiag_msg ge mid ->
     fx_format vb fp mid [WPtr a0; WPtr pfx; WPtr nm]
       (F ∗ (word_string DfracDiscarded a0 s0 ∗ word_string DfracDiscarded pfx sp ∗ word_string DfracDiscarded nm sn)) Q) ->
  (forall pfx sp nm sn, fx_format vb fp f140 [WPtr pfx; WPtr nm]
     (F ∗ (word_string DfracDiscarded pfx sp ∗ word_string DfracDiscarded nm sn)) Q) ->
  fx_format vb fp f141 [] (F ∗ True) Q ->
  getopt_ldiag_rule w0 registry ge (dgx_G v) (dgx_T v) fp dom.
Proof.
  intros Hp Hm Hlm H140 Hr140 H141 Hr141 Hfm Hfm140 Hfm141.
  pose proof Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd & Hf & _).
  refine (conj Hd (conj Hf (conj (dgx_cap v) (conj _ (conj _ (conj _ _)))))).
  - intros f e ls l d args rest j mid Φ Hmid Hargs. exact (dgx_translate v _ f e ls l d args rest j mid Φ Hp Hm Hmid Hargs).
  - intros f e ls l d args rest j mid q a0 s0 pfx sp nm sn Φ Hmid Hargs. iIntros "HT Ha Hp Hn HK".
    pose proof (Hm mid Hmid).
    iApply (dgx_print_t v mid q [WPtr a0; WPtr pfx; WPtr nm]
      (word_string DfracDiscarded a0 s0 ∗ word_string DfracDiscarded pfx sp ∗ word_string DfracDiscarded nm sn)%I with "HT [$Ha $Hp $Hn] HK"); first [exact Hp | lia | reflexivity |
      exact (Hlm mid (or_introl Hmid)) | exact (Hfm mid a0 s0 pfx sp nm sn Hmid) | exact Hargs].
  - intros f e ls l d args rest j fmt pfx sp nm sn Φ Hfmt Hargs. rewrite H140 in Hfmt. injection Hfmt as <-.
    iIntros "HG Hp Hn HK".
    iApply (dgx_print_g v f140 [WPtr pfx; WPtr nm] (word_string DfracDiscarded pfx sp ∗ word_string DfracDiscarded nm sn)%I with "HG [$Hp $Hn] HK"); first [exact Hp | exact Hr140 | reflexivity |
      exact (Hlm f140 (or_intror (or_introl eq_refl))) | exact (Hfm140 pfx sp nm sn) | exact Hargs].
  - intros f e ls l d args rest j fmt Φ Hfmt Hargs. rewrite H141 in Hfmt. injection Hfmt as <-.
    iIntros "HG HK".
    iApply (dgx_print_g v f141 [] True%I with "HG [//] HK"); first [exact Hp | exact Hr141 | reflexivity |
      exact (Hlm f141 (or_intror (or_intror eq_refl))) | exact Hfm141 | exact Hargs].
Qed.

(** ## Lending errno to the formatter

    A real formatter may write errno, for example when a write fails,
    so it needs the errno cell while it runs. The rules above leave that
    cell beside the translation's resources, and a formatter whose F
    claimed errno too would ask for the same cell twice. The rules below
    take errno out of the held resources at each print and lend it to the
    formatter once, beside F. The formatter hands errno back with some
    value, and the rules rebuild the same G. *)

(** The formatter returns errno with any bytes, F, and a stream that is
    not wide. *)
Definition dgx_qe : Prop := forall x m, Q x m ⊢ ⌜m = 0 \/ m = 2 ^ 32 - 1⌝ ∗ errno_any eb ∗ F.

(** The rules below need the same program and global cells as the rules
    above. Only the promise about what the formatter returns changes:
    it must now hand errno back as well. *)
Definition dgx_premises_e (v : Z) : Prop :=
  hello_link ge ob /\ hello_gettext_link ge /\
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) /\
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) /\
  rw_ready lk1 a1 ar1 tb tbreg r1 cw1 tid /\ rw_ready lk2 a2 ar2 tb tbreg r2 cw2 tid /\ rw_ready lkt a3 ar3 tb tbreg r3 cw3 tid /\
  locale_cells gb go greg lp lb lreg /\
  (0 < rb /\ 0 <= ro /\ (rb + ro) mod 8 = 0 /\ rb + ro + 8 <= r_end rreg /\ r_end rreg <= 2 ^ 48) /\
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec /\
  dci_bounds db dbreg nb ib ic ireg k sec secreg /\ 0 <= v < 2 ^ 32 /\
  find_fn ge (TAtom "__fxprintf_nocancel") = Some (Defined glibc_fxprintf_nocancel) /\
  ptr_addr (ow_self w0) <> 0 /\ 0 <= ptr_addr (ow_self w0) < 2 ^ 64 /\
  lookup (TAtom "__GI__libc_intl_domainname") (ge_globals ge) = Some dom /\ 0 <= ptr_addr fp < 2 ^ 64 /\
  dgx_qe.

(** A formatter that returns errno also returns F, so the translation
    can still use the facts of the rules above. *)
Lemma dgx_premises_of_e v : dgx_premises_e v -> dgx_premises v.
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & Hqe).
  refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A9 (conj A10 (conj A11
    (conj A12 (conj A13 (conj A14 (conj A15 (conj A16 (conj A17 _))))))))))))))))).
  intros x m. iIntros "HQ". iDestruct (Hqe x m with "HQ") as "($ & _ & $)".
Qed.

(** The resources before a translation hold errno's bytes once, and
    the rest of them accepts any new bytes. *)
Lemma dgx_errno v bs : dgx_before v bs ⊢ errno_own eb bs ∗ (∀ bs', errno_own eb bs' -∗ dgx_before v bs').
Proof using Type.
  unfold dgx_before, dcg_before_v. iIntros "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & He)".
  iSplitL "He"; [iExact "He"|]. iIntros (bs') "He". iSplitL "H1"; [iExact "H1"|].
  iSplitL "H2"; [iExact "H2"|]. iSplitL "H3"; [iExact "H3"|]. iSplitL "H4"; [iExact "H4"|].
  iSplitL "H5"; [iExact "H5"|]. iSplitL "H6"; [iExact "H6"|]. iSplitL "H7"; [iExact "H7"|]. iExact "He".
Qed.

(** A print lends the stream to the wrapper, and the wrapper lends the
    errno cell and F to the formatter. The caller keeps the rest of its
    resources. After the call it gets the stream back in the mode that
    the formatter left, and errno back with new bytes. *)
Lemma dgx_loan_e K Kb fmt :
  0 <= ptr_addr fmt < 2 ^ 64 ->
  (Lm ⊢ ∃ dq reg, live_capq dq (ptr_cap fmt) reg ∗ (live_capq dq (ptr_cap fmt) reg -∗ Lm)) ->
  dgx_qe -> (K ∗ errno_any eb ⊢ Kb) ->
  fx_loan ((K ∗ errno_any eb) ∗ dgx_stream ∗ Lm) vb sb sreg fp fmt (errno_any eb ∗ F) Q (Kb ∗ dgx_stream ∗ Lm).
Proof using Type.
  intros Hfr Hl Hqe Hk. unfold fx_loan, dgx_stream.
  iIntros "((HK & He) & (#Hs & %mode & %flags2 & %held & %Hp & Hst & Ho & HF) & HL)".
  iDestruct (Hl with "HL") as (dq reg) "[Hc HL]".
  iExists mode, flags2, held, dq, reg. iSplit; [iPureIntro; tauto|]. iSplitR; [iExact "Hs"|].
  iSplitL "Hst"; [iExact "Hst"|]. iSplitL "Ho"; [iExact "Ho"|]. iSplitL "Hc"; [iExact "Hc"|].
  iSplitL "He HF"; [iSplitL "He"; [iExact "He" | iExact "HF"]|].
  iIntros (x mode') "Hst Ho Hc HQ". iDestruct (Hqe x mode' with "HQ") as "(%Hm & He & HF)".
  iSplitL "HK He"; [iApply Hk; iSplitL "HK"; [iExact "HK" | iExact "He"]|]. iSplitR "Hc HL"; [|iApply ("HL" with "Hc")].
  iSplitR; [iExact "Hs"|]. iExists mode', flags2, held. iFrame "Hst Ho HF". iPureIntro. tauto.
Qed.

(** After the print, the caller puts errno back with the resources that
    it kept. The bytes of errno do not matter, because G does not fix
    them. *)
Lemma dgx_errno_back v :
  (∀ bs', errno_own eb bs' -∗ dgx_before v bs') ∗ errno_any eb ⊢ ∃ bs, dgx_before v bs.
Proof using Type. iIntros "[HK [%bs He]]". iExists bs. iApply ("HK" with "He"). Qed.

(** Printing a translated message takes T and gives G back, and the
    formatter borrows errno once. *)
Lemma dgx_print_t_e v mid q ys X f e ls l d args rest j Φ :
  dgx_premises_e v -> 0 <= ptr_addr mid < 2 ^ 64 -> forallb snapshot_word ys = true ->
  (Lm ⊢ ∃ dq reg, live_capq dq (ptr_cap mid) reg ∗ (live_capq dq (ptr_cap mid) reg -∗ Lm)) ->
  fx_format vb fp mid ys ((errno_any eb ∗ F) ∗ X) Q ->
  map_option (arg_x ge e) args = Some (WPtr fp :: WPtr q :: ys) ->
  ⊢ dgx_T v mid q -∗ X -∗ ▷ (∀ x, dgx_G v -∗ WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame f e ls None
      (Exec l (Call (CResult d W) (Global (TAtom "__fxprintf_nocancel")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Hreg.
  intros Hp Hmr Hys Hlm Hfm Hargs. pose proof Hp as (Hk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfn & Hself & Hselfr & _ & _ & Hqe).
  iIntros "((%bs & HA) & HS & HL) HX HK". iDestruct (dgx_cycle with "HA") as "[%Hq HB]". subst q.
  iDestruct (dgx_errno with "HB") as "[He HB]".
  iAssert (errno_any eb) with "[He]" as "He"; [iExists _; iExact "He"|].
  iApply (wp_call_fx_loan Hreg (hk_sys _ _ Hk)
    (((∀ bs', errno_own eb bs' -∗ dgx_before v bs') ∗ errno_any eb) ∗ dgx_stream ∗ Lm) (dgx_G v)
    vb sb sreg fp mid ys (errno_any eb ∗ F) X Q with "[$HB $He $HS $HL] HX [HK]");
    [exact Hfn | exact Hself | exact Hselfr | exact Hargs | exact Hys | | exact Hfm |].
  - apply dgx_loan_e; [exact Hmr | exact Hlm | exact Hqe | apply dgx_errno_back].
  - iNext. iIntros (x) "HG". iApply ("HK" $! (x mod 2 ^ 32) with "HG").
Qed.

(** Printing an untranslated format takes G and gives G back, and the
    formatter borrows errno once. *)
Lemma dgx_print_g_e v fmt ys X f e ls l d args rest j Φ :
  dgx_premises_e v -> 0 <= ptr_addr fmt < 2 ^ 64 -> forallb snapshot_word ys = true ->
  (Lm ⊢ ∃ dq reg, live_capq dq (ptr_cap fmt) reg ∗ (live_capq dq (ptr_cap fmt) reg -∗ Lm)) ->
  fx_format vb fp fmt ys ((errno_any eb ∗ F) ∗ X) Q ->
  map_option (arg_x ge e) args = Some (WPtr fp :: WPtr fmt :: ys) ->
  ⊢ dgx_G v -∗ X -∗ ▷ (∀ x, dgx_G v -∗ WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame f e ls None
      (Exec l (Call (CResult d W) (Global (TAtom "__fxprintf_nocancel")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Hreg.
  intros Hp Hmr Hys Hlm Hfm Hargs. pose proof Hp as (Hk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfn & Hself & Hselfr & _ & _ & Hqe).
  iIntros "((%bs & HB) & HS & HL) HX HK". iDestruct (dgx_errno with "HB") as "[He HB]".
  iAssert (errno_any eb) with "[He]" as "He"; [iExists _; iExact "He"|].
  iApply (wp_call_fx_loan Hreg (hk_sys _ _ Hk)
    (((∀ bs', errno_own eb bs' -∗ dgx_before v bs') ∗ errno_any eb) ∗ dgx_stream ∗ Lm) (dgx_G v)
    vb sb sreg fp fmt ys (errno_any eb ∗ F) X Q with "[$HB $He $HS $HL] HX [HK]");
    [exact Hfn | exact Hself | exact Hselfr | exact Hargs | exact Hys | | exact Hfm |].
  - apply dgx_loan_e; [exact Hmr | exact Hlm | exact Hqe | apply dgx_errno_back].
  - iNext. iIntros (x) "HG". iApply ("HK" $! (x mod 2 ^ 32) with "HG").
Qed.

(** This is the short-option rule with errno lent to the formatter. *)
Lemma hello_getopt_diag_rule_gettext_e v :
  dgx_premises_e v -> (forall mid, diag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) -> dgx_lends (diag_msg ge) ->
  (forall mid a0 s0 c, diag_msg ge mid -> 0 <= c < 2 ^ 32 ->
     fx_format vb fp mid [WPtr a0; WInt c] ((errno_any eb ∗ F) ∗ word_string DfracDiscarded a0 s0) Q) ->
  getopt_diag_rule w0 registry ge (dgx_G v) (dgx_T v) fp dom.
Proof.
  intros Hp Hm Hlm Hfm. pose proof (dgx_premises_of_e v Hp) as Ho.
  pose proof Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd & Hf & _).
  refine (conj Hd (conj Hf (conj (dgx_cap v) (conj _ _)))).
  - intros f e ls l d args rest j mid Φ Hmid Hargs. exact (dgx_translate v _ f e ls l d args rest j mid Φ Ho Hm Hmid Hargs).
  - intros f e ls l d args rest j mid q a0 s0 c Φ Hmid Hc Hargs.
    pose proof (Hm mid Hmid). eapply (dgx_print_t_e v mid q [WPtr a0; WInt c]); first [exact Hp | lia | reflexivity | exact (Hlm mid Hmid) |
      exact (Hfm mid a0 s0 c Hmid Hc) | exact Hargs].
Qed.

(** This is the long-option rule with errno lent to the formatter. *)
Lemma hello_getopt_ldiag_rule_gettext_e v :
  dgx_premises_e v -> (forall mid, ldiag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  dgx_lends (fun p => ldiag_msg ge p \/ p = f140 \/ p = f141) ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 -> 0 <= ptr_addr f140 < 2 ^ 64 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 -> 0 <= ptr_addr f141 < 2 ^ 64 ->
  (forall mid a0 s0 pfx sp nm sn, ldiag_msg ge mid ->
     fx_format vb fp mid [WPtr a0; WPtr pfx; WPtr nm]
       ((errno_any eb ∗ F) ∗ (word_string DfracDiscarded a0 s0 ∗ word_string DfracDiscarded pfx sp ∗
         word_string DfracDiscarded nm sn)) Q) ->
  (forall pfx sp nm sn, fx_format vb fp f140 [WPtr pfx; WPtr nm]
     ((errno_any eb ∗ F) ∗ (word_string DfracDiscarded pfx sp ∗ word_string DfracDiscarded nm sn)) Q) ->
  fx_format vb fp f141 [] ((errno_any eb ∗ F) ∗ True) Q ->
  getopt_ldiag_rule w0 registry ge (dgx_G v) (dgx_T v) fp dom.
Proof.
  intros Hp Hm Hlm H140 Hr140 H141 Hr141 Hfm Hfm140 Hfm141. pose proof (dgx_premises_of_e v Hp) as Ho.
  pose proof Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd & Hf & _).
  refine (conj Hd (conj Hf (conj (dgx_cap v) (conj _ (conj _ (conj _ _)))))).
  - intros f e ls l d args rest j mid Φ Hmid Hargs. exact (dgx_translate v _ f e ls l d args rest j mid Φ Ho Hm Hmid Hargs).
  - intros f e ls l d args rest j mid q a0 s0 pfx sp nm sn Φ Hmid Hargs. iIntros "HT Ha Hp Hn HK".
    pose proof (Hm mid Hmid).
    iApply (dgx_print_t_e v mid q [WPtr a0; WPtr pfx; WPtr nm]
      (word_string DfracDiscarded a0 s0 ∗ word_string DfracDiscarded pfx sp ∗ word_string DfracDiscarded nm sn)%I with "HT [$Ha $Hp $Hn] HK"); first [exact Hp | lia | reflexivity |
      exact (Hlm mid (or_introl Hmid)) | exact (Hfm mid a0 s0 pfx sp nm sn Hmid) | exact Hargs].
  - intros f e ls l d args rest j fmt pfx sp nm sn Φ Hfmt Hargs. rewrite H140 in Hfmt. injection Hfmt as <-.
    iIntros "HG Hp Hn HK".
    iApply (dgx_print_g_e v f140 [WPtr pfx; WPtr nm] (word_string DfracDiscarded pfx sp ∗ word_string DfracDiscarded nm sn)%I with "HG [$Hp $Hn] HK"); first [exact Hp | exact Hr140 | reflexivity |
      exact (Hlm f140 (or_intror (or_introl eq_refl))) | exact (Hfm140 pfx sp nm sn) | exact Hargs].
  - intros f e ls l d args rest j fmt Φ Hfmt Hargs. rewrite H141 in Hfmt. injection Hfmt as <-.
    iIntros "HG HK".
    iApply (dgx_print_g_e v f141 [] True%I with "HG [//] HK"); first [exact Hp | exact Hr141 | reflexivity |
      exact (Hlm f141 (or_intror (or_intror eq_refl))) | exact Hfm141 | exact Hargs].
Qed.

(** ## Controls *)

(** The rules ask for the same premises when the flag reads 0, 1 or
    0xdeadbeef, because the backend's strchr bindings serve a set flag.
    A value that is not a 32-bit word is refused. *)
Example dgx_flag_controls :
  (dgx_premises 0 <-> dgx_premises 1) /\ (dgx_premises 1 <-> dgx_premises 3735928559) /\ ~ dgx_premises (2 ^ 32).
Proof.
  assert (Hmv : forall v v', 0 <= v' < 2 ^ 32 -> dgx_premises v -> dgx_premises v').
  { intros v v' Hv' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & _ & A13 & A14 & A15 & A16 & A17 & A18).
    exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A9 (conj A10 (conj A11
      (conj Hv' (conj A13 (conj A14 (conj A15 (conj A16 (conj A17 A18))))))))))))))))). }
  split_and!; try split; try (apply Hmv; lia).
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hv & _). lia.
Qed.

(** After a translation the caller holds the message as the result and
    the flag with the value it lent. *)
Example dgx_after_controls v bs mid q :
  dgx_after v bs mid q ⊢ ⌜q = mid⌝ ∗ liveq dqs sec secreg ∗ int_cellq dqs sec 0 v.
Proof. unfold dgx_after. apply dcg_after_v_flag. Qed.

(** Errno's bytes change across a translation, so G cannot fix them.
    Four bytes come back as they were, but two bytes come back as four
    zeros, and the cycle still closes because G hides the bytes. *)
Example dgx_errno_controls :
  le_bytes (dci_w [1; 2; 3; 4]) 4 = [1; 2; 3; 4] /\ le_bytes (dci_w [9; 9]) 4 = [0; 0; 0; 0] /\
  (forall v bs mid q, dgx_after v bs mid q ⊢ ⌜q = mid⌝ ∗ ∃ bs', dgx_before v bs').
Proof.
  split; [vm_compute; reflexivity | split; [vm_compute; reflexivity |]].
  intros v bs mid q. iIntros "H". iDestruct (dgx_cycle with "H") as "[$ H]". iExists _. iExact "H".
Qed.

(** The wrapper copies the arguments that follow the format, and it
    accepts the lists that getopt's four prints pass. The stream that G
    lends cannot be in the wide mode 1. *)
Example dgx_print_controls a0 c pfx nm :
  forallb snapshot_word [WPtr a0; WInt c] = true /\ forallb snapshot_word [WPtr a0; WPtr pfx; WPtr nm] = true /\
  forallb snapshot_word [WPtr pfx; WPtr nm] = true /\ forallb snapshot_word [] = true /\
  ~ (1 = 0 \/ 1 = 2 ^ 32 - 1).
Proof. split_and!; first [reflexivity | lia]. Qed.
(** A formatter that may leave the stream wide cannot meet the rules'
    premise, because the next report needs a stream that is not wide. *)
Example dgx_wide_refused : ~ (forall (x m : Z), (⌜m = 1⌝ : iProp Σ) ⊢ ⌜m = 0 \/ m = 2 ^ 32 - 1⌝ ∗ F).
Proof.
  intros H. assert (Hp : ⊢ (⌜1 = 0 \/ 1 = 2 ^ 32 - 1⌝ : iProp Σ)).
  { iDestruct (H 0 1 with "[//]") as "[$ _]". }
  apply sbi.pure_soundness in Hp. lia.
Qed.
(** Errno changes twice in each report. The translation returns
    errno's bytes in the four-byte form, and the formatter then writes
    any bytes it likes. Here a first report keeps [1; 2; 3; 4] through
    the translation and the formatter writes EBADF, 9. The second report
    keeps 9 through its translation, and its formatter writes 0. *)
Example dgx_errno_cycle_controls v mid1 qa mid2 qb :
  (dgx_after v [1; 2; 3; 4] mid1 qa ⊢ ⌜qa = mid1⌝ ∗ errno_own eb [1; 2; 3; 4] ∗
     (errno_own eb [9; 0; 0; 0] -∗ ∃ bs, dgx_before v bs)) /\
  (dgx_after v [9; 0; 0; 0] mid2 qb ⊢ ⌜qb = mid2⌝ ∗ errno_own eb [9; 0; 0; 0] ∗
     (errno_own eb [0; 0; 0; 0] -∗ ∃ bs, dgx_before v bs)) /\
  ([1; 2; 3; 4] <> [9; 0; 0; 0] /\ [9; 0; 0; 0] <> [0; 0; 0; 0]).
Proof.
  assert (H : forall bs bs2 mid q, le_bytes (dci_w bs) 4 = bs ->
    dgx_after v bs mid q ⊢ ⌜q = mid⌝ ∗ errno_own eb bs ∗ (errno_own eb bs2 -∗ ∃ bs, dgx_before v bs)).
  { intros bs bs2 mid q Hb. iIntros "HA". iDestruct (dgx_cycle with "HA") as "[$ HB]". rewrite Hb.
    iDestruct (dgx_errno with "HB") as "[$ HB]". iIntros "He". iExists bs2. iApply ("HB" with "He"). }
  split; [apply H; vm_compute; reflexivity|]. split; [apply H; vm_compute; reflexivity|]. split; discriminate.
Qed.

(** A formatter that owns nothing of its own still works. It gets the
    errno cell from the loan, not from F, and it meets the rules'
    promise by handing errno back with a narrow stream. *)
Example dgx_empty_frame_controls :
  (F ⊣⊢ emp) -> (forall x m, Q x m ⊣⊢ ⌜m = 0⌝ ∗ errno_any eb) -> dgx_qe /\ (errno_any eb ∗ F ⊣⊢ errno_any eb).
Proof.
  intros HF HQ. split.
  - intros x m. rewrite HQ HF. iIntros "[-> He]". iSplit; [iPureIntro; left; reflexivity|]. iFrame "He".
  - rewrite HF. apply bi.sep_emp.
Qed.

(** Errno's bytes have one owner. If F also claimed errno, G would ask
    for the same cell twice, and no state could hold it. *)
Example dgx_duplicate_errno_refused v : (F ⊢ errno_any eb ∗ True) -> dgx_G v ⊢ False.
Proof.
  intros HF. unfold dgx_G, dgx_stream. iIntros "((%bs & HB) & (_ & %mode & %flags2 & %held & _ & _ & _ & HF) & _)".
  iDestruct (dgx_errno with "HB") as "[He _]". iDestruct (HF with "HF") as "[[%bs' He'] _]".
  iDestruct "He" as (cs) "([%Hl _] & He)". iDestruct "He'" as (cs') "([%Hl' _] & He')".
  destruct bs as [|b0 bs]; [discriminate|]. destruct bs' as [|b0' bs']; [discriminate|].
  rewrite byte_ps_cons byte_ps_cons /pts /ptsq /=. iDestruct "He" as "[He _]". iDestruct "He'" as "[He' _]".
  iDestruct (pointsto_valid_2 with "He He'") as %[Hv _].
  rewrite dfrac_op_own dfrac_valid_own in Hv. exfalso. apply (Qp.not_add_le_l 1 1). exact Hv.
Qed.
End rules.
