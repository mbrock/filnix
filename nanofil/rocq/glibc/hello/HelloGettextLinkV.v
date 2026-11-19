From Glibc Require Import GlibcProgram.
(** HelloGettextLink.v proves a getopt diagnostic's translation in
    Hello's link, but only for a privilege flag that reads 0. Hello's
    linked image starts the flag at 1. This module proves the same
    translation for any 32-bit value of the flag, using the rules of
    DcgettextRealV.v.

    A set flag makes gettext call strchr and strchrnul, and neither link
    record says where those two functions live. This module leaves both
    records as they are. The caller instead shows that Hello's program
    finds the two functions where the selection of HelloStrchrImage.v
    finds them. The producer checked this on the full image, but Rocq has
    not. A caller whose flag reads 0 needs no such premise. *)
From Glibc Require Import GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv LibioLogic StrlenLogic WordString SysWrappers.
From Glibc Require Import AllocLogic AllocCall HelloGlibcDebts HelloGlibcLibsT.
From Glibc Require Import TfindEmpty LocalenameLogic.
From Glibc Require Import GetoptDiag GetoptLongDiag GetoptDiagFx.
From Glibc Require Import DcigettextRoute DcigettextSecure.
From Glibc Require Import DcgettextC DcgettextLocale DcgettextRwlock DcgettextRealV.
From Glibc Require Import HelloGettextLink HelloGettextImage HelloStrchrImageCode HelloStrchrImage.
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

(** A caller with a nonzero flag shows that Hello's module agrees with
    the strchr selection. This predicate states that choice. *)
Definition hello_secure_links (v : Z) : Prop :=
  v = 0 \/ Forall (lookup_agrees (ge_module ge) hellostrchrimage_module) hello_strchr_names.

Lemma hello_secure_links_dci v : hello_secure_links v -> v = 0 \/ dci_strchr_links.
Proof using Type. intros [H | H]; [left; exact H | right; exact (dci_strchr_links_of_agree H)]. Qed.

(** ## The translation in Hello's link *)

(** In Hello's link, a getopt diagnostic's call to dcgettext follows the
    C-locale route for every value of the flag. *)
Lemma wp_dcgettext_c_hello_v f e ls l d args rest j mid dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg v
    tc dd bs ob dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    lk1 a1 ar1 r1 cw1 sh1 fl1 q1 i1 lk2 a2 ar2 r2 cw2 sh2 fl2 q2 i2 lkt a3 ar3 r3 cw3 sh3 fl3 q3 i3 tb tbreg tid Φ :
  hello_link ge ob -> hello_gettext_link ge -> rw_ready lk1 a1 ar1 tb tbreg r1 cw1 tid -> rw_ready lk2 a2 ar2 tb tbreg r2 cw2 tid -> rw_ready lkt a3 ar3 tb tbreg r3 cw3 tid ->
  locale_cells gb go greg lp lb lreg ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  0 <= v < 2 ^ 32 -> hello_secure_links v ->
  map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] -> 0 < ptr_addr mid < 2 ^ 64 ->
  dcg_before_v eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hello_gettext_cache ob) bs -∗
  ▷ (∀ q, dcg_after_v eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hello_gettext_cache ob) bs mid q -∗
      WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hk Hg ? ? ? ? ? ? ? ? ? ? ? ? Hs. pose proof (hello_heap_glibc ob Hk Hg) as Hh.
  pose proof (hello_secure_links_dci v Hs) as Hl.
  pose proof (hk_gi_strlen _ _ Hk). pose proof (hk_free _ _ Hk).
  pose proof (hk_malloc _ _ Hk). pose proof (hk_malloc2 _ _ Hk).
  destruct Hg as [? ? ? ? ? ? ? ? ? _].
  eapply (wp_dcgettext_c_real_v eb Herr Hreg (hk_sys _ _ Hk)); first [exact Hh | exact Hl | eassumption | exact _].
Qed.

(** This lemma builds the short-option translation premise in the same
    way. *)
Lemma dcg_diag_translate_hello_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg v
    tc dd bs ob dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    lk1 a1 ar1 r1 cw1 sh1 fl1 q1 i1 lk2 a2 ar2 r2 cw2 sh2 fl2 q2 i2 lkt a3 ar3 r3 cw3 sh3 fl3 q3 i3 tb tbreg tid :
  hello_link ge ob -> hello_gettext_link ge -> rw_ready lk1 a1 ar1 tb tbreg r1 cw1 tid -> rw_ready lk2 a2 ar2 tb tbreg r2 cw2 tid -> rw_ready lkt a3 ar3 tb tbreg r3 cw3 tid ->
  locale_cells gb go greg lp lb lreg ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  0 <= v < 2 ^ 32 -> hello_secure_links v ->
  (forall mid, diag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  diag_translate (dcg_before_v eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hello_gettext_cache ob) bs)
    (dcg_after_v eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hello_gettext_cache ob) bs)
    dom.
Proof using Type*.
  intros Hk Hg ? ? ? ? ? ? ? ? ? ? ? ? Hs Hm f e ls l d args rest j mid Φ Hmsg Hargs.
  iIntros "Hb HK". iApply (wp_dcgettext_c_hello_v with "Hb HK"); try eassumption. exact (Hm mid Hmsg).
Qed.

(** This lemma builds the long-option translation premise in the same
    way. *)
Lemma dcg_ldiag_translate_hello_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg v
    tc dd bs ob dqr rb ro rreg gb go greg dqg lp lb lreg dql dqn dqt treg
    lk1 a1 ar1 r1 cw1 sh1 fl1 q1 i1 lk2 a2 ar2 r2 cw2 sh2 fl2 q2 i2 lkt a3 ar3 r3 cw3 sh3 fl3 q3 i3 tb tbreg tid :
  hello_link ge ob -> hello_gettext_link ge -> rw_ready lk1 a1 ar1 tb tbreg r1 cw1 tid -> rw_ready lk2 a2 ar2 tb tbreg r2 cw2 tid -> rw_ready lkt a3 ar3 tb tbreg r3 cw3 tid ->
  locale_cells gb go greg lp lb lreg ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  0 <= v < 2 ^ 32 -> hello_secure_links v ->
  (forall mid, ldiag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64) ->
  ldiag_translate (dcg_before_v eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hello_gettext_cache ob) bs)
    (dcg_after_v eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hello_gettext_cache ob) bs)
    dom.
Proof using Type*.
  intros Hk Hg ? ? ? ? ? ? ? ? ? ? ? ? Hs Hm f e ls l d args rest j mid Φ Hmsg Hargs.
  iIntros "Hb HK". iApply (wp_dcgettext_c_hello_v with "Hb HK"); try eassumption. exact (Hm mid Hmsg).
Qed.

(** ## Controls

    The controls fix one Hello link and one set of lent resources, and
    vary only the flag. *)
Section controls.
Context (dom : ptr) (ds : list Z) (dqd : dfrac) (nb : Z) (nc : cap) (k : Z) (cat : list Z) (dqc : dfrac)
  (cv p276 p277 : ptr) (db : Z) (dqb : dfrac) (dbreg : region) (ib : Z) (ic : cap) (dqi : dfrac) (ireg : region)
  (sec : Z) (dqs : dfrac) (secreg : region) (tc dd : ptr) (bs : list Z) (ob : hello_objs)
  (dqr : dfrac) (rb ro : Z) (rreg : region) (gb go : Z) (greg : region) (dqg : dfrac) (lp : ptr) (lb : Z) (lreg : region)
  (dql dqn dqt : dfrac) (treg : region)
  (lk1 : ptr) (a1 : Z) (ar1 : region) (r1 cw1 sh1 fl1 : Z) (q1 i1 : dfrac)
  (lk2 : ptr) (a2 : Z) (ar2 : region) (r2 cw2 sh2 fl2 : Z) (q2 i2 : dfrac)
  (lkt : ptr) (a3 : Z) (ar3 : region) (r3 cw3 sh3 fl3 : Z) (q3 i3 : dfrac) (tb : Z) (tbreg : region) (tid : Z).
Context (Hk : hello_link ge ob) (Hg : hello_gettext_link ge)
  (H1 : rw_ready lk1 a1 ar1 tb tbreg r1 cw1 tid) (H2 : rw_ready lk2 a2 ar2 tb tbreg r2 cw2 tid)
  (H3 : rw_ready lkt a3 ar3 tb tbreg r3 cw3 tid) (Hl : locale_cells gb go greg lp lb lreg)
  (Hrb : 0 < rb) (Hro : 0 <= ro) (Hal : (rb + ro) mod 8 = 0) (Hend : rb + ro + 8 <= r_end rreg) (Hrr : r_end rreg <= 2 ^ 48)
  (Hglo : dci_globals eb lk1 lk2 lkt (mkPtr (rb + ro) (Obj rb)) tc dd db nb nc ib ic p276 p277 sec)
  (Hbnd : dci_bounds db dbreg nb ib ic ireg k sec secreg)
  (Hm : forall mid, diag_msg ge mid -> 0 < ptr_addr mid < 2 ^ 64).

Let Hb v := dcg_before_v eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v
  (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
  (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
  (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hello_gettext_cache ob) bs.
Let Ha v := dcg_after_v eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v
  (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
  (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
  (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hello_gettext_cache ob) bs.

(** A flag that reads 0 needs no strchr agreement, and its translation
    is the old one of HelloGettextLink.v. *)
Example hello_v_zero :
  diag_translate (Hb 0) (Ha 0) dom /\
  diag_translate (Hb 0) (Ha 0) dom =
  diag_translate (dcg_before eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hello_gettext_cache ob) bs)
    (dcg_after eb dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg
      (rw_held a1 ar1 r1 cw1 sh1 fl1 q1 tb tbreg i1 tid) (rw_held a2 ar2 r2 cw2 sh2 fl2 q2 tb tbreg i2 tid)
      (rw_held a3 ar3 r3 cw3 sh3 fl3 q3 tb tbreg i3 tid)
      (tfind_root dqr rb ro rreg) (locale_name_res dqg gb go greg lp dql lb lreg dqn 5 cv dqt treg) (hello_gettext_cache ob) bs)
    dom.
Proof using H1 H2 H3 Hal Hbnd Hend Herr Hg Hglo Hk Hl Hm Hrb Hreg Hro Hrr.
  split; [|reflexivity]. unfold Hb, Ha.
  eapply dcg_diag_translate_hello_v; try eassumption; [lia | left; reflexivity].
Qed.

(** The flag values 1 and 0xdeadbeef take the strchr branch, so their
    translations need the agreement. Each returns the message and the
    flag with the value that the caller lent. *)
Example hello_v_set :
  Forall (lookup_agrees (ge_module ge) hellostrchrimage_module) hello_strchr_names ->
  diag_translate (Hb 1) (Ha 1) dom /\ diag_translate (Hb 3735928559) (Ha 3735928559) dom /\
  (forall mid q, Ha 1 mid q ⊢ ⌜q = mid⌝ ∗ liveq dqs sec secreg ∗ int_cellq dqs sec 0 1) /\
  (forall mid q, Ha 3735928559 mid q ⊢ ⌜q = mid⌝ ∗ liveq dqs sec secreg ∗ int_cellq dqs sec 0 3735928559).
Proof using H1 H2 H3 Hal Hbnd Hend Herr Hg Hglo Hk Hl Hm Hrb Hreg Hro Hrr bs cat cv dqb dqc dqd dqg dqi dql dqn dqr dqt ds fl1 fl2 fl3 i1 i2 i3 q1 q2 q3 sh1 sh2 sh3 treg.
  intros Hagree. unfold Hb, Ha. split_and!;
    try (eapply dcg_diag_translate_hello_v; try eassumption; [lia | right; exact Hagree]);
    intros mid q; apply dcg_after_v_flag.
Qed.

(** A nonzero flag cannot drop the agreement, and a value that is not
    a 32-bit word is refused. *)
Example hello_v_refuses :
  (hello_secure_links 1 -> Forall (lookup_agrees (ge_module ge) hellostrchrimage_module) hello_strchr_names) /\
  (hello_secure_links 3735928559 -> Forall (lookup_agrees (ge_module ge) hellostrchrimage_module) hello_strchr_names) /\
  ~ (0 <= 2 ^ 32 < 2 ^ 32).
Proof using Type. unfold hello_secure_links. split_and!; try (intros [H | H]; [discriminate H | exact H]); lia. Qed.
End controls.
End rules.
