(** When the ASCII step of Hello's wide stream meets a character that
    has no byte, it calls `c: __gconv_transliterate` to find a
    replacement in the C locale. This file proves that whole call: the
    function reads only the locale's tables and the caller's input, and
    it writes only the caller's output window, its cursors and the
    step's flags.

    The function first loads the step and the locale's tables. Then it
    searches the table of source strings, which
    [LibioWConvTranslitSearch] proves. A match leads to the replacement
    strings of [LibioWConvTranslitRepl], and a search without a match
    leads to the default replacement of [LibioWConvTranslitFallback]. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic AbsInfer.
From Glibc Require Import CodePrelude HelloImageLoad HelloImageCode70 HelloImageWConvObjs StartImageEarly
  OsWorld FileInv LibioLogic LibioDefaultXsputnBuf LibioWIdle Mbrtowc CBlocks Fix LibioWConvAscii
  LibioWConvConsts LibioWConvTranslitCmp LibioWConvTranslitSearch LibioWConvTranslitFallback
  LibioWConvTranslitRepl LibioWConvLast.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation objp b := (mkPtr b (Obj b)).
Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation tmb := (img_a "glibc_wcsmbsload#to_mb").
Local Abbreviation fct := (mkPtr (img_a "__gconv_transform_internal_ascii") (Fn (TAtom "__gconv_transform_internal_ascii"))).

(** ## The entry

    The function starts by allocating four eight-byte cursor cells for
    the conversions that it may run. It then reads the step's function
    pointer and the C locale's transliteration tables, which never
    change. These tactics handle those first blocks. *)

(** The tactic [tr_alloc] allocates one cursor cell, which starts zeroed. *)
Local Ltac tr_alloc b H L C :=
  iApply wp_alloc; [reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |]; iNext; iIntros (b H) "Hob";
  change (0 < b /\ b mod 16 = 0 /\ b + 16 <= 2^48) in H;
  iDestruct (obj_zero_block with "Hob") as "(Hobl & Hobb & Hoba)"; [vm_compute; congruence|];
  iDestruct (Mbrtowc.MbVL.zero_cell_prefix b 0 8 with "Hobb Hoba") as "(Hobc & _ & _)";
  iAssert (live b (mkRegion b (b + 16) Heap Live)) with "Hobl" as L;
  iAssert (∃ x, pcell b 0 x)%I with "[Hobc]" as C; [by iExists _|].

(** The tactic [ctype_field] follows the thread's locale pointer to the
    character category and checks the read of one of its fields. *)
Local Ltac ctype_field Hts :=
  step_global Hts; check "Hts"; load_pointer_dq "Hts Hts0 Hgl" by a2; iNext; iIntros "Hts Hts0 Hgl";
  check "Hgl"; load_pointer_dq "Hgl Hgl0 Hcc" by a2; iNext; iIntros "Hgl Hgl0 _";
  do 2 step; check_read_dq "Hcc" by a2; iNext; iIntros "_".

(** A conversion may set bit 30 of the flags, the bit that records
    illegal input, and it never clears that bit. Two conversions in a
    row therefore also leave the flags as they were or with bit 30 set. *)
Lemma flags_step fl fl' fl'' : (fl' = fl \/ fl' = Z.lor fl (2 ^ 30)) ->
  (fl'' = fl' \/ fl'' = Z.lor fl' (2 ^ 30)) -> fl'' = fl \/ fl'' = Z.lor fl (2 ^ 30).
Proof using Type. intros [-> | ->] [-> | ->]; auto. right. rewrite <- Z.lor_assoc, Z.lor_diag. reflexivity. Qed.

Section translit.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hascii : !Defines ge "__gconv_transform_internal_ascii" glibc_internal_ascii}
  (Hfp : function_check_res ge fct = Some ok)
  (Hts : lookup (TAtom "__libc_tsd_LOCALE") (ge_globals ge) = Some (objp (img_a "__libc_tsd_LOCALE"))).
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** The entry reads the step's fields through a read-only pointer, so
    its half check needs only a share of the step's life. This copies
    the rule of [LibioWConvOut], which reads the same step. *)
Local Lemma wp_half_check_read_dq f e ls l d bd lo hi al args rest j classes p1 p b reg dq' Φ :
  op_arg_classes (HalfCheck bd lo hi Read al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p1; WPtr p] ->
  ptr_cap p1 = ptr_cap p -> ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  b <= raw_address (ptr_addr p) lo -> raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg ->
  lo < hi -> r_end reg <= 2 ^ 63 -> raw_address (ptr_addr p) lo mod al = 0 ->
  liveq dq' b reg -∗
  ▷ (liveq dq' b reg -∗ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (HalfCheck bd lo hi Read al) args :: rest) j)) : sexpr) {{ Φ }}.
Proof using Type.
  intros Hc Hx Hp1 Hp H1 H2 H3 H4 H5. apply (wp_read_dq registry (os_wi w0) ge dq' _ _ _ []).
  intros m fuel (Hf & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E Lv] _].
  apply rule_let with (classes := classes) (xs := [WPtr p1; WPtr p]); [reflexivity | exact Hc | exact Hx |].
  exact (op_half_check_read _ _ _ _ _ _ _ _ _ Hp1 Hp E Lv H1 H2 H3 H4 H5).
Qed.

(** The characters to convert can sit in the wide stream's own buffer,
    which lives in the same heap object as the stream. In that case the
    caller holds one lifetime for both. The search wants its own share
    of the input's lifetime, so these two lemmas hand the stream's
    lifetime to the search and take it back afterwards. *)
Lemma input_lend wd wreg ib ireg di : (ib = wd -> ireg = wreg) ->
  live wd wreg ∗ (if decide (ib = wd) then True else liveq di ib ireg) ⊢
  liveq (if decide (ib = wd) then DfracOwn 1 else di) ib ireg ∗ (if decide (ib = wd) then True else live wd wreg).
Proof using Type.
  intros H. iIntros "[A B]". destruct (decide (ib = wd)) as [E | E]; [subst ib; rewrite (H eq_refl) |].
  - iSplitL "A"; [iExact "A" | done].
  - iFrame.
Qed.

Lemma input_return wd wreg ib ireg di : (ib = wd -> ireg = wreg) ->
  liveq (if decide (ib = wd) then DfracOwn 1 else di) ib ireg ∗ (if decide (ib = wd) then True else live wd wreg) ⊢
  live wd wreg ∗ (if decide (ib = wd) then True else liveq di ib ireg).
Proof using Type.
  intros H. iIntros "[A B]". destruct (decide (ib = wd)) as [E | E]; [subst ib; rewrite (H eq_refl) |].
  - iSplitL "A"; [iExact "A" | done].
  - iFrame.
Qed.

(** This is the return of `c: __gconv_transliterate` as its caller
    states it. The status st comes with the input cursor at k', the
    output cursor at j', the output bytes zs' and the flags fl'. *)
Definition translit_k (Φ : outcome -> iProp Σ) wd wreg ib ireg di dqb ic io (ws : list Z) k tb treg to (zs : list Z) j fl pi pireg po poreg lb lbreg dl : iProp Σ :=
  let n := Z.of_nat (length ws) in let m := Z.of_nat (length zs) in
  ∀ st k' j' zs' fl' cnt', ⌜k <= k' <= n /\ j <= j' <= m /\ length zs' = length zs /\
       Forall (fun z => 0 <= z < 256) zs' /\ wflags_ok fl' /\ (fl' = fl \/ fl' = Z.lor fl (2 ^ 30))⌝ -∗
     wlocale dl -∗ live wd wreg -∗ pcell wd 176 (mkPtr (tb + to + m) (Obj tb)) -∗ bytes wd 184 (int_bytes fl') -∗
     (if decide (ib = wd) then True else liveq di ib ireg) -∗ bytesq dqb ib io (le_words ws) -∗ live tb treg -∗ bytes tb to zs' -∗
     live pi pireg -∗ pcell pi 0 (mkPtr (ib + io + 4 * k') ic) -∗ live po poreg -∗ pcell po 0 (mkPtr (tb + to + j') (Obj tb)) -∗
     live lb lbreg -∗ icell lb 0 cnt' -∗ Φ (Ret (WInt st)).

(** The cursor cells that the function allocates hold some pointer. *)
Definition cell16 (b : Z) : iProp Σ := live b (mkRegion b (b + 16) Heap Live) ∗ ∃ x, pcell b 0 x.

Lemma wp_translit fr ip0 wd wreg ib ireg di dqb ic io ws k tb treg to zs j fl pi pireg po poreg lb lbreg cnt dl Φ :
  let n := Z.of_nat (length ws) in let m := Z.of_nat (length zs) in
  call_frame glibc_translit [WPtr (rop tmb); WPtr (mkPtr (wd + 168) (Obj wd)); WPtr ip0; WPtr (objp pi);
    WPtr (mkPtr (ib + io + 4 * n) ic); WPtr (objp po); WPtr (objp lb)] = Some fr ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 ->
  ic = Obj ib \/ ic = Ro ib -> 0 < ib -> 0 <= io -> ib + io + 4 * n <= r_end ireg -> r_end ireg <= 2 ^ 63 ->
  (ib = wd -> ireg = wreg) -> Forall (fun c => 0 <= c < 2 ^ 32) ws -> 0 <= k < n ->
  0 < tb -> 0 <= to -> tb + to + m <= r_end treg -> r_end treg <= 2 ^ 63 -> 0 <= j <= m ->
  Forall (fun z => 0 <= z < 256) zs ->
  0 < pi -> pi mod 8 = 0 -> pi + 8 <= r_end pireg -> r_end pireg <= 2 ^ 63 ->
  0 < po -> po mod 8 = 0 -> po + 8 <= r_end poreg -> r_end poreg <= 2 ^ 63 ->
  0 < lb -> lb mod 8 = 0 -> lb + 8 <= r_end lbreg -> r_end lbreg <= 2 ^ 63 -> wflags_ok fl ->
  wconv_consts -∗ wlocale dl -∗
  live wd wreg -∗ pcell wd 176 (mkPtr (tb + to + m) (Obj tb)) -∗ bytes wd 184 (int_bytes fl) -∗
  (if decide (ib = wd) then True else liveq di ib ireg) -∗ bytesq dqb ib io (le_words ws) -∗ live tb treg -∗ bytes tb to zs -∗
  live pi pireg -∗ pcell pi 0 (mkPtr (ib + io + 4 * k) ic) -∗ live po poreg -∗ pcell po 0 (mkPtr (tb + to + j) (Obj tb)) -∗
  live lb lbreg -∗ icell lb 0 cnt -∗
  ▷ (∀ st k' j' zs' fl' cnt', ⌜k <= k' <= n /\ j <= j' <= m /\ length zs' = length zs /\
       Forall (fun z => 0 <= z < 256) zs' /\ wflags_ok fl' /\ (fl' = fl \/ fl' = Z.lor fl (2 ^ 30))⌝ -∗
     wlocale dl -∗ live wd wreg -∗ pcell wd 176 (mkPtr (tb + to + m) (Obj tb)) -∗ bytes wd 184 (int_bytes fl') -∗
     (if decide (ib = wd) then True else liveq di ib ireg) -∗ bytesq dqb ib io (le_words ws) -∗ live tb treg -∗ bytes tb to zs' -∗
     live pi pireg -∗ pcell pi 0 (mkPtr (ib + io + 4 * k') ic) -∗ live po poreg -∗ pcell po 0 (mkPtr (tb + to + j') (Obj tb)) -∗
     live lb lbreg -∗ icell lb 0 cnt' -∗ Φ (Ret (WInt st))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros n m Hfr Hwd Hwa Hwe Hwr Hic Hib Hio Hie Hir Halias Hws Hk Htb Hto Hte Htr Hj Hzs
    Hpi Hpia Hpie Hpir Hpo Hpoa Hpoe Hpor Hlb Hlba Hlbe Hlbr Hfl.
  iIntros "#Hc Hloc Hwl Hoe Hfl Hil Hin Htl Hzs Hpil Hpi Hpol Hpo Hll Hcnt HK".
  injection Hfr as <-.
  step. tr_alloc b211 H211 "H1l" "H1". tr_alloc b212 H212 "H2l" "H2". tr_alloc b481 H481 "H3l" "H3". tr_alloc b494 H494 "H4l" "H4".
  iDestruct (input_lend with "[$Hwl $Hil]") as "[Hil Hwl]"; [exact Halias|].
  set (dI := if decide (ib = wd) then DfracOwn 1 else di).
  assert (Hlc : forall dq, live_capq dq ic ireg = liveq dq ib ireg) by (intros; destruct Hic as [-> | ->]; reflexivity).
  iPoseProof "Hc" as "(Html & Htm0 & Htm40 & _)".
  check "Hpil". iEval (rewrite -Hlc) in "Hil". load_pointer_dq "Hpil Hpi Hil" by a2.
  iNext. iIntros "Hpil Hpi Hil". iEval (rewrite Hlc) in "Hil". step.
  check_read_dq "Html" by a2. iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Html Htm40 []"); [reflexivity | vx | right; reflexivity | a2 | a2 | a2 | done |].
  iNext. iIntros "_ _ _".
  iApply (wp_half_check_read_dq with "Html"); [reflexivity | vx | reflexivity | right; reflexivity | a2 | a2 | lia | a2 | a2 |].
  iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Html Htm0 []"); [reflexivity | vx | right; reflexivity | a2 | a2 | cbn; lia | done |].
  iNext. iIntros "_ _ _". do 3 step. branch. step.
  step. step. iDestruct "Hloc" as "(Hts & Hts0 & Hgl & Hgl0)".
  iPoseProof "Hc" as "(_ & _ & _ & Hcc & H544 & H552 & H560 & H568 & H576 & _ & _ & _ & _ & _ & Hfil & _ & Hftl & _ & Htil & _ & Httl & _)".
  ctype_field Hts. load_bytes_dq "Hcc H544" decode reflexivity by a2. iNext. iIntros "_ _". step. branch. step.
  ctype_field Hts. load_pointer_dq "Hcc H552 Hfil" by a2. iNext. iIntros "_ _ _".
  ctype_field Hts. load_pointer_dq "Hcc H560 Hftl" by a2. iNext. iIntros "_ _ _".
  ctype_field Hts. load_pointer_dq "Hcc H568 Htil" by a2. iNext. iIntros "_ _ _".
  ctype_field Hts. load_pointer_dq "Hcc H576 Httl" by a2. iNext. iIntros "_ _ _".
  do 4 step.
  branch_w true.
  lazymatch goal with |- context [ERun (mkFrame _ ?E _ _ _)] => set (e0 := E) end.
  Local Ltac lk0 := repeat (rewrite Symbolic.lookup_after_put_other; [|reflexivity]); rewrite Symbolic.lookup_after_put_same;
    try reflexivity; do 2 f_equal; unwrap2; try reflexivity; lia.
  assert (V0 : lookup (TAtom "v0") e0 = Some (WPtr (rop tmb))) by lk0.
  assert (V2 : lookup (TAtom "v2") e0 = Some (WPtr (mkPtr (wd + 168) (Obj wd)))) by lk0.
  assert (V6 : lookup (TAtom "v6") e0 = Some (WPtr (objp pi))) by lk0.
  assert (C0 : lookup (TAtom "chk0") e0 = Some (WPtr (objp pi))) by lk0.
  assert (V8 : lookup (TAtom "v8") e0 = Some (WPtr (mkPtr (ib + io + 4 * n) ic))) by lk0.
  assert (V10 : lookup (TAtom "v10") e0 = Some (WPtr (objp po))) by lk0.
  assert (V12 : lookup (TAtom "v12") e0 = Some (WPtr (objp lb))) by lk0.
  assert (V24 : lookup (TAtom "v24") e0 = Some (WPtr (mkPtr (ib + io + 4 * k) ic))) by lk0.
  assert (V29 : lookup (TAtom "v29") e0 = Some (WPtr fct)) by lk0.
  assert (V211 : lookup (TAtom "v211") e0 = Some (WPtr (objp b211))) by lk0.
  assert (V212 : lookup (TAtom "v212") e0 = Some (WPtr (objp b212))) by lk0.
  assert (V481 : lookup (TAtom "v481") e0 = Some (WPtr (objp b481))) by lk0.
  assert (V494 : lookup (TAtom "v494") e0 = Some (WPtr (objp b494))) by lk0.
  assert (V65 : lookup (TAtom "v65") e0 = Some (WPtr (rop (img_a "glibc_C_ctype#translit_from_idx")))) by lk0.
  assert (V75 : lookup (TAtom "v75") e0 = Some (WPtr (rop (img_a "glibc_C_ctype#translit_from_tbl")))) by lk0.
  assert (V85 : lookup (TAtom "v85") e0 = Some (WPtr (rop (img_a "glibc_C_ctype#translit_to_idx")))) by lk0.
  assert (V95 : lookup (TAtom "v95") e0 = Some (WPtr (rop (img_a "glibc_C_ctype#translit_to_tbl")))) by lk0.
  assert (V103 : lookup (TAtom "v103") e0 = Some (WInt (ib + io + 4 * n))) by lk0.
  assert (V48 : lookup (TAtom "v48") e0 = Some (WInt 1659)) by lk0.
  clearbody e0.
  iAssert (translit_k Φ wd wreg ib ireg di dqb ic io ws k tb treg to zs j fl pi pireg po poreg lb lbreg dl) with "HK" as "HK".
  set (G := fun (zs' : list Z) (fl' : Z) => (⌜length zs' = length zs /\ Forall (fun z => 0 <= z < 256) zs' /\ wflags_ok fl' /\
    (fl' = fl \/ fl' = Z.lor fl (2 ^ 30))⌝ ∗ wlocale dl ∗ (if decide (ib = wd) then True else live wd wreg) ∗
    pcell wd 176 (mkPtr (tb + to + m) (Obj tb)) ∗ bytes wd 184 (int_bytes fl') ∗ live tb treg ∗ bytes tb to zs' ∗
    live pi pireg ∗ pcell pi 0 (mkPtr (ib + io + 4 * k) ic) ∗ live po poreg ∗ pcell po 0 (mkPtr (tb + to + j) (Obj tb)) ∗
    live lb lbreg ∗ icell lb 0 cnt ∗ cell16 b211 ∗ cell16 b212 ∗ cell16 b481 ∗ cell16 b494 ∗
    translit_k Φ wd wreg ib ireg di dqb ic io ws k tb treg to zs j fl pi pireg po poreg lb lbreg dl : iProp Σ)%I).
  iAssert (□ ∀ zs' fl', liveq dI ib ireg -∗ bytesq dqb ib io (le_words ws) -∗ G zs' fl' -∗ Φ (Ret (WInt 7)))%I as "#K7".
  { iIntros "!>" (zs' fl') "Hil Hin (%Hg & Hloc & Hwl & Hoe & Hfl & Htl & Hzs & Hpil & Hpi & Hpol & Hpo & Hll & Hcnt & _ & _ & _ & _ & HK)".
    destruct Hg as (Hlen & Hz' & Hf' & Hfr).
    iDestruct (input_return with "[$Hil $Hwl]") as "[Hwl Hil]"; [exact Halias|].
    iApply ("HK" $! 7 k j zs' fl' cnt with "[%] Hloc Hwl Hoe Hfl Hil Hin Htl Hzs Hpil Hpi Hpol Hpo Hll Hcnt").
    split_and!; try lia; assumption. }
  iAssert (□ ∀ e' zs' fl', ⌜same_out search_names e0 e'⌝ -∗ liveq dI ib ireg -∗ bytesq dqb ib io (le_words ws) -∗ G zs' fl' -∗
    WP (ERun (mkFrame glibc_translit e' [] None (body_at glibc_translit "L54")) : sexpr) {{ Φ }})%I as "#K54".
  { iIntros "!>" (e' zs' fl' Hs) "Hil Hin (%Hg & Hloc & Hwl & Hoe & Hfl & Htl & Hzs & Hpil & Hpi & Hpol & Hpo & Hll & Hcnt & _ & _ & [H3l H3] & [H4l H4] & HK)".
    destruct Hg as (Hlen & Hz' & Hf' & Hfr).
    iDestruct (input_return with "[$Hil $Hwl]") as "[Hwl Hil]"; [exact Halias|].
    iDestruct (pcell_congr _ _ _ (tb + to + Z.of_nat (length zs')) _ with "Hoe") as "Hoe"; [unfold m; rewrite Hlen; reflexivity|].
    iApply (translit_fallback Hfp Hts e' wd wreg ib ireg di dqb ic io ws k tb treg to zs' j fl' pi pireg po poreg lb lbreg cnt dl b481 b494 Φ
      with "Hc Hloc Hwl Hoe Hfl Hil Hin Htl Hzs Hpil Hpi Hpol Hpo Hll Hcnt H3l H3 H4l H4 [HK]");
      try solve [rewrite ?Hlen; first [assumption | lia] | erewrite Hs; [eassumption | reflexivity]].
    iIntros (st k' j' zs'' fl'' cnt' (Hk' & Hj' & Hl'' & Hz'' & Hf'' & Hfr'')) "Hloc Hwl Hoe Hfl Hil Hin Htl Hzs Hpil Hpi Hpol Hpo Hll Hcnt".
    iDestruct (pcell_congr _ _ _ (tb + to + m) _ with "Hoe") as "Hoe"; [unfold m; rewrite Hlen; reflexivity|].
    rewrite Hlen in Hj'.
    iApply ("HK" $! st k' j' zs'' fl'' cnt' with "[%] Hloc Hwl Hoe Hfl Hil Hin Htl Hzs Hpil Hpi Hpol Hpo Hll Hcnt").
    split_and!; try lia; try assumption. exact (flags_step _ _ _ Hfr Hfr''). }
  iAssert (□ ∀ e' zs' fl' med c, ⌜same_out search_names e0 e' /\ 0 <= med < 1659 /\ 0 < c < 2 ^ 31 /\ k + c <= n /\
      lookup (TAtom "v132") e' = Some (WInt (4 * med)) /\ lookup (TAtom "pr.6") e' = Some (WInt c)⌝ -∗
    liveq dI ib ireg -∗ bytesq dqb ib io (le_words ws) -∗ G zs' fl' -∗
    (∀ e'' zs'' fl'', ⌜same_out repl_names e' e''⌝ -∗ liveq dI ib ireg -∗ bytesq dqb ib io (le_words ws) -∗ G zs'' fl'' -∗
      WP (ERun (mkFrame glibc_translit e'' [] None (body_at glibc_translit "L183")) : sexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame glibc_translit e' [] None (body_at glibc_translit "L181")) : sexpr) {{ Φ }})%I as "#K181".
  { iIntros "!>" (e' zs' fl' med c (Hs & Hmed & Hc & Hkc & V132 & P6))
      "Hil Hin (%Hg & Hloc & Hwl & Hoe & Hfl & Htl & Hzs & Hpil & Hpi & Hpol & Hpo & Hll & Hcnt & [H1l H1] & [H2l H2] & H3 & H4 & HK) HR".
    destruct Hg as (Hlen & Hz' & Hf' & Hfr).
    iDestruct (input_return with "[$Hil $Hwl]") as "[Hwl Hil]"; [exact Halias|].
    iDestruct (pcell_congr _ _ _ (tb + to + Z.of_nat (length zs')) _ with "Hoe") as "Hoe"; [unfold m; rewrite Hlen; reflexivity|].
    iApply (translit_repl Hfp e' wd wreg ib ireg di dqb ic io ws k tb treg to zs' j fl' pi pireg po poreg lb lbreg cnt dl b211 b212 med c Φ
      with "Hc Hloc Hwl Hoe Hfl Hil Hin Htl Hzs Hpil Hpi Hpol Hpo Hll Hcnt H1l H1 H2l H2 [HK HR H3 H4]");
      try solve [rewrite ?Hlen; first [assumption | lia] | erewrite Hs; [eassumption | reflexivity]].
    iSplit.
    - iIntros (st k' j' zs'' fl'' cnt' (Hk' & Hj' & Hl'' & Hz'' & Hf'' & Hfr'')) "Hloc Hwl Hoe Hfl Hil Hin Htl Hzs Hpil Hpi Hpol Hpo Hll Hcnt".
      iDestruct (pcell_congr _ _ _ (tb + to + m) _ with "Hoe") as "Hoe"; [unfold m; rewrite Hlen; reflexivity|].
      rewrite Hlen in Hj'.
      iApply ("HK" $! st k' j' zs'' fl'' cnt' with "[%] Hloc Hwl Hoe Hfl Hil Hin Htl Hzs Hpil Hpi Hpol Hpo Hll Hcnt").
      split_and!; try lia; try assumption. exact (flags_step _ _ _ Hfr Hfr'').
    - iIntros (e'' zs'' fl'' (Hr & Hl'' & Hz'' & Hf'' & Hfr'')) "Hloc Hwl Hoe Hfl Hil Hin Htl Hzs Hpil Hpi Hpol Hpo Hll Hcnt H1l H1 H2l H2".
      iDestruct (input_lend with "[$Hwl $Hil]") as "[Hil Hwl]"; [exact Halias|].
      iDestruct (pcell_congr _ _ _ (tb + to + m) _ with "Hoe") as "Hoe"; [unfold m; rewrite Hlen; reflexivity|].
      iApply ("HR" $! e'' zs'' fl'' with "[%] Hil Hin [-]"); [exact Hr|].
      unfold G. iSplitR; [iPureIntro; split_and!; try lia; try assumption; exact (flags_step _ _ _ Hfr Hfr'')|].
      iFrame "Hloc Hwl Hoe Hfl Htl Hzs Hpil Hpi Hpol Hpo Hll Hcnt H3 H4 HK". rewrite /cell16. iFrame "H1l H1 H2l H2". }
  step.
  iApply (translit_search G Φ e0 dI dqb ib ireg io ic ws k with "Hc K181 K54 K7 [%] Hil Hin [-]"); try assumption.
  { split_and!; [| | | rewrite Symbolic.lookup_after_put_same; reflexivity |
      rewrite Symbolic.lookup_after_put_other; [rewrite Symbolic.lookup_after_put_same; reflexivity | reflexivity] | same_tac].
    1-3: change (0 mod 2 ^ 32) with 0; change (1659 mod 2 ^ 32) with 1659; lia. }
  unfold G, cell16. iSplitR; [iPureIntro; split_and!; [reflexivity | exact Hzs | exact Hfl | left; reflexivity]|].
  iFrame "Hts Hts0 Hgl Hgl0 Hwl Hoe Hfl Htl Hzs Hpil Hpi Hpol Hpo Hll Hcnt H1l H1 H2l H2 H3l H3 H4l H4 HK".
  Unshelve. all: first [exact DfracDiscarded | exact wreg].
Qed.

(** The last conversion step of [LibioWConvLast] states the same call
    with the caller's cursors and flags bundled as [conv_cursors]. *)
Lemma translit_rule_holds : translit_rule.
Proof using Type*.
  intros fr ip0 wd wreg ib ireg di dqb ic io ws k tb treg to zs j fl pi pireg po poreg lb lbreg cnt dl Φ n m Hfr
    Hwd Hwa Hwe Hwr Hic Hib Hio Hie Hir Halias Hws Hk Htb Hto Hte Htr Hj Hzs
    Hpi Hpia Hpie Hpir Hpo Hpoa Hpoe Hpor Hlb Hlba Hlbe Hlbr Hfl.
  iIntros "Hc (Hloc & Hwl & Hoe & Hfl & Hil & Hin & Htl & Hzs & Hpil & Hpi & Hpol & Hpo & Hll & Hcnt) HK".
  iApply (wp_translit with "Hc Hloc Hwl Hoe Hfl Hil Hin Htl Hzs Hpil Hpi Hpol Hpo Hll Hcnt [HK]"); try eassumption.
  iNext. iIntros (st k' j' zs' fl' cnt' Hp) "Hloc Hwl Hoe Hfl Hil Hin Htl Hzs Hpil Hpi Hpol Hpo Hll Hcnt".
  iApply ("HK" with "[%] [$Hloc $Hwl $Hoe $Hfl $Hil $Hin $Htl $Hzs $Hpil $Hpi $Hpol $Hpo $Hll $Hcnt]"). exact Hp.
Qed.

End translit.
