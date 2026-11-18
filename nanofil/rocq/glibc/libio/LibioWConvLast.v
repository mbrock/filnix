(** The last ASCII conversion step writes directly into the stream's
    output window. When it finds a character that has no ASCII byte,
    it lends the two cursors and its counter to transliteration, then
    continues from the positions that transliteration returns. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic AbsInfer.
From Glibc Require Import CodePrelude HelloImageLoad HelloImageWConvObjs OsWorld FileInv LibioLogic
  LibioDefaultXsputnBuf LibioWIdle Mbrtowc CBlocks Fix LibioWConvAscii LibioWConvConsts LibioWConvOut.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation objp b := (mkPtr b (Obj b)).
Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation tmb := (img_a "glibc_wcsmbsload#to_mb").
Local Abbreviation localreg b := (mkRegion b (b + 16) Heap Live).

Section last.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** The two functions pass the same state back and forth. The input
    can lie in the stream's own wide buffer, so it borrows a separate
    share of its object's lifetime only when the two objects differ. *)
Definition conv_cursors dl wd wreg ib ireg di dqb ic io ws tb treg to m ip ipreg op opreg lp lreg k j zs fl cnt : iProp Σ :=
  wlocale dl ∗ live wd wreg ∗ pcell wd 176 (mkPtr (tb+to+m) (Obj tb)) ∗ bytes wd 184 (int_bytes fl) ∗
  (if decide (ib = wd) then True%I else liveq di ib ireg) ∗ bytesq dqb ib io (le_words ws) ∗
  live tb treg ∗ bytes tb to zs ∗ live ip ipreg ∗ pcell ip 0 (mkPtr (ib+io+4*k) ic) ∗
  live op opreg ∗ pcell op 0 (mkPtr (tb+to+j) (Obj tb)) ∗ live lp lreg ∗ icell lp 0 cnt.

(** Transliteration can stop without consuming a character. Its
    caller needs only that neither cursor moves backwards and that
    the illegal-input flag, once set, stays set. *)
Definition translit_rule : Prop := forall fr ip0 wd wreg ib ireg di dqb ic io ws k tb treg to zs j fl ip ipreg op opreg lp lreg cnt dl Φ,
  let n := Z.of_nat (length ws) in let m := Z.of_nat (length zs) in
  call_frame glibc_translit [WPtr (rop tmb); WPtr (mkPtr (wd+168) (Obj wd)); WPtr ip0; WPtr (objp ip);
    WPtr (mkPtr (ib+io+4*n) ic); WPtr (objp op); WPtr (objp lp)] = Some fr ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wreg -> r_end wreg <= 2^63 ->
  ic = Obj ib \/ ic = Ro ib -> 0 < ib -> 0 <= io -> ib+io+4*n <= r_end ireg -> r_end ireg <= 2^63 ->
  (ib = wd -> ireg = wreg) -> Forall (fun c => 0 <= c < 2^32) ws -> 0 <= k < n ->
  0 < tb -> 0 <= to -> tb+to+m <= r_end treg -> r_end treg <= 2^63 -> 0 <= j <= m -> Forall (fun z => 0 <= z < 256) zs ->
  0 < ip -> ip mod 8 = 0 -> ip+8 <= r_end ipreg -> r_end ipreg <= 2^63 ->
  0 < op -> op mod 8 = 0 -> op+8 <= r_end opreg -> r_end opreg <= 2^63 ->
  0 < lp -> lp mod 8 = 0 -> lp+8 <= r_end lreg -> r_end lreg <= 2^63 -> wflags_ok fl ->
  ⊢ wconv_consts -∗ conv_cursors dl wd wreg ib ireg di dqb ic io ws tb treg to m ip ipreg op opreg lp lreg k j zs fl cnt -∗
    ▷ (∀ st k' j' zs' fl' cnt', ⌜k <= k' <= n /\ j <= j' <= m /\ length zs' = length zs /\
        Forall (fun z => 0 <= z < 256) zs' /\ wflags_ok fl' /\ (fl' = fl \/ fl' = Z.lor fl (2^30))⌝ -∗
      conv_cursors dl wd wreg ib ireg di dqb ic io ws tb treg to m ip ipreg op opreg lp lreg k' j' zs' fl' cnt' -∗ Φ (Ret (WInt st))) -∗
    WP (ERun fr : sexpr) {{ Φ }}.

Context `{Htrdef : !Defines ge "__GI___gconv_transliterate" glibc_translit} (Htrans : translit_rule).

(** A read of the source borrows whichever lifetime protects it and
    returns that share to its owner after the read. *)
Local Lemma lend_input wd wreg ib ireg di : (ib = wd -> ireg = wreg) ->
  live wd wreg -∗ (if decide (ib = wd) then True else liveq di ib ireg) -∗
  ∃ dq, liveq dq ib ireg ∗ (liveq dq ib ireg -∗ live wd wreg ∗ (if decide (ib = wd) then True else liveq di ib ireg)).
Proof using Type.
  intros H. destruct (decide (ib = wd)) as [E|E]; iIntros "Hwl His".
  - rewrite (H E) E. iExists (DfracOwn 1). iSplitL "Hwl"; [iExact "Hwl"|]. iIntros "$".
  - iExists di. iFrame "His". iIntros "$". iExact "Hwl".
Qed.

Local Ltac read_input Hcap :=
  let q := fresh "share" in iDestruct (lend_input with "Hwl His") as (q) "[Hsrc Hback]"; [assumption|];
  iEval (rewrite -Hcap) in "Hsrc"; load_pointer_dq "Hpil Hpi Hsrc" by a2; iNext; iIntros "Hpil Hpi Hsrc";
  iEval (rewrite Hcap) in "Hsrc"; iDestruct ("Hback" with "Hsrc") as "[Hwl His]".

(** The conversion starts the shared ASCII loop again after a successful
    transliteration. Its [[later-modality|guarded induction hypothesis]]
    requires an execution step, not an increase in the input position. *)
Local Lemma last_loop e0 wd wreg ib ireg dq ic io ws tb treg to (xs : list Z) pi pireg ip op lp fl0 dl Φ :
  let n := Z.of_nat (length ws) in let m := Z.of_nat (length xs) in
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wreg -> r_end wreg <= 2^63 ->
  ic = Obj ib \/ ic = Ro ib -> 0 < ib -> 0 <= io -> ib+io+4*n <= r_end ireg -> r_end ireg <= 2^63 ->
  (ib = wd -> ireg = wreg) -> Forall (fun c => 0 <= c < 2^32) ws ->
  0 < tb -> 0 <= to -> tb+to+m <= r_end treg -> r_end treg <= 2^63 ->
  0 < pi -> pi mod 8 = 0 -> pi+8 <= r_end pireg -> r_end pireg <= 2^63 ->
  0 < ip -> ip mod 16 = 0 -> ip+16 <= 2^48 -> 0 < op -> op mod 16 = 0 -> op+16 <= 2^48 ->
  0 < lp -> lp mod 16 = 0 -> lp+16 <= 2^48 -> wflags_ok fl0 ->
  lookup (TAtom "v0") e0 = Some (WPtr (rop tmb)) -> lookup (TAtom "v2") e0 = Some (WPtr (mkPtr (wd+168) (Obj wd))) ->
  lookup (TAtom "chk0") e0 = Some (WPtr (mkPtr (wd+184) (Obj wd))) -> lookup (TAtom "v4") e0 = Some (WPtr (objp pi)) ->
  lookup (TAtom "chk6") e0 = Some (WPtr (objp pi)) -> lookup (TAtom "v6") e0 = Some (WPtr (mkPtr (ib+io+4*n) ic)) ->
  lookup (TAtom "iw_3.v19") e0 = Some (WPtr (objp ip)) -> lookup (TAtom "chk87") e0 = Some (WPtr (objp ip)) ->
  lookup (TAtom "iw_3.v22") e0 = Some (WPtr (objp op)) -> lookup (TAtom "chk88") e0 = Some (WPtr (objp op)) ->
  lookup (TAtom "v101") e0 = Some (WPtr (mkPtr (tb+to+m) (Obj tb))) -> lookup (TAtom "v111") e0 = Some (WPtr (objp lp)) ->
  lookup (TAtom "v89") e0 = Some (WInt 0) -> lookup (TAtom "iw_3.v17") e0 = Some (WInt fl0) ->
  let curs := conv_cursors dl wd wreg ib ireg dq dq ic io ws tb treg to m ip (localreg ip) op (localreg op) lp (localreg lp) in
  ⊢ wconv_consts -∗ ∀ e st k j zs fl cnt,
    ⌜same_out ia_loop_names e0 e /\ lookup (TAtom "iw_3.pr.2") e = Some (WInt st) /\ 0 <= st < 2^32 /\
      0 <= k <= n /\ 0 <= j <= m /\ length zs = length xs /\ Forall (fun z => 0 <= z < 256) zs /\ wflags_ok fl /\
      (fl = fl0 \/ fl = Z.lor fl0 (2^30))⌝ -∗
    curs k j zs fl cnt -∗ live pi pireg -∗ pcell pi 0 (mkPtr (ib+io) ic) -∗
    (∀ er r kr jr out f v, ⌜same_out ia_loop_names e0 er /\ lookup (TAtom "iw_3.pr.3") er = Some (WInt r) /\
       0 <= kr <= n /\ 0 <= jr <= m /\ length out = length xs /\ Forall (fun z => 0 <= z < 256) out /\ wflags_ok f /\
       (f = fl0 \/ f = Z.lor fl0 (2^30))⌝ -∗
       curs kr jr out f v -∗ live pi pireg -∗ pcell pi 0 (mkPtr (ib+io) ic) -∗
       WP (ERun (mkFrame glibc_internal_ascii er [] None (body_at glibc_internal_ascii "iw_3.L27")) : sexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame glibc_internal_ascii e [] None (body_at glibc_internal_ascii "iw_3.L25")) : sexpr) {{ Φ }}.
Proof using Type*.
  intros n m Hwd Hw8 Hwe Hwr Hic Hib Hio Hie Hir Halias Hws Htb Hto Hte Htr Hpi Hpi8 Hpie Hpir
    Hip Hip16 Hipe Hop Hop16 Hope Hlp Hlp16 Hlpe Hfl0 V0 V2 C0 V4 C6 V6 V19 C87 V22 C88 V101 V111 V89 V17 curs.
  assert (Hip8 := mod16_mod8 _ Hip16). assert (Hop8 := mod16_mod8 _ Hop16). assert (Hlp8 := mod16_mod8 _ Hlp16).
  assert (Hcap : forall q, live_capq q ic ireg = liveq q ib ireg) by (intros; destruct Hic as [-> | ->]; reflexivity).
  iIntros "#Hro". iLöb as "IH". iIntros (e st k j zs fl cnt (Hs & P2 & Hst & Hk & Hj & Hlen & Hbytes & Hfl & Hsticky))
    "(Hloc & Hwl & Hoe & Hfl & His & Hin & Htl & Hzs & Hil & Hi & Hol & Ho & Hll & Hl) Hpil Hpi HK".
  iDestruct (lend_input with "Hwl His") as (d) "[Hsrc Hback]"; [exact Halias|].
  iApply (ia_loop ib ireg d dq ic io ws tb treg to ip _ op _ (Some lp) Φ with "[%] Hsrc Hin Htl Hzs Hil Hi Hol Ho");
    try solve [assumption | cbn [r_end]; lia].
  { rewrite Hlen. split_and!; first [exact P2 | assumption | lia | rewrite Hs; [assumption|reflexivity]]. }
  iNext. iIntros (er status kr jr out (Hs1 & P3 & Hkr & Hjr & Hl1 & Hout)) "Hsrc Hin Htl Hzs Hil Hi Hol Ho".
  iDestruct ("Hback" with "Hsrc") as "[Hwl His]". pose proof (same_out_trans _ _ _ _ Hs Hs1) as Hsr.
  destruct status as [r|].
  - iApply ("HK" $! er r kr jr out fl cnt with "[%] [$Hloc $Hwl $Hoe $Hfl $His $Hin $Htl $Hzs $Hil $Hi $Hol $Ho $Hll $Hl] Hpil Hpi").
    split_and!; first [assumption|lia].
  - destruct P3 as [_ Hkrn].
    Local Ltac regain H V := lazymatch type of V with lookup ?x _ = _ =>
      let T := fresh "V" in pose proof (H x eq_refl) as T; rewrite V in T end.
    regain Hsr V111. regain Hsr V89. regain Hsr V2. regain Hsr C0. regain Hsr V4. regain Hsr C6. regain Hsr V0. regain Hsr V6. regain Hsr V19. regain Hsr V22. regain Hsr V17.
    destruct (wflags_bits fl Hfl) as (Hfl31 & _ & Hbit & _). assert (Hfl32 : 0 <= fl < 2^32) by lia.
    body_start glibc_internal_ascii "iw_3.L93". do 2 step. branch_as true. do 2 step. check "Hwl".
    load_s32 "Hwl" "Hfl". do 2 step. rewrite !(Z.mod_small fl (2^32)); [|lia..]. change (8 mod 2^32) with 8.
    rewrite Hbit. branch_as false. step. check "Hpil". read_input Hcap.
    iApply wp_call_bind; [vx | exact Htrdef | reflexivity |]. iNext.
    iApply (Htrans _ (mkPtr (ib+io) ic) wd wreg ib ireg dq dq ic io ws kr tb treg to out jr fl ip _ op _ lp _ cnt dl _
      with "Hro [$Hloc $Hwl Hoe $Hfl $His $Hin $Htl $Hzs $Hil $Hi $Hol $Ho $Hll $Hl]");
      try solve [assumption | cbn [r_end]; lia | rewrite Hl1 Hlen; assumption | reflexivity].
    { by rewrite Hl1 Hlen. }
    iNext. iIntros (r k' j' zs' fl' cnt' (Hk' & Hj' & Hlen' & Hb' & Hfl' & Hff)) "Hstate".
    iEval (rewrite Hl1 Hlen) in "Hstate".
    assert (Hsticky' : fl'=fl0 \/ fl'=Z.lor fl0 (2^30)).
    { destruct Hff as [-> | ->], Hsticky as [-> | ->]; auto. right. by rewrite -Z.lor_assoc Z.lor_diag. }
    block_resume. do 3 step. set (u := r mod 2^32). assert (Hu : 0 <= u < 2^32) by (apply Z.mod_pos_bound; lia).
    Local Ltac finish_loop := iApply ("HK" $! _ _ _ _ _ _ _ with "[%] Hstate Hpil Hpi");
      split_and!; try assumption; try lia; first [same_tac | vx].
    destruct (Z.eq_dec u 6) as [E6|E6].
    + branch_as true. do 2 step. branch_as false. do 5 step.
      destruct (wflags_bits fl0 Hfl0) as (Hfl032 & _ & _ & Hbit2).
      rewrite !(Z.mod_small fl0 (2^32)); [|lia..]. change (2 mod 2^32) with 2. rewrite Hbit2.
      branch_as true. step. finish_loop.
    + branch_as false. do 2 step. destruct (Z.eq_dec u 5) as [E5|E5].
      * branch_as false. step. finish_loop.
      * branch_as true. step. iApply ("IH" $! _ u k' j' zs' fl' cnt' with "[%] Hstate Hpil Hpi HK").
        split_and!; try assumption; try lia; first [same_tac | rewrite Symbolic.lookup_after_put_same; do 2 f_equal; unwrap2; lia].
Qed.

(** The last step publishes both cursors, counts the invocation, and
    adds the local irreversible count to the caller's count. Neither
    the step nor transliteration writes the input characters. *)
Lemma wp_ia_last dl : ia_last_rule dl.
Proof using Type*.
  intros fr wd wreg ib ireg dq ic io ws tb treg to xs fl cnt pi pireg lb lbreg c0 Φ n m Hfr Hfl
    Hwd Hw8 Hwe Hwr Hic Hib Hio Hie Hir Halias Hws Htb Hto Hte Htr Hxs Hpi Hpi8 Hpie Hpir Hlb Hlb8 Hlbe Hlbr.
  iIntros "Hro Hloc Hwl Hob Hoe [%Hfl32 Hfl] [%Hcnt32 Hcnt] His Hin Htl Hzs Hpil Hpi Hbl Hb HK".
  iPoseProof (wconv_ro_consts with "Hro") as "#Hconst". injection Hfr as <-.
  destruct (wflags_bits fl Hfl) as (Hfl31 & Hb1 & _ & _).
  assert (Hcap : forall q, live_capq q ic ireg = liveq q ib ireg) by (intros; destruct Hic as [-> | ->]; reflexivity).
  Local Ltac cell8 b H L C :=
    iApply wp_alloc; [reflexivity | vm_compute; congruence | vm_compute; congruence |
      intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |]; iNext; iIntros (b H) "Hob0";
    change (0 < b /\ b mod 16 = 0 /\ b + 16 <= 2^48) in H;
    iDestruct (obj_zero_block with "Hob0") as "(Hobl & Hobb & Hoba)"; [vm_compute; congruence|];
    iDestruct (Mbrtowc.MbVL.zero_cell_prefix b 0 8 with "Hobb Hoba") as "(Hobc & _ & _)";
    iAssert (live b (localreg b)) with "Hobl" as L; iRename "Hobc" into C.
  step. cell8 lp Hlp "Hll" "Hl". destruct Hlp as (Hlp & Hlp16 & Hlpe).
  iAssert (icell lp 0 0) with "[Hl]" as "Hl".
  { rewrite /pcell /icell /pts big_sepL_cons. iDestruct "Hl" as "[_ $]". }
  iApply wp_alloc; [reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |]; iNext. iIntros (? _) "_".
  do 3 step. check "Hwl". load_s32 "Hwl" "Hfl". step.
  Local Ltac last_flag f Hb :=
    iStartProof; eapply step_wand; [eapply wp_branch; inst; vx |]; rewrite !(Z.mod_small f (2^32)); [|lia..];
    change (1 mod 2^32) with 1; rewrite Hb; change (1 mod 2^32 =? 0) with false; cbn [edge_label].
  last_flag fl Hb1. do 3 step. branch_as true. step. check "Hpil". read_input Hcap.
  do 3 step. branch_as false. step. check "Hwl". load_pointer_dq "Hwl Hob Htl" by a2. iNext. iIntros "Hwl Hob Htl".
  do 3 step. check "Hwl". load_pointer_dq "Hwl Hoe Htl" by a2. iNext. iIntros "Hwl Hoe Htl".
  check "Hll". store_long "Hll" "Hl". do 2 step. branch_as false. do 2 step. branch_as true. step. branch_as true. step.
  check "Hpil". read_input Hcap. check "Hll".
  Local Ltac load64 hs := iApply (wp_raw_load with hs); [reflexivity | vx | reflexivity | a2 |]; iNext; iIntros hs.
  load64 "Hll Hl". branch_as false. step. check "Hbl". load64 "Hbl Hb". do 3 step.
  cell8 ip Hip "Hil" "Hi". cell8 oq Hop "Hol" "Ho". step. check "Hwl". load_s32 "Hwl" "Hfl".
  check "Hpil". read_input Hcap. check "Hil". store "Hil" "Hi". check "Hol". store "Hol" "Ho". do 2 step.
  destruct Hip as (Hip & Hip16 & Hipe), Hop as (Hop & Hop16 & Hope).
  lazymatch goal with |- context [mkFrame _ ?e _ _ _] =>
    iApply (last_loop e wd wreg ib ireg dq ic io ws tb treg to xs pi pireg ip oq lp fl dl Φ with
      "Hconst [%] [$Hloc $Hwl $Hoe $Hfl $His $Hin $Htl $Hzs $Hil Hi $Hol Ho $Hll $Hl] Hpil Hpi") end;
    try solve [eassumption | reflexivity].
  - change (Some (WPtr (mkPtr (((wd+168) mod 2^64 + 16 mod 2^64) mod 2^64) (Obj wd))) = Some (WPtr (mkPtr (wd+184) (Obj wd)))).
    do 3 f_equal. unwrap2. lia.
  - split_and!; try apply same_out_refl; try reflexivity; try assumption; try (instantiate (1:=0); lia); try lia;
      first [left; reflexivity | vm_compute; congruence].
  - iSplitL "Hi"; [iApply (pcell_congr with "Hi") | iApply (pcell_congr with "Ho")]; lia.
  - iIntros (e r k j zs f v (Hs & P3 & Hk & Hj & Hlen & Hzs & Hf & Hsticky))
      "(Hloc & Hwl & Hoe & Hfl & His & Hin & Htl & Hzs & Hil & Hi & Hol & Ho & Hll & Hl) Hpil Hpi".
    Local Ltac keep H name := let V := fresh "V" in pose proof (H (TAtom name) eq_refl) as V; cbn in V.
    keep Hs "chk87". keep Hs "iw_3.v19". keep Hs "chk6". keep Hs "v4". keep Hs "chk88". keep Hs "iw_3.v22".
    keep Hs "v88". keep Hs "v89". keep Hs "v2". keep Hs "chk0". keep Hs "v10". keep Hs "chk10". keep Hs "v103". keep Hs "v14".
    body_start glibc_internal_ascii "iw_3.L27". check "Hil".
    iDestruct (lend_input with "Hwl His") as (d) "[Hsrc Hback]"; [exact Halias|].
    iEval (rewrite -Hcap) in "Hsrc". load_pointer_dq "Hil Hi Hsrc" by a2. iNext. iIntros "_ _ Hsrc".
    iEval (rewrite Hcap) in "Hsrc". iDestruct ("Hback" with "Hsrc") as "[Hwl His]".
    check "Hpil". store "Hpil" "Hpi". check "Hol". load_pointer_dq "Hol Ho Htl" by a2. iNext. iIntros "_ _ Htl".
    step. branch_as true. do 2 step. check "Hwl". load_s32 "Hwl" "Hcnt". step. check "Hwl". store_int "Hwl" "Hcnt".
    destruct (wflags_bits f Hf) as (Hf31 & Hbit & _). assert (Hf32 : 0 <= f < 2^32) by lia.
    step. check "Hwl". load_s32 "Hwl" "Hfl". step. last_flag f Hbit.
    step. check "Hwl". store "Hwl" "Hob". check "Hbl". load64 "Hbl Hb". check "Hll". load64 "Hll Hl".
    step. check "Hbl". store_long "Hbl" "Hb". do 4 step. branch_as true. step. branch_as true. step.
    iApply wp_ret; [reflexivity | vx |]. iNext. iApply ("HK" $! _ k j zs f _ _ with
      "[%] Hloc Hwl [Hob] Hoe [Hfl] [Hcnt] His Hin Htl Hzs Hpil [Hpi] Hbl Hb").
    + split_and!; first [assumption|lia].
    + iApply (pcell_congr with "Hob"). unwrap2. lia.
    + iSplit; [iPureIntro; lia|iExact "Hfl"].
    + iSplit; [iPureIntro; apply Z.mod_pos_bound; lia|iExact "Hcnt"].
    + iApply (pcell_congr with "Hpi"). unwrap2. lia.
Qed.
End last.
