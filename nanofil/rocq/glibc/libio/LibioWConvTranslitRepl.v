(** When a source string matches the input, glibc looks up its list of
    replacements. If none works, the search resumes with its public
    cursors unchanged. If a replacement converts, glibc copies the local
    output cursor back unless the output window filled. *)

From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import CodePrelude CLocaleCells CtypeTranslitTables OsWorld FileInv LibioLogic
  LibioDefaultXsputnBuf CBlocks Fix LibioWConvAscii LibioWConvConsts LibioWConvTranslitCmp LibioWConvTranslitTry.
From Glibc Require Export LibioWConvTranslitCall.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation objp b := (mkPtr b (Obj b)).
Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation tmb := (conv_addr "glibc_wcsmbsload#to_mb").
Local Abbreviation tia := (conv_addr "glibc_C_ctype#translit_to_idx").
Local Abbreviation tta := (conv_addr "glibc_C_ctype#translit_to_tbl").
Local Abbreviation fp := (mkPtr (conv_addr "__gconv_transform_internal_ascii") (Fn (TAtom "__gconv_transform_internal_ascii"))).

(** Each replacement index names a list in the table. Its words, including
    the extra zero at the end of the image object, fit in unsigned integers. *)
Lemma repl_table_info :
  Z.of_nat (length wc_to_idx) = 1659 /\ Z.of_nat (length wc_tt) = 5887 /\
  Forall (fun x => 0 <= x < 2^32) wc_tt /\
  forall i z, wc_to_idx !! i = Some z -> 0 <= z < 2^32 /\ list_okb wc_tt (Z.to_nat z) 64 = true.
Proof using Type.
  assert (words : forall x, In x (wc_from_idx ++ wc_to_idx ++ wc_from_tbl ++ wc_to_tbl) -> 0 <= x < 2^32).
  { intros x H. pose proof wc_words_okb as T. apply forallb_forall with (x:=x) in T; [|exact H].
    unfold word_okb in T. apply Bool.andb_true_iff in T as [A B]. split; [by apply Z.leb_le | by apply Z.ltb_lt]. }
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split.
  - unfold wc_tt. apply Forall_app. split; [|repeat constructor; lia]. apply Forall_forall. intros x H.
    apply words. do 3 (apply in_or_app; right). exact H.
  - intros i z H. apply list_elem_of_lookup_2, list_elem_of_In in H. split.
    + apply words. apply in_or_app. right. apply in_or_app. by left.
    + pose proof wc_to_okb as T. apply forallb_forall with (x:=z) in T; [|exact H].
      unfold to_okb in T. by apply Bool.andb_true_iff in T as [_ T].
Qed.
Local Opaque wc_to_idx wc_tt.

Section replacement.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hascii : !Defines ge "__gconv_transform_internal_ascii" glibc_internal_ascii} (Hfp : function_check_res ge fp = Some ok).
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** A completed replacement consumes the source characters that matched,
    not the number of characters in the replacement. An exhausted list
    leaves those source characters available for the next probe. The
    caller states the return and the resumption as one conjunction:
    only one of them runs, and both need the caller's own frame. *)
Lemma translit_repl e wd wreg ib ireg di dqb ic io ws k tb treg to zs j fl pi pireg po poreg lb lbreg cnt dl a1 a2 med c Φ :
  let n := Z.of_nat (length ws) in let m := Z.of_nat (length zs) in
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2^63 ->
  ic = Obj ib \/ ic = Ro ib -> 0 < ib -> 0 <= io -> ib + io + 4*n <= r_end ireg -> r_end ireg <= 2^63 ->
  (ib = wd -> ireg = wreg) -> Forall (fun c => 0 <= c < 2^32) ws -> 0 <= k < n ->
  0 < tb -> 0 <= to -> tb + to + m <= r_end treg -> r_end treg <= 2^63 -> 0 <= j <= m -> Forall (fun z => 0 <= z < 256) zs ->
  0 < pi -> pi mod 8 = 0 -> pi + 8 <= r_end pireg -> r_end pireg <= 2^63 ->
  0 < po -> po mod 8 = 0 -> po + 8 <= r_end poreg -> r_end poreg <= 2^63 ->
  0 < lb -> lb mod 8 = 0 -> lb + 8 <= r_end lbreg -> r_end lbreg <= 2^63 -> wflags_ok fl ->
  0 < a1 -> a1 mod 16 = 0 -> a1+16 <= 2^48 -> 0 < a2 -> a2 mod 16 = 0 -> a2+16 <= 2^48 ->
  0 <= med < 1659 -> 0 < c < 2^31 -> k+c <= n ->
  lookup (TAtom "v0") e = Some (WPtr (rop tmb)) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr (wd+168) (Obj wd))) ->
  lookup (TAtom "v6") e = Some (WPtr (objp pi)) -> lookup (TAtom "chk0") e = Some (WPtr (objp pi)) ->
  lookup (TAtom "v10") e = Some (WPtr (objp po)) -> lookup (TAtom "v12") e = Some (WPtr (objp lb)) -> lookup (TAtom "v29") e = Some (WPtr fp) ->
  lookup (TAtom "v211") e = Some (WPtr (objp a1)) -> lookup (TAtom "v212") e = Some (WPtr (objp a2)) ->
  lookup (TAtom "v85") e = Some (WPtr (rop tia)) -> lookup (TAtom "v95") e = Some (WPtr (rop tta)) ->
  lookup (TAtom "v132") e = Some (WInt (4*med)) -> lookup (TAtom "pr.6") e = Some (WInt c) ->
  wconv_consts -∗ wlocale dl -∗ live wd wreg -∗ pcell wd 176 (mkPtr (tb+to+m) (Obj tb)) -∗ bytes wd 184 (int_bytes fl) -∗
  (if decide (ib = wd) then True else liveq di ib ireg) -∗ bytesq dqb ib io (le_words ws) -∗ live tb treg -∗ bytes tb to zs -∗
  live pi pireg -∗ pcell pi 0 (mkPtr (ib+io+4*k) ic) -∗ live po poreg -∗ pcell po 0 (mkPtr (tb+to+j) (Obj tb)) -∗ live lb lbreg -∗ icell lb 0 cnt -∗
  live a1 (mkRegion a1 (a1+16) Heap Live) -∗ (∃ x, pcell a1 0 x) -∗ live a2 (mkRegion a2 (a2+16) Heap Live) -∗ (∃ x, pcell a2 0 x) -∗
  ((∀ st k' j' zs' fl' cnt', ⌜k <= k' <= n /\ j <= j' <= m /\ length zs' = length zs /\ Forall (fun z => 0 <= z < 256) zs' /\
       wflags_ok fl' /\ (fl'=fl \/ fl'=Z.lor fl (2^30))⌝ -∗
     wlocale dl -∗ live wd wreg -∗ pcell wd 176 (mkPtr (tb+to+m) (Obj tb)) -∗ bytes wd 184 (int_bytes fl') -∗
     (if decide (ib = wd) then True else liveq di ib ireg) -∗ bytesq dqb ib io (le_words ws) -∗ live tb treg -∗ bytes tb to zs' -∗
     live pi pireg -∗ pcell pi 0 (mkPtr (ib+io+4*k') ic) -∗ live po poreg -∗ pcell po 0 (mkPtr (tb+to+j') (Obj tb)) -∗
     live lb lbreg -∗ icell lb 0 cnt' -∗ Φ (Ret (WInt st))) ∧
  (∀ e' zs' fl', ⌜same_out repl_names e e' /\ length zs' = length zs /\ Forall (fun z => 0 <= z < 256) zs' /\
       wflags_ok fl' /\ (fl'=fl \/ fl'=Z.lor fl (2^30))⌝ -∗
     wlocale dl -∗ live wd wreg -∗ pcell wd 176 (mkPtr (tb+to+m) (Obj tb)) -∗ bytes wd 184 (int_bytes fl') -∗
     (if decide (ib = wd) then True else liveq di ib ireg) -∗ bytesq dqb ib io (le_words ws) -∗ live tb treg -∗ bytes tb to zs' -∗
     live pi pireg -∗ pcell pi 0 (mkPtr (ib+io+4*k) ic) -∗ live po poreg -∗ pcell po 0 (mkPtr (tb+to+j) (Obj tb)) -∗ live lb lbreg -∗ icell lb 0 cnt -∗
     live a1 (mkRegion a1 (a1+16) Heap Live) -∗ (∃ x, pcell a1 0 x) -∗ live a2 (mkRegion a2 (a2+16) Heap Live) -∗ (∃ x, pcell a2 0 x) -∗
     WP (ERun (mkFrame glibc_translit e' [] None (body_at glibc_translit "L183")) : sexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_translit e [] None (body_at glibc_translit "L181")) : sexpr) {{ Φ }}.
Proof using Type*.
  intros n m Hwd Hw8 Hwe Hwr Hic Hib Hio Hie Hir Halias Hws Hk Htb Hto Hte Htr Hj Hzs Hpi Hpi8 Hpie Hpir
    Hpo Hpo8 Hpoe Hpor Hlb Hlb8 Hlbe Hlbr Hfl Ha1 Ha16 Ha1e Ha2 Ha26 Ha2e Hmed Hc Hkc V0 V2 V6 C0 V10 V12 V29 V211 V212 V85 V95 V132 P6.
  iIntros "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hil & Hidx & Hrl & Htbl)
    Hloc Hwl Hoe Hfl His Hsrc Htl Hbuf Hpil Hpi Hpol Hpo Hll Hcnt H1l [%x1 H1] H2l [%x2 H2] HKM".
  destruct repl_table_info as (Hni & Hnt & Htbl & Hidx).
  destruct (lookup_lt_is_Some_2 wc_to_idx (Z.to_nat med) ltac:(lia)) as [z Hz]. destruct (Hidx _ _ Hz) as [Hz32 Hok].
  body_start glibc_translit "L181". step. check_read_dq "Hil" by a4. iNext. iIntros "Hil".
  iDestruct (word_at _ _ 0 _ med z with "Hidx") as "[Hz _]"; [lia | exact Hz |].
  load_bytes_dq "Hil Hz" decode (apply load_uw_char; exact Hz32) by a4. iNext. iIntros "_ _". do 2 step.
  iApply (repl_try (rop tmb) wd wreg fl tta _ wc_tt tb treg to j po poreg a1 a2 Φ with "[%] Hwl Hoe Hfl Hrl Htbl Htl Hbuf Hpol Hpo H1l H1 H2l H2");
    try first [exact Hfp | assumption | cbn [r_end]; lia].
  { split_and!; try exact Hok; try assumption; try lia; try solve [vx].
    rewrite Symbolic.lookup_after_put_same. do 2 f_equal. unwrap2. lia. }
  iIntros (er st jj out u (Hs & Hjj & Hl & Hb & V245 & C26 & C27)) "Hwl Hoe Hfl Htl Hbuf Hpol Hpo H1l H1 H2l H2".
  assert (Hs0 : same_out repl_names e er) by (eapply same_out_trans; [|exact Hs]; same_tac).
  destruct (st mod 2^32 =? 6).
  - iDestruct "HKM" as "[_ HM]". iApply ("HM" $! er out fl with "[%] Hloc Hwl Hoe Hfl His Hsrc Htl Hbuf Hpil Hpi Hpol Hpo Hll Hcnt H1l [H1] H2l [H2]");
      [split_and!; first [assumption | left; reflexivity] | by iExists _ | by iExists _].
  - iDestruct "HKM" as "[HK _]".
    Local Ltac remember_reg H s Hs := let T := fresh "V" in pose proof (Hs (TAtom s) eq_refl) as T; rewrite H in T.
    remember_reg V6 "v6" Hs0. remember_reg C0 "chk0" Hs0. remember_reg V10 "v10" Hs0. remember_reg V12 "v12" Hs0.
    remember_reg V212 "v212" Hs0. remember_reg P6 "pr.6" Hs0. pose proof (mod16_mod8 _ Ha26).
    body_start glibc_translit "L246". step. branch_cases.
    Local Ltac return_repl k' j' := iApply wp_ret; [reflexivity | vx |]; iNext;
      iApply ("HK" $! _ k' j' _ _ _ with "[%] Hloc Hwl Hoe Hfl His Hsrc Htl Hbuf Hpil Hpi Hpol Hpo Hll Hcnt");
      split_and!; first [assumption | lia | left; reflexivity].
    Local Ltac copy_out := check "H2l"; load_pointer_dq "H2l H2 Htl" by a2; iNext; iIntros "_ _ Htl";
      check "Hpol"; store "Hpol" "Hpo"; do 2 step.
    + step. step. branch_cases; step; [return_repl k j | copy_out; return_repl k jj].
    + step. check "Hpil".
      assert (Hcap : forall dq, live_capq dq ic ireg = liveq dq ib ireg) by (intros; destruct Hic as [-> | ->]; reflexivity).
      iAssert (∃ dq, live_capq dq ic ireg ∗ (live_capq dq ic ireg -∗ live wd wreg ∗
        (if decide (ib = wd) then True else liveq di ib ireg)))%I with "[Hwl His]" as "[%dq [Hcap Hrestore]]".
      { destruct (decide (ib = wd)) as [E|E].
        - iExists (DfracOwn 1). rewrite Hcap (Halias E) E. iSplitL "Hwl"; [iExact "Hwl"|]. iIntros "Hwl". iFrame.
        - iExists di. rewrite Hcap. iFrame "His". iIntros "$". iFrame. }
      load_pointer_dq "Hpil Hpi Hcap" by a2. iNext. iIntros "Hpil Hpi Hcap". iDestruct ("Hrestore" with "Hcap") as "[Hwl His]".
      do 3 step. check "Hpil". store "Hpil" "Hpi".
      iDestruct (pcell_congr _ _ _ (ib+io+4*(k+c)) _ with "Hpi") as "Hpi"; [cbn [ptr_addr ptr_cap]; wnorm; lia|].
      check "Hll". iApply (wp_raw_load with "Hll Hcnt"); [reflexivity | vx | reflexivity | a2 |]. iNext. iIntros "Hll Hcnt".
      step. check "Hll". store_long "Hll" "Hcnt". do 3 step. branch_as false. step. copy_out. return_repl (k+c) jj.
Qed.
End replacement.
