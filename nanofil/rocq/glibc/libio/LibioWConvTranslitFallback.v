(** When transliteration finds no match, the C locale supplies a
    question mark as its default replacement. Glibc converts that
    character with temporary input and output cursors. The status of
    the conversion determines which cursors it copies back. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic AbsInfer.
From Glibc Require Import CodePrelude CLocaleCells CtypeTranslitTables OsWorld
  FileInv LibioLogic LibioDefaultXsputnBuf LibioWIdle CBlocks Fix LibioWConvAscii LibioWConvConsts.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation objp b := (mkPtr b (Obj b)).
Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation tmb := (conv_addr "glibc_wcsmbsload#to_mb").
Local Abbreviation s280 := (conv_addr "glibc_C_ctype#str.280").
Local Abbreviation fct := (mkPtr (conv_addr "__gconv_transform_internal_ascii") (Fn (TAtom "__gconv_transform_internal_ascii"))).

Section fallback.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hascii : !Defines ge "__gconv_transform_internal_ascii" glibc_internal_ascii}
  (Hfp : function_check_res ge fct = Some ok)
  (Hts : lookup (TAtom "__libc_tsd_LOCALE") (ge_globals ge) = Some (objp (conv_addr "__libc_tsd_LOCALE"))).
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** The fallback reads the current thread's character category before each lookup. *)
Local Ltac ctype_field Hts :=
  step_global Hts; check "Hts"; load_pointer_dq "Hts Hts0 Hgl" by a2; iNext; iIntros "Hts Hts0 Hgl";
  check "Hgl"; load_pointer_dq "Hgl Hgl0 Hcc" by a2; iNext; iIntros "Hgl Hgl0 _";
  do 2 step; check_read_dq "Hcc" by a2; iNext; iIntros "_".

(** The fallback returns without moving either of the caller's cursors
    outside its window. The input can share the wide stream's object;
    in that case the stream already supplies its lifetime. *)
Lemma translit_fallback e wd wreg ib ireg di dqb ic io ws k tb treg to zs j fl pi pireg po poreg lb lbreg cnt dl a3 a4 Φ :
  let n := Z.of_nat (length ws) in let m := Z.of_nat (length zs) in
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 ->
  ic = Obj ib \/ ic = Ro ib -> 0 < ib -> 0 <= io -> ib + io + 4 * n <= r_end ireg -> r_end ireg <= 2 ^ 63 ->
  (ib = wd -> ireg = wreg) -> Forall (fun c => 0 <= c < 2 ^ 32) ws -> 0 <= k < n ->
  0 < tb -> 0 <= to -> tb + to + m <= r_end treg -> r_end treg <= 2 ^ 63 -> 0 <= j <= m ->
  Forall (fun z => 0 <= z < 256) zs ->
  0 < pi -> pi mod 8 = 0 -> pi + 8 <= r_end pireg -> r_end pireg <= 2 ^ 63 ->
  0 < po -> po mod 8 = 0 -> po + 8 <= r_end poreg -> r_end poreg <= 2 ^ 63 ->
  0 < lb -> lb mod 8 = 0 -> lb + 8 <= r_end lbreg -> r_end lbreg <= 2 ^ 63 -> wflags_ok fl ->
  0 < a3 -> a3 mod 16 = 0 -> a3 + 16 <= 2 ^ 48 -> 0 < a4 -> a4 mod 16 = 0 -> a4 + 16 <= 2 ^ 48 ->
  lookup (TAtom "v0") e = Some (WPtr (rop tmb)) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr (wd + 168) (Obj wd))) ->
  lookup (TAtom "v6") e = Some (WPtr (objp pi)) -> lookup (TAtom "chk0") e = Some (WPtr (objp pi)) ->
  lookup (TAtom "v8") e = Some (WPtr (mkPtr (ib + io + 4 * n) ic)) ->
  lookup (TAtom "v10") e = Some (WPtr (objp po)) -> lookup (TAtom "v12") e = Some (WPtr (objp lb)) ->
  lookup (TAtom "v24") e = Some (WPtr (mkPtr (ib + io + 4 * k) ic)) ->
  lookup (TAtom "v29") e = Some (WPtr fct) ->
  lookup (TAtom "v481") e = Some (WPtr (objp a3)) -> lookup (TAtom "v494") e = Some (WPtr (objp a4)) ->
  wconv_consts -∗ wlocale dl -∗
  live wd wreg -∗ pcell wd 176 (mkPtr (tb + to + m) (Obj tb)) -∗ bytes wd 184 (int_bytes fl) -∗
  (if decide (ib = wd) then True else liveq di ib ireg) -∗ bytesq dqb ib io (le_words ws) -∗ live tb treg -∗ bytes tb to zs -∗
  live pi pireg -∗ pcell pi 0 (mkPtr (ib + io + 4 * k) ic) -∗ live po poreg -∗ pcell po 0 (mkPtr (tb + to + j) (Obj tb)) -∗
  live lb lbreg -∗ icell lb 0 cnt -∗
  live a3 (mkRegion a3 (a3 + 16) Heap Live) -∗ (∃ x, pcell a3 0 x) -∗
  live a4 (mkRegion a4 (a4 + 16) Heap Live) -∗ (∃ x, pcell a4 0 x) -∗
  (∀ st k' j' zs' fl' cnt', ⌜k <= k' <= n /\ j <= j' <= m /\ length zs' = length zs /\
       Forall (fun z => 0 <= z < 256) zs' /\ wflags_ok fl' /\ (fl' = fl \/ fl' = Z.lor fl (2 ^ 30))⌝ -∗
     wlocale dl -∗ live wd wreg -∗ pcell wd 176 (mkPtr (tb + to + m) (Obj tb)) -∗ bytes wd 184 (int_bytes fl') -∗
     (if decide (ib = wd) then True else liveq di ib ireg) -∗ bytesq dqb ib io (le_words ws) -∗ live tb treg -∗ bytes tb to zs' -∗
     live pi pireg -∗ pcell pi 0 (mkPtr (ib + io + 4 * k') ic) -∗ live po poreg -∗ pcell po 0 (mkPtr (tb + to + j') (Obj tb)) -∗
     live lb lbreg -∗ icell lb 0 cnt' -∗ Φ (Ret (WInt st))) -∗
  WP (ERun (mkFrame glibc_translit e [] None (body_at glibc_translit "L54")) : sexpr) {{ Φ }}.
Proof using Type*.
  intros n m Hwd Hwa Hwe Hwr Hic Hib Hio Hie Hir Halias Hws Hk Htb Hto Hte Htr Hj Hzs
    Hpi Hpia Hpie Hpir Hpo Hpoa Hpoe Hpor Hlb Hlba Hlbe Hlbr Hfl Ha3 Ha3m Ha3e Ha4 Ha4m Ha4e
    V0 V2 V6 C0 V8 V10 V12 V24 V29 V481 V494.
  pose proof (mod16_mod8 _ Ha3m) as Ha38. pose proof (mod16_mod8 _ Ha4m) as Ha48.
  iIntros "#(_ & _ & _ & Hcc & _ & _ & _ & _ & _ & Hone & Hdef & Hzero & Hsl & Hword & _)
    (Hts & Hts0 & Hgl & Hgl0) Hwl Hoe Hfl Hil Hin Htl Hzs Hpil Hpi Hpol Hpo Hll Hcnt H3l [%x H3] H4l [%y H4] HK".
  body_start glibc_translit "L54". ctype_field Hts.
  load_bytes_dq "Hcc Hzero" decode reflexivity by a2. iNext. iIntros "_ _". step. branch. step.
  ctype_field Hts. load_bytes_dq "Hcc Hone" decode reflexivity by a2. iNext. iIntros "_ _". step. branch. step.
  ctype_field Hts. load_pointer_dq "Hcc Hdef Hsl" by a2. iNext. iIntros "_ _ _".
  check "H3l". store "H3l" "H3".
  ctype_field Hts. load_bytes_dq "Hcc Hone" decode reflexivity by a2. iNext. iIntros "_ _".
  do 4 step. branch_as true. step. check "Hpol". load_pointer_dq "Hpol Hpo Htl" by a2. iNext. iIntros "Hpol Hpo Htl".
  check "H4l". store "H4l" "H4". do 3 step.
  iApply wp_check_function; [vx | exact Hfp |]. iNext.
  iApply wp_raw_call_bind; [vx | reflexivity | exact Hfp | vx | exact Hascii | reflexivity | reflexivity |]. iNext.
  iApply (wp_ia_inner _ (rop tmb) wd wreg s280 _ DfracDiscarded DfracDiscarded (Ro s280) 0 [63]
    tb treg to zs j fl a3 _ a4 _ _ with "Hwl Hoe Hfl Hsl Hword Htl Hzs H3l H3 H4l H4");
    try solve [reflexivity | assumption | right; reflexivity | cbn [length r_end]; lia | repeat constructor; lia].
  iNext. iIntros (st ki jo out fl2 (Hki & Hjo & Hlen & Hout & ->)) "Hwl Hoe Hfl _ _ Htl Hzs _ _ H4l H4".
  block_resume. step. branch_cases.
  - step. step. check "Hwl". pose proof (wflags_bits _ Hfl) as (Hfl31 & _).
    load_bytes_dq "Hwl Hfl" decode (apply load_sw_int; lia) by a2. iNext. iIntros "Hwl Hfl".
    step. check "Hwl". store_int "Hwl" "Hfl". iApply wp_ret; [reflexivity | vx |]. iNext.
    iApply ("HK" $! _ k j out _ cnt with "[%] [$Hts $Hts0 $Hgl $Hgl0] Hwl Hoe Hfl Hil Hin Htl Hzs Hpil Hpi Hpol Hpo Hll Hcnt").
    split_and!; try lia; try assumption; destruct Hfl as [-> | ->]; right; vm_compute; reflexivity.
  - step. step. branch_cases.
    Local Ltac return_output k' :=
      step; check "H4l"; load_pointer_dq "H4l H4 Htl" by a2; iNext; iIntros "_ _ Htl";
      check "Hpol"; store "Hpol" "Hpo"; iApply wp_ret; [reflexivity | vx |]; iNext;
      iApply ("HK" $! _ k' _ _ _ _ with "[%] [$Hts $Hts0 $Hgl $Hgl0] Hwl Hoe Hfl Hil Hin Htl Hzs Hpil Hpi Hpol Hpo Hll Hcnt");
      split_and!; try lia; first [assumption | left; reflexivity].
    + return_output k.
    + step. check "Hll". iApply (wp_raw_load with "Hll Hcnt"); [reflexivity | vx | reflexivity | a2 |].
      iNext. iIntros "Hll Hcnt". step. check "Hll". store_long "Hll" "Hcnt". check "Hpil".
      assert (Hcap : forall dq, live_capq dq ic ireg = liveq dq ib ireg) by (intros; destruct Hic as [-> | ->]; reflexivity).
      iAssert (∃ dq, live_capq dq ic ireg ∗ (live_capq dq ic ireg -∗ live wd wreg ∗
        (if decide (ib = wd) then True else liveq di ib ireg)))%I with "[Hwl Hil]" as "[%dq [Hcap Hrestore]]".
      { destruct (decide (ib = wd)) as [E | E].
        - iExists (DfracOwn 1). rewrite Hcap (Halias E) E. iSplitL "Hwl"; [iExact "Hwl"|].
          iIntros "Hwl". iSplitL "Hwl"; [iExact "Hwl" | done].
        - iExists di. rewrite Hcap. iFrame "Hil". iIntros "$". iFrame. }
      load_pointer_dq "Hpil Hpi Hcap" by a2. iNext. iIntros "Hpil Hpi Hcap".
      iDestruct ("Hrestore" with "Hcap") as "[Hwl Hil]". step. check "Hpil". store "Hpil" "Hpi".
      iDestruct (pcell_congr _ _ _ (ib + io + 4 * (k + 1)) _ with "Hpi") as "Hpi"; [cbn [ptr_addr ptr_cap]; unwrap2; lia |].
      step. return_output (k + 1).
Qed.
End fallback.
