(** Glibc tries a replacement by passing its words to the ASCII converter.
    The converter uses two local cursor cells, so a failed attempt can
    change the output bytes without moving the caller's output cursor. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic AbsInfer.
From Glibc Require Import CodePrelude CLocaleCells CtypeTranslitTables OsWorld FileInv LibioLogic
  LibioDefaultXsputnBuf CBlocks Fix LibioWConvAscii LibioWConvTranslitCmp.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation objp b := (mkPtr b (Obj b)).
Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation fp := (mkPtr (conv_addr "__gconv_transform_internal_ascii") (Fn (TAtom "__gconv_transform_internal_ascii"))).

(** The search needs to keep the original probe when no replacement works.
    These are all the names that can change while glibc tries replacements. *)
Definition repl_names : list name := Eval vm_compute in
  flat_map (fun b => app (map (fun p => match p with Phi d _ _ => d end) (b_phis b)) (flat_map inst_defs (b_insts b)))
    (filter (fun b => match b_label b with TAtom s => existsb (String.eqb s)
       ["L181"; "L206"; "L213"; "L214"; "L215"; "L246"; "L251"; "L253"; "L265"; "L267"; "L248"]%string | _ => false end)
      (fn_blocks glibc_translit)).

Section repl_call.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hascii : !Defines ge "__gconv_transform_internal_ascii" glibc_internal_ascii}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** The converter reads just the measured replacement, starting at word p. *)
Lemma replacement_words fb tbl p q : (p + q <= length tbl)%nat ->
  bytesq DfracDiscarded fb 0 (le_words tbl) ⊢
  bytesq DfracDiscarded fb (4 * Z.of_nat p) (le_words (take q (drop p tbl))).
Proof using Type.
  intros Hpq. rewrite -{1}(take_drop p tbl) /le_words flat_map_app /bytesq byte_ps_app ptsq_app.
  fold (le_words (take p tbl)). rewrite le_words_length length_take_le; [|lia].
  replace (0 + Z.of_nat (4 * p)) with (4 * Z.of_nat p) by lia.
  rewrite -{1}(take_drop q (drop p tbl)) flat_map_app byte_ps_app ptsq_app.
  iIntros "[_ [$ _]]".
Qed.

(** One call either completes an attempt or rejects it. The two successors
    use its status and the private output cursor, and the retry also needs
    the replacement's offset and length. *)
Lemma repl_call e stp wd wreg fl fb freg tbl p q tb treg to zs j po poreg a1 a2 x1 x2 Φ :
  let m := Z.of_nat (length zs) in
  function_check_res ge fp = Some ok ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2^63 -> wflags_ok fl ->
  0 < fb -> fb + 4 * Z.of_nat (length tbl) <= r_end freg -> r_end freg <= 2^63 ->
  Z.of_nat (length tbl) < 2^30 -> Forall (fun x => 0 <= x < 2^32) tbl -> (p + q < length tbl)%nat ->
  0 < tb -> 0 <= to -> tb + to + m <= r_end treg -> r_end treg <= 2^63 -> 0 <= j <= m ->
  Forall (fun x => 0 <= x < 256) zs ->
  0 < po -> po mod 8 = 0 -> po + 8 <= r_end poreg -> r_end poreg <= 2^63 ->
  0 < a1 -> a1 mod 16 = 0 -> a1 + 16 <= 2^48 -> 0 < a2 -> a2 mod 16 = 0 -> a2 + 16 <= 2^48 ->
  lookup (TAtom "v0") e = Some (WPtr stp) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr (wd+168) (Obj wd))) ->
  lookup (TAtom "v10") e = Some (WPtr (objp po)) -> lookup (TAtom "v29") e = Some (WPtr fp) ->
  lookup (TAtom "v211") e = Some (WPtr (objp a1)) -> lookup (TAtom "v212") e = Some (WPtr (objp a2)) ->
  lookup (TAtom "pr.7") e = Some (WInt (Z.of_nat p)) -> lookup (TAtom "pr.8") e = Some (WInt (Z.of_nat q)) ->
  lookup (TAtom "v95") e = Some (WPtr (rop fb)) ->
  lookup (TAtom "v222") e = Some (WPtr (mkPtr (fb + 4 * Z.of_nat (p+q)) (Ro fb))) ->
  live wd wreg -∗ pcell wd 176 (mkPtr (tb+to+m) (Obj tb)) -∗ bytes wd 184 (int_bytes fl) -∗
  liveq DfracDiscarded fb freg -∗ bytesq DfracDiscarded fb 0 (le_words tbl) -∗
  live tb treg -∗ bytes tb to zs -∗ live po poreg -∗ pcell po 0 (mkPtr (tb+to+j) (Obj tb)) -∗
  live a1 (mkRegion a1 (a1+16) Heap Live) -∗ pcell a1 0 x1 -∗
  live a2 (mkRegion a2 (a2+16) Heap Live) -∗ pcell a2 0 x2 -∗
  (∀ e' st jj out u, ⌜same_out repl_names e e' /\ j <= jj <= m /\ length out = length zs /\
      Forall (fun x => 0 <= x < 256) out /\ lookup (TAtom "v245") e' = Some (WInt st) /\
      lookup (TAtom "chk26") e' = Some (WPtr (objp po)) /\ lookup (TAtom "chk27") e' = Some (WPtr (objp a2)) /\
      lookup (TAtom "pr.7") e' = Some (WInt (Z.of_nat p)) /\ lookup (TAtom "pr.8") e' = Some (WInt (Z.of_nat q))⌝ -∗
    live wd wreg -∗ pcell wd 176 (mkPtr (tb+to+m) (Obj tb)) -∗ bytes wd 184 (int_bytes fl) -∗
    live tb treg -∗ bytes tb to out -∗ live po poreg -∗ pcell po 0 (mkPtr (tb+to+j) (Obj tb)) -∗
    live a1 (mkRegion a1 (a1+16) Heap Live) -∗ pcell a1 0 u -∗
    live a2 (mkRegion a2 (a2+16) Heap Live) -∗ pcell a2 0 (mkPtr (tb+to+jj) (Obj tb)) -∗
    WP (ERun (mkFrame glibc_translit e' [] None (body_at glibc_translit (if st mod 2^32 =? 6 then "L248" else "L246"))) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_translit e [] None (body_at glibc_translit "L215")) : sexpr) {{ Φ }}.
Proof using Type*.
  intros m Hfp Hwd Hw8 Hwe Hwr Hfl Hfb Hfe Hfr Hsize Hwords Hpq Htb Hto Hte Htr Hj Hzs
    Hpo Hpo8 Hpoe Hpor Ha1 Ha16 Ha1e Ha2 Ha26 Ha2e V0 V2 V10 V29 V211 V212 P7 P8 V95 V222.
  iIntros "Hwl Hoe Hfl Hrl Hrs Htl Hzs Hpol Hpo H1l H1 H2l H2 HK".
  assert (Ha18 := mod16_mod8 _ Ha16). assert (Ha28 := mod16_mod8 _ Ha26).
  set (ws := take q (drop p tbl)). assert (Hlen : length ws = q).
  { unfold ws. rewrite length_take_le; [reflexivity|]. rewrite length_drop. lia. }
  body_start glibc_translit "L215". do 3 step. check "H1l". store "H1l" "H1".
  check "Hpol". load_pointer_dq "Hpol Hpo Htl" by a2. iNext. iIntros "Hpol Hpo Htl".
  check "H2l". store "H2l" "H2". iApply wp_check_function; [vx | exact Hfp |]. iNext.
  iApply wp_raw_call_bind; [vx | reflexivity | exact Hfp | vx | exact Hascii | reflexivity | reflexivity |]. iNext.
  iDestruct (replacement_words fb tbl p q with "Hrs") as "Hsrc"; [lia|].
  iApply (wp_ia_inner _ stp wd wreg fb freg DfracDiscarded DfracDiscarded (Ro fb) (4 * Z.of_nat p) ws
    tb treg to zs j fl a1 _ a2 _ _ with "Hwl Hoe Hfl Hrl Hsrc Htl Hzs H1l [H1] H2l H2");
    try solve [assumption | right; reflexivity | cbn [r_end]; lia | apply Forall_take; apply Forall_drop; assumption].
  - rewrite Hlen. replace (fb + 4 * Z.of_nat p + 4 * Z.of_nat q) with (fb + 4 * Z.of_nat (p+q)) by lia. reflexivity.
  - iApply (pcell_congr with "H1"). cbn [ptr_addr ptr_cap]. wnorm. lia.
  - iNext. iIntros (st ki jj out fl' (Hki & Hjj & Hl & Hb & ->)) "Hwl Hoe Hfl _ _ Htl Hzs H1l H1 H2l H2".
    block_resume. step. destruct ((st mod 2^32) =? 6) eqn:E;
      [apply Z.eqb_eq in E as Es; branch_as true | apply Z.eqb_neq in E as Es; branch_as false]; step;
      iSpecialize ("HK" $! _ (st mod 2^32) jj out _); iEval (rewrite Z.mod_mod; [rewrite E | lia]) in "HK";
      iApply ("HK" with "[%] Hwl Hoe Hfl Htl Hzs Hpol Hpo H1l H1 H2l H2");
      split_and!; first [same_tac | lia | assumption | vx].
Qed.
End repl_call.
