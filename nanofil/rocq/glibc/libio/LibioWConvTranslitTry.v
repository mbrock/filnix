(** Glibc tries the replacements for one source string in order. An illegal
    replacement leaves the public output cursor alone, but the converter
    may already have written some bytes. The next attempt starts at that
    same cursor in the buffer as the previous attempt left it. *)

From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import CodePrelude CLocaleCells CtypeTranslitTables OsWorld FileInv LibioLogic
  LibioDefaultXsputnBuf CBlocks Fix LibioWConvAscii LibioWConvTranslitCmp LibioWConvTranslitLen LibioWConvTranslitCall.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation objp b := (mkPtr b (Obj b)).
Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation fp := (mkPtr (conv_addr "__gconv_transform_internal_ascii") (Fn (TAtom "__gconv_transform_internal_ascii"))).

(** The scan assigns only temporaries that belong to the replacement loop. *)
Lemma len_same_repl (e e' : list (name * word)) : same_out len_names e e' -> same_out repl_names e e'.
Proof using Type.
  intros H x Hx. apply H. change repl_names with (take 4 repl_names ++ len_names ++ drop (4 + length len_names) repl_names)%list in Hx.
  rewrite !existsb_app in Hx. apply Bool.orb_false_iff in Hx as [_ Hx]. by apply Bool.orb_false_iff in Hx as [Hx _].
Qed.

Section attempts.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hascii : !Defines ge "__gconv_transform_internal_ascii" glibc_internal_ascii}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** A status other than six selects a replacement. Status six returns to
    the search only after the loop has tried the whole list. *)
Lemma repl_try stp wd wreg fl fb freg tbl tb treg to j po poreg a1 a2 Φ :
  function_check_res ge fp = Some ok ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2^63 -> wflags_ok fl ->
  0 < fb -> fb + 4 * Z.of_nat (length tbl) <= r_end freg -> r_end freg <= 2^63 ->
  Z.of_nat (length tbl) < 2^30 -> Forall (fun x => 0 <= x < 2^32) tbl ->
  0 < tb -> 0 <= to -> r_end treg <= 2^63 ->
  0 < po -> po mod 8 = 0 -> po + 8 <= r_end poreg -> r_end poreg <= 2^63 ->
  0 < a1 -> a1 mod 16 = 0 -> a1 + 16 <= 2^48 -> 0 < a2 -> a2 mod 16 = 0 -> a2 + 16 <= 2^48 ->
  ⊢ ∀ e p fuel zs x1 x2, let m := Z.of_nat (length zs) in
    ⌜list_okb tbl p fuel = true /\ tb + to + m <= r_end treg /\ 0 <= j <= m /\ Forall (fun x => 0 <= x < 256) zs /\
      lookup (TAtom "v0") e = Some (WPtr stp) /\ lookup (TAtom "v2") e = Some (WPtr (mkPtr (wd+168) (Obj wd))) /\
      lookup (TAtom "v10") e = Some (WPtr (objp po)) /\ lookup (TAtom "v29") e = Some (WPtr fp) /\
      lookup (TAtom "v211") e = Some (WPtr (objp a1)) /\ lookup (TAtom "v212") e = Some (WPtr (objp a2)) /\
      lookup (TAtom "v95") e = Some (WPtr (rop fb)) /\ lookup (TAtom "pr.7") e = Some (WInt (Z.of_nat p))⌝ -∗
    live wd wreg -∗ pcell wd 176 (mkPtr (tb+to+m) (Obj tb)) -∗ bytes wd 184 (int_bytes fl) -∗
    liveq DfracDiscarded fb freg -∗ bytesq DfracDiscarded fb 0 (le_words tbl) -∗
    live tb treg -∗ bytes tb to zs -∗ live po poreg -∗ pcell po 0 (mkPtr (tb+to+j) (Obj tb)) -∗
    live a1 (mkRegion a1 (a1+16) Heap Live) -∗ pcell a1 0 x1 -∗
    live a2 (mkRegion a2 (a2+16) Heap Live) -∗ pcell a2 0 x2 -∗
    (∀ e' st jj out u, ⌜same_out repl_names e e' /\ j <= jj <= m /\ length out = length zs /\
        Forall (fun x => 0 <= x < 256) out /\ lookup (TAtom "v245") e' = Some (WInt st) /\
        lookup (TAtom "chk26") e' = Some (WPtr (objp po)) /\ lookup (TAtom "chk27") e' = Some (WPtr (objp a2))⌝ -∗
      live wd wreg -∗ pcell wd 176 (mkPtr (tb+to+m) (Obj tb)) -∗ bytes wd 184 (int_bytes fl) -∗
      live tb treg -∗ bytes tb to out -∗ live po poreg -∗ pcell po 0 (mkPtr (tb+to+j) (Obj tb)) -∗
      live a1 (mkRegion a1 (a1+16) Heap Live) -∗ pcell a1 0 u -∗
      live a2 (mkRegion a2 (a2+16) Heap Live) -∗ pcell a2 0 (mkPtr (tb+to+jj) (Obj tb)) -∗
      WP (ERun (mkFrame glibc_translit e' [] None (body_at glibc_translit (if st mod 2^32 =? 6 then "L183" else "L246"))) : sexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame glibc_translit e [] None (body_at glibc_translit "L206")) : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfp Hwd Hw8 Hwe Hwr Hfl Hfb Hfe Hfr Hsize Hwords Htb Hto Htr Hpo Hpo8 Hpoe Hpor Ha1 Ha16 Ha1e Ha2 Ha26 Ha2e.
  iLöb as "IH". iIntros (e p f zs x1 x2 (Hok & Hte & Hj & Hzs & V0 & V2 & V10 & V29 & V211 & V212 & V95 & P7))
    "Hwl Hoe Hfl #Hrl #Hrs Htl Hzs Hpol Hpo H1l H1 H2l H2 HK".
  destruct (list_okb_step _ _ _ Hok) as (q & y & Hq & Hy & Hnext). destruct (nul_at_spec _ _ _ _ Hq) as [Hz Hnz].
  pose proof (lookup_lt_Some _ _ _ Hy) as Hbound. assert (Hy32 := word_bound _ _ _ Hwords Hy).
  body_start glibc_translit "L206". do 2 step.
  iApply (repl_len [] fb freg tbl p q Φ with "[%] Hrl Hrs"); try assumption.
  { split_and!; [instantiate (1:=0%nat); lia | vx | reflexivity | vx]. }
  iIntros (el (Hs & P8 & V222)).
  Local Ltac retain H s := let T := fresh "V" in pose proof (H (TAtom s) eq_refl) as T; cbn in T.
  assert (Hs0 : same_out repl_names e el) by (eapply same_out_trans; [|exact (len_same_repl _ _ Hs)]; same_tac).
  Local Ltac regs H := retain H "v0"; retain H "v2"; retain H "v10"; retain H "v29";
    retain H "v211"; retain H "v212"; retain H "v95".
  regs Hs0.
  iApply (repl_call el stp wd wreg fl fb freg tbl p q tb treg to zs j po poreg a1 a2 x1 x2 Φ
    with "Hwl Hoe Hfl Hrl Hrs Htl Hzs Hpol Hpo H1l H1 H2l H2"); try first [assumption | lia | congruence].
  { rewrite (Hs (TAtom "pr.7") eq_refl). vx. }
  iIntros (ec st jj out u (Hsc & Hjj & Hl & Hb & V245 & C26 & C27 & P7c & P8c))
    "Hwl Hoe Hfl Htl Hzs Hpol Hpo H1l H1 H2l H2".
  assert (Hsc0 := same_out_trans _ _ _ _ Hs0 Hsc).
  destruct (st mod 2^32 =? 6) eqn:Es.
  2: { iSpecialize ("HK" $! ec st jj out u). iEval (rewrite Es) in "HK".
       iApply ("HK" with "[%] Hwl Hoe Hfl Htl Hzs Hpol Hpo H1l H1 H2l H2"). split_and!; first [assumption | lia]. }
  assert (V95c : lookup (TAtom "v95") ec = Some (WPtr (rop fb))) by (rewrite (Hsc0 (TAtom "v95") eq_refl); exact V95).
  assert (0 <= Z.of_nat p + (Z.of_nat q + 1) < Z.of_nat (length tbl)) by lia.
  body_start glibc_translit "L248". do 5 step. check_read_dq "Hrl" by a4. iNext. iIntros "_".
  iDestruct (wchar_at _ _ _ _ _ y Hy with "Hrs") as "[Hy _]".
  load_bytes_dq "Hrl Hy" decode (apply load_uw_char; exact Hy32) by a4. iNext. iIntros "_ _". step.
  destruct (Z.eq_dec y 0) as [-> | Ny].
  - branch_as true. step. iSpecialize ("HK" $! _ st jj out u). iEval (rewrite Es) in "HK".
    iApply ("HK" with "[%] Hwl Hoe Hfl Htl Hzs Hpol Hpo H1l H1 H2l H2").
    split_and!; first [same_tac | assumption | lia | vx].
  - branch_as false. step. destruct Hnext as [-> | [f' Hf']]; [contradiction|].
    iApply ("IH" $! _ (p+q+1)%nat f' out u _ with "[%] Hwl [Hoe] Hfl Hrl Hrs Htl Hzs Hpol Hpo H1l H1 H2l H2 [HK]").
    + rewrite Hl. split_and!; try assumption; try solve [vx]; try lia;
        repeat (rewrite Symbolic.lookup_after_put_other; [|reflexivity]); try (rewrite Hsc0; [assumption|reflexivity]).
      rewrite Symbolic.lookup_after_put_same. do 2 f_equal. unwrap2. lia.
    + by rewrite Hl.
    + iIntros (e' st' jj' out' u' (Hs' & Hj' & Hl' & Hb' & V245' & C26' & C27'))
        "Hwl Hoe Hfl Htl Hzs Hpol Hpo H1l H1 H2l H2".
      iApply ("HK" $! e' st' jj' out' u' with "[%] Hwl [Hoe] Hfl Htl Hzs Hpol Hpo H1l H1 H2l H2"); [|by rewrite Hl].
      split_and!; try assumption; try lia. eapply same_out_trans; [|exact Hs']. same_tac.
Qed.
End attempts.
