(** To recognize a string conversion, glibc advances past the percent
    sign and reads the letter s from memory. This proof follows that
    read and preserves the caller's permission to read the format text.

    A second rule first checks that no custom conversions are registered.
    The caller must supply the three null pointers that glibc checks.
    Neither rule initializes those pointers or proves startup behavior. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps FormatterCode
  Fix WordString MemFwdLogic FormatterRegistration.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L LibioLogic LibioCloseSteps.
Open Scope Z_scope.
(** The first parser iteration initializes its counters and remembers
    the conversion letter after advancing the saved format pointer. *)
Definition percent_string_env e cb p wb p9 :=
  fold_left (fun e nw => put (fst nw) (snd nw) e)
    [(TAtom "pr.16", WInt 0); (TAtom "pr.11", WInt 0);
     (TAtom "pr.9", WPtr p9); (TAtom "pr.4", WPtr null);
     (TAtom "v102", WPtr (mkPtr (wb + 1000) (Obj wb)));
     (TAtom "chk9", WPtr (mkPtr cb (Obj cb))); (TAtom "v108", WPtr p);
     (TAtom "v109", WPtr (ptr_add p 1)); (TAtom "chk10", WPtr (mkPtr cb (Obj cb)));
     (TAtom "chk11", WPtr (ptr_add p 1)); (TAtom "v110", WInt 115);
     (TAtom "v111", WInt 115); (TAtom "v116", WInt 0);
     (TAtom "v120", WInt 0); (TAtom "v122", WInt 0)] e.
Section parser.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** The byte read uses the format's existing share. Advancing the
    pointer requires full ownership of its cell, but it does not require
    exclusive ownership of the format text. *)
Lemma wp_formatter_percent_string e ls cb cr wb p9 p dq Φ :
  lookup (TAtom "v23") e = Some (WPtr p9) ->
  lookup (TAtom "v13") e = Some (WPtr (mkPtr wb (Obj wb))) ->
  lookup (TAtom "v10") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  lookup (TAtom "chk3") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  0 <= wb -> wb + 1000 < 2^64 ->
  0 < cb -> cb mod 8 = 0 -> cb + 8 <= r_end cr -> r_end cr <= 2^63 ->
  live cb cr -∗ pcell cb 0 p -∗ word_string dq p [37;115] -∗
  ▷ (live cb cr -∗ pcell cb 0 (ptr_add p 1) -∗ word_string dq p [37;115] -∗
    WP (ERun (mkFrame glibc_printf_buffer (percent_string_env e cb p wb p9) ls None
      (Enter (TAtom "L113") (Some (TAtom "L118")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_printf_buffer e ls None
    (Enter (TAtom "L79") (Some (TAtom "L67")))) : gexpr) {{ Φ }}.
Proof.
  intros H9 Hw Hv Hchk Hwb Hwe Hcb Hca Hce Hcr. iIntros "Hl Hcell Hs HK".
  iDestruct (word_string_bytes with "Hs") as (sb sr ws) "(%Hshape & Hsl & Hbytes & Hback)".
  pose proof Hshape as [Hcap Hsb Hsa Hst Hfit Hspace Hlen Hws Hby Hch].
  assert (Hpend : ptr_addr p + 3 <= r_end sr).
  { unfold wstart in Hfit. cbn [length] in Hlen.
    pose proof (Z.div_mod (ptr_addr p mod 8 + 2 + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + 2 + 8) 8 ltac:(lia)). lia. }
  iAssert (live_capq dq (ptr_cap p) sr) with "[Hsl]" as "Hsl".
  { destruct Hcap as [-> | ->]; iExact "Hsl". }
  iApply wp_enter; [reflexivity | vx |]. iNext.
  cbn [b_insts b_jump]. step. norm. check "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hcell Hsl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; lia |].
  iNext. iIntros "Hl Hcell Hsl". step. norm.
  check "Hl". store "Hl" "Hcell".
  iAssert (liveq dq sb sr) with "[Hsl]" as "Hsl".
  { destruct Hcap as [Hc | Hc]; iEval (cbn [ptr_cap]; rewrite Hc) in "Hsl"; iExact "Hsl". }
  check_read_dq "Hsl" by (cbn [ptr_add ptr_addr]; ar).
  iNext. iIntros "Hsl".
  assert (Hparts : byte_ps sb (ptr_addr p - sb) [37;115;0] =
    byte_ps sb (ptr_addr p - sb) [37] ++ byte_ps sb (ptr_addr p - sb + 1) [115] ++
    byte_ps sb (ptr_addr p - sb + 1 + 1) [0]).
  { rewrite !byte_ps_cons. reflexivity. }
  iEval (unfold MemFwdLogic.ML.bytesq; cbn [app]; rewrite Hparts !ptsq_app) in "Hbytes".
  iDestruct "Hbytes" as "(Hpercent & Hletter & Hnul)".
  load_bytes_dq "Hsl Hletter" decode (reflexivity) by (cbn [ptr_add ptr_addr]; ar).
  iNext. iIntros "Hsl Hletter".
  step. step. closed_ints. branch. step. step. closed_ints. step.
  iApply wp_enter; [reflexivity | vx |]. iNext. branch.
  iApply ("HK" with "Hl Hcell [Hsl Hpercent Hletter Hnul Hback]").
  iApply ("Hback" with "Hsl [Hpercent Hletter Hnul]").
  rewrite /MemFwdLogic.ML.bytesq /= Hparts !ptsq_app. iFrame.
Qed.
(** Glibc uses its built-in parser when no custom conversions are
    registered. The caller supplies three null pointers for the proof
    to check before reading the conversion letter. The pointers and
    permission to read the format text remain unchanged. *)
Lemma wp_formatter_registered_string e ls from rb rr mb mr ab ar cb cr wb p9 p dq Φ :
  lookup (TAtom "__printf_function_table") (ge_globals ge) = Some (mkPtr rb (Obj rb)) ->
  lookup (TAtom "__printf_modifier_table") (ge_globals ge) = Some (mkPtr mb (Obj mb)) ->
  lookup (TAtom "__printf_va_arg_table") (ge_globals ge) = Some (mkPtr ab (Obj ab)) ->
  lookup (TAtom "v23") e = Some (WPtr p9) ->
  lookup (TAtom "v13") e = Some (WPtr (mkPtr wb (Obj wb))) ->
  lookup (TAtom "v10") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  lookup (TAtom "chk3") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  0 < rb -> rb mod 8 = 0 -> rb + 8 <= r_end rr -> r_end rr <= 2^63 ->
  0 < mb -> mb mod 8 = 0 -> mb + 8 <= r_end mr -> r_end mr <= 2^63 ->
  0 < ab -> ab mod 8 = 0 -> ab + 8 <= r_end ar -> r_end ar <= 2^63 ->
  0 <= wb -> wb + 1000 < 2^64 ->
  0 < cb -> cb mod 8 = 0 -> cb + 8 <= r_end cr -> r_end cr <= 2^63 ->
  live rb rr -∗ pcell rb 0 null -∗ live mb mr -∗ pcell mb 0 null -∗ live ab ar -∗ pcell ab 0 null -∗
  live cb cr -∗ pcell cb 0 p -∗ word_string dq p [37;115] -∗
  ▷ (live rb rr -∗ pcell rb 0 null -∗ live mb mr -∗ pcell mb 0 null -∗ live ab ar -∗ pcell ab 0 null -∗
    live cb cr -∗ pcell cb 0 (ptr_add p 1) -∗ word_string dq p [37;115] -∗
    WP (ERun (mkFrame glibc_printf_buffer
      (percent_string_env (registration_env e rb mb ab) cb p wb p9) ls None
      (Enter (TAtom "L113") (Some (TAtom "L118")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_printf_buffer e ls None (Enter (TAtom "L44") from)) : gexpr) {{ Φ }}.
Proof.
  intros Hrf Hmf Haf H9 Hw Hv Hchk Hrb Hra Hre Hrr Hmb Hma Hme Hmr Hab Haa Hae Har
    Hwb Hwe Hcb Hca Hce Hcr.
  iIntros "Hrl Hrc Hml Hmc Hal Hac Hl Hcell Hs HK".
  iApply (wp_formatter_registration with "Hrl Hrc Hml Hmc Hal Hac"); try assumption.
  iNext. iIntros "Hrl Hrc Hml Hmc Hal Hac".
  iApply (wp_formatter_percent_string _ ls cb cr wb p9 p dq with "Hl Hcell Hs"); try assumption.
  - unfold registration_env. cbn [fold_left fst snd]. lookups; done.
  - unfold registration_env. cbn [fold_left fst snd]. lookups; done.
  - unfold registration_env. cbn [fold_left fst snd]. lookups; done.
  - unfold registration_env. cbn [fold_left fst snd]. lookups; done.
  - iNext. iIntros "Hl Hcell Hs".
    iApply ("HK" with "Hrl Hrc Hml Hmc Hal Hac Hl Hcell Hs").
Qed.
End parser.
