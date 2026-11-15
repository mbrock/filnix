(** Glibc scans the format before checking for registered conversions.
    For a format beginning with percent, the initial literal write has
    length zero. These rules follow that scan and the subsequent byte
    read without deriving caller memory or registration values from startup. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps FormatterCode
  Fix WordString FormatterScan StrchrCode StrchrnulLogic MemFwdLogic
  FormatterLiteral FormatterSuffixReturn PrintfBufferIoCode FormatterRegistration.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L LibioLogic LibioCloseSteps.
Open Scope Z_scope.
(** The formatter needs temporary memory before it can scan the format.
    This proof starts after that memory is allocated and the position
    in the argument list is copied. *)
Definition initial_scan_block := Eval vm_compute in
  match find_block (TAtom "start") (fn_blocks glibc_printf_buffer) with
  | Some b => b | None => mkBlock (TAtom "absent") [] [] JRetVoid end.
(** The selector retains the actual entry block. *)
Lemma initial_scan_block_found :
  find_block (TAtom "start") (fn_blocks glibc_printf_buffer) = Some initial_scan_block.
Proof. vm_compute. reflexivity. Qed.
(** The byte test leaves the saved format pointer unchanged. Its
    environment records the actual loads before registration is checked. *)
Definition initial_percent_env e cb p :=
  fold_left (fun e nw => put (fst nw) (snd nw) e)
    [(TAtom "chk4", WPtr (mkPtr cb (Obj cb))); (TAtom "v45", WPtr p);
     (TAtom "chk5", WPtr p); (TAtom "v46", WInt 37); (TAtom "v47", WInt 0)] e.
(** The formatter remembers where its search stopped and whether writing
    failed. These register values record a percent sign found at the
    beginning of the format and a buffer that has not failed. *)
Definition initial_scan_env e cb p :=
  fold_left (fun e nw => put (fst nw) (snd nw) e)
    [(TAtom "v27", WPtr p); (TAtom "chk3", WPtr (mkPtr cb (Obj cb)));
     (TAtom "v32", WInt (ptr_addr p)); (TAtom "v33", WInt (ptr_addr p));
     (TAtom "v34", WInt 0); (TAtom "v39", WInt 0); (TAtom "v40", WInt 0)] e.
Section initial.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** A readable percent byte selects the registration checks rather than
    returning at NUL. The caller retains the original format share and
    supplies any registration cells through the continuation. *)
Lemma wp_formatter_initial_percent e ls cb cr p dq Φ :
  lookup (TAtom "v10") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  lookup (TAtom "chk3") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  0 < cb -> cb mod 8 = 0 -> cb + 8 <= r_end cr -> r_end cr <= 2^63 ->
  live cb cr -∗ pcell cb 0 p -∗ word_string dq p [37;115] -∗
  ▷ (live cb cr -∗ pcell cb 0 p -∗ word_string dq p [37;115] -∗
    WP (ERun (mkFrame glibc_printf_buffer (initial_percent_env e cb p) ls None
      (Enter (TAtom "L44") (Some (TAtom "L37")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_printf_buffer e ls None
    (Enter (TAtom "L37") (Some (TAtom "start")))) : gexpr) {{ Φ }}.
Proof.
  intros Hv Hchk Hcb Hca Hce Hcr. iIntros "Hl Hcell Hs HK".
  iDestruct (word_string_bytes with "Hs") as (sb sr ws) "(%Hshape & Hsl & Hbytes & Hback)".
  pose proof Hshape as [Hcap Hsb Hsa Hst Hfit Hspace Hlen Hws Hby Hch].
  assert (Hpend : ptr_addr p + 3 <= r_end sr).
  { unfold wstart in Hfit. cbn [length] in Hlen.
    pose proof (Z.div_mod (ptr_addr p mod 8 + 2 + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + 2 + 8) 8 ltac:(lia)). lia. }
  iAssert (live_capq dq (ptr_cap p) sr) with "[Hsl]" as "Hsl".
  { destruct Hcap as [-> | ->]; iExact "Hsl". }
  iApply wp_enter; [reflexivity | vx |]. iNext.
  cbn [b_insts b_jump]. check "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hcell Hsl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; lia |].
  iNext. iIntros "Hl Hcell Hsl".
  iAssert (liveq dq sb sr) with "[Hsl]" as "Hsl".
  { destruct Hcap as [Hc | Hc]; iEval (cbn [ptr_cap]; rewrite Hc) in "Hsl"; iExact "Hsl". }
  check_read_dq "Hsl" by ar. iNext. iIntros "Hsl".
  assert (Hparts : byte_ps sb (ptr_addr p - sb) [37;115;0] =
    (byte_ps sb (ptr_addr p - sb) [37] ++ byte_ps sb (ptr_addr p - sb + 1) [115;0])%list).
  { rewrite !byte_ps_cons. reflexivity. }
  iEval (unfold MemFwdLogic.ML.bytesq; cbn [app]; rewrite Hparts ptsq_app) in "Hbytes".
  iDestruct "Hbytes" as "[Hpercent Hrest]".
  load_bytes_dq "Hsl Hpercent" decode (reflexivity) by ar.
  iNext. iIntros "Hsl Hpercent". step. closed_ints. branch.
  iApply ("HK" with "Hl Hcell [Hsl Hpercent Hrest Hback]").
  iApply ("Hback" with "Hsl [Hpercent Hrest]").
  rewrite /MemFwdLogic.ML.bytesq /= Hparts ptsq_app. iFrame.
Qed.
(** A format beginning with percent has no literal text to copy first.
    Glibc still calls the writer with length zero and checks whether
    the buffer has failed. These calls leave the format readable with
    the caller's original permission. *)
Lemma wp_formatter_initial_scan e ls cb cr old bb br p dq Φ :
  lookup (TAtom "v10") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  lookup (TAtom "v2") e = Some (WPtr p) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  find_fn ge (TAtom "glibc_vfprintf_internal#__find_specmb.gnu_inline") = Some (Defined glibc_find_specmb) ->
  find_fn ge (TAtom "__printf_buffer_write") = Some (Defined glibc___printf_buffer_write) ->
  find_fn ge (TAtom "glibc_vfprintf_internal#__printf_buffer_has_failed") = Some (Defined glibc_format_failed) ->
  0 < cb -> cb mod 8 = 0 -> cb + 8 <= r_end cr -> r_end cr <= 2^63 ->
  0 < bb -> bb mod 8 = 0 -> bb + 36 <= r_end br -> r_end br <= 2^63 ->
  live cb cr -∗ pcell cb 0 old -∗ word_string dq p [37;115] -∗
  live bb br -∗ int_cell bb 32 4 -∗
  ▷ (live cb cr -∗ pcell cb 0 p -∗ word_string dq p [37;115] -∗
    live bb br -∗ int_cell bb 32 4 -∗
    WP (ERun (mkFrame glibc_printf_buffer
      (initial_percent_env (initial_scan_env e cb p) cb p) ls None
      (Enter (TAtom "L44") (Some (TAtom "L37")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_printf_buffer e ls None
    (Exec (TAtom "start") (skipn 19 (b_insts initial_scan_block)) (b_jump initial_scan_block))) : gexpr) {{ Φ }}.
Proof.
  intros Hv Hp Hb Hchr Hscan Hwrite Hfailed Hcb Hca Hce Hcr Hbb Hba Hbe Hbr.
  iIntros "Hcl Hcell Hs Hl Hmode HK".
  iDestruct "Hs" as (sb sr ws) "[%Hshape Hw]".
  pose proof Hshape as [Hcap Hsb Hsa Hst Hfit Hspace Hlen Hws Hby Hch].
  assert (Hpend : ptr_addr p + 3 <= r_end sr).
  { unfold wstart in Hfit. cbn [length] in Hlen.
    pose proof (Z.div_mod (ptr_addr p mod 8 + 2 + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + 2 + 8) 8 ltac:(lia)). lia. }
  assert (Hpa : 0 < ptr_addr p < 2^63) by lia.
  iAssert (word_string dq p [37;115]) with "[Hw]" as "Hs".
  { iExists sb, sr, ws. iSplit; [done|iExact "Hw"]. }
  cbn [skipn b_insts b_jump initial_scan_block].
  iApply wp_call_bind; [vx | exact Hscan | reflexivity |]. iNext.
  iApply (wp_wand with "[Hs]").
  { iApply (wp_find_specmb dq p [37;115]
      (fun v => ⌜v = Ret (WPtr p)⌝ ∗ word_string dq p [37;115])%I with "Hs"); [exact Hchr|].
    iIntros "Hs". iFrame. iPureIntro.
    change (Ret (WPtr (ptr_add p 0)) = Ret (WPtr p)).
    replace (ptr_add p 0) with p by (destruct p; unfold ptr_add; cbn; f_equal; lia). reflexivity. }
  iIntros (v) "[-> Hs]". resume.
  check "Hcl". store "Hcl" "Hcell".
  do 3 step. norm. closed_ints.
  replace (ptr_addr p - ptr_addr p) with 0 by lia.
  iApply wp_call_bind; [vx | exact Hwrite | reflexivity |]. iNext.
  iApply (wp_wand with "[Hl Hmode]").
  { iApply (wp_printf_buffer_write_zero _ bb br p
      (fun v => ⌜v = RetVoid⌝ ∗ live bb br ∗ int_cell bb 32 4)%I with "Hl Hmode");
      try assumption; try reflexivity.
    iNext. iIntros "Hl Hmode". iFrame. done. }
  iIntros (v) "(-> & Hl & Hmode)". resume.
  iApply wp_call_bind; [vx | exact Hfailed | reflexivity |]. iNext.
  iApply (wp_wand with "[Hl Hmode]").
  { iApply (wp_format_has_not_failed _ bb br
      (fun v => ⌜v = Ret (WInt 0)⌝ ∗ live bb br ∗ int_cell bb 32 4)%I with "Hl Hmode");
      try assumption; try reflexivity.
    iNext. iIntros "Hl Hmode". iFrame. done. }
  iIntros (v) "(-> & Hl & Hmode)". resume. step. branch.
  iApply (wp_formatter_initial_percent _ ls cb cr p dq with "Hcl Hcell Hs"); try assumption.
  - lookups; done.
  - lookups; done.
  - iNext. iIntros "Hcl Hcell Hs".
    iApply ("HK" with "Hcl Hcell Hs Hl Hmode").
Qed.
(** The three extension cells are separate inputs, not consequences of
    scanning. Their null values let the handover reach the built-in
    parser while preserving every supplied cell and the format share. *)
Lemma wp_formatter_initial_registered e ls cb cr old bb br p dq rb rr mb mr ab ar Φ :
  lookup (TAtom "v10") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  lookup (TAtom "v2") e = Some (WPtr p) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  find_fn ge (TAtom "glibc_vfprintf_internal#__find_specmb.gnu_inline") = Some (Defined glibc_find_specmb) ->
  find_fn ge (TAtom "__printf_buffer_write") = Some (Defined glibc___printf_buffer_write) ->
  find_fn ge (TAtom "glibc_vfprintf_internal#__printf_buffer_has_failed") = Some (Defined glibc_format_failed) ->
  lookup (TAtom "__printf_function_table") (ge_globals ge) = Some (mkPtr rb (Obj rb)) ->
  lookup (TAtom "__printf_modifier_table") (ge_globals ge) = Some (mkPtr mb (Obj mb)) ->
  lookup (TAtom "__printf_va_arg_table") (ge_globals ge) = Some (mkPtr ab (Obj ab)) ->
  0 < cb -> cb mod 8 = 0 -> cb + 8 <= r_end cr -> r_end cr <= 2^63 ->
  0 < bb -> bb mod 8 = 0 -> bb + 36 <= r_end br -> r_end br <= 2^63 ->
  0 < rb -> rb mod 8 = 0 -> rb + 8 <= r_end rr -> r_end rr <= 2^63 ->
  0 < mb -> mb mod 8 = 0 -> mb + 8 <= r_end mr -> r_end mr <= 2^63 ->
  0 < ab -> ab mod 8 = 0 -> ab + 8 <= r_end ar -> r_end ar <= 2^63 ->
  live cb cr -∗ pcell cb 0 old -∗ word_string dq p [37;115] -∗
  live bb br -∗ int_cell bb 32 4 -∗
  live rb rr -∗ pcell rb 0 null -∗ live mb mr -∗ pcell mb 0 null -∗ live ab ar -∗ pcell ab 0 null -∗
  ▷ (live cb cr -∗ pcell cb 0 p -∗ word_string dq p [37;115] -∗
    live bb br -∗ int_cell bb 32 4 -∗
    live rb rr -∗ pcell rb 0 null -∗ live mb mr -∗ pcell mb 0 null -∗ live ab ar -∗ pcell ab 0 null -∗
    WP (ERun (mkFrame glibc_printf_buffer
      (registration_env (initial_percent_env (initial_scan_env e cb p) cb p) rb mb ab) ls None
      (Enter (TAtom "L79") (Some (TAtom "L67")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_printf_buffer e ls None
    (Exec (TAtom "start") (skipn 19 (b_insts initial_scan_block)) (b_jump initial_scan_block))) : gexpr) {{ Φ }}.
Proof.
  intros Hv Hp Hb Hchr Hscan Hwrite Hfailed Hrf Hmf Haf
    Hcb Hca Hce Hcr Hbb Hba Hbe Hbr Hrb Hra Hre Hrr Hmb Hma Hme Hmr Hab Haa Hae Har.
  iIntros "Hcl Hcell Hs Hl Hmode Hrl Hrc Hml Hmc Hal Hac HK".
  iApply (wp_formatter_initial_scan with "Hcl Hcell Hs Hl Hmode"); try assumption.
  iNext. iIntros "Hcl Hcell Hs Hl Hmode".
  iApply (wp_formatter_registration with "Hrl Hrc Hml Hmc Hal Hac"); try assumption.
  iNext. iIntros "Hrl Hrc Hml Hmc Hal Hac".
  iApply ("HK" with "Hcl Hcell Hs Hl Hmode Hrl Hrc Hml Hmc Hal Hac").
Qed.
End initial.
