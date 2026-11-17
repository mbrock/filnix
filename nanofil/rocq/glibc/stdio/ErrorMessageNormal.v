(** Error checks the result of message printing before counting the report.
    This rule runs the narrow vfxprintf call and those checks together.
    The formatter implementation and the wide fallback remain explicit
    contracts; a failed ENOMEM result with positive mode still calls the
    fallback.

    Printing starts with an unlocked stream whose mode is zero or UINT_MAX.
    The caller owns the stream and provides readable format bytes. Printing
    preserves the original argument cursor, but may change errno and mode.
    Later text and newline printing receive the permissions left after
    the failure checks finish. *)
From Glibc Require Import GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces
  Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  ErrorCode ErrorCall ErrorEntry ErrorMessage ErrorMessageNarrow
  FxprintfNormalCode VfxprintfSelect VfxprintfNarrow.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section message.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Checking for failure must not consume the format bytes or leave the
    stream locked. These permissions remain available while error reads
    errno and mode. The fallback returns them too, even when it fails. *)
Definition error_message_fields fb fl lb lbreg fmt fmtb fmtreg dqf dqb chars eb ereg
    (Q : Z -> Z -> Z -> iProp Σ) r en md : iProp Σ :=
  int_cell fb 0 fl ∗ pcell fb 136 (mkPtr lb (Obj lb)) ∗ lock_state lb lbreg 0 0 null ∗
  live_capq dqf (ptr_cap fmt) fmtreg ∗ bytesq dqb fmtb (ptr_addr fmt - fmtb) (chars ++ [0]) ∗
  error_message_spare fb eb ereg r en md ∗ Q r en md.

Context (Hregistry : holds_os registry) (Hext : sys_external ge).
Context (fb : Z) (freg : region) (fl lb : Z) (lbreg : region) (md : Z)
  (fmt : ptr) (fmtb : Z) (fmtreg : region) (dqf dqb : dfrac) (chars : list Z)
  (ap : ptr) (status errnum : Z) (ys : list word) (flags : Z)
  (sb : Z) (sreg : region) (gb : Z) (greg : region) (eb : Z) (ereg : region)
  (R E : iProp Σ) (Q : Z -> Z -> Z -> iProp Σ).
Let fields := error_message_fields fb fl lb lbreg fmt fmtb fmtreg dqf dqb chars eb ereg Q.
Let ready := (single_ro ge sb sreg ∗ int_cell fb 0 fl ∗ pcell fb 136 (mkPtr lb (Obj lb)) ∗
  lock_state lb lbreg 0 0 null ∗ int_cell fb 192 md ∗ live_capq dqf (ptr_cap fmt) fmtreg ∗
  bytesq dqb fmtb (ptr_addr fmt - fmtb) (chars ++ [0]) ∗ R)%I.

(** Success bypasses errno; failure reads the errno actually left by the
    formatter. ENOMEM with positive returned mode invokes the supplied
    fallback contract, which may change errno again. The saved error
    argument and its cursor remain separate from both errno values. *)
Lemma wp_error_message_normal e from cb wide widefn wideframe Φ :
  error_inputs e status errnum fmt ap flags cb ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr gb (Obj gb)) ->
  0 < gb -> gb mod 8 = 0 -> gb + 8 <= r_end greg -> r_end greg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 -> 0 <= ptr_addr fmt < 2 ^ 64 -> md = 0 \/ md = 2 ^ 32 - 1 ->
  ptr_addr (ow_self w0) <> 0 -> 0 <= ptr_addr (ow_self w0) < 2 ^ 64 ->
  StringLogic.string_ok fmt fmtb fmtreg chars -> error_errno_bounds eb ereg ->
  find_fn ge (TAtom "__vfxprintf") = Some (Defined glibc_vfxprintf) ->
  lookup (TAtom "glibc_error#str.253") (ge_globals ge) = Some wide ->
  find_fn ge (TAtom "__GI_fputws_unlocked") = Some (Defined widefn) ->
  call_frame widefn [WPtr wide;WPtr (mkPtr fb (Obj fb))] = Some wideframe ->
  vfxprintf_formatter fb freg fl lb lbreg fmt ap (flags mod 2 ^ 32) md dqf fmtreg
    (fun p => error_va p (WInt status :: WInt errnum :: WPtr fmt :: ys))
    (bytesq dqb fmtb (ptr_addr fmt - fmtb) (chars ++ [0]) ∗ R)%I
    (fun r => bytesq dqb fmtb (ptr_addr fmt - fmtb) (chars ++ [0]) ∗
      ∃ en md', live eb ereg ∗ int_cell eb 0 en ∗ int_cell fb 192 md' ∗ Q (r mod 2 ^ 32) en md')%I ->
  (forall r en md', 0 < md' < 2 ^ 31 -> ⊢ live fb freg -∗ int_cell fb 192 md' -∗
    (live eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ fields r en md') -∗
    WP (ERun wideframe : gexpr) {{ v, ∃ result, ⌜v = Ret (WInt result)⌝ ∗
      live fb freg ∗ int_cell fb 192 md' ∗
      (live eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ fields r en md') }}) ->
  live gb greg -∗ pcell gb 0 (mkPtr fb (Obj fb)) -∗ live fb freg -∗
  error_va ap (WInt status :: WInt errnum :: WPtr fmt :: ys) -∗ ready -∗ E -∗
  (∀ e' predecessor r en md', ⌜error_inputs e' status errnum fmt ap flags cb⌝ -∗
    live gb greg -∗ pcell gb 0 (mkPtr fb (Obj fb)) -∗ live fb freg -∗
    error_va ap (WInt status :: WInt errnum :: WPtr fmt :: ys) -∗
    error_message_returned fb freg eb ereg r en md' -∗ fields r en md' -∗ E -∗
    WP (ERun (mkFrame glibc_error_internal e' [] None
      (Enter (TAtom "iw_2.L19") (Some predecessor))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_error_internal e [] None
    (Enter (TAtom "iw_2.start") (Some from))) : gexpr) {{ Φ }}.
Proof using Hext Hregistry sb sreg.
  intros Hinputs Hg Hgb Hga Hge Hgr Hfb Hal Hend Hreg Huser Hfmt Hmd Hself Hselfr
    Hstring Herrno Hfn Hwide Hwidefn Hwideframe Hformat Hfallback.
  iIntros "Hgl Hgp Hl HV HR HE HK".
  iApply (wp_error_message e from status errnum fmt ap flags cb gb greg fb freg (DfracOwn 1) eb ereg
    glibc_vfxprintf (vfxprintf_frame (mkPtr fb (Obj fb)) fmt ap (flags mod 2 ^ 32))
    wide widefn wideframe
    (fun p => error_va p (WInt status :: WInt errnum :: WPtr fmt :: ys)) ready fields E
    with "Hgl Hgp Hl HV HR HE HK"); try assumption.
  - lia.
  - apply vfxprintf_call_frame.
  - iIntros "Hl HV HR".
    iApply (wp_wand with "[Hl HV HR]").
    { iApply (wp_error_message_narrow Hregistry Hext fb freg fl lb lbreg md fmt fmtb fmtreg dqf dqb chars
        ap (flags mod 2 ^ 32) status errnum ys sb sreg eb ereg R emp
        (fun r => Q (r mod 2 ^ 32)) with "Hl HV HR []"); try assumption; done. }
    iIntros (v) "H". iDestruct "H" as (r en md' ->) "(Hl & HV & Hp & Hfields)".
    iExists (r mod 2 ^ 32), en, md'. iSplit; [done |]. iFrame "Hl HV".
    unfold fields, error_message_fields, error_message_pending, error_message_spare.
    rewrite Z.mod_mod; [|lia]. iFrame "Hp".
    iDestruct "Hfields" as "(Hfl & Hlp & Hlk & Hfmt & Hbytes & Hspare & HQ & _)". iFrame.
Qed.
End message.
