(** Error prints the program name with the format "%s: ". The normal
    NULL-stream wrapper selects stderr, locks it, calls the formatter and
    releases the lock. This proof returns the same stream and name access
    supplied by the caller, even when the formatter reports failure.

    The caller supplies permission to read the name through its terminating
    NUL. The separate name lifetime is borrowed once, not included again
    with the bytes. Printing may change errno and the stream mode; later
    message printing must account for the mode actually returned. *)
From Glibc Require Import GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsRegistry SysWrappers FileInv LibioLogic LibioCloseSteps
  FxprintfStream FxprintfNormalCode FxprintfNormalCall FxprintfNormalNull VfxprintfNarrow.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section prefix.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Reading the name requires permission to read each byte, not just its
    address and length. The caller supplies these bytes separately from
    the lifetime already borrowed by the entry rule. *)
Definition error_prefix_name pname nameb namer dqb chars : iProp Σ :=
  ⌜StringLogic.string_ok pname nameb namer chars⌝ ∗
    bytesq dqb nameb (ptr_addr pname - nameb) (chars ++ [0]).

Definition error_prefix_fields fb fl lb lbreg md nb nreg : iProp Σ :=
  int_cell fb 0 fl ∗ pcell fb 136 (mkPtr lb (Obj lb)) ∗ lock_state lb lbreg 0 0 null ∗
  int_cell fb 192 md ∗ live_capq DfracDiscarded (Ro nb) nreg ∗
  bytesq DfracDiscarded nb 0 [37;115;58;32;0].

(** The formatter receives the original name capability share together with
    its bytes. The wrapper returns both and releases the stream lock after
    formatting. No narrow-mode condition is imposed on the returned mode. *)
Lemma wp_error_prefix (Hregistry : holds_os registry) (Hext : sys_external ge)
    fb freg fl lb lbreg md nb nreg sb sreg gb greg pname nameb namer dqn dqb chars
    (R E : iProp Σ) (Q : Z -> Z -> iProp Σ) :
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr gb (Obj gb)) ->
  0 < gb -> gb mod 8 = 0 -> gb + 8 <= r_end greg -> r_end greg <= 2 ^ 63 ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 -> 0 <= nb < 2 ^ 64 -> md = 0 \/ md = 2 ^ 32 - 1 ->
  ptr_addr (ow_self w0) <> 0 -> 0 <= ptr_addr (ow_self w0) < 2 ^ 64 ->
  find_fn ge (TAtom "__vfxprintf") = Some (Defined glibc_vfxprintf) ->
  (forall ap, vfxprintf_formatter fb freg fl lb lbreg (mkPtr nb (Ro nb)) ap 0 md DfracDiscarded nreg
    (fun q => fx_va q [WPtr null;WPtr (mkPtr nb (Ro nb));WPtr pname])
    (bytesq DfracDiscarded nb 0 [37;115;58;32;0] ∗ live_capq dqn (ptr_cap pname) namer ∗
      error_prefix_name pname nameb namer dqb chars ∗ R)%I
    (fun r => bytesq DfracDiscarded nb 0 [37;115;58;32;0] ∗ live_capq dqn (ptr_cap pname) namer ∗
      error_prefix_name pname nameb namer dqb chars ∗ ∃ md', int_cell fb 192 md' ∗ Q r md')%I) ->
  live_capq dqn (ptr_cap pname) namer -∗
  (single_ro ge sb sreg ∗ live gb greg ∗ pcell gb 0 (mkPtr fb (Obj fb)) ∗ live fb freg ∗
    error_prefix_fields fb fl lb lbreg md nb nreg ∗ error_prefix_name pname nameb namer dqb chars ∗ R) -∗ E -∗
  WP (ERun (fxprintf_normal_frame null (mkPtr nb (Ro nb)) [WPtr pname]) : gexpr)
    {{ v, ∃ r md', ⌜v = Ret (WInt (r mod 2 ^ 32))⌝ ∗ live_capq dqn (ptr_cap pname) namer ∗
      live gb greg ∗ pcell gb 0 (mkPtr fb (Obj fb)) ∗ live fb freg ∗
      error_prefix_fields fb fl lb lbreg md' nb nreg ∗ error_prefix_name pname nameb namer dqb chars ∗ Q r md' ∗ E }}.
Proof using Type.
  intros Hg Hgb Hga Hge Hgr Hfb Hal Hend Hreg Huser Hnb Hmd Hself Hselfr Hfn Hformat.
  iIntros "Hname (#Hs & Hgl & Hgp & Hl & (Hfl & Hlp & Hlk & Hmd & Hfmt & Htext) & Hbytes & HR) HE".
  iApply (wp_fxprintf_normal_null Hregistry Hext fb freg fl lb lbreg (mkPtr nb (Ro nb)) [WPtr pname] md
    DfracDiscarded nreg sb sreg gb greg
    (bytesq DfracDiscarded nb 0 [37;115;58;32;0] ∗ live_capq dqn (ptr_cap pname) namer ∗
      error_prefix_name pname nameb namer dqb chars ∗ R)%I E
    (fun r => bytesq DfracDiscarded nb 0 [37;115;58;32;0] ∗ live_capq dqn (ptr_cap pname) namer ∗
      error_prefix_name pname nameb namer dqb chars ∗ ∃ md', int_cell fb 192 md' ∗ Q r md')%I
    with "Hs Hgl Hgp Hl Hfl Hlp Hlk Hmd Hfmt [$Htext $Hname $Hbytes $HR] HE []"); try assumption; try reflexivity.
  iNext. iIntros (r) "Hgl Hgp Hl Hfl Hlp Hlk Hfmt _ (Htext & Hname & Hbytes & Hmode) HE".
  iDestruct "Hmode" as (md') "[Hmd HQ]".
  iExists r, md'. iSplit; [done |]. unfold error_prefix_fields. iFrame.
Qed.
End prefix.
