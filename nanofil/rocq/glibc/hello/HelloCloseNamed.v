(** Hello saves errno before quoting a filename for a close error.
    Quoting may change errno, but the report must use the saved value.
    This proof follows the named report and joins it with the unnamed
    report, leaving only the quoting and error function contracts unproved.

    The caller supplies readable filename bytes and their object's lifetime.
    Quoting receives that ownership and returns ownership of a quoted string.
    This transfer permits the returned pointer to alias the input without
    requiring two copies of one object's lifetime. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic HelloClose.
From Glibc Require Import Unit_posix__exit_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics OsBlocks OsWorld OsRegistry
  FileInv LibioLogic LibioCloseSteps HelloCloseErrno HelloCloseDiagnostic LeavesLogic SysWrappers.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Module NS := StringLogicOn Fix.R Fix.LG0.

Section named.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context `{!Defines ge "__errno_location" errno_location_fn}
  `{!Defines ge "_exit" Unit_posix__exit_os.fn___GI__exit}.
#[local] Hint Opaque live live_cap pcell int_cell bytes errno_any NS.string : typeclass_instances.

Context (nb : Z) (nreg : region) (filename : ptr) (preg : region)
  (xc : Z) (xreg : region) (status eb : Z) (fmt text : ptr)
  (quotefn errorfn : func) (quoteframe : frame) (errorframe : Z -> ptr -> frame)
  (R Q : iProp Σ) (T : ptr -> iProp Σ).
Context (Hname : lookup (TAtom "closeout#file_name") (ge_globals ge) = Some (mkPtr nb (Obj nb)))
  (Hnb : 0 < nb) (Hnba : nb mod 8 = 0) (Hnbe : nb + 8 <= r_end nreg) (Hnbr : r_end nreg <= 2 ^ 63)
  (Hpr : 0 <= ptr_addr filename < 2 ^ 64)
  (Hfmt : lookup (TAtom "closeout#str.54") (ge_globals ge) = Some fmt)
  (Hexit : lookup (TAtom "exit_failure") (ge_globals ge) = Some (mkPtr xc (Obj xc)))
  (Hxc : 0 < xc) (Hxce : xc + 4 <= r_end xreg) (Hxcr : r_end xreg <= 2 ^ 63)
  (Hglobal : lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)))
  (He : ow_errno w0 = Some (mkPtr eb (Obj eb)))
  (Hquote : find_fn ge (TAtom "quotearg_colon") = Some (Defined quotefn))
  (Hqframe : call_frame quotefn [WPtr filename] = Some quoteframe)
  (Herror : find_fn ge (TAtom "error") = Some (Defined errorfn))
  (Hframe : forall n q, call_frame errorfn [WInt 0; WInt n; WPtr fmt; WPtr q; WPtr text] = Some (errorframe n q)).

(** Quoting receives the filename bytes, their lifetime, errno and the
    caller's resources R. Its result supplies a readable quoted string
    and resources T; it need not preserve errno. The error function receives
    those resources and a separate integer argument for the saved errno. *)
Context (Hqcall : forall b xs, string_ok filename b preg xs ->
  ⊢ live_cap (ptr_cap filename) preg -∗ bytes b (ptr_addr filename - b) (xs ++ [0]) -∗ errno_any eb -∗ R -∗
    WP (ERun quoteframe : gexpr) {{ v, ∃ q qb qr qs,
      ⌜v = Ret (WPtr q) ∧ 0 <= ptr_addr q < 2 ^ 64⌝ ∗
      NS.string q qb qr qs ∗ errno_any eb ∗ T q }})
  (Hcall : forall n q qb qr qs, 0 <= n < 2 ^ 32 -> 0 <= ptr_addr q < 2 ^ 64 ->
    ⊢ NS.string q qb qr qs -∗ errno_any eb -∗ T q -∗
    WP (ERun (errorframe n q) : gexpr) {{ v, ⌜v = RetVoid⌝ ∗ errno_any eb ∗ Q }}).

(** The named path loads the filename cell again after reading errno.
    It reports the saved errno even if quoting changes the current value,
    then loads the configured failure status and executes the real hard exit. *)
Lemma wp_close_stdout_named e b xs (E : iProp Σ) Φ :
  lookup (TAtom "v23") e = Some (WPtr text) -> string_ok filename b preg xs ->
  live nb nreg -∗ pcell nb 0 filename -∗ live_cap (ptr_cap filename) preg -∗
  bytes b (ptr_addr filename - b) (xs ++ [0]) -∗
  live xc xreg -∗ int_cell xc 0 status -∗ errno_any eb -∗ R -∗ E -∗
  WP (ERun (mkFrame close_stdout_fn e [] None
    (Enter (TAtom "L31") (Some (TAtom "L0")))) : gexpr) {{ Φ }}.
Proof using Defines0 Defines1 Hcall He Herror Hexit Hext Hfmt Hframe Hglobal Hname Hnb Hnba Hnbe Hpr Hqcall Hqframe Hquote Hreg Hxc Hxce.
  intros Htext Hstr. iIntros "Hnl Hnp Hpl Hbytes Hxl Hstatus Herr HR HE".
  step. iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
  iApply (wp_glibc_errno_location registry (os_wi w0) ge _ _ Hglobal). resume.
  iApply (wp_close_errno_check eb He); [vx |]. iNext.
  iEval (unfold errno_any) in "Herr". iEval (unfold errno_own) in "Herr".
  iDestruct "Herr" as (bs cs [Hbs Hcs]) "Hp".
  rewrite pts_app. iDestruct "Hp" as "[Hb Haux]".
  iApply (wp_close_errno_load eb He with "Hb"); [vx | exact Hbs |]. iNext. iIntros "Hb".
  iAssert (errno_any eb) with "[Hb Haux]" as "Herr".
  { rewrite /errno_any /errno_own. iExists bs, cs. rewrite pts_app. iFrame. auto. }
  step. step. iApply (wp_live_fit1 with "Hnl"). iIntros ([Hn0 Hn48]) "Hnl".
  check "Hnl". load "Hnl" "Hnp" "Hpl".
  iApply wp_call_bind; [vx | exact Hquote | exact Hqframe |]. iNext.
  iApply (wp_wand with "[Hpl Hbytes Herr HR]").
  { iApply (Hqcall with "Hpl Hbytes Herr HR"). exact Hstr. }
  iIntros (v) "Hret". iDestruct "Hret" as (q qb qr qs [-> Hqr]) "(Hstr & Herr & HT)". resume.
  iApply wp_call_bind; [vx | exact Herror | apply Hframe |]. iNext.
  iApply (wp_wand with "[Hstr Herr HT]").
  { iApply (Hcall with "Hstr Herr HT"); [apply Z.mod_pos_bound; lia | exact Hqr]. }
  iIntros (v) "(-> & Herr & HQ)". resume.
  step. step. step. iApply (wp_live_fit1 with "Hxl"). iIntros ([Hx0 Hx48]) "Hxl".
  check "Hxl". iEval (unfold int_cell) in "Hstatus".
  iDestruct "Hstatus" as "[%Hstatus Hb]". load_s32 "Hxl" "Hb".
  iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
  iApply (SysWrappers.wp_glibc__exit Hreg Hext). reflexivity.
Qed.

(** Both report paths now end in the configured hard exit. Filename bytes
    are required only when the pointer is nonzero. The remaining premises
    describe the quoting and error calls, not a block of close_stdout. *)
Lemma wp_close_stdout_diagnostics e unnamedfmt namedfmt unnamedframe (F E : iProp Σ) Φ :
  lookup (TAtom "closeout#str.52") (ge_globals ge) = Some namedfmt ->
  lookup (TAtom "closeout#str.53") (ge_globals ge) = Some text ->
  lookup (TAtom "closeout#str.55") (ge_globals ge) = Some unnamedfmt ->
  (forall n, call_frame errorfn [WInt 0; WInt n; WPtr unnamedfmt; WPtr text] = Some (unnamedframe n)) ->
  (forall n, 0 <= n < 2 ^ 32 -> ⊢ errno_any eb -∗ R -∗
    WP (ERun (unnamedframe n) : gexpr) {{ v, ⌜v = RetVoid⌝ ∗ errno_any eb ∗ Q }}) ->
  (ptr_addr filename <> 0 -> ⊢ F -∗ ∃ b xs, ⌜string_ok filename b preg xs⌝ ∗
    bytes b (ptr_addr filename - b) (xs ++ [0])) ->
  live nb nreg -∗ pcell nb 0 filename -∗ live_cap (ptr_cap filename) preg -∗
  live xc xreg -∗ int_cell xc 0 status -∗ errno_any eb -∗ R -∗ F -∗ E -∗
  WP (ERun (mkFrame close_stdout_fn e [] None
    (Enter (TAtom "L0") (Some (TAtom "L8")))) : gexpr) {{ Φ }}.
Proof using Defines0 Defines1 Hcall He Herror Hexit Hext Hfmt Hframe Hglobal Hname Hnb Hnba Hnbe Hnbr Hpr Hqcall Hqframe Hquote Hreg Hxc Hxce Hxcr.
  intros Hnamed Htext Hunnamed Huframe Hucall Hread.
  iIntros "Hnl Hnp Hpl Hxl Hstatus Herr HR HF HE".
  iApply (wp_close_stdout_diagnostic Hreg Hext e nb nreg filename preg xc xreg status eb unnamedfmt text namedfmt
    errorfn unnamedframe R Q (F ∗ E)%I with "Hnl Hnp Hpl Hxl Hstatus Herr HR [$HF $HE] []"); try assumption.
  iIntros (e') "%Hnz %Hlookup Hnl Hnp Hpl Hxl Hstatus Herr HR [HF HE]".
  iDestruct (Hread Hnz with "HF") as (b xs Hstr) "Hbytes".
  iApply (wp_close_stdout_named with "Hnl Hnp Hpl Hbytes Hxl Hstatus Herr HR HE");
    [exact (proj2 (proj2 Hlookup)) | exact Hstr].
Qed.
End named.
