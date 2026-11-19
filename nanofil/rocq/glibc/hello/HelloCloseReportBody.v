(** Error prints the caller's message before it looks up the error
    number. If the print fails, it reads the current errno, not the
    number the caller passed. On ENOMEM it also reads the stream
    mode. Hello's idle stderr is never wide, so all three paths reach
    the report counter without a second print. *)

From Glibc Require Import Unit_misc_error_os Unit_stdioZ2dcommon_fxprintf_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine ExternalCalls
  ExternalMachine Pieces StepRules Heap Language Logic MemLogic VariadicLogic.
From Glibc Require Import HelloBodies.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv FileIdle LibioLogic LibioCloseSteps SysWrappers
  WordString NarrowArgs NarrowFormat PrintfSpec AllocRo LibioFputsSpec
  ErrorEntry HelloErrorOpen HelloErrorOperand HelloVfxprintfIdle HelloCloseErrno Fix.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic LibioCloseSteps SysWrappers.
Open Scope Z_scope.

Section message.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hvf : !HasSpec registry (os_wi w0) ge (TAtom "__vfprintf_internal") vfprintf_spec}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The caller's cursor holds just the pointer to “write error” after
    the three named arguments. Printing may change errno. The next
    block still has the original error number in its locals. *)
Lemma wp_report_body eb (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb)))
    (Hgerr : lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)))
    (Hreg : holds_os registry) (Hext : sys_external ge) vb sb sreg fe e from k fmt text ap cb Φ :
  find_fn ge (TAtom "__vfxprintf") = Some (Defined Unit_stdioZ2dcommon_fxprintf_os.fn___vfxprintf) ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr sb (Obj sb)) ->
  0 < sb -> sb mod 8 = 0 -> sb+8 <= r_end sreg -> r_end sreg <= 2^63 ->
  0 < ptr_addr (ow_self w0) < 2^64 -> In 2 (ow_fds w0) -> error_inputs e 0 k fmt ap 0 cb ->
  let St := file_idle vb (ow_self w0) (mkPtr fe (Obj fe)) 2 in
  liveq DfracDiscarded sb sreg -∗ pcellq DfracDiscarded sb 0 (mkPtr fe (Obj fe)) -∗
  word_string DfracDiscarded fmt [37;115] -∗ str_arg (WPtr text) -∗
  printf_ro -∗ fputs_ro vb -∗ malloc_ro -∗ va_at ap 24 [WInt 0;WInt k;WPtr fmt;WPtr text] -∗ St -∗ errno_any eb -∗
  (∀ e' pred, ⌜error_inputs e' 0 k fmt ap 0 cb⌝ -∗ St -∗ errno_any eb -∗
    WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e' [] None (Enter (TAtom "iw_2.L19") (Some pred))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e [] None (Enter (TAtom "iw_2.start") (Some from))) : gexpr) {{ Φ }}.
Proof using Hvf.
  intros Hvfx Hs Hsb Hsa Hse Hsr Hself Hfd Hin St. iIntros "#Hsl #Hsp #Hfmt Htext #Hp #Hf #Hm Hva Herr He HK".
  destruct Hin as (Hst & Hen & Hfm & Hap & Hmo & Hsv & Hchk).
  iDestruct (file_idle_open with "Herr") as (freg md (Hfe0 & Hfea & Hfee & Hfer & Hmd)) "(Hfl & Hmc & W)".
  iApply (wp_live_fit with "Hsl"). iIntros ([Hs0 Hs48]) "_".
  step. step. check_persistent "Hsl".
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ sb sreg 0 (mkPtr fe (Obj fe)) freg
    DfracDiscarded DfracDiscarded (DfracOwn 1) with "Hsl Hsp [Hfl]");
    [reflexivity|vx|left; reflexivity|cbn; unfold raw_address; rewrite !Z.add_0_r; apply Z.mod_small; lia|
     rewrite Z.add_0_r; exact Hsa|cbn [ptr_addr]; lia|iExact "Hfl"|].
  iNext. iIntros "_ _ Hfl". iDestruct ("W" with "Hfl Hmc") as "Herr".
  iDestruct (ws_life with "Hfmt") as (r) "[#Hcap %Haddr]".
  iApply wp_call_bind; [vx|exact Hvfx|reflexivity|]. iNext.
  iApply (wp_vfxprintf_idle eb Herr Hgerr Hreg Hext ltac:(lia) ltac:(lia) vb 2 fe fmt r [37;115] [FmtStr] ap 24
    [WInt 0;WInt k;WPtr fmt;WPtr text] with "Herr Hcap Hfmt Hva [Htext] He Hp Hf Hm");
    [reflexivity|apply narrow_fits_all; eapply args_conversion; constructor|lia|reflexivity|exact Hfd|exact Haddr| |].
  { iSplitL "Htext"; [iExact "Htext"|done]. }
  iNext. iIntros (n) "Herr He _". resume. step.
  destruct (Z_le_dec (2^31) ((n mod 2^32) mod 2^32)) as [Hneg|Hpos]; cycle 1.
  { assert (Hlo : 0 <= (n mod 2^32) mod 2^32 < 2^31) by (pose proof (Z.mod_pos_bound (n mod 2^32) (2^32) ltac:(lia)); lia).
    branch_as true. step. branch. step. branch. iApply ("HK" with "[%] Herr He"). unfold error_inputs. repeat split; lk_prove. }
  branch_as false. step. step. iApply (wp_close_errno_check eb Herr); [vx|]. iNext.
  iDestruct "He" as (bs cs [Hbl Hcsl]) "Hpts". rewrite pts_app. iDestruct "Hpts" as "[Hbs Hax]".
  iApply (wp_close_errno_load eb Herr with "[Hbs]"); [vx|exact Hbl|iExact "Hbs"|]. iNext. iIntros "Hbs".
  step. step. iAssert (errno_any eb) with "[Hbs Hax]" as "He".
  { iExists bs, cs. iSplit; [done|]. rewrite pts_app. iFrame. }
  destruct (close_w bs mod 2^32 =? 12 mod 2^32) eqn:H12; cycle 1.
  { step. branch. step. branch. iApply ("HK" with "[%] Herr He"). unfold error_inputs. repeat split; lk_prove. }
  step. branch.
  iDestruct (file_idle_open with "Herr") as (fr md2 (Hfb & Hfa & Hfe & Hfr & Hmd2)) "(Hfl & Hmc & W)".
  step. step. check_persistent "Hsl".
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ sb sreg 0 (mkPtr fe (Obj fe)) fr
    DfracDiscarded DfracDiscarded (DfracOwn 1) with "Hsl Hsp [Hfl]");
    [reflexivity|vx|left; reflexivity|cbn; unfold raw_address; rewrite !Z.add_0_r; apply Z.mod_small; lia|
     rewrite Z.add_0_r; exact Hsa|cbn [ptr_addr]; lia|iExact "Hfl"|].
  iNext. iIntros "_ _ Hfl". step. iApply (wp_live_fit with "Hfl"). iIntros ([Hf0 Hf48]) "Hfl".
  check_read_dq "Hfl" by a2. iNext. iIntros "Hfl". iDestruct "Hmc" as "[%Hmr Hmb]". load_s32 "Hfl" "Hmb". step. step. step.
  destruct Hmd2 as [-> | ->]; branch_as true;
    iDestruct ("W" with "Hfl [Hmb]") as "Herr"; [iSplit; [done|iExact "Hmb"] | | iSplit; [done|iExact "Hmb"]|];
    iApply ("HK" with "[%] Herr He"); unfold error_inputs; repeat split; lk_prove.
Qed.
End message.
