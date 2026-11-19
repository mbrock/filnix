(** Hello reports an extra operand with glibc's `c: error` while
    stdout and stderr are both open and idle. This module proves that
    report over the image's code. The call flushes stdout, prints the
    program name, the message and a newline to stderr, flushes stderr
    and gives both streams back idle.

    Error reads the stream pointers itself before it hands each stream
    to a print or a flush. Reading a pointer needs the stream object to
    be alive. The caller holds each stream as idle, so the proof briefly
    takes the object's lifetime out of that idle state for the read and
    puts it back before the call. *)

From Glibc Require Import PrintfTables Unit_misc_error_os Unit_nptl_pthread_setcancelstate_os
  Unit_stdioZ2dcommon_fxprintf_os GlibcProgram GlibcSpec GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic VariadicLogic.
From Glibc Require Import HelloBodies.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysWrappers FileInv FileIdle LibioLogic LibioCloseSteps
  WordString NarrowFormat NarrowArgs PrintfSpec AllocRo LibioFputsSpec LibioFflushSpec
  FxprintfNormalCall ErrorCall ErrorEntry
  ErrorText ErrorTail HelloErrorCall HelloCloseErrno HelloVfxprintfIdle
  HelloErrorOpen Fix.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section operand.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hvf : !HasSpec registry (os_wi w0) ge (TAtom "__vfprintf_internal") vfprintf_spec}.
Context `{Hff : !HasSpec registry (os_wi w0) ge (TAtom "__GI__IO_fflush") fflush_spec}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** ## Small facts

    The proof below lends read-only strings and the argument cursor to
    the printing calls. These facts turn what the caller holds into the
    forms those calls ask for. *)

(** A read-only string carries a persistent share of its object's
    lifetime, and its address is a machine word. *)
Lemma ws_life p s :
  word_string DfracDiscarded p s ⊢ ∃ reg, live_capq DfracDiscarded (ptr_cap p) reg ∗ ⌜0 <= ptr_addr p < 2 ^ 64⌝.
Proof using Type.
  iIntros "(%b & %reg & %ws & %Hsh & Hlv & _)".
  pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)).
  pose proof (ss_base _ _ _ _ _ Hsh). pose proof (ss_start _ _ _ _ _ Hsh).
  pose proof (ss_fit _ _ _ _ _ Hsh). pose proof (ss_space _ _ _ _ _ Hsh). unfold wstart in *.
  iExists reg. iSplit; [|iPureIntro; lia].
  destruct (ss_cap _ _ _ _ _ Hsh) as [-> | ->]; cbn; iExact "Hlv".
Qed.

(** A read-only string is a valid string argument. *)
Lemma ws_arg p bs : word_string DfracDiscarded p bs ⊢ str_arg (WPtr p).
Proof using Type.
  iIntros "Hs". iRight. iExists p, bs, 0%nat. iFrame "Hs". iPureIntro. split; [|lia].
  destruct p as [a c]. unfold ptr_add. cbn. rewrite Z.add_0_r. reflexivity.
Qed.

(** The wrapper `c: error` leaves its cursor 24 bytes into the
    snapshot, past the status, the error number and the format. That
    cursor is the formatter's argument cursor at offset 24. *)
Lemma error_va_at ap xs : (3 <= length xs)%nat -> error_va ap xs -∗ va_at ap 24 xs.
Proof using Type.
  intros Hl. iIntros "H". iDestruct "H" as (cb sb Hp) "[Hc Hs]".
  iExists cb, sb. iFrame. iPureIntro. destruct Hp as (? & ? & ? & ? & ? & ? & ?). split_and!; auto; lia.
Qed.

(** To read a stream pointer, error needs the stream object to be
    alive. An idle stream can lend that lifetime for the read and take
    it back afterwards. *)
Lemma file_idle_lend vb fb fd :
  file_idle vb (ow_self w0) (mkPtr fb (Obj fb)) fd ⊢
  ∃ dq reg, live_capq dq (ptr_cap (mkPtr fb (Obj fb))) reg ∗
    (live_capq dq (ptr_cap (mkPtr fb (Obj fb))) reg -∗ file_idle vb (ow_self w0) (mkPtr fb (Obj fb)) fd).
Proof using Type.
  iIntros "H". iDestruct (file_idle_open with "H") as (freg md _) "(Hl & Hmd & W)".
  iExists (DfracOwn 1), freg. cbn. iFrame "Hl". iIntros "Hl". iApply ("W" with "Hl Hmd").
Qed.

(** The formatter and the flush read errno through the global
    `c: __libc_errno`, which must be the thread's errno cell, and the
    stream functions check that the thread has an identity. *)
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb)))
  (Hgerr : lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb))).
Context (Hregistry : holds_os registry) (Hext : sys_external ge)
  (Hself : ptr_addr (ow_self w0) <> 0) (Hselfr : 0 <= ptr_addr (ow_self w0) < 2 ^ 64).

(** The format grammar accepts the arguments of each print. *)
Ltac nargs := repeat first [apply args_end | apply args_literal; [reflexivity|] | apply args_percent |
  eapply args_conversion; [constructor|] ].

(** ## The report

    The internal function `c: __error_internal` runs the whole report.
    Hello calls it with status 0 and error number 0, and with the
    program-name callback left null. The lemma below follows the code
    from the cancellation switch to the restore at the end. *)

(** The read-only strings and tables that the printing calls read are
    persistent, so the proof hands them to each call as one bundle. *)
Definition op_ro vb sb sreg fe prefix newline pname pbytes fmt fbytes : iProp Σ :=
  fputs_ro vb ∗ printf_ro ∗ malloc_ro ∗
  liveq DfracDiscarded sb sreg ∗ pcellq DfracDiscarded sb 0 (mkPtr fe (Obj fe)) ∗
  word_string DfracDiscarded prefix [37; 115; 58; 32] ∗ word_string DfracDiscarded newline [10] ∗
  word_string DfracDiscarded pname pbytes ∗ word_string DfracDiscarded fmt fbytes.

Global Instance op_ro_persistent vb sb sreg fe prefix newline pname pbytes fmt fbytes :
  Persistent (op_ro vb sb sreg fe prefix newline pname pbytes fmt fbytes).
Proof using Type. rewrite /op_ro /liveq /pcellq. apply _. Qed.

(** A report with status 0 and error number 0 prints the program name,
    the message and a newline to stderr, and flushes both streams. It
    gives both streams back idle, counts one more report, and restores
    the thread's cancellation state. *)
Lemma wp_error_internal_operand vb ob oreg fo sb sreg fe pb preg nb nreg pname pbytes
    prefix newline wide widefn wideframe fmt fbytes ds ys cnb cnreg count ap Φ :
  find_fn ge (TAtom "__GI___pthread_setcancelstate") = Some (Defined Unit_nptl_pthread_setcancelstate_os.fn___GI___pthread_setcancelstate) ->
  find_fn ge (TAtom "__fxprintf") = Some (Defined Unit_stdioZ2dcommon_fxprintf_os.fn___fxprintf) ->
  find_fn ge (TAtom "__vfxprintf") = Some (Defined Unit_stdioZ2dcommon_fxprintf_os.fn___vfxprintf) ->
  lookup (TAtom "stdout") (ge_globals ge) = Some (mkPtr ob (Obj ob)) ->
  0 < ob -> ob mod 8 = 0 -> ob + 8 <= r_end oreg -> r_end oreg <= 2 ^ 63 ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr sb (Obj sb)) ->
  0 < sb -> sb mod 8 = 0 -> sb + 8 <= r_end sreg -> r_end sreg <= 2 ^ 63 ->
  lookup (TAtom "error_print_progname") (ge_globals ge) = Some (mkPtr pb (Obj pb)) ->
  0 < pb -> pb mod 8 = 0 -> pb + 8 <= r_end preg -> r_end preg <= 2 ^ 63 ->
  lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (mkPtr nb (Obj nb)) ->
  0 < nb -> nb mod 8 = 0 -> nb + 8 <= r_end nreg -> r_end nreg <= 2 ^ 63 ->
  lookup (TAtom "glibc_error#str.255") (ge_globals ge) = Some prefix ->
  lookup (TAtom "glibc_error#str.254") (ge_globals ge) = Some newline ->
  lookup (TAtom "glibc_error#str.253") (ge_globals ge) = Some wide ->
  find_fn ge (TAtom "__GI_fputws_unlocked") = Some (Defined widefn) ->
  call_frame widefn [WPtr wide; WPtr (mkPtr fe (Obj fe))] = Some wideframe ->
  lookup (TAtom "error_message_count") (ge_globals ge) = Some (mkPtr cnb (Obj cnb)) ->
  0 < cnb -> cnb + 4 <= r_end cnreg -> r_end cnreg <= 2 ^ 63 ->
  In 1 (ow_fds w0) -> In 2 (ow_fds w0) ->
  parse_narrow fbytes = Some ds -> narrow_fits ds ys [] ->
  liveq DfracDiscarded ob oreg -∗ pcellq DfracDiscarded ob 0 (mkPtr fo (Obj fo)) -∗
  file_idle vb (ow_self w0) (mkPtr fo (Obj fo)) 1 -∗
  file_idle vb (ow_self w0) (mkPtr fe (Obj fe)) 2 -∗
  liveq DfracDiscarded pb preg -∗ pcellq DfracDiscarded pb 0 null -∗
  live nb nreg -∗ pcell nb 0 pname -∗
  op_ro vb sb sreg fe prefix newline pname pbytes fmt fbytes -∗
  ([∗ list] a ∈ ys, str_arg a) -∗ va_at ap 24 (WInt 0 :: WInt 0 :: WPtr fmt :: ys) -∗
  tcb_cleanup_inv (ow_self w0) -∗ errno_any eb -∗ live cnb cnreg -∗ int_cell cnb 0 count -∗
  (file_idle vb (ow_self w0) (mkPtr fo (Obj fo)) 1 -∗ file_idle vb (ow_self w0) (mkPtr fe (Obj fe)) 2 -∗
    live nb nreg -∗ pcell nb 0 pname -∗ tcb_cleanup_inv (ow_self w0) -∗ errno_any eb -∗
    live cnb cnreg -∗ int_cell cnb 0 ((count + 1) mod 2 ^ 32) -∗ Φ RetVoid) -∗
  WP (ERun (error_internal_frame 0 0 fmt ap 0) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hcancel Hfx Hvfx Ho Hob Hoa Hoe Hor Hs Hsb Hsa Hse Hsr Hp Hpb Hpa Hpe Hpr Hn Hnb Hna Hne Hnr
    Hprefix Hnewline Hwide Hwidefn Hwideframe Hc Hcb Hce Hcr Hfd1 Hfd2 Hparse Hfits.
  iIntros "#Hol #Hop Hout Herr #Hpl #Hpp Hnl Hnp #Hro Hys Hva Htcb He Hcl Hcnt HK".
  iPoseProof "Hro" as "(#Hfro & #Hpro & #Hmro & #Hsl & #Hsp & #Hpre & #Hnew & #Hname & #Hfmt)".
  iDestruct (error_cleanup_exchange with "Htcb") as (tb treg jb Hth) "(Ht & Hflag & Hcf)".
  destruct Hth as (Hselftb & Htb & Hta & Hte & Htr).
  iDestruct (ws_life with "Hname") as (namer) "[#Hnamecap %Hpn]".
  iDestruct (file_idle_open with "Hout") as (foreg fomd (Hfo0 & _ & Hfoe & Hfor & _)) "(Hofl & Homd & Wo)".
  iDestruct ("Wo" with "Hofl Homd") as "Hout".
  destruct (Hff (FflushIn vb (mkPtr fo (Obj fo)) 1 eb)) as (gf & Hgf & [ffo Hffo] & Hfto).
  iApply (wp_error_internal_entry_lend Hregistry Hext (dqs := DfracDiscarded) (dqp := DfracDiscarded) 0 0 fmt ap 0 tb treg 0
    ob oreg (mkPtr fo (Obj fo)) (file_idle vb (ow_self w0) (mkPtr fo (Obj fo)) 1)
    pb preg null DfracDiscarded (mkRegion 0 0 Heap Live) nb nreg pname DfracDiscarded namer prefix
    gf ffo Unit_stdioZ2dcommon_fxprintf_os.fn___fxprintf (fxprintf_normal_frame null prefix [WPtr pname]) (TAtom "error") Unit_misc_error_os.fn___error ffo
    (errno_any eb ∗ file_idle vb (ow_self w0) (mkPtr fe (Obj fe)) 2 ∗ op_ro vb sb sreg fe prefix newline pname pbytes fmt fbytes)%I
    (errno_any eb ∗ file_idle vb (ow_self w0) (mkPtr fe (Obj fe)) 2 ∗ op_ro vb sb sreg fe prefix newline pname pbytes fmt fbytes)%I
    (errno_any eb ∗ file_idle vb (ow_self w0) (mkPtr fe (Obj fe)) 2)%I
    (([∗ list] a ∈ ys, str_arg a) ∗ va_at ap 24 (WInt 0 :: WInt 0 :: WPtr fmt :: ys) ∗
     error_cleanup_fields tb jb ∗ live cnb cnreg ∗ int_cell cnb 0 count)%I
    with "Ht Hflag Hol Hop Hout Hpl Hpp [] Hnl Hnp Hnamecap [$He $Herr $Hro] [$Hys $Hva $Hcf $Hcl $Hcnt]").
  all: try (intros Hz; exfalso; apply Hz; reflexivity).
  all: try (cbn; lia).
  all: try assumption.
  all: try exact (fxprintf_normal_call_frame _ _ _).
  all: try (iApply file_idle_lend).
  { iIntros "HO (He & Herr & #Hro2)". iPoseProof "Hro2" as "(#Hfro2 & _)".
    iApply (Hfto ffo with "[HO He]"); [exact Hffo | |].
    - cbn [fs_pre fflush_spec ff_vb ff_fp ff_fd ff_eb]. iSplit; [iPureIntro; split; [exact Herr | exact Hfd1]|].
      iFrame "HO He Hfro2".
    - iIntros (v) "(%r & [-> _] & HO & He)". iExists r. iSplit; [done|]. iFrame "HO He Herr Hro2". }
  { iIntros "Hcap (He & Herr & #Hro2)".
    iPoseProof "Hro2" as "(#Hfro2 & #Hpro2 & #Hmro2 & #Hsl2 & #Hsp2 & #Hpre2 & _ & #Hname2 & _)".
    iDestruct (ws_life with "Hpre2") as (prer) "[#Hprecap %Hprer]".
    iApply (wp_fxprintf_idle_null eb Herr Hgerr Hregistry Hext Hself Hselfr vb 2 fe sb sreg prefix prer
      [37;115;58;32] _ [WPtr pname]
      with "Hsl2 Hsp2 Herr Hprecap Hpre2 [] He Hpro2 Hfro2 Hmro2 [Hcap]");
      [exact Hvfx | reflexivity | vm_compute; reflexivity | apply narrow_fits_all; nargs | exact Hfd2 |
       exact Hprer | exact Hs | exact Hsb | exact Hsa | exact Hse | exact Hsr | | ].
    - cbn [big_opL]. iSplit; [iApply ws_arg; iExact "Hname2" | done].
    - iNext. iIntros (n) "Herr He _". iExists _. iSplit; [done|]. iFrame "Hcap He Herr". }
  { cbn. done. }
  iIntros (e from cb Hinputs) "Ht Hflag Hcbl Hsaved _ _ Hout _ _ _ Hnl Hnp _ [He Herr] (Hys & Hva & Hcf & Hcl & Hcnt)".
  iDestruct (file_idle_open with "Herr") as (freg md (Hfe0 & Hfea & Hfee & Hfer & Hmd)) "(Hfl & Hmdc & W)".
  destruct Hinputs as (Hst & Hen & Hfm & Hap & Hmo & Hsv & Hchk).
  iApply (wp_live_fit with "Hsl"). iIntros ([Hs0 Hs48]) "_".
  step. step. check_persistent "Hsl".
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ sb sreg 0 (mkPtr fe (Obj fe)) freg
            DfracDiscarded DfracDiscarded (DfracOwn 1) with "Hsl Hsp [Hfl]");
    [reflexivity | vx | left; reflexivity |
     cbn; unfold raw_address; rewrite !Z.add_0_r; apply Z.mod_small; lia | rewrite Z.add_0_r; exact Hsa |
     cbn [ptr_addr]; lia | iExact "Hfl" |].
  iNext. iIntros "_ _ Hfl". iDestruct ("W" with "Hfl Hmdc") as "Herr".
  iDestruct (ws_life with "Hfmt") as (fmtr) "[#Hfmtcap %Hfmtr]".
  iApply wp_call_bind; [vx | exact Hvfx | reflexivity |]. iNext.
  iApply (wp_vfxprintf_idle eb Herr Hgerr Hregistry Hext Hself Hselfr vb 2 fe fmt fmtr fbytes ds ap 24
      (WInt 0 :: WInt 0 :: WPtr fmt :: ys) with "Herr Hfmtcap Hfmt Hva [Hys] He Hpro Hfro Hmro");
    [exact Hparse | exact Hfits | lia | reflexivity | exact Hfd2 | exact Hfmtr | iExact "Hys" |].
  iNext. iIntros (n) "Herr He _". resume. step.
  iAssert (∀ e2 pred, ⌜error_inputs e2 0 0 fmt ap 0 cb⌝ -∗ file_idle vb (ow_self w0) (mkPtr fe (Obj fe)) 2 -∗
    errno_any eb -∗
    WP (ERun (mkFrame Unit_misc_error_os.fn___error_internal e2 [] None (Enter (TAtom "iw_2.L19") (Some pred))) : gexpr) {{ Φ }})%I
    with "[Ht Hflag Hcbl Hsaved Hout Hnl Hnp Hcf Hcl Hcnt HK]" as "HL19".
  { iIntros (e2 pred Hin2) "Herr He".
    iApply (wp_error_count_zero e2 pred 0 fmt ap 0 cb cnb cnreg count True%I with "Hcl Hcnt [//]"); try assumption.
    iIntros (e3 pred3 Hin3) "Hcl Hcnt _".
    destruct (Hff (FflushIn vb (mkPtr fe (Obj fe)) 2 eb)) as (gf2 & Hgf2 & [ffe Hffe] & Hfte).
    iApply (wp_error_tail_lend Hregistry Hext (dqs := DfracDiscarded) tb treg 0 sb sreg (mkPtr fe (Obj fe))
      newline Unit_stdioZ2dcommon_fxprintf_os.fn___fxprintf (fxprintf_normal_frame null newline []) gf2 ffe
      (file_idle vb (ow_self w0) (mkPtr fe (Obj fe)) 2)
      (errno_any eb ∗ op_ro vb sb sreg fe prefix newline pname pbytes fmt fbytes)%I
      (errno_any eb ∗ op_ro vb sb sreg fe prefix newline pname pbytes fmt fbytes)%I (errno_any eb)%I True%I
      e3 pred3 0 0 fmt ap 0 cb
      with "Ht Hflag Hcbl Hsaved Hsl Hsp Herr [$He $Hro] [//]").
    all: try (left; reflexivity).
    all: try (cbn; lia).
    all: try assumption.
    all: try exact (fxprintf_normal_call_frame _ _ _).
    all: try (iApply file_idle_lend).
    - iIntros "#Hsl2 #Hsp2 Herr [He #Hro2]".
      iPoseProof "Hro2" as "(#Hfro2 & #Hpro2 & #Hmro2 & _ & _ & _ & #Hnew2 & _)".
      iDestruct (ws_life with "Hnew2") as (nlr) "[#Hnlcap %Hnlr]".
      iApply (wp_fxprintf_idle_null eb Herr Hgerr Hregistry Hext Hself Hselfr vb 2 fe sb sreg newline nlr
        [10] _ [] with "Hsl2 Hsp2 Herr Hnlcap Hnew2 [] He Hpro2 Hfro2 Hmro2 [Hsl2]");
        [exact Hvfx | reflexivity | vm_compute; reflexivity | apply narrow_fits_all; nargs | exact Hfd2 |
         exact Hnlr | exact Hs | exact Hsb | exact Hsa | exact Hse | exact Hsr | done | ].
      iNext. iIntros (k) "Herr He _". iExists _. iSplit; [done|]. iSplitR; [iExact "Hsl2"|]. iSplitR; [iExact "Hsp2"|].
      iSplitL "Herr"; [iExact "Herr"|]. iSplitL "He"; [iExact "He" | iExact "Hro2"].
    - iIntros "HO [He #Hro2]". iPoseProof "Hro2" as "(#Hfro2 & _)".
      iApply (Hfte ffe with "[HO He]"); [exact Hffe | |].
      + cbn [fs_pre fflush_spec ff_vb ff_fp ff_fd ff_eb]. iSplit; [iPureIntro; split; [exact Herr | exact Hfd2]|].
        iFrame "HO He Hfro2".
      + iIntros (v) "(%r & [-> _] & HO & He)". iExists r. iSplit; [done|]. iFrame "HO He".
    - iSplit.
      + iIntros "Ht Hflag _ _ _ _ Herr He _".
        iApply ("HK" with "Hout Herr Hnl Hnp [Ht Hflag Hcf] He Hcl Hcnt").
        iApply error_cleanup_exchange. iExists tb, treg, jb. iFrame. iPureIntro. split_and!; assumption.
      + iIntros (e' Hnz). contradiction. }
  destruct (Z_le_dec (2 ^ 31) ((n mod 2 ^ 32) mod 2 ^ 32)) as [Hneg | Hpos]; cycle 1.
  { assert (Hpp2 : 0 <= (n mod 2 ^ 32) mod 2 ^ 32 < 2 ^ 31)
      by (pose proof (Z.mod_pos_bound (n mod 2 ^ 32) (2 ^ 32) ltac:(lia)); lia).
    branch_as true. step. branch. step. branch.
    iApply ("HL19" with "[%] Herr He"). unfold error_inputs. repeat split; lk_prove. }
  (* A negative result reads errno, which the formatter may have set to
     any value, so the proof reads it as four raw bytes. *)
  branch_as false. step. step.
  iApply (wp_close_errno_check eb Herr); [vx|]. iNext.
  iDestruct "He" as (bs cs [Hbl Hcsl]) "Hpts". rewrite pts_app. iDestruct "Hpts" as "[Hbs Hax]".
  iApply (wp_close_errno_load eb Herr with "[Hbs]"); [vx | exact Hbl | iExact "Hbs" |]. iNext. iIntros "Hbs".
  step. step.
  iAssert (errno_any eb) with "[Hbs Hax]" as "He".
  { iExists bs, cs. iSplit; [done|]. rewrite pts_app. iFrame. }
  destruct (close_w bs mod 2 ^ 32 =? 12 mod 2 ^ 32) eqn:H12; cycle 1.
  { step. branch. step. branch.
    iApply ("HL19" with "[%] Herr He"). unfold error_inputs. repeat split; lk_prove. }
  (* On ENOMEM error reads the stream's mode. An idle stream is never
     wide, so the mode is 0 or -1 and the wide fallback is skipped. *)
  step. branch.
  iDestruct (file_idle_open with "Herr") as (freg2 md2 (Hfe20 & Hfe2a & Hfe2e & Hfe2r & Hmd2)) "(Hfl & Hmdc & W)".
  step. step. check_persistent "Hsl".
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ sb sreg 0 (mkPtr fe (Obj fe)) freg2
            DfracDiscarded DfracDiscarded (DfracOwn 1) with "Hsl Hsp [Hfl]");
    [reflexivity | vx | left; reflexivity |
     cbn; unfold raw_address; rewrite !Z.add_0_r; apply Z.mod_small; lia | rewrite Z.add_0_r; exact Hsa |
     cbn [ptr_addr]; lia | iExact "Hfl" |].
  iNext. iIntros "_ _ Hfl". step.
  iApply (wp_live_fit with "Hfl"). iIntros ([Hf0 Hf48]) "Hfl".
  check_read_dq "Hfl" by a2. iNext. iIntros "Hfl".
  iDestruct "Hmdc" as "[%Hmdr Hmb]". load_s32 "Hfl" "Hmb". step. step. step.
  destruct Hmd2 as [-> | ->]; branch_as true;
    iDestruct ("W" with "Hfl [Hmb]") as "Herr"; [iSplit; [done | iExact "Hmb"] | | iSplit; [done | iExact "Hmb"] |];
    iApply ("HL19" with "[%] Herr He"); unfold error_inputs; repeat split; lk_prove.
Qed.

(** The public `c: error` snapshots its arguments and calls the internal
    function with a cursor past the first three. The report above then
    runs with that cursor. *)
Lemma wp_error_operand vb ob oreg fo sb sreg fe pb preg nb nreg pname pbytes
    prefix newline wide widefn wideframe fmt fbytes ds ys cnb cnreg count Φ :
  find_fn ge (TAtom "__error_internal") = Some (Defined Unit_misc_error_os.fn___error_internal) ->
  forallb snapshot_word ys = true ->
  find_fn ge (TAtom "__GI___pthread_setcancelstate") = Some (Defined Unit_nptl_pthread_setcancelstate_os.fn___GI___pthread_setcancelstate) ->
  find_fn ge (TAtom "__fxprintf") = Some (Defined Unit_stdioZ2dcommon_fxprintf_os.fn___fxprintf) ->
  find_fn ge (TAtom "__vfxprintf") = Some (Defined Unit_stdioZ2dcommon_fxprintf_os.fn___vfxprintf) ->
  lookup (TAtom "stdout") (ge_globals ge) = Some (mkPtr ob (Obj ob)) ->
  0 < ob -> ob mod 8 = 0 -> ob + 8 <= r_end oreg -> r_end oreg <= 2 ^ 63 ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr sb (Obj sb)) ->
  0 < sb -> sb mod 8 = 0 -> sb + 8 <= r_end sreg -> r_end sreg <= 2 ^ 63 ->
  lookup (TAtom "error_print_progname") (ge_globals ge) = Some (mkPtr pb (Obj pb)) ->
  0 < pb -> pb mod 8 = 0 -> pb + 8 <= r_end preg -> r_end preg <= 2 ^ 63 ->
  lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (mkPtr nb (Obj nb)) ->
  0 < nb -> nb mod 8 = 0 -> nb + 8 <= r_end nreg -> r_end nreg <= 2 ^ 63 ->
  lookup (TAtom "glibc_error#str.255") (ge_globals ge) = Some prefix ->
  lookup (TAtom "glibc_error#str.254") (ge_globals ge) = Some newline ->
  lookup (TAtom "glibc_error#str.253") (ge_globals ge) = Some wide ->
  find_fn ge (TAtom "__GI_fputws_unlocked") = Some (Defined widefn) ->
  call_frame widefn [WPtr wide; WPtr (mkPtr fe (Obj fe))] = Some wideframe ->
  lookup (TAtom "error_message_count") (ge_globals ge) = Some (mkPtr cnb (Obj cnb)) ->
  0 < cnb -> cnb + 4 <= r_end cnreg -> r_end cnreg <= 2 ^ 63 ->
  In 1 (ow_fds w0) -> In 2 (ow_fds w0) ->
  parse_narrow fbytes = Some ds -> narrow_fits ds ys [] ->
  liveq DfracDiscarded ob oreg -∗ pcellq DfracDiscarded ob 0 (mkPtr fo (Obj fo)) -∗
  file_idle vb (ow_self w0) (mkPtr fo (Obj fo)) 1 -∗
  file_idle vb (ow_self w0) (mkPtr fe (Obj fe)) 2 -∗
  liveq DfracDiscarded pb preg -∗ pcellq DfracDiscarded pb 0 null -∗
  live nb nreg -∗ pcell nb 0 pname -∗
  op_ro vb sb sreg fe prefix newline pname pbytes fmt fbytes -∗ ([∗ list] a ∈ ys, str_arg a) -∗
  tcb_cleanup_inv (ow_self w0) -∗ errno_any eb -∗ live cnb cnreg -∗ int_cell cnb 0 count -∗
  ▷ (file_idle vb (ow_self w0) (mkPtr fo (Obj fo)) 1 -∗ file_idle vb (ow_self w0) (mkPtr fe (Obj fe)) 2 -∗
    live nb nreg -∗ pcell nb 0 pname -∗ tcb_cleanup_inv (ow_self w0) -∗ errno_any eb -∗
    live cnb cnreg -∗ int_cell cnb 0 ((count + 1) mod 2 ^ 32) -∗ Φ RetVoid) -∗
  WP (ERun (error_frame 0 0 fmt ys) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hint Hys Hcancel Hfx Hvfx Ho Hob Hoa Hoe Hor Hs Hsb Hsa Hse Hsr Hp Hpb Hpa Hpe Hpr Hn Hnb Hna Hne Hnr
    Hprefix Hnewline Hwide Hwidefn Hwideframe Hc Hcb Hce Hcr Hfd1 Hfd2 Hparse Hfits.
  iIntros "#Hol #Hop Hout Herr #Hpl #Hpp Hnl Hnp #Hro Hys Htcb He Hcl Hcnt HK".
  iApply (wp_error_wrapper 0 0 fmt ys (fun ap => error_internal_frame 0 0 fmt ap 0)
    ((liveq DfracDiscarded ob oreg ∗ pcellq DfracDiscarded ob 0 (mkPtr fo (Obj fo)) ∗
      liveq DfracDiscarded pb preg ∗ pcellq DfracDiscarded pb 0 null ∗
      op_ro vb sb sreg fe prefix newline pname pbytes fmt fbytes) ∗
     file_idle vb (ow_self w0) (mkPtr fo (Obj fo)) 1 ∗ file_idle vb (ow_self w0) (mkPtr fe (Obj fe)) 2 ∗
     live nb nreg ∗ pcell nb 0 pname ∗ ([∗ list] a ∈ ys, str_arg a) ∗ tcb_cleanup_inv (ow_self w0) ∗
     errno_any eb ∗ live cnb cnreg ∗ int_cell cnb 0 count)%I
    (file_idle vb (ow_self w0) (mkPtr fo (Obj fo)) 1 ∗ file_idle vb (ow_self w0) (mkPtr fe (Obj fe)) 2 ∗
     live nb nreg ∗ pcell nb 0 pname ∗ tcb_cleanup_inv (ow_self w0) ∗
     errno_any eb ∗ live cnb cnreg ∗ int_cell cnb 0 ((count + 1) mod 2 ^ 32))%I emp%I
    with "[Hout Herr Hnl Hnp Hys Htcb He Hcl Hcnt] [//] [HK]");
    [exact Hys | lia | lia | exact Hint | intros; apply error_internal_call_frame | | | ].
  - intros ap. iIntros "Hva ((#Hol & #Hop & #Hpl & #Hpp & #Hro) & Hout & Herr & Hnl & Hnp & Hys & Htcb & He & Hcl & Hcnt)".
    iPoseProof (error_va_at with "Hva") as "Hva"; [cbn; lia |].
    iApply (wp_error_internal_operand vb ob oreg fo sb sreg fe pb preg nb nreg pname pbytes
      prefix newline wide widefn wideframe fmt fbytes ds ys cnb cnreg count ap _
      Hcancel Hfx Hvfx Ho Hob Hoa Hoe Hor Hs Hsb Hsa Hse Hsr Hp Hpb Hpa Hpe Hpr Hn Hnb Hna Hne Hnr
      Hprefix Hnewline Hwide Hwidefn Hwideframe Hc Hcb Hce Hcr Hfd1 Hfd2 Hparse Hfits
      with "Hol Hop Hout Herr Hpl Hpp Hnl Hnp Hro Hys Hva Htcb He Hcl Hcnt").
    iIntros "Hout Herr Hnl Hnp Htcb He Hcl Hcnt". iSplit; [done|]. iFrame "Hout Herr Hnl Hnp Htcb He Hcl Hcnt".
  - iSplitR; [iSplitR; [iExact "Hol"|]; iSplitR; [iExact "Hop"|]; iSplitR; [iExact "Hpl"|];
      iSplitR; [iExact "Hpp" | iExact "Hro"]|]. iFrame "Hout Herr Hnl Hnp Hys Htcb He Hcl Hcnt".
  - iNext. iIntros "(Hout & Herr & Hnl & Hnp & Htcb & He & Hcl & Hcnt) _".
    iApply ("HK" with "Hout Herr Hnl Hnp Htcb He Hcl Hcnt").
Qed.

End operand.
