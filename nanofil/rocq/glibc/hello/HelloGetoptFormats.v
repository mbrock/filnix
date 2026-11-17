(** When getopt reports a bad option, it prints the message through
    `c: __fxprintf_nocancel`, and that wrapper calls glibc's formatter,
    `c: __vfprintf_internal`. The diagnostic rules of
    [HelloGetoptDiagLock](HelloGetoptDiagLock.v) ask the caller for one
    premise per format, [fx_format], which says what the formatter call
    does. This module derives those premises from the formatter's
    contract [vfprintf_spec] for the nine formats that getopt uses.

    Nobody has proved the formatter yet, so this module assumes its
    contract. Once the formatter is proved, getopt's prints need no
    more work here. *)

From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Pieces Heap Logic MemLogic.
From Glibc Require Import OsWorld OsBlocks FileInv WordString PrintfStreamInv FxprintfStream NarrowFormat NarrowArgs
  PrintfSpec GetoptDiag GetoptLongDiag GetoptDiagFx HelloImageModule HelloStartKept.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** ## The formats *)

(** This function gives the bytes of a format in Hello's image, up to
    its terminating zero. *)
Definition getopt_fmt (n : string) : list Z := upto_zero (data_bytes hello_image_module n).

(** These are the names of the nine formats that getopt prints. *)
Definition getopt_fmt_names : list string :=
  ["glibc_getopt#str.138"; "glibc_getopt#str.139"; "glibc_getopt#str.140"; "glibc_getopt#str.141";
   "glibc_getopt#str.142"; "glibc_getopt#str.143"; "glibc_getopt#str.144"; "glibc_getopt#str.148";
   "glibc_getopt#str.149"]%string.

(** The tactic [narrow_args_by] proves that a list of arguments fits a
    format whose directives are known. *)
Ltac narrow_args_by :=
  repeat first
    [ apply args_end
    | apply args_literal; [reflexivity|]
    | apply args_percent
    | eapply args_conversion; [constructor; unfold promoted_int; lia|] ].

(** ## From the contract to one format *)

Section bridge.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hvf : !HasSpec registry (os_wi w0) ge (TAtom "__vfprintf_internal") vfprintf_spec}.
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).

(** Arguments that fit a format are also a valid start of the
    formatter's progress through them. *)
Lemma narrow_progress_all ds ys : narrow_args ds ys -> narrow_progress ds ys [].
Proof using Type. intros H. exists ds, [], ys. rw !app_nil_r. auto. Qed.

(** A call of the formatter on a narrow or unoriented stream leaves a
    narrow stream with the same flags and lock count. The resource R
    must lend errno, the format, the formatter's tables and the string
    arguments, and it must turn errno and the format back into the
    caller's result resource. *)
Lemma fx_rule_of_vfprintf vb fp fmt bytes ds ys mode flags2 held (R : iProp Σ) (Q : Z -> Z -> iProp Σ) :
  parse_narrow bytes = Some ds -> narrow_args ds ys -> mode = 0 \/ mode = 2 ^ 32 - 1 ->
  (R ⊢ ∃ dq, errno_any eb ∗ word_string dq fmt bytes ∗ printf_ro ∗ ([∗ list] a ∈ ys, str_arg a) ∗
       (∀ x, errno_any eb -∗ word_string dq fmt bytes -∗ Q x (2 ^ 32 - 1))) ->
  fx_vfprintf_rule_at vb fp fmt (WPtr fp :: WPtr fmt :: ys) mode flags2 held R Q.
Proof using Herr Hvf.
  intros Hp Ha Hm HR f e ls l d args rest j ap Φ Hargs.
  iIntros "Hs HR Hva HK". iDestruct (HR with "HR") as (dq) "(He & Hf & #Hro & Hys & HQ)".
  iApply (wp_call_spec registry (os_wi w0) ge _ vfprintf_spec
    (VfpIn vb fp mode (Z.lor flags2 2) (Some (fx_cnt held)) fmt dq bytes ds ap 16 (WPtr fp :: WPtr fmt :: ys) [] eb)
    with "[Hs Hf Hva Hys He]"); [exact Hargs| |].
  - cbn [fs_pre vfprintf_spec vi_vb vi_fp vi_mode vi_flags2 vi_held vi_fmt vi_dq vi_bytes vi_ds vi_ap vi_skip vi_xs vi_rest vi_eb].
    change (skipn (Z.to_nat (16 / 8)) (WPtr fp :: WPtr fmt :: ys)) with ys.
    iFrame "Hs Hf Hys He Hro". iSplit; [iPureIntro; split_and!; [exact Hp | exact (narrow_fits_all _ _ Ha) | lia | reflexivity | exact Herr]|].
    iExact "Hva".
  - iIntros (v). cbn [fs_post vfprintf_spec vi_vb vi_fp vi_mode vi_flags2 vi_held vi_fmt vi_dq vi_bytes vi_eb].
    iIntros "(%n & [-> %Hn] & Hs & Hf & He)". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
    cbn. rewrite (Z.mod_small n); [|lia]. rewrite (narrow_mode_stays mode Hm).
    iApply ("HK" with "Hs"). iApply ("HQ" with "He Hf").
Qed.

(** A read-only string is a valid string argument. *)
Lemma str_arg_of_string p s : word_string DfracDiscarded p s ⊢ str_arg (WPtr p).
Proof using Type.
  iIntros "Hs". iRight. iExists p, s, 0%nat. iFrame "Hs". iPureIntro. split; [|lia].
  destruct p as [a c]. unfold ptr_add. cbn. rewrite Z.add_0_r. reflexivity.
Qed.

(** ## The nine formats *)

(** Every diagnostic prints to standard error, here the stream fp. A
    print borrows errno and the caller's other resources F. Afterwards
    the caller must rebuild what it promised, Q, from errno and F. *)
Context (vb : Z) (fp : ptr) (F : iProp Σ) (Q : Z -> Z -> iProp Σ).

(** The natural result resource says that the stream stays narrow and
    gives back errno and F. It meets both the hypothesis below and the
    promise [dgx_qe] that the diagnostic rules ask of Q. *)
Definition getopt_q (x m : Z) : iProp Σ := ⌜m = 0 \/ m = 2 ^ 32 - 1⌝ ∗ errno_any eb ∗ F.

Lemma getopt_q_narrow x : errno_any eb ∗ F ⊢ getopt_q x (2 ^ 32 - 1).
Proof using Type. iIntros "[He HF]". iFrame. iPureIntro. right. reflexivity. Qed.

Context (HQ : forall x, errno_any eb ∗ F ⊢ Q x (2 ^ 32 - 1)).

(** F lends each format string, with the formatter's tables, for the
    length of one print. *)
Context (Hws : forall n mid, In n getopt_fmt_names -> lookup (TAtom n) (ge_globals ge) = Some mid ->
  F ⊢ ∃ dq, word_string dq mid (getopt_fmt n) ∗ printf_ro ∗ (word_string dq mid (getopt_fmt n) -∗ F)).

(** A print is safe when its arguments fit the format and the caller
    can show their strings. The resource W holds those strings. *)
Lemma fx_format_named n mid ds ys (W : iProp Σ) :
  In n getopt_fmt_names -> lookup (TAtom n) (ge_globals ge) = Some mid ->
  parse_narrow (getopt_fmt n) = Some ds -> narrow_args ds ys -> (W ⊢ [∗ list] a ∈ ys, str_arg a) ->
  fx_format vb fp mid ys ((errno_any eb ∗ F) ∗ W) Q.
Proof using Herr Hvf HQ Hws.
  intros Hin Hl Hp Ha HW mode flags2 held Hm. apply (fx_rule_of_vfprintf _ _ _ (getopt_fmt n) ds); [exact Hp | exact Ha | exact Hm |].
  iIntros "[[He HF] HW]". iDestruct (Hws n mid Hin Hl with "HF") as (dq) "(Hf & #Hro & HF)".
  iDestruct (HW with "HW") as "Hys". iExists dq. iFrame "He Hf Hro Hys". iIntros (x) "He Hf".
  iApply HQ. iFrame "He". iApply ("HF" with "Hf").
Qed.

(** The short-option diagnostics print the program name and the
    option character. *)
Lemma getopt_diag_formats mid a0 s0 c :
  diag_msg ge mid -> 0 <= c < 2 ^ 32 ->
  fx_format vb fp mid [WPtr a0; WInt c] ((errno_any eb ∗ F) ∗ word_string DfracDiscarded a0 s0) Q.
Proof using Herr Hvf HQ Hws.
  intros Hm Hc. assert (HW : word_string DfracDiscarded a0 s0 ⊢ [∗ list] a ∈ [WPtr a0; WInt c], str_arg a).
  { iIntros "Hs". cbn. iSplitL; [iApply (str_arg_of_string with "Hs") | done]. }
  destruct Hm as [Hl | Hl].
  - eapply (fx_format_named "glibc_getopt#str.148"); [cbn; tauto | exact Hl | vm_compute; reflexivity | narrow_args_by | exact HW].
  - eapply (fx_format_named "glibc_getopt#str.149"); [cbn; tauto | exact Hl | vm_compute; reflexivity | narrow_args_by | exact HW].
Qed.

(** The long-option diagnostics print the program name, the prefix and
    the option's name. *)
Lemma getopt_ldiag_formats mid a0 s0 pfx sp nm sn :
  ldiag_msg ge mid ->
  fx_format vb fp mid [WPtr a0; WPtr pfx; WPtr nm]
    ((errno_any eb ∗ F) ∗ (word_string DfracDiscarded a0 s0 ∗ word_string DfracDiscarded pfx sp ∗
      word_string DfracDiscarded nm sn)) Q.
Proof using Herr Hvf HQ Hws.
  intros Hm. assert (HW : word_string DfracDiscarded a0 s0 ∗ word_string DfracDiscarded pfx sp ∗
      word_string DfracDiscarded nm sn ⊢ [∗ list] a ∈ [WPtr a0; WPtr pfx; WPtr nm], str_arg a).
  { iIntros "(H1 & H2 & H3)". cbn. iSplitL "H1"; [iApply (str_arg_of_string with "H1")|].
    iSplitL "H2"; [iApply (str_arg_of_string with "H2")|]. iSplitL; [iApply (str_arg_of_string with "H3") | done]. }
  apply List.Exists_exists in Hm as (n & Hin & Hl). cbn in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]].
  all: refine (fx_format_named _ _ _ _ _ _ Hl _ _ HW); [cbn; tauto | vm_compute; reflexivity | narrow_args_by].
Qed.

(** One long-option diagnostic ends with a list of the options that
    match, and str.140 prints each of them as a prefix and a name. *)
Lemma getopt_f140_format f140 pfx sp nm sn :
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  fx_format vb fp f140 [WPtr pfx; WPtr nm]
    ((errno_any eb ∗ F) ∗ (word_string DfracDiscarded pfx sp ∗ word_string DfracDiscarded nm sn)) Q.
Proof using Herr Hvf HQ Hws.
  intros Hl. eapply (fx_format_named "glibc_getopt#str.140"); [cbn; tauto | exact Hl | vm_compute; reflexivity | narrow_args_by |].
  iIntros "(H1 & H2)". cbn. iSplitL "H1"; [iApply (str_arg_of_string with "H1")|].
  iSplitL; [iApply (str_arg_of_string with "H2") | done].
Qed.

(** The list ends with a newline, which str.141 prints. *)
Lemma getopt_f141_format f141 :
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  fx_format vb fp f141 [] ((errno_any eb ∗ F) ∗ True) Q.
Proof using Herr Hvf HQ Hws.
  intros Hl. eapply (fx_format_named "glibc_getopt#str.141"); [cbn; tauto | exact Hl | vm_compute; reflexivity | narrow_args_by |].
  iIntros "_". done.
Qed.

End bridge.
