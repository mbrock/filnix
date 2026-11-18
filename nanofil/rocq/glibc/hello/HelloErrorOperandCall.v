(** When Hello gets more operands than it accepts, main reports the
    extra one with glibc's `c: error`. The proof of main states that
    call in terms of the standard streams and read-only data it holds
    between calls. This module derives that statement from the proof of
    the image's code in [HelloErrorOperand](HelloErrorOperand.v). *)

From Glibc Require Import GlibcProgram GlibcTactics GlibcSpec LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls Pieces StepRules Heap Language Logic StringLogic MemLogic VariadicLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry WordString FileInv FileIdle LibioLogic LibioFputsSpec
  LibioFflushSpec PrintfSpec NarrowFormat NarrowArgs AllocRo FxprintfStream FxprintfNormalCall VfxprintfSelect
  PrintfStateCode FxprintfNormalCode ErrorCode ErrorCall LibioCleanupExit HelloVersionLits HelloGlibcDebts HelloGlibcLibsT HelloEmitBug HelloVersionEtc
  HelloErrorOperand.
From Glibc Require Import HelloImageModule HelloImageLoad HelloImageLayout.
From Glibc Require HelloGlibcDebts LibioLogic.
From Glibc Require Import Fix.
Import ListNotations.
Import HelloGlibcDebts HelloGlibcDebts.SW HelloGlibcDebts.SW.FI.ML HelloGlibcDebts.SW.FI.LG
  HelloGlibcDebts.SW.FI.L HelloGlibcDebts.SW.OW HelloGlibcDebts.SW.FI.
Open Scope Z_scope.

Section call.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (Hy : hello_layout ge o) (Hk : hello_link ge o).

Local Definition call_program : GlibcProgram Σ := program_of w0 glibc_os_registry ge.

(** An idle stream is a stream object whose pointer carries the
    object's own capability. *)
Lemma file_idle_obj vb self fp fd :
  file_idle vb self fp fd ⊢ ⌜∃ fb, fp = mkPtr fb (Obj fb)⌝ ∗ file_idle vb self fp fd.
Proof using Type.
  iIntros "H". iDestruct "H" as (fb freg st nb Hp) "R".
  iSplit; [iPureIntro; exists fb; apply Hp|]. iExists fb, freg, st, nb. iSplit; [done | iExact "R"].
Qed.

(** The linked program must run glibc's own `c: error` and the
    functions it calls, and give it the strings and counter it reads.
    These facts are about the linked image alone; the image's proof
    checks them by computation. *)
Record error_link (ge : genv) (o : hello_objs) : Prop := mkErrorLink {
  erl_error : find_fn ge (TAtom "error") = Some (Defined glibc_error);
  erl_internal : find_fn ge (TAtom "__error_internal") = Some (Defined glibc_error_internal);
  erl_cancel : find_fn ge (TAtom "__GI___pthread_setcancelstate") = Some (Defined glibc___pthread_setcancelstate);
  erl_fx : find_fn ge (TAtom "__fxprintf") = Some (Defined glibc_fxprintf);
  erl_vfx : find_fn ge (TAtom "__vfxprintf") = Some (Defined glibc_vfxprintf);
  erl_wide : exists wide widefn wideframe, lookup (TAtom "glibc_error#str.253") (ge_globals ge) = Some wide /\
    find_fn ge (TAtom "__GI_fputws_unlocked") = Some (Defined widefn) /\
    call_frame widefn [WPtr wide; WPtr (ho_err o)] = Some wideframe;
  erl_prefix : lookup (TAtom "glibc_error#str.255") (ge_globals ge) = Some (sym_ptr ge "glibc_error#str.255");
  erl_newline : lookup (TAtom "glibc_error#str.254") (ge_globals ge) = Some (sym_ptr ge "glibc_error#str.254");
  erl_pos : 0 < ho_so o /\ 0 < ho_se o /\ 0 < ho_nb o;
  erl_progname : forall pb, lookup (TAtom "error_print_progname") (ge_globals ge) = Some (mkPtr pb (Obj pb)) -> 0 < pb;
  erl_count : forall cb, lookup (TAtom "error_message_count") (ge_globals ge) = Some (mkPtr cb (Obj cb)) -> 0 < cb
}.

Context (El : error_link ge o) (Hos : hello_os_layout w0 o).
Context (Herr : ow_errno w0 = Some (mkPtr (ho_eb o) (Obj (ho_eb o)))) (Hfd1 : In 1 (ow_fds w0)) (Hfd2 : In 2 (ow_fds w0)).
Context `{Hvf : !HasSpec glibc_os_registry (os_wi w0) ge (TAtom "__vfprintf_internal") (vfprintf_spec (glibc_program := call_program))}.
Context `{Hff : !HasSpec glibc_os_registry (os_wi w0) ge (TAtom "__GI__IO_fflush") (fflush_spec (glibc_program := call_program))}.

Local Ltac lit_in := cbn [version_lits]; repeat (first [left; reflexivity | right]).
Local Ltac nargs := repeat first [apply args_end | apply args_literal; [reflexivity|] | apply args_percent |
  eapply args_conversion; [constructor|] ].

(** The call `c: error (0, 0, "%s: %s", "extra operand", q)` keeps the
    standard streams, the program-name cells and any state P of the
    caller. *)
Lemma error_operand_hello (P : iProp Σ) q :
  fn_triple w0 ge (TAtom "error")
    [WInt 0; WInt 0; WPtr (sym_ptr ge "hello#str.77"); WPtr (sym_ptr ge "hello#str.78"); WPtr q]
    (hello_ro ge o ∗ hello_stdio w0 ge o ∗ P ∗ names o ∗ str_arg (WPtr q))%I
    (fun r => ⌜r = RetVoid⌝ ∗ hello_stdio w0 ge o ∗ P ∗ names o)%I.
Proof using Type*.
  destruct El as [Hfe1 Hfi Hfc Hfx Hfv (wide & widefn & wideframe & Hw1 & Hw2 & Hw3) Hpre Hnew (Hso0 & Hse0 & Hnb0)
    Hpbpos Hcbpos].
  exists glibc_error. split; [exact Hfe1|]. split; [eexists; apply error_call_frame|].
  intros fr Φ Hfr. rewrite error_call_frame in Hfr. injection Hfr as <-.
  iIntros "(#Hro & (Hout & Herr & Hin & Hio & Htcb & He & Hec) & HP & Hnames & #Hq) HK".
  iDestruct "Hnames" as (x y z) "((Hpl & Hpp & Hnl & Hnp & Hsl & Hsp) & Hx & #Hy & Hz)".
  iDestruct "Hy" as (pbytes) "#Hy".
  iDestruct "Hec" as (cnb cnreg n [Hcn [Hcm [Hce Hcr]]]) "[Hcl Hcnt]".
  iPoseProof "Hro" as "(#Hv & #Hsg & #Hsol & #Hsoc & #Hsel & #Hsec & #Hel & #Htc & _ & _ & #Hlits & #Hver &
    #Hpr & #Hprog & #Hfmts)".
  iAssert (word_string DfracDiscarded (sym_ptr ge "hello#str.77") [37; 115; 58; 32; 37; 115]) as "#Hfmt".
  { iEval (rewrite /print_fmt_ro /print_fmts big_sepL_cons) in "Hfmts". iDestruct "Hfmts" as "[#H77 _]".
    iExact "H77". }
  iDestruct "Hprog" as (pb preg [Hp1 [Hp2 [Hp3 Hp4]]]) "[Hpgl Hpgp]".
  iDestruct (file_idle_obj with "Hout") as ([fo Hfo]) "Hout".
  iDestruct (file_idle_obj with "Herr") as ([fe Hfe]) "Herr".
  pose proof (hy_so_at _ _ Hy) as (Hso1 & Hso2 & Hso3 & Hso4).
  pose proof (hy_se_at _ _ Hy) as (Hse1 & Hse2 & Hse3 & Hse4).
  pose proof (hk_nb_at _ _ Hk) as (Hnb1 & Hnb2 & Hnb3 & Hnb4).
  pose proof Hos as [[Hs1 Hs2] _].
  iAssert (pcellq DfracDiscarded (ho_so o) 0 (mkPtr fo (Obj fo))) as "#Hsoc2". { rewrite -Hfo. iExact "Hsoc". }
  iAssert (pcellq DfracDiscarded (ho_se o) 0 (mkPtr fe (Obj fe))) as "#Hsec2". { rewrite -Hfe. iExact "Hsec". }
  iEval (rewrite Hfo) in "Hout". iEval (rewrite Hfe) in "Herr". rewrite Hfe in Hw3.
  assert (Hself : ptr_addr (ow_self w0) <> 0) by lia.
  assert (Hselfr : 0 <= ptr_addr (ow_self w0) < 2 ^ 64) by lia.
  iApply (wp_error_operand (glibc_program := call_program) (ho_eb o) Herr (hk_errno_at _ _ Hk) holds_os_glibc
    (hk_sys _ _ Hk) Hself Hselfr (ho_vb o) (ho_so o) (ho_soreg o) fo (ho_se o) (ho_sereg o) fe pb preg
    (ho_nb o) (ho_nreg o) y pbytes (sym_ptr ge "glibc_error#str.255") (sym_ptr ge "glibc_error#str.254")
    wide widefn wideframe (sym_ptr ge "hello#str.77") [37;115;58;32;37;115] _
    [WPtr (sym_ptr ge "hello#str.78"); WPtr q] cnb cnreg n Φ
    with "Hsol Hsoc2 Hout Herr Hpgl Hpgp Hnl Hnp [] [] Htcb He Hcl Hcnt [HK Hin Hio HP Hpl Hpp Hsl Hsp Hx Hz]").
  all: unfold call_program; cbn [program_of program_ge program_world].
  all: try assumption.
  all: try lia.
  all: try reflexivity.
  all: try exact (hy_so _ _ Hy).
  all: try exact (hy_se _ _ Hy).
  all: try exact (hk_nb _ _ Hk).
  all: try exact (Hpbpos _ Hp1).
  all: try exact (Hcbpos _ Hcn).
  all: try (apply narrow_fits_all; nargs).
  { unfold op_ro.
    iSplitR; [iExists _, _, _; iSplitR; [iExact "Hv" | iExact "Hsg"]|].
    iSplitR; [iExact "Hpr"|].
    iSplitR; [iApply (malloc_ro_of_hello_ro w0 ge o Hk with "Hro")|].
    iSplitR; [iExact "Hsel"|]. iSplitR; [iExact "Hsec2"|].
    iSplitR; [iApply (version_lit ge o ("glibc_error#str.255", [37;115;58;32]) with "Hro"); lit_in|].
    iSplitR; [iApply (version_lit ge o ("glibc_error#str.254", [10]) with "Hro"); lit_in|].
    iSplitR; [iExact "Hy" | iExact "Hfmt"]. }
  { iDestruct (hello_lit_ro ge o "hello#str.78" with "Hro") as (s78) "#H78"; [cbn; tauto|].
    cbn [big_opL]. iSplitR; [iApply (ws_arg (glibc_program := call_program) with "H78")|].
    iSplitR; [iExact "Hq" | done]. }
  iNext. iIntros "Hout Herr Hnl Hnp Htcb He Hcl Hcnt".
  iEval (rewrite -Hfo) in "Hout". iEval (rewrite -Hfe) in "Herr".
  iApply "HK". iSplitR; [done|].
  iSplitR "HP Hpl Hpp Hnl Hnp Hsl Hsp Hx Hz".
  { iSplitL "Hout"; [iExact "Hout"|]. iSplitL "Herr"; [iExact "Herr"|]. iSplitL "Hin"; [iExact "Hin"|].
    iSplitL "Hio"; [iExact "Hio"|]. iSplitL "Htcb"; [iExact "Htcb"|]. iSplitL "He"; [iExact "He"|].
    iExists cnb, cnreg, _. iSplitR; [iPureIntro; split_and!; assumption|].
    iSplitL "Hcl"; [iExact "Hcl" | iExact "Hcnt"]. }
  iSplitL "HP"; [iExact "HP"|].
  iExists x, y, z. iSplitL "Hpl Hpp Hnl Hnp Hsl Hsp".
  { iSplitL "Hpl"; [iExact "Hpl"|]. iSplitL "Hpp"; [iExact "Hpp"|]. iSplitL "Hnl"; [iExact "Hnl"|].
    iSplitL "Hnp"; [iExact "Hnp"|]. iSplitL "Hsl"; [iExact "Hsl" | iExact "Hsp"]. }
  iSplitL "Hx"; [iExact "Hx"|]. iSplitR; [iExists pbytes; iExact "Hy" | iExact "Hz"].
Qed.

End call.

(** Hello's linked image runs glibc's own error functions and places
    the strings and the counter they read. *)
Lemma hello_error_link_image fr : error_link (mkGenv hello_image_module img_globals fr) hello_image_objs.
Proof.
  constructor.
  all: try (vm_compute; reflexivity).
  - do 3 eexists. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. vm_compute; reflexivity.
  - cbn [hello_image_objs ho_so ho_se ho_nb]. vm_compute. split_and!; reflexivity.
  - intros pb H. vm_compute in H. injection H as <-. vm_compute. reflexivity.
  - intros cb H. vm_compute in H. injection H as <-. vm_compute. reflexivity.
Qed.
