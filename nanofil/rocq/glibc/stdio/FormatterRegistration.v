(** The formatter uses its built-in parser only when all three extension
    tables are null. These checks read genuine linked global cells;
    importing their names does not establish their values or ownership. *)
From Glibc Require Import Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld FileInv LibioCloseSteps LibioLogic Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L LibioCloseSteps LibioLogic.
Open Scope Z_scope.

(** The checks leave all earlier registers available. This environment
    records their temporary loads and comparisons in execution order. *)
Definition registration_env e fb mb ab :=
  fold_left (fun e nw => put (fst nw) (snd nw) e)
    [(TAtom "v52", WPtr (mkPtr fb (Obj fb))); (TAtom "chk6", WPtr (mkPtr fb (Obj fb)));
     (TAtom "v53", WPtr null); (TAtom "v54", WInt 0); (TAtom "v55", WInt 0); (TAtom "v56", WInt 0);
     (TAtom "v59", WPtr (mkPtr mb (Obj mb))); (TAtom "chk7", WPtr (mkPtr mb (Obj mb)));
     (TAtom "v60", WPtr null); (TAtom "v61", WInt 0); (TAtom "v63", WInt 0); (TAtom "v65", WInt 0);
     (TAtom "v68", WPtr (mkPtr ab (Obj ab))); (TAtom "chk8", WPtr (mkPtr ab (Obj ab)));
     (TAtom "v69", WPtr null); (TAtom "v70", WInt 0); (TAtom "v72", WInt 0); (TAtom "v74", WInt 0)] e.

Section registration.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Three owned null cells select the built-in parser. The rule returns
    those cells unchanged at its entry, with the same local allocations.
    It does not derive the cells from startup or interpret a directive.
    Other stream, cursor and errno ownership remains in the [[frame]]. *)
Lemma wp_formatter_registration e ls from fb fr mb mr ab ar Φ :
  lookup (TAtom "__printf_function_table") (ge_globals ge) = Some (mkPtr fb (Obj fb)) ->
  lookup (TAtom "__printf_modifier_table") (ge_globals ge) = Some (mkPtr mb (Obj mb)) ->
  lookup (TAtom "__printf_va_arg_table") (ge_globals ge) = Some (mkPtr ab (Obj ab)) ->
  0 < fb -> fb mod 8 = 0 -> fb + 8 <= r_end fr -> r_end fr <= 2 ^ 63 ->
  0 < mb -> mb mod 8 = 0 -> mb + 8 <= r_end mr -> r_end mr <= 2 ^ 63 ->
  0 < ab -> ab mod 8 = 0 -> ab + 8 <= r_end ar -> r_end ar <= 2 ^ 63 ->
  live fb fr -∗ pcell fb 0 null -∗ live mb mr -∗ pcell mb 0 null -∗
  live ab ar -∗ pcell ab 0 null -∗
  ▷ (live fb fr -∗ pcell fb 0 null -∗ live mb mr -∗ pcell mb 0 null -∗
    live ab ar -∗ pcell ab 0 null -∗
    WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer (registration_env e fb mb ab) ls None
      (Enter (TAtom "L79") (Some (TAtom "L67")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer e ls None
    (Enter (TAtom "L44") from)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hf Hm Ha Hfb Hfa Hfe Hfr Hmb Hma Hme Hmr Hab Haa Hae Har.
  iIntros "Hfl Hfc Hml Hmc Hal Hac HK".
  iApply wp_enter; [reflexivity | destruct from; reflexivity |]. iNext.
  cbn [b_insts b_jump].
  step. check "Hfl".
  iApply (wp_raw_load_null with "Hfl Hfc"); [reflexivity | vx | reflexivity | a2 | a2 |].
  iNext. iIntros "Hfl Hfc".
  do 3 step. closed_ints. branch. step.
  step. check "Hml".
  iApply (wp_raw_load_null with "Hml Hmc"); [reflexivity | vx | reflexivity | a2 | a2 |].
  iNext. iIntros "Hml Hmc".
  do 2 step. closed_ints. step. step. branch. step.
  step. check "Hal".
  iApply (wp_raw_load_null with "Hal Hac"); [reflexivity | vx | reflexivity | a2 | a2 |].
  iNext. iIntros "Hal Hac".
  do 2 step. closed_ints. step. step. branch.
  iApply ("HK" with "Hfl Hfc Hml Hmc Hal Hac").
Qed.
End registration.
