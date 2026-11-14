(** Calling getenv requires a readable name and ownership of the environment.
    These rules enter the linked internal function through its real call frame.
    They return the caller's resources when execution resumes. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Semantics Run
  Pieces Heap Language Logic ExternalCalls.
From Glibc Require Import GlibcProgram WordString GetenvCode GetenvEntry
  GetenvScan GetenvStatic StrlenLogic StrncmpCode OsWorld.
Import ListNotations LG0 LG0.L ProgramAbbreviations.
Open Scope Z_scope.

Section named_rule.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Local Instance named_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A parser asks getenv about one linked name. Its loan must provide the
    memory needed for that name, rather than support arbitrary arguments. *)
Definition getenv_at_rule (G : iProp Σ) (p : ptr) : Prop :=
  forall f e ls l d args rest j Φ, map_option (arg_x ge e) args = Some [WPtr p] ->
  ⊢ G -∗ ▷ (∀ q, G -∗
    WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d P) (Global (TAtom "__GI_getenv")) args :: rest) j)) : gexpr) {{ Φ }}.

(** Extra resources travel beside the name's loan and return unchanged.
    This lets the parser carry the stack-size cell needed by its cutoff. *)
Lemma getenv_at_rule_sep (G R : iProp Σ) p :
  getenv_at_rule G p -> getenv_at_rule (G ∗ R) p.
Proof.
  intros Hg f e ls l d args rest j Φ Hargs. iIntros "[HG HR] HK".
  iApply (Hg with "HG"); [exact Hargs|]. iNext. iIntros (q) "HG".
  iApply ("HK" with "[$HG $HR]").
Qed.
End named_rule.

Section calls.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{!Defines ge "__GI_getenv" glibc_getenv}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A caller with a readable name can use a frame contract for any resource G.
    The rule does not accept arbitrary argument words or unreadable pointers. *)
Lemma wp_call_getenv_readable f e ls l d args rest j p s (G : iProp Σ) Φ :
  map_option (arg_x ge e) args = Some [WPtr p] ->
  getenv_name_contract G p s -∗ word_string DfracDiscarded p s -∗ G -∗
  ▷ (∀ q, G -∗
    WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d P) (Global (TAtom "__GI_getenv")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hargs. iIntros "#Hcontract #Hname HG HK".
  iApply (wp_call_bind registry (os_wi w0) ge); [exact Hargs|apply defines|apply getenv_call_frame|].
  iNext. iPoseProof ("Hcontract" with "Hname HG") as "Hcall".
  iApply (wp_wand with "Hcall").
  iIntros (v) "H". iDestruct "H" as (q ->) "HG".
  iExists (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)).
  iSplit; [done|]. iNext. iApply ("HK" with "HG").
Qed.

(** The parser keeps the name readable while getenv searches the environment.
    Putting that read permission beside G supplies the one-name call rule. *)
Lemma getenv_name_at_rule (G : iProp Σ) p s :
  (⊢ getenv_name_contract G p s) ->
  getenv_at_rule w0 registry ge (G ∗ word_string DfracDiscarded p s) p.
Proof.
  intros Hcontract f e ls l d args rest j Φ Hargs. iIntros "[HG #Hname] HK".
  iApply (wp_call_getenv_readable with "[] Hname HG"); [exact Hargs|iApply Hcontract|].
  iNext. iIntros (q) "HG". iApply ("HK" with "[$HG $Hname]").
Qed.

Context `{!Defines ge "__GI_strlen" glibc_strlen}.
Context `{!Defines ge "__GI_strncmp" glibc_strncmp}.

(** The static environment implementation returns its exact computed pointer.
    Both global cells, the array, entry lifetimes, and arbitrary caller resources
    remain available. A nonnull result also carries a readable value string. *)
Lemma wp_call_getenv_static f e ls l d args rest j p s entries ep dq dqa dqt
    bc rc be re counter (G : iProp Σ) Φ :
  map_option (arg_x ge e) args = Some [WPtr p] ->
  lookup (TAtom "__environ_counter") (ge_globals ge) = Some (mkPtr bc (Obj bc)) ->
  lookup (TAtom "__environ") (ge_globals ge) = Some (mkPtr be (Obj be)) ->
  0 < bc -> bc + 8 <= r_end rc -> r_end rc <= 2 ^ 48 ->
  0 < be -> be + 8 <= r_end re -> r_end re <= 2 ^ 48 -> be mod 8 = 0 ->
  word_string DfracDiscarded p s -∗ getenv_globals dq bc rc be re counter ep -∗
  getenv_storage dqa dqt ep entries -∗ G -∗
  ▷ (getenv_globals dq bc rc be re counter ep -∗ getenv_storage dqa dqt ep entries -∗ G -∗
    getenv_value (getenv_result s entries) -∗
    WP (ERun (mkFrame f (put d (WPtr (getenv_result s entries)) e) ls None
      (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d P) (Global (TAtom "__GI_getenv")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hargs Hcounter Henv Hbc Hrc Hrcmax Hbe Hre Hremax Hal.
  iIntros "#Hname HG HS HE HK".
  iApply (wp_call_bind registry (os_wi w0) ge); [exact Hargs|apply defines|apply getenv_call_frame|].
  iNext. iApply (getenv_static_call with "Hname HG HS HE"); try eassumption.
  iIntros "HG HS HE Hv".
  iExists (mkFrame f (put d (WPtr (getenv_result s entries)) e) ls None (Exec l rest j)).
  iSplit; [done|]. iNext. iApply ("HK" with "HG HS HE Hv").
Qed.
End calls.
