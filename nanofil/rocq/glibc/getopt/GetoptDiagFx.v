(** getopt's two diagnostic rules, in GetoptDiag.v and GetoptLongDiag.v,
    are premises that a caller supplies for the calls that print a report:
    __GI___dcgettext translates a message, and __fxprintf_nocancel writes it
    to the error stream. FxprintfCall.v proves the real wrapper
    __fxprintf_nocancel up to its formatter. This file builds the printing
    part of both rules from that proof, so a caller of the parser no longer
    supplies a separate rule for the wrapper.

    Printing a report involves two more steps that this file does not
    prove, so a caller still supplies both of them. First, glibc looks up
    the translated message, and the caller states what __GI___dcgettext
    does. Second, glibc formats the output, and the caller states what
    __vfprintf_internal does with each format string and its arguments. A
    rule built here therefore does not prove the diagnostics.

    The caller's resources must lend the wrapper an unoriented or narrow
    stream whose lock is free or already held by this thread, and a share
    of the format string's lifetime. The wrapper gives back the stream at
    the same flags2 word and lock state, and the formatter's result
    resource may record the stream's new orientation. *)
From Glibc Require Import GetoptMessages OsExternals Unit_stdioZ2dcommon_fxprintf_os GlibcProgram
  GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld FileInv SysWrappers WordString
  FxprintfTidy FxprintfStream FxprintfCall GetoptDiag GetoptLongDiag.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import SysWrappers Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv.

Import ProgramAbbreviations.
Section bridge.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** ## Lending the stream

    A report hands the wrapper some of the caller's resources and gets
    them back when the wrapper returns. This section states what the
    caller must lend for one call, and it proves that one call returns
    the caller's resources together with the result. *)

(** Before it prints, the caller must hand the wrapper everything that the
    wrapper reads and writes, and it must get all of it back afterwards.
    A loan from S names those resources. It hands over the flag that says
    the process is single-threaded, the stream with its flags2 word and
    its lock, and a share of the lock owner's lifetime when the lock is
    held. It also hands over a share of the format string's lifetime and
    the formatter's resource R. The stream is tidy, so it is unoriented
    or narrow, and it writes to an open descriptor fd. The formatter
    takes the lock once more than the wrapper does, so a held lock's
    count must leave room for two more acquisitions. When the call
    returns, the caller gives back the stream at the same flags2 word and
    lock state, in any mode, together with the formatter's result
    resource Q, and it receives G. *)
Definition fx_loan (S : iProp Σ) (vb sb : Z) (sreg : region) (fp fmt : ptr) (R : iProp Σ)
    (Q : Z -> Z -> iProp Σ) (G : iProp Σ) : Prop :=
  ⊢ S -∗ ∃ fd mode flags2 held dqf regf,
    ⌜In fd (ow_fds w0) /\ (forall c, held = Some c -> 0 <= c /\ c + 2 < 2 ^ 32) /\
     0 <= ptr_addr fmt < 2 ^ 64⌝ ∗
    single_ro ge sb sreg ∗ fx_stream vb (ow_self w0) fp fd mode flags2 held ∗ fx_owner (ow_self w0) held ∗
    live_capq dqf (ptr_cap fmt) regf ∗ R ∗
    (∀ x mode', fx_stream vb (ow_self w0) fp fd mode' flags2 held -∗ fx_owner (ow_self w0) held -∗
       live_capq dqf (ptr_cap fmt) regf -∗ Q x mode' -∗ G).

(** A caller cannot know in advance which state a loan will hand over,
    so it must show that the formatter call is safe in all of them. The
    stream may write to any open descriptor, hold any second flags word,
    and have any lock count that leaves room for two more acquisitions.
    The caller proves this for the format string fmt and the remaining
    arguments ys. *)
Definition fx_format (vb : Z) (fp fmt : ptr) (ys : list word) (R : iProp Σ) (Q : Z -> Z -> iProp Σ) : Prop :=
  forall fd mode flags2 held, In fd (ow_fds w0) -> (forall c, held = Some c -> 0 <= c /\ c + 2 < 2 ^ 32) ->
    fx_vfprintf_rule_at vb fd fp fmt (WPtr fp :: WPtr fmt :: ys) mode flags2 held R Q.

(** This lemma lets a report use the wrapper proof. Given a loan and a
    formatter premise, one call of __fxprintf_nocancel takes S and the
    resources X of its other arguments. The caller then continues with G
    and the result reduced to a C int. *)
Lemma wp_call_fx_loan S G vb sb sreg fp fmt ys R X Q f e ls l d args rest j Φ :
  find_fn ge (TAtom "__fxprintf_nocancel") = Some (Defined Unit_stdioZ2dcommon_fxprintf_os.fn___fxprintf_nocancel) ->
  ptr_addr (ow_self w0) <> 0 -> 0 <= ptr_addr (ow_self w0) < 2 ^ 64 ->
  map_option (arg_x ge e) args = Some (WPtr fp :: WPtr fmt :: ys) -> forallb snapshot_word ys = true ->
  fx_loan S vb sb sreg fp fmt R Q G -> fx_format vb fp fmt ys (R ∗ X) Q ->
  S -∗ X -∗
  ▷ (∀ x, G -∗ WP (ERun (mkFrame f (put d (WInt (x mod 2 ^ 32)) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d W) (Global (TAtom "__fxprintf_nocancel")) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hfn Hself Hselfr Hargs Hys Hl Hfm. iIntros "HS HX HK".
  iDestruct (Hl with "HS") as (fd mode flags2 held dqf regf (Hfd & Hc & Hfr)) "(#Hs & Hst & Ho & Hfc & HR & Hb)".
  iDestruct (fx_stream_mode with "Hst") as %Hm.
  iApply (wp_call_fxprintf_at Hreg Hext f e ls l d args rest j vb fd sb sreg fp fmt ys mode flags2 held dqf regf
    (R ∗ X) Q with "Hs Hst Ho Hfc [$HR $HX]"); [exact Hargs | exact Hfn | exact Hys | exact Hself |
    exact Hselfr | exact Hfr | exact Hm | | exact (Hfm fd mode flags2 held Hfd Hc) |].
  { intros c Hcs. destruct (Hc c Hcs). lia. }
  iNext. iIntros (x mode') "Hst Ho Hfc HQ". iApply "HK". iApply ("Hb" with "Hst Ho Hfc HQ").
Qed.

(** These controls show the argument shapes that the reports pass. The
    snapshot accepts integers and pointers, and it rejects a limit word. *)
Example fx_args_controls a0 c pfx nm cp n :
  forallb snapshot_word [WPtr a0; WInt c] = true /\ forallb snapshot_word [WPtr a0; WPtr pfx; WPtr nm] = true /\
  forallb snapshot_word [WPtr pfx; WLimit cp n] = false.
Proof using Type*. repeat split. Qed.

(** A loan admits the unoriented mode 0 and the narrow mode -1 as a
    32-bit word. It excludes the wide mode 1. *)
Example fx_mode_controls : (0 = 0 \/ 0 = 2 ^ 32 - 1) /\ (2 ^ 32 - 1 = 0 \/ 2 ^ 32 - 1 = 2 ^ 32 - 1) /\
  ~ (1 = 0 \/ 1 = 2 ^ 32 - 1).
Proof using Type*. lia. Qed.

(** ## The short-option rule

    A short-option report translates one of two messages into T and
    prints the translation with the program name and the option
    character. The caller lends the wrapper's resources from T. *)

(** A report prints the translated message, so the caller lends the
    wrapper's resources from the translation's resource T. The caller
    gives such a loan for every translation q of a message. It also says
    what the formatter does with that translation, any program name a0 and
    any option character c. *)
Definition diag_fx_loan (G : iProp Σ) (T : ptr -> ptr -> iProp Σ) (vb sb : Z) (sreg : region) (fp : ptr)
    (R : ptr -> ptr -> iProp Σ) (Q : ptr -> ptr -> Z -> Z -> iProp Σ) : Prop :=
  forall mid q, diag_msg ge mid -> fx_loan (T mid q) vb sb sreg fp q (R mid q) (Q mid q) G.
Definition diag_fx_format (vb : Z) (fp : ptr) (R : ptr -> ptr -> iProp Σ) (Q : ptr -> ptr -> Z -> Z -> iProp Σ) :
    Prop :=
  forall mid q a0 s0 c, diag_msg ge mid -> 0 <= c < 2 ^ 32 ->
    fx_format vb fp q [WPtr a0; WInt c] (R mid q ∗ word_string DfracDiscarded a0 s0) (Q mid q).

(** With these premises, the caller no longer assumes anything about the
    print call itself. The wrapper's proof supplies that part of the
    short-option rule, and the caller supplies the rest. *)
Lemma getopt_diag_rule_fx G T vb sb sreg fp dom R Q :
  find_fn ge (TAtom "__fxprintf_nocancel") = Some (Defined Unit_stdioZ2dcommon_fxprintf_os.fn___fxprintf_nocancel) ->
  ptr_addr (ow_self w0) <> 0 -> 0 <= ptr_addr (ow_self w0) < 2 ^ 64 ->
  lookup (TAtom "__GI__libc_intl_domainname") (ge_globals ge) = Some dom -> 0 <= ptr_addr fp < 2 ^ 64 ->
  (⊢ G -∗ ∃ dq reg, live_capq dq (ptr_cap fp) reg ∗ (live_capq dq (ptr_cap fp) reg -∗ G)) ->
  diag_translate G T dom -> diag_fx_loan G T vb sb sreg fp R Q -> diag_fx_format vb fp R Q ->
  getopt_diag_rule w0 registry ge G T fp dom.
Proof using Type*.
  intros Hfn Hself Hselfr Hd Hf Hcap Htr Hl Hfm.
  refine (conj Hd (conj Hf (conj Hcap (conj Htr _)))).
  intros f e ls l d args rest j mid q a0 s0 c Φ Hm Hc Hx. iIntros "HT Ha HK".
  iApply (wp_call_fx_loan with "HT Ha [HK]");
    [exact Hfn | exact Hself | exact Hselfr | exact Hx | reflexivity | exact (Hl mid q Hm) |
     exact (Hfm mid q a0 s0 c Hm Hc) |].
  iNext. iIntros (x) "HG". iApply ("HK" $! (x mod 2 ^ 32) with "HG").
Qed.

(** ## The long-option rule

    A long-option report either translates one of five messages and
    prints it with the program name, the option prefix and a name, or
    prints one of two formats that the parser does not translate. The
    translated prints lend from T. The two untranslated prints lend from
    G and give G back. *)

(** The translated long-option prints lend from T, and their formatter
    premise covers any program name, prefix and option name. *)
Definition ldiag_fx_loan (G : iProp Σ) (T : ptr -> ptr -> iProp Σ) (vb sb : Z) (sreg : region) (fp : ptr)
    (R : ptr -> ptr -> iProp Σ) (Q : ptr -> ptr -> Z -> Z -> iProp Σ) : Prop :=
  forall mid q, ldiag_msg ge mid -> fx_loan (T mid q) vb sb sreg fp q (R mid q) (Q mid q) G.
Definition ldiag_fx_format (vb : Z) (fp : ptr) (R : ptr -> ptr -> iProp Σ) (Q : ptr -> ptr -> Z -> Z -> iProp Σ) :
    Prop :=
  forall mid q a0 s0 pfx sp nm sn, ldiag_msg ge mid ->
    fx_format vb fp q [WPtr a0; WPtr pfx; WPtr nm]
      (R mid q ∗ word_string DfracDiscarded a0 s0 ∗ word_string DfracDiscarded pfx sp ∗
       word_string DfracDiscarded nm sn) (Q mid q).

(** A long-option report is handled the same way as a short-option
    report. Its caller supplies the translation premise, a formatter
    premise for each kind of print, and loans for the translated prints and
    for the two untranslated formats. *)
Lemma getopt_ldiag_rule_fx G T vb sb sreg fp dom f140 f141 R Q R140 Q140 R141 Q141 :
  find_fn ge (TAtom "__fxprintf_nocancel") = Some (Defined Unit_stdioZ2dcommon_fxprintf_os.fn___fxprintf_nocancel) ->
  ptr_addr (ow_self w0) <> 0 -> 0 <= ptr_addr (ow_self w0) < 2 ^ 64 ->
  lookup (TAtom "__GI__libc_intl_domainname") (ge_globals ge) = Some dom -> 0 <= ptr_addr fp < 2 ^ 64 ->
  (⊢ G -∗ ∃ dq reg, live_capq dq (ptr_cap fp) reg ∗ (live_capq dq (ptr_cap fp) reg -∗ G)) ->
  ldiag_translate G T dom -> ldiag_fx_loan G T vb sb sreg fp R Q -> ldiag_fx_format vb fp R Q ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  fx_loan G vb sb sreg fp f140 R140 Q140 G ->
  (forall pfx sp nm sn, fx_format vb fp f140 [WPtr pfx; WPtr nm]
     (R140 ∗ word_string DfracDiscarded pfx sp ∗ word_string DfracDiscarded nm sn) Q140) ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  fx_loan G vb sb sreg fp f141 R141 Q141 G -> fx_format vb fp f141 [] (R141 ∗ True) Q141 ->
  getopt_ldiag_rule w0 registry ge G T fp dom.
Proof using Type*.
  intros Hfn Hself Hselfr Hd Hf Hcap Htr Hl Hfm H140 Hl140 Hfm140 H141 Hl141 Hfm141.
  refine (conj Hd (conj Hf (conj Hcap (conj Htr (conj _ (conj _ _)))))).
  - intros f e ls l d args rest j mid q a0 s0 pfx sp nm sn Φ Hm Hx. iIntros "HT Ha Hp Hn HK".
    iApply (wp_call_fx_loan _ _ _ _ _ _ _ _ _ ((word_string DfracDiscarded a0 s0 ∗ word_string DfracDiscarded pfx sp ∗
      word_string DfracDiscarded nm sn)%I) with "HT [$Ha $Hp $Hn] [HK]");
      [exact Hfn | exact Hself | exact Hselfr | exact Hx | reflexivity | exact (Hl mid q Hm) |
       exact (Hfm mid q a0 s0 pfx sp nm sn Hm) |].
    iNext. iIntros (x) "HG". iApply ("HK" $! (x mod 2 ^ 32) with "HG").
  - intros f e ls l d args rest j fmt pfx sp nm sn Φ Hm Hx.
    rewrite H140 in Hm. injection Hm as <-. iIntros "HG Hp Hn HK".
    iApply (wp_call_fx_loan _ _ _ _ _ _ _ _ _ ((word_string DfracDiscarded pfx sp ∗ word_string DfracDiscarded nm sn)%I)
      with "HG [$Hp $Hn] [HK]");
      [exact Hfn | exact Hself | exact Hselfr | exact Hx | reflexivity | exact Hl140 | exact (Hfm140 pfx sp nm sn) |].
    iNext. iIntros (x) "HG". iApply ("HK" $! (x mod 2 ^ 32) with "HG").
  - intros f e ls l d args rest j fmt Φ Hm Hx.
    rewrite H141 in Hm. injection Hm as <-. iIntros "HG HK".
    iApply (wp_call_fx_loan _ _ _ _ _ _ _ _ _ (True%I) with "HG [//] [HK]");
      [exact Hfn | exact Hself | exact Hselfr | exact Hx | reflexivity | exact Hl141 | exact Hfm141 |].
    iNext. iIntros (x) "HG". iApply ("HK" $! (x mod 2 ^ 32) with "HG").
Qed.

End bridge.
