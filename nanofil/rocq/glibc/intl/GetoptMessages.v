(** Getopt asks dcgettext to translate a short or long option diagnostic.
    These contracts describe the message pointers that the parser supplies
    and the translation that the caller receives. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import List String ZArith.
From Nanofil Require Import Term Syntax Values Ops Semantics Machine Run Language.
From Glibc Require Import GlibcProgram Fix.
Import ListNotations ProgramAbbreviations Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

Definition diag_msg (ge : genv) (mid : ptr) : Prop :=
  lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid \/
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid.

Definition ldiag_msg (ge : genv) (mid : ptr) : Prop :=
  List.Exists (fun n => lookup (TAtom n) (ge_globals ge) = Some mid)
    ["glibc_getopt#str.138"; "glibc_getopt#str.139"; "glibc_getopt#str.142"; "glibc_getopt#str.143";
     "glibc_getopt#str.144"]%string.

Section translation.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The parser's caller must still say how a message is translated. This
    premise is that part of getopt_diag_rule, stated on its own so that the
    construction below takes it as a separate hypothesis. *)
Definition diag_translate (G : iProp Σ) (T : ptr -> ptr -> iProp Σ) (dom : ptr) : Prop :=
  forall f e ls l d args rest j mid Φ, diag_msg ge mid ->
    map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] ->
    ⊢ G -∗ ▷ (∀ q, T mid q -∗ WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
      WP (ERun (mkFrame f e ls None
        (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.

(** The caller must also say how a long-option message is translated.
    This premise is that part of getopt_ldiag_rule, stated on its own so
    that the construction below takes it as a separate hypothesis. *)
Definition ldiag_translate (G : iProp Σ) (T : ptr -> ptr -> iProp Σ) (dom : ptr) : Prop :=
  forall f e ls l d args rest j mid Φ, ldiag_msg ge mid ->
    map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] ->
    ⊢ G -∗ ▷ (∀ q, T mid q -∗ WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
      WP (ERun (mkFrame f e ls None
        (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}.
End translation.
