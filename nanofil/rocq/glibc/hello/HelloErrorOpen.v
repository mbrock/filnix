(** Hello reports an extra operand with glibc's `c: error` while
    stdout and stderr are both open and idle. This module proves that
    report over the image's code. The call flushes stdout, prints the
    program name, the message and a newline to stderr, flushes stderr
    and gives both streams back idle. *)

From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysWrappers FileInv FileIdle LibioLogic LibioCloseSteps
  WordString PrintfSpec AllocRo LibioFputsSpec LibioFflushSpec Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section open.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** Error reads two parts of an idle stream directly: the stream
    pointer's target must be alive when error loads it, and error reads
    the mode field after a failed print. An idle stream lends both and
    takes them back. An idle stream is never oriented wide, so the mode
    is zero or minus one. *)
Lemma file_idle_open vb self fb fd :
  file_idle vb self (mkPtr fb (Obj fb)) fd ⊢
  ∃ freg md, ⌜0 < fb /\ fb mod 8 = 0 /\ fb + 224 <= r_end freg /\ r_end freg <= 2 ^ 63 /\
              (md = 0 \/ md = 2 ^ 32 - 1)⌝ ∗
    live fb freg ∗ int_cell fb 192 md ∗
    (live fb freg -∗ int_cell fb 192 md -∗ file_idle vb self (mkPtr fb (Obj fb)) fd).
Proof using Type.
  iIntros "(%fb' & %freg & %st & %nb & %Hp & Hl & Hf & Hlk & Hb & Hw)".
  destruct Hp as (Hfp & Hal & Hfb & Hend & Hreg & Hfl & Hidle & Hvt & Hbuf & Hshort).
  injection Hfp as <-.
  iDestruct "Hf" as "(%Hlen & Hfl & Hps & Hfn & Hf2 & Hoo & %Hcol & Hc & Hlock & Hoff & Hcv & Hwd &
    Hfr1 & Hfr2 & Hmd & Htot & Hvt)".
  iExists freg, (fs_mode st). iFrame "Hl".
  change off_mode with 192. iFrame "Hmd".
  iSplit.
  { iPureIntro. unfold file_size in Hend. destruct Hidle as (_ & _ & Hm & _). split_and!; auto; lia. }
  iIntros "Hl Hmd". iExists fb, freg, st, nb. iFrame. iPureIntro. split_and!; auto.
Qed.

End open.
