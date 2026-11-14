From Glibc Require Import GlibcProgram.
(** The getopt wrapper calls the reentrant parser with eight arguments.
    Its proof hands the parser a frame built by the machine's call rule,
    which starts by entering the first block. The proof of the parser's
    first blocks starts one step later, inside that block, with the
    arguments already in named temporaries. This file joins the two: it
    takes the real call frame into the first blocks, and it packages the
    result in the form that the wrapper's proof asks of the parser. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString GetoptModule GetoptState GetoptBytes
  GetoptInitialize GetoptColon GetoptEntry GetoptEntryPre.
From Glibc Require FileInv GetoptEntry GetoptEntryPre GetoptInitialize GetoptState OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Transparent glibc_getopt_internal_r.

(** ## The parser's call frame

    A call binds the parser's eight parameters in order and enters its
    first block with no stack objects. The facts below compute that
    frame and check that the first block has no phi nodes, so entering
    it leaves the temporaries as the call bound them. *)

(** The call binds argc, argv, the option string, the long-option table,
    the index pointer, the long-only flag, the private object and the
    POSIX flag to the temporaries v0 through v14. *)
Definition getopt_r_env (n : Z) (av : Z) (p lo li : ptr) (lonly b pc : Z) : env :=
  put (TAtom "v14") (WInt pc) (put (TAtom "v12") (WPtr (mkPtr b (Obj b)))
    (put (TAtom "v10") (WInt lonly) (put (TAtom "v8") (WPtr li) (put (TAtom "v6") (WPtr lo)
      (put (TAtom "v4") (WPtr p) (put (TAtom "v2") (WPtr (mkPtr av (Obj av))) (put (TAtom "v0") (WInt n) []))))))).

(** The call frame enters the block named start with that environment. *)
Lemma getopt_r_call_frame n av p lo li lonly b pc :
  call_frame glibc_getopt_internal_r
    [WInt n; WPtr (mkPtr av (Obj av)); WPtr p; WPtr lo; WPtr li; WInt lonly; WPtr (mkPtr b (Obj b)); WInt pc] =
  Some (mkFrame glibc_getopt_internal_r (getopt_r_env n av p lo li lonly b pc) [] None (Enter (TAtom "start") None)).
Proof. reflexivity. Qed.

(** The block named start is the first block that the entry proof runs. *)
Lemma getopt_r_find_start : find_block (TAtom "start") (fn_blocks glibc_getopt_internal_r) = Some getopt_blk_start.
Proof. vm_compute. reflexivity. Qed.

(** This example checks the order of the last two arguments. A call
    passes the private object at address 128 and the POSIX flag 1, and
    each value lands where the parser reads it. *)
Lemma getopt_r_env_ctl : lookup (TAtom "v12") (getopt_r_env 3 64 null null null 0 128 1) = Some (WPtr (mkPtr 128 (Obj 128))) /\
  lookup (TAtom "v14") (getopt_r_env 3 64 null null null 0 128 1) = Some (WInt 1).
Proof. split; reflexivity. Qed.

Import GetoptState FileInv FileInv.ML FileInv.LG FileInv.L.

Import ProgramAbbreviations.
Section entry_call.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance ec_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** ## Entering the first blocks from the call

    The entry rule names its two exits, at the blocks L73 and L75, and
    the program states what it does at each. The definition below gives
    those two exits one name, so that the three rules of this file can
    pass them on unchanged. *)

(** These are the two exits of [wp_getopt_entry_pre], word for word. *)
Definition getopt_entry_exits (n av : Z) (ar : region) (p : ptr) (os : list Z) (lo li : ptr)
    (lonly b : Z) (r : region) (ps : list ptr) (j : Z) (G : iProp Σ) (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ :=
  (∀ e' s s', ⌜entry_state s s' /\
        entry_env e' n (mkPtr av (Obj av)) (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b (print_errors os (gs_err s)) /\
        gs_ind s = j /\ gs_initialized s' = 1 /\ 0 <= gs_order s' <= 2 /\ getopt_bounds n (gs_ind s') s' /\
        gs_arg s' = null /\ gs_ind s' = (if j =? 0 then 1 else j) /\
        0 < b /\ b mod 8 = 0 /\ b + 56 <= r_end r /\ r_end r <= 2 ^ 48 /\
        0 < av /\ av mod 8 = 0 /\ av + 8 * (n + 1) <= r_end ar /\ r_end ar <= 2 ^ 48⌝ -∗
      live b r -∗ int_cell b 0 (gs_ind s') -∗ int_cell b 4 (gs_err s') -∗ int_cell b 8 (gs_opt s') -∗
      pcell b 16 (gs_arg s') -∗ int_cell b 24 (gs_initialized s') -∗ pcell b 32 (gs_next s') -∗
      int_cell b 40 (gs_order s') -∗ int_cell b 44 (gs_first s') -∗ int_cell b 48 (gs_last s') -∗
      (⌜gs_next s' = null⌝ ∨ word_string DfracDiscarded (gs_next s') []) -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L73") (Some (TAtom "L83")))) : gexpr)
        {{ Φ }}) ∧
  (∀ e' s q sq k0, ⌜entry_env e' n (mkPtr av (Obj av)) (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b
          (print_errors os (gs_err s)) /\
        ~ needs_init s /\ gs_ind s = j /\ gs_initialized s = 1 /\ 0 <= gs_order s <= 2 /\ getopt_bounds n j s /\
        0 <= j < n /\ ps !! Z.to_nat j = Some q /\ (k0 < length sq)%nat /\ sbyte sq k0 <> 0 /\
        gs_next s = ptr_add q (Z.of_nat k0) /\ gs_last s <= j /\
        0 < b /\ b mod 8 = 0 /\ b + 56 <= r_end r /\ r_end r <= 2 ^ 48 /\
        0 < av /\ av mod 8 = 0 /\ av + 8 * (n + 1) <= r_end ar /\ r_end ar <= 2 ^ 48⌝ -∗
      word_string DfracDiscarded q sq -∗ word_string DfracDiscarded (gs_next s) (drop k0 sq) -∗
      live b r -∗ int_cell b 0 j -∗ int_cell b 4 (gs_err s) -∗ int_cell b 8 (gs_opt s) -∗ pcell b 16 null -∗
      int_cell b 24 1 -∗ pcell b 32 (gs_next s) -∗ int_cell b 40 (gs_order s) -∗ int_cell b 44 (gs_first s) -∗
      int_cell b 48 (gs_last s) -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L75") (Some (TAtom "L83")))) : gexpr)
        {{ Φ }}).

(** A real call of the parser reaches the two exits of the first blocks.
    The call enters the first block with the arguments in place, and the
    entry rule runs from there. The argument count is the length of the
    argument vector, which lies between 1 and 2 ^ 31. *)
Lemma wp_getopt_entry_call cf n av ar p os lo li lonly pc penv b r ps j (G : iProp Σ) Φ :
  call_frame glibc_getopt_internal_r
    [WInt n; WPtr (mkPtr av (Obj av)); WPtr p; WPtr lo; WPtr li; WInt lonly; WPtr (mkPtr b (Obj b)); WInt pc] = Some cf ->
  GetoptInitialize.getenv_rule w0 registry ge G -> lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv ->
  Z.of_nat (length ps) = n ->
  getopt_entry_pre b r av ar ps j -∗ word_string DfracDiscarded p os -∗ G -∗
  getopt_entry_exits n av ar p os lo li lonly b r ps j G Φ -∗
  WP (ERun cf : gexpr) {{ Φ }}.
Proof.
  intros Hcf Hget Hpenv Hlen. rewrite getopt_r_call_frame in Hcf. injection Hcf as <-.
  iIntros "Hpre Hos HG HK".
  iApply wp_enter; [exact getopt_r_find_start | reflexivity |]. iNext.
  iApply (GetoptEntryPre.wp_getopt_entry_pre (getopt_r_env n av p lo li lonly b pc) n av ar p os lo li lonly pc penv
            b r ps j G with "Hpre Hos HG HK"); try reflexivity; assumption.
Qed.

(** ## The parser premise of the wrapper

    The wrapper does not know how the parser behaves, so its proof asks
    the program for that as a premise. The two lemmas below supply it.
    A program keeps most of the private object while the wrapper runs,
    and it gets those fields back when the parser's first blocks end. *)

(** A program that left optind at the session's index, or set it to 0,
    may call getopt again. It lends the wrapper two fields of the object,
    and it gets back the parser rule that the wrapper needs. *)
Lemma getopt_callee_session n av ar p os lo li lonly pc penv b r ps i j err (G : iProp Σ) Φ :
  j = i \/ j = 0 ->
  GetoptInitialize.getenv_rule w0 registry ge G -> lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv ->
  Z.of_nat (length ps) = n ->
  getopt_session b r av ar ps i -∗ word_string DfracDiscarded p os -∗ G -∗
  getopt_entry_exits n av ar p os lo li lonly b r ps j G Φ -∗
  ∃ i0 e0, ⌜1 <= n < 2 ^ 31⌝ ∗ live b r ∗ int_cell b 0 i0 ∗ int_cell b 4 e0 ∗
    (∀ cf, ⌜call_frame glibc_getopt_internal_r
              [WInt n; WPtr (mkPtr av (Obj av)); WPtr p; WPtr lo; WPtr li; WInt lonly; WPtr (mkPtr b (Obj b)); WInt pc] =
            Some cf⌝ -∗
       live b r -∗ int_cell b 0 j -∗ int_cell b 4 err -∗ WP (ERun cf : gexpr) {{ Φ }}).
Proof.
  intros Hj Hget Hpenv Hlen. iIntros "Hss #Hos HG HK".
  iAssert ⌜1 <= n < 2 ^ 31⌝%I as %Hn.
  { iDestruct "Hss" as "[_ (%s & _ & %Hbd & _)]". iPureIntro. unfold getopt_bounds in Hbd. lia. }
  iDestruct (GetoptEntryPre.session_entry_pre b r av ar ps i j err Hj with "Hss") as (i0 e0) "(Hl & Hi & He & Hw)".
  iExists i0, e0. iFrame "Hl Hi He". iSplit; [done|].
  iIntros (cf Hcf) "Hl Hi He". iDestruct ("Hw" with "Hl Hi He") as "Hpre".
  iApply (wp_getopt_entry_call cf n av ar p os lo li lonly pc penv b r ps j G Φ with "Hpre Hos HG HK"); assumption.
Qed.

(** Fresh zero storage may be called with any public index within the
    argument count, and the first blocks set it up at that index. *)
Lemma getopt_callee_zero n av ar p os lo li lonly pc penv b r ps j err (G : iProp Σ) Φ :
  0 < av -> av mod 8 = 0 -> av + 8 * (n + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  1 <= n < 2 ^ 31 -> 0 <= j <= n ->
  GetoptInitialize.getenv_rule w0 registry ge G -> lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv ->
  Z.of_nat (length ps) = n ->
  getopt_state_own b r getopt_zero -∗ word_string DfracDiscarded p os -∗ G -∗
  getopt_entry_exits n av ar p os lo li lonly b r ps j G Φ -∗
  live b r ∗ int_cell b 0 0 ∗ int_cell b 4 0 ∗
    (∀ cf, ⌜call_frame glibc_getopt_internal_r
              [WInt n; WPtr (mkPtr av (Obj av)); WPtr p; WPtr lo; WPtr li; WInt lonly; WPtr (mkPtr b (Obj b)); WInt pc] =
            Some cf⌝ -∗
       live b r -∗ int_cell b 0 j -∗ int_cell b 4 err -∗ WP (ERun cf : gexpr) {{ Φ }}).
Proof.
  intros Hav Hal Hfit Har Hn Hj Hget Hpenv Hlen. subst n. iIntros "Hz #Hos HG HK".
  iDestruct (GetoptEntryPre.zero_entry_pre b r av ar ps j err with "Hz") as "(Hl & Hi & He & Hw)"; try assumption.
  iFrame "Hl Hi He". iIntros (cf Hcf) "Hl Hi He". iDestruct ("Hw" with "Hl Hi He") as "Hpre".
  iApply (wp_getopt_entry_call cf (Z.of_nat (length ps)) av ar p os lo li lonly pc penv b r ps j G Φ
            with "Hpre Hos HG HK"); try assumption; reflexivity.
Qed.

End entry_call.
