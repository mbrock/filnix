From Glibc Require Import GlibcProgram.
(** Hello uses glibc's setlocale lock in two ways. Setlocale takes it
    for writing once, and gettext takes it for reading every time it
    translates a message. A proof of Hello must carry the lock's state
    from one call to the next without knowing their order, so it needs a
    description of the lock that every one of these calls preserves.

    This module gives that description and proves that each call keeps
    it. The proofs of the individual calls are in the neighbouring files
    of this directory, one for each route through glibc's code. 

    A lock is ready for a reader when its word holds a whole number of
    readers with no flag set, or the same with only the write-phase bit
    set, which is how a writer leaves it. In the second form the
    write-phase futex must have no waiter bit. A lock is idle when it is
    ready and no reader holds it. Taking and releasing the lock for
    reading keeps it ready, and taking and releasing it for writing keeps
    it idle. In both cases the calling thread must not be the writer, and
    nobody waits on the lock's futexes. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry FileInv LibioLogic SysWrappers.
From Glibc Require Import RdlockCode RwunlockCode WrlockCode RdlockLogic RdlockPhase RwunlockLogic WrlockLogic
  RwunlockWrite.
From Glibc Require FileInv LibioLogic OsThread OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

(** ## The states of the lock

    The lock's state is described by plain integers: the lock word, the
    write-phase futex and the writers futex. These definitions say which
    values a reader or a writer may find, and what a read lock leaves. *)

(** A reader may take the lock when its word r has room for one more
    reader and either has no flag set or has only the write-phase bit
    set. In the second case the write-phase futex wp is 0 or 1, so its
    waiter bit is clear. *)
Definition rw_word_ready (r wp : Z) : Prop :=
  0 <= r /\ r + 8 < 2 ^ 31 /\ (r mod 8 = 0 \/ (r mod 8 = 1 /\ (wp = 0 \/ wp = 1))).

(** A writer may take the lock when no reader holds it and neither futex
    has its waiter bit set. *)
Definition rw_word_idle (r wp wf : Z) : Prop :=
  (r = 0 \/ r = 1) /\ (wp = 0 \/ wp = 1) /\ (wf = 0 \/ wf = 1).

(** A read lock adds 8 to a word without flags. On a word in the write
    phase it also clears that bit, so it adds 7 and sets the write-phase
    futex to 0. *)
Definition rd_word (r : Z) : Z := if r mod 8 =? 0 then r + 8 else r + 7.
Definition rd_wp (r wp : Z) : Z := if r mod 8 =? 0 then wp else 0.

(** An idle lock is ready for a reader. *)
Lemma rw_idle_ready r wp wf : rw_word_idle r wp wf -> rw_word_ready r wp.
Proof.
  intros ([-> | ->] & Hwp & _); unfold rw_word_ready; (split; [lia|split; [lia|]]); [left | right]; reflexivity || (split; [reflexivity | exact Hwp]).
Qed.

(** The word that a reader holds has no flag and counts that reader. *)
Lemma rd_word_held r wp : rw_word_ready r wp -> rd_word r mod 8 = 0 /\ 8 <= rd_word r /\ rd_word r < 2 ^ 31.
Proof.
  unfold rw_word_ready, rd_word. intros (H0 & H8 & [Hm | [Hm _]]); rewrite Hm; cbn;
    Z.div_mod_to_equations; lia.
Qed.

(** After the reader unlocks, the word has no flag and the lock is ready
    again, so any number of translations may follow one another. *)
Lemma rd_word_after r wp : rw_word_ready r wp -> rw_word_ready (rd_word r - 8) (rd_wp r wp).
Proof.
  unfold rw_word_ready, rd_word, rd_wp. intros (H0 & H8 & [Hm | [Hm _]]); rewrite Hm; cbn.
  - split; [lia|]. split; [lia|]. left. replace (r + 8 - 8) with r by lia. exact Hm.
  - split; [Z.div_mod_to_equations; lia|]. split; [lia|]. left. Z.div_mod_to_equations; lia.
Qed.

(** Setlocale may run more than once, so the lock it releases must be
    one it can take again. After a write lock and its unlock, the word
    is 1, the writers futex is 0, and the write-phase futex is 1 or what
    it was before, and that state is idle. *)
Definition wr_wp (r wp : Z) : Z := if r =? 0 then 1 else wp.

Lemma wr_word_after r wp wf : rw_word_idle r wp wf -> rw_word_idle 1 (wr_wp r wp) 0.
Proof.
  unfold rw_word_idle, wr_wp. intros ([-> | ->] & Hwp & _); cbn; lia.
Qed.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** ## The lock's memory

    Each call below reads or writes some of the lock's fields. To chain
    the calls in any order, a caller should hold one resource of the
    same shape before and after every call. So every rule takes and
    gives back all six fields together with a share of the calling
    thread's id. *)

(** Owning the lock at lb means owning its lifetime and the six fields
    that the calls use: the word r, the two futexes wp and wf, the
    writer cw, the shared flag sh and the flags fl. *)
Definition rw_cells (lb : Z) (lreg : region) (r wp wf cw sh fl : Z) : iProp Σ :=
  live lb lreg ∗ int_cell lb 0 r ∗ int_cell lb 8 wp ∗ int_cell lb 12 wf ∗ int_cell lb 24 cw ∗
  int_cell lb 28 sh ∗ int_cell lb 48 fl.

(** A call of a name bound to the captured read lock, on a lock that is
    ready for a reader, returns 0 and leaves the word [rd_word] r. *)
Lemma wp_call_rdlock_ready `{!Defines ge "__GI___pthread_rwlock_rdlock" glibc_pthread_rwlock_rdlock}
    f e ls l d args rest j lk lb lreg tb treg r wp wf cw sh fl dqt dqi tid Φ :
  map_option (arg_x ge e) args = Some [WPtr lk] -> rw_place lk lb lreg tb treg ->
  rw_word_ready r wp -> cw <> tid ->
  rw_cells lb lreg r wp wf cw sh fl ∗ rw_self dqt tb treg dqi tid -∗
  ▷ (rw_cells lb lreg (rd_word r) (rd_wp r wp) wf cw sh fl ∗ rw_self dqt tb treg dqi tid -∗
     WP (ERun (mkFrame f (put d (WInt 0) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d W) (Global (TAtom "__GI___pthread_rwlock_rdlock")) args :: rest) j)) : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hargs (-> & Hlb & Hlal & Hlend & Hlreg & Hself & Htb & Htend & Htreg) Hr Hcw.
  iIntros "[(Hl & Hr & Hwp & Hwf & Hcw & Hsh & Hfl) [Htl Hti]] HK".
  iApply wp_call_bind; [exact Hargs | apply defines | reflexivity |]. iNext.
  destruct Hr as (Hr0 & Hr8 & [Hm | [Hm Hwp0]]).
  - iApply (wp_glibc_rdlock_free Hreg Hext with "Hl Hr Hcw Hfl Htl Hti"); first [reflexivity | eassumption | idtac].
    iNext. iIntros "Hl Hr Hcw Hfl Htl Hti". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
    unfold rd_word, rd_wp. rewrite Hm. cbn. iApply ("HK" with "[$Hl $Hr $Hwp $Hwf $Hcw $Hsh $Hfl $Htl $Hti]").
  - iApply (wp_glibc_rdlock_phase Hreg Hext with "Hl Hr Hwp Hcw Hfl Htl Hti"); first [reflexivity | eassumption | idtac].
    iNext. iIntros "Hl Hr Hwp Hcw Hfl Htl Hti". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
    unfold rd_word, rd_wp. rewrite Hm. cbn. iApply ("HK" with "[$Hl $Hr $Hwp $Hwf $Hcw $Hsh $Hfl $Htl $Hti]").
Qed.

(** A reader that unlocks a word it holds, with no flag set, removes
    itself. *)
Lemma wp_call_rwunlock_held `{!Defines ge "__GI___pthread_rwlock_unlock" glibc_pthread_rwlock_unlock}
    f e ls l d args rest j lk lb lreg tb treg r wp wf cw sh fl dqt dqi tid Φ :
  map_option (arg_x ge e) args = Some [WPtr lk] -> rw_place lk lb lreg tb treg ->
  r mod 8 = 0 -> 8 <= r -> cw <> tid ->
  rw_cells lb lreg r wp wf cw sh fl ∗ rw_self dqt tb treg dqi tid -∗
  ▷ (rw_cells lb lreg (r - 8) wp wf cw sh fl ∗ rw_self dqt tb treg dqi tid -∗
     WP (ERun (mkFrame f (put d (WInt 0) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d W) (Global (TAtom "__GI___pthread_rwlock_unlock")) args :: rest) j)) : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hargs Hp Hr Hr8 Hcw.
  iIntros "[(Hl & Hr & Hwp & Hwf & Hcw & Hsh & Hfl) U] HK".
  iApply (wp_call_glibc_rwunlock Hreg Hext with "[$Hl $Hr $Hcw $Hsh $Hfl $U]"); try eassumption.
  iNext. iIntros "[(Hl & Hr & Hcw & Hsh & Hfl) U]". iApply ("HK" with "[$Hl $Hr $Hwp $Hwf $Hcw $Hsh $Hfl $U]").
Qed.

(** A call of a name bound to the captured write lock, on an idle lock,
    returns 0 and leaves the word 3 with the calling thread as writer. *)
Lemma wp_call_wrlock_idle `{!Defines ge "__GI___pthread_rwlock_wrlock" glibc_pthread_rwlock_wrlock}
    f e ls l d args rest j lk lb lreg tb treg r wp wf cw sh fl dqt dqi tid Φ :
  map_option (arg_x ge e) args = Some [WPtr lk] -> rw_place lk lb lreg tb treg ->
  rw_word_idle r wp wf -> cw <> tid ->
  rw_cells lb lreg r wp wf cw sh fl ∗ rw_self dqt tb treg dqi tid -∗
  ▷ (rw_cells lb lreg 3 (wr_wp r wp) 1 tid sh fl ∗ rw_self dqt tb treg dqi tid -∗
     WP (ERun (mkFrame f (put d (WInt 0) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d W) (Global (TAtom "__GI___pthread_rwlock_wrlock")) args :: rest) j)) : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hargs (-> & Hlb & Hlal & Hlend & Hlreg & Hself & Htb & Htend & Htreg) (Hr & _ & _) Hcw.
  iIntros "[(Hl & Hr & Hwp & Hwf & Hcw & Hsh & Hfl) [Htl Hti]] HK".
  iApply wp_call_bind; [exact Hargs | apply defines | reflexivity |]. iNext.
  iApply (wp_glibc_wrlock_idle Hreg Hext with "Hl Hr Hwp Hwf Hcw Htl Hti"); first [reflexivity | eassumption | idtac].
  iNext. iIntros "Hl Hr Hwp Hwf Hcw Htl Hti". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  iApply ("HK" with "[$Hl $Hr $Hwp $Hwf $Hcw $Hsh $Hfl $Htl $Hti]").
Qed.

(** Setlocale releases the lock it took, and later calls need it idle.
    This rule says the release leaves no writer, the word 1 and the
    writers futex 0. It holds for a lock that prefers readers, as a
    lock with flags 0 does. *)
Lemma wp_call_rwunlock_writer `{!Defines ge "__GI___pthread_rwlock_unlock" glibc_pthread_rwlock_unlock}
    f e ls l d args rest j lk lb lreg tb treg wp wf sh dqt dqi tid Φ :
  map_option (arg_x ge e) args = Some [WPtr lk] -> rw_place lk lb lreg tb treg -> (wf = 0 \/ wf = 1) ->
  rw_cells lb lreg 3 wp wf tid sh 0 ∗ rw_self dqt tb treg dqi tid -∗
  ▷ (rw_cells lb lreg 1 wp 0 0 sh 0 ∗ rw_self dqt tb treg dqi tid -∗
     WP (ERun (mkFrame f (put d (WInt 0) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d W) (Global (TAtom "__GI___pthread_rwlock_unlock")) args :: rest) j)) : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hargs (-> & Hlb & Hlal & Hlend & Hlreg & Hself & Htb & Htend & Htreg) Hwf.
  iIntros "[(Hl & Hr & Hwp & Hwf & Hcw & Hsh & Hfl) [Htl Hti]] HK".
  iApply wp_call_bind; [exact Hargs | apply defines | reflexivity |]. iNext.
  iApply (wp_glibc_rwunlock_write Hreg Hext with "Hl Hr Hwf Hcw Hsh Hfl Htl Hti"); first [reflexivity | eassumption | idtac].
  iNext. iIntros "Hl Hr Hwf Hcw Hsh Hfl Htl Hti". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  iApply ("HK" with "[$Hl $Hr $Hwp $Hwf $Hcw $Hsh $Hfl $Htl $Hti]").
Qed.

End rules.
