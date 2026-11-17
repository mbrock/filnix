From Glibc Require Import GlibcProgram.
(** glibc's `c: pthread_rwlock_rdlock` takes a read lock on a rwlock.
    The gettext lookup takes three such locks around its search, so a
    proof of a translation must know what this call does. This module
    proves the captured function on the route that a lock with no writer
    and no waiting thread takes, and leaves every other route outside its
    contract.

    The lock's word `c: __readers` counts readers in its upper bits and
    keeps three flags in its low three bits: the writer phase, a held
    write lock and waiting readers. The function first compares the
    lock's `c: __cur_writer` with the calling thread's id, which it reads
    from the thread descriptor that `c: zthread_self_cookie` returns.
    Then it tests `c: __flags` for writer preference, adds 8 to the
    reader count with a compare-and-swap loop, rejects a count that
    reaches 2^31, and returns 0 when the writer phase is off.

    A read lock is easy to state only when no other thread is using the
    lock, so the proof asks the caller to show that. The caller owns the
    lock, its count has all three flags clear and room for one more
    reader, and the calling thread does not hold the write lock. The
    caller also lends a share of the thread's id. Under these conditions
    the writer-preference loop exits at once, so the proof covers both
    answers of that test. A held write lock, a writer phase, a full count
    and every wait on a futex stay outside the contract. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry FileInv LibioLogic SysWrappers RdlockCode.
From Glibc Require FileInv LibioLogic OsThread OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Ltac rw_small x := repeat (rewrite (Z.mod_small x (2 ^ 32)); [|lia]).

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

Ltac self_side := first [apply (reg_of registry Hreg); reflexivity
  | apply (ext_fn ge Hext); cbn; tauto | apply (ext_data ge Hext); cbn; tauto].

Lemma load_uw_int x : 0 <= x < 2 ^ 32 -> extended Uw W (of_bytes (le_bytes x 4)) = Some (WInt x).
Proof using Type*. intros Hx. rewrite of_bytes_int; [|exact Hx]. cbn. f_equal. f_equal. rewrite !Z.mod_small; lia. Qed.

Lemma land_low r m : r mod 8 = 0 -> Z.land 7 m = m -> Z.land r m = 0.
Proof using Type*.
  intros H Hm. rewrite <- Hm. rewrite Z.land_assoc. change 7 with (Z.ones 3). rewrite Z.land_ones; [|lia].
  change (2 ^ 3) with 8. rewrite H. apply Z.land_0_l.
Qed.

Lemma wp_glibc_rdlock_free fr lb lreg r cw fl tb treg dqt dqi tid Φ :
  call_frame glibc_pthread_rwlock_rdlock [WPtr (mkPtr lb (Obj lb))] = Some fr ->
  ow_self w0 = mkPtr tb (Obj tb) -> 0 < tb -> tb + 724 <= r_end treg -> r_end treg <= 2 ^ 63 ->
  0 < lb -> lb mod 8 = 0 -> lb + 56 <= r_end lreg -> r_end lreg <= 2 ^ 63 ->
  r mod 8 = 0 -> r + 8 < 2 ^ 31 -> cw <> tid ->
  live lb lreg -∗ int_cell lb 0 r -∗ int_cell lb 24 cw -∗ int_cell lb 48 fl -∗
  liveq dqt tb treg -∗ int_cellq dqi tb 720 tid -∗
  ▷ (live lb lreg -∗ int_cell lb 0 (r + 8) -∗ int_cell lb 24 cw -∗ int_cell lb 48 fl -∗
     liveq dqt tb treg -∗ int_cellq dqi tb 720 tid -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hself Htb Htend Htreg Hlb Hlal Hlend Hlreg Hr Hr8 Hcw. injection Hfr as <-.
  iIntros "Hl [%Hr0 Hrb] [%Hcw0 Hcwb] [%Hfl0 Hflb] Htl [%Htid0 Htidb] HK".
  repeat step. closed_ints. branch. repeat step. closed_ints. branch. repeat step.
  check "Hl".
  load_bytes_dq "Hl Hcwb" decode (apply load_sw_int; exact Hcw0) by ar.
  iNext. iIntros "Hl Hcwb".
  iApply (OsThread.wp_zthread_self_cookie); try self_side; [rewrite Hself; cbn; lia|]. iNext. rewrite Hself.
  repeat step. norm.
  check_read_dq "Htl" by ar. iNext. iIntros "Htl".
  load_bytes_dq "Htl Htidb" decode (apply load_sw_int; exact Htid0) by ar.
  iNext. iIntros "Htl Htidb".
  repeat step. rewrite (Z.mod_small cw); [|lia]. rewrite (Z.mod_small tid); [|lia].
  rewrite (proj2 (Z.eqb_neq cw tid) Hcw). closed_ints. branch. repeat step.
  check "Hl".
  load_bytes_dq "Hl Hflb" decode (apply load_uw_int; exact Hfl0) by ar.
  iNext. iIntros "Hl Hflb". repeat step.
  assert (Hb1 : Z.land r 1 = 0) by (apply land_low; [exact Hr | reflexivity]).
  assert (Hb2 : Z.land r 2 = 0) by (apply land_low; [exact Hr | reflexivity]).
  assert (Hr8m : (r + 8) mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (Hodd : Z.land (r + 8) 1 = 0) by (apply land_low; [exact Hr8m | reflexivity]).
  branch_cases; [|
    repeat step; check "Hl";
    load_bytes_dq "Hl Hrb" decode (apply load_uw_int; exact Hr0) by ar;
    iNext; iIntros "Hl Hrb"; repeat step; rw_small r; change (1 mod 2 ^ 32) with 1; rewrite Hb1; closed_ints;
    branch; repeat step; rw_small r; change (2 mod 2 ^ 32) with 2; rewrite Hb2; closed_ints; branch; repeat step;
    closed_ints; branch; repeat step].
  all: repeat step; check "Hl".
  all: load_bytes_dq "Hl Hrb" decode (apply load_uw_int; exact Hr0) by ar.
  all: iNext; iIntros "Hl Hrb"; repeat step; check "Hl".
  all: iApply (wp_raw_cas_w with "Hl Hrb");
      [right; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ar | ar | intros _; wi_store |].
  all: iNext; iIntros "Hl Hrb"; rewrite of_bytes_int; [|lia]; rw_small r; rewrite Z.eqb_refl.
  all: repeat step; rewrite ?Z.eqb_refl; closed_ints; branch; repeat step; rw_small (r + 8).
  all: rewrite (proj2 (Z.leb_gt 2147483648 (r + 8)) ltac:(lia)); closed_ints; branch; repeat step.
  all: rw_small (r + 8); change (1 mod 2 ^ 32) with 1; rewrite Hodd; closed_ints; branch; repeat step.
  all: iApply wp_ret; [reflexivity | reflexivity |]; iNext; closed_ints.
  all: iApply ("HK" with "Hl [Hrb] [Hcwb] [Hflb] Htl [Htidb]");
    [iSplit; [iPureIntro; lia | iExact "Hrb"] | iSplit; [iPureIntro; lia | iExact "Hcwb"] |
     iSplit; [iPureIntro; lia | iExact "Hflb"] | iSplit; [iPureIntro; lia | iExact "Htidb"]].
Qed.


(** ## The call

    A caller holds the lock through these resources. The lock is an
    object of 56 bytes at lb, and the rule reads four of its fields. The
    thread's id lies 720 bytes into the descriptor that the runtime
    returns for the calling thread. *)

(** This resource owns the lock fields that the two functions read or
    write. *)
Definition rw_lock (lb : Z) (lreg : region) (r cw sh fl : Z) : iProp Σ :=
  live lb lreg ∗ int_cell lb 0 r ∗ int_cell lb 24 cw ∗ int_cell lb 28 sh ∗ int_cell lb 48 fl.
(** This resource holds a share of the calling thread's id. *)
Definition rw_self (dqt : dfrac) (tb : Z) (treg : region) (dqi : dfrac) (tid : Z) : iProp Σ :=
  liveq dqt tb treg ∗ int_cellq dqi tb 720 tid.
(** The lock pointer names the start of object lb, and the descriptor is
    the runtime's answer for the calling thread. Both objects fit in
    their regions. *)
Definition rw_place (lk : ptr) (lb : Z) (lreg : region) (tb : Z) (treg : region) : Prop :=
  lk = mkPtr lb (Obj lb) /\ 0 < lb /\ lb mod 8 = 0 /\ lb + 56 <= r_end lreg /\ r_end lreg <= 2 ^ 63 /\
  ow_self w0 = mkPtr tb (Obj tb) /\ 0 < tb /\ tb + 724 <= r_end treg /\ r_end treg <= 2 ^ 63.

(** A call of a name bound to the captured function with a free lock
    adds one reader and resumes the caller with 0. *)
Lemma wp_call_glibc_rdlock `{!Defines ge "__GI___pthread_rwlock_rdlock" glibc_pthread_rwlock_rdlock}
    f e ls l d args rest j lk lb lreg tb treg r cw sh fl dqt dqi tid Φ :
  map_option (arg_x ge e) args = Some [WPtr lk] -> rw_place lk lb lreg tb treg ->
  r mod 8 = 0 -> r + 8 < 2 ^ 31 -> cw <> tid ->
  rw_lock lb lreg r cw sh fl ∗ rw_self dqt tb treg dqi tid -∗
  ▷ (rw_lock lb lreg (r + 8) cw sh fl ∗ rw_self dqt tb treg dqi tid -∗
     WP (ERun (mkFrame f (put d (WInt 0) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d W) (Global (TAtom "__GI___pthread_rwlock_rdlock")) args :: rest) j)) : sexpr) {{ Φ }}.
Proof.
  intros Hargs (-> & Hlb & Hlal & Hlend & Hlreg & Hself & Htb & Htend & Htreg) Hr Hr8 Hcw.
  iIntros "[(Hl & Hr & Hcw & Hsh & Hfl) [Htl Hti]] HK".
  iApply wp_call_bind; [exact Hargs | apply defines | reflexivity |]. iNext.
  iApply (wp_glibc_rdlock_free with "Hl Hr Hcw Hfl Htl Hti"); first [reflexivity | eassumption | idtac].
  iNext. iIntros "Hl Hr Hcw Hfl Htl Hti". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  iApply ("HK" with "[$Hl $Hr $Hcw $Hsh $Hfl $Htl $Hti]").
Qed.
End rules.

(** ## Controls

    These examples check the proof's route against the captured code.
    The route calls only the runtime's thread query, while the blocks it
    avoids wait on or wake a futex. *)

(** This definition finds the block named l of a function. *)
Definition rw_blk (fn : func) (l : string) : block :=
  match find_block (TAtom l) (fn_blocks fn) with Some b => b | None => mkBlock (TAtom l) [] [] JUnreachable end.
(** This definition lists the globals that a block calls. *)
Definition blk_callees (b : block) : list name :=
  flat_map (fun i => match i with Call _ (Global s) _ | RawCall _ (Global s) _ => [s] | _ => [] end) (b_insts b).
(** This definition gives the value that a block's first phi takes from
    the block named l. *)
Definition phi_from (b : block) (l : string) : option value :=
  match b_phis b with
  | Phi _ _ ps :: _ => option_map snd (find (fun p => name_eqb (fst p) (TAtom l)) ps)
  | [] => None
  end.

(** This list names the blocks that the proof steps through. *)
Definition rd_route : list string :=
  ["start"; "iw_1.L14"; "iw_1.L9"; "iw_1.L35"; "iw_1.L46"; "iw_1.L55"; "iw_1.L61"; "iw_1.L62"; "iw_1.L69";
   "iw_1.L48"; "iw_1.L119"; "iw_1.L127"; "iw_1.L129"; "iw_1.join"].
Example rdlock_route_calls :
  flat_map (fun l => blk_callees (rw_blk glibc_pthread_rwlock_rdlock l)) rd_route = [TAtom "zthread_self_cookie"].
Proof. vm_compute. reflexivity. Qed.
(** The blocks that wait for a writer and wake waiters call the futex. *)
Example rdlock_wait_calls :
  blk_callees (rw_blk glibc_pthread_rwlock_rdlock "iw_1.iw_3.L4") = [TAtom "__GI___futex_abstimed_wait64"] /\
  blk_callees (rw_blk glibc_pthread_rwlock_rdlock "iw_1.iw_5.L30") = [TAtom "zsys_futex_wake"].
Proof. vm_compute. split; reflexivity. Qed.
(** The function returns 35 when the thread holds the write lock, 11
    when the count overflows, and 0 from the route's last test. *)
Example rdlock_results :
  phi_from (rw_blk glibc_pthread_rwlock_rdlock "iw_1.join") "iw_1.L9" = Some (Const 35) /\
  phi_from (rw_blk glibc_pthread_rwlock_rdlock "iw_1.join") "iw_1.L148" = Some (Const 11) /\
  phi_from (rw_blk glibc_pthread_rwlock_rdlock "iw_1.join") "iw_1.L129" = Some (Const 0).
Proof. vm_compute. repeat split. Qed.
(** The overflow test compares the new count with 2^31 without sign. *)
Example rdlock_overflow_test :
  b_insts (rw_blk glibc_pthread_rwlock_rdlock "iw_1.L127") =
    [Let (TAtom "iw_1.v134") W (Cmp Uge W) [Tmp (TAtom "iw_1.pr.1"); Const 2147483648]].
Proof. vm_compute. reflexivity. Qed.
(** The name that gettext calls is an alias of the captured body. *)
Example rdlock_alias : find_alias (TAtom "__GI___pthread_rwlock_rdlock") rdlock_module = Some (TAtom "___pthread_rwlock_rdlock").
Proof. vm_compute. reflexivity. Qed.

(** The contract admits a count with clear flags below the overflow
    bound and rejects each flag and the bound itself. A count of
    2^32 - 8 is rejected too, although the code's 32-bit sum would wrap
    to 0 and pass its own test. *)
Definition rd_free (r : Z) : bool := (r mod 8 =? 0) && (r + 8 <? 2 ^ 31).
Example rd_free_controls :
  map rd_free [0; 8; 2 ^ 31 - 16] = [true; true; true] /\
  map rd_free [1; 2; 4; 2 ^ 31 - 8; 2 ^ 32 - 8] = [false; false; false; false; false].
Proof. vm_compute. split; reflexivity. Qed.
