From Glibc Require Import Unit_nptl_pthread_rwlock_unlock_os.
From Glibc Require Import GlibcProgram.
(** glibc's `c: pthread_rwlock_unlock` releases a rwlock. The gettext
    lookup releases each read lock it took, so this module proves the
    captured function for a reader that leaves a lock with no writer and
    no waiting thread. Other routes stay outside its contract.

    The function first asks whether the calling thread holds the write
    lock, by comparing the lock's `c: __cur_writer` with the thread's id.
    A reader goes on to read `c: __shared`, which selects the futex kind
    for a later wake, and then subtracts 8 from `c: __readers` with a
    compare-and-swap loop. When the last reader leaves, it clears the
    waiting-readers flag and sets the writer phase if a writer holds the
    lock. It wakes a futex only when the writer phase is set or the
    waiting-readers flag changed.

    The result of an unlock is simple to describe when no other thread
    uses the lock, so the proof asks the caller to show that. The caller
    owns the lock and lends a share of the thread's id. The lock's count
    must hold at least one reader and have all three flags clear. In that
    state neither wake runs, and the count drops by 8 whether or not the
    reader was the last one. The proof covers both values of the shared
    flag. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry FileInv LibioLogic SysWrappers RwunlockCode RdlockLogic.
From Glibc Require FileInv LibioLogic OsThread OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

Ltac self_side := first [apply (reg_of registry Hreg); reflexivity
  | apply (ext_fn ge Hext); cbn; tauto | apply (ext_data ge Hext); cbn; tauto].

Lemma wp_glibc_rwunlock_read fr lb lreg r cw sh tb treg dqt dqi tid Φ :
  call_frame Unit_nptl_pthread_rwlock_unlock_os.fn____pthread_rwlock_unlock [WPtr (mkPtr lb (Obj lb))] = Some fr ->
  ow_self w0 = mkPtr tb (Obj tb) -> 0 < tb -> tb + 724 <= r_end treg -> r_end treg <= 2 ^ 63 ->
  0 < lb -> lb mod 8 = 0 -> lb + 56 <= r_end lreg -> r_end lreg <= 2 ^ 63 ->
  r mod 8 = 0 -> 8 <= r -> cw <> tid ->
  live lb lreg -∗ int_cell lb 0 r -∗ int_cell lb 24 cw -∗ int_cell lb 28 sh -∗
  liveq dqt tb treg -∗ int_cellq dqi tb 720 tid -∗
  ▷ (live lb lreg -∗ int_cell lb 0 (r - 8) -∗ int_cell lb 24 cw -∗ int_cell lb 28 sh -∗
     liveq dqt tb treg -∗ int_cellq dqi tb 720 tid -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hself Htb Htend Htreg Hlb Hlal Hlend Hlreg Hr Hr8 Hcw. injection Hfr as <-.
  iIntros "Hl [%Hr0 Hrb] [%Hcw0 Hcwb] [%Hsh0 Hshb] Htl [%Htid0 Htidb] HK".
  repeat step. check "Hl".
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
  load_bytes_dq "Hl Hshb" decode (apply load_sw_int; exact Hsh0) by ar.
  iNext. iIntros "Hl Hshb". repeat step.
  branch_cases; repeat step.
  all: check "Hl".
  all: load_bytes_dq "Hl Hrb" decode (apply load_uw_int; exact Hr0) by ar.
  all: iNext; iIntros "Hl Hrb"; repeat step.
  all: rewrite (Z.mod_small r); [|lia]; rewrite (Z.mod_small r); [|lia]; change (8 mod 2 ^ 32) with 8;
    change ((3 mod 2 ^ 32) mod 32) with 3; change (0 mod 2 ^ 32) with 0; change (2 ^ 3) with 8;
    rewrite (Z.mod_small (r - 8)); [|lia]; rewrite (Z.mod_small (r - 8)); [|lia];
    rewrite (Z.mod_small ((r - 8) / 8)); [|split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia].
  all: assert (Hm8 : (r - 8) mod 8 = 0) by (Z.div_mod_to_equations; lia).
  all: assert (Hb1 : Z.land (r - 8) 1 = 0) by (apply land_low; [exact Hm8 | reflexivity]).
  all: assert (Hb4 : Z.land (r - 8) 4 = 0) by (apply land_low; [exact Hm8 | reflexivity]).
  all: assert (Hc4 : Z.land r 4 = 0) by (apply land_low; [exact Hr | reflexivity]).
  all: destruct (Z.eqb_spec ((r - 8) / 8) 0) as [Hq | Hq].
  1, 3: assert (E8 : r = 8) by (Z.div_mod_to_equations; lia); subst r; closed_ints; branch; repeat step;
    closed_ints; branch; repeat step.
  all: try (match goal with Hq : _ <> 0 |- _ => closed_ints; branch; repeat step end).
  all: check "Hl".
  all: iApply (wp_raw_cas_w with "Hl Hrb");
      [right; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ar | ar | intros _; wi_store |].
  all: iNext; iIntros "Hl Hrb"; rewrite of_bytes_int; [|lia]; try rw_small r; try rw_small 8; rewrite ?Z.eqb_refl.
  all: repeat step; rewrite ?Z.eqb_refl; closed_ints; branch; repeat step; branch; repeat step.
  all: try rw_small (r - 8); change (1 mod 2 ^ 32) with 1; rewrite ?Hb1; closed_ints; branch; repeat step.
  all: try rw_small (r - 8); try rw_small r; change (4 mod 2 ^ 32) with 4; rewrite ?Hb4 ?Hc4; closed_ints; branch; repeat step.
  all: iApply wp_ret; [reflexivity | reflexivity |]; iNext; closed_ints.
  all: iApply ("HK" with "Hl [Hrb] [Hcwb] [Hshb] Htl [Htidb]");
    [iSplit; [iPureIntro; lia | iExact "Hrb"] | iSplit; [iPureIntro; lia | iExact "Hcwb"] |
     iSplit; [iPureIntro; lia | iExact "Hshb"] | iSplit; [iPureIntro; lia | iExact "Htidb"]].
Qed.

(** A call of a name bound to the captured function by a reader of a
    free lock removes that reader and resumes the caller with 0. *)
Lemma wp_call_glibc_rwunlock `{!Defines ge "__GI___pthread_rwlock_unlock" Unit_nptl_pthread_rwlock_unlock_os.fn____pthread_rwlock_unlock}
    f e ls l d args rest j lk lb lreg tb treg r cw sh fl dqt dqi tid Φ :
  map_option (arg_x ge e) args = Some [WPtr lk] -> rw_place lk lb lreg tb treg ->
  r mod 8 = 0 -> 8 <= r -> cw <> tid ->
  rw_lock lb lreg r cw sh fl ∗ rw_self dqt tb treg dqi tid -∗
  ▷ (rw_lock lb lreg (r - 8) cw sh fl ∗ rw_self dqt tb treg dqi tid -∗
     WP (ERun (mkFrame f (put d (WInt 0) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Call (CResult d W) (Global (TAtom "__GI___pthread_rwlock_unlock")) args :: rest) j)) : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hargs (-> & Hlb & Hlal & Hlend & Hlreg & Hself & Htb & Htend & Htreg) Hr Hr8 Hcw.
  iIntros "[(Hl & Hr & Hcw & Hsh & Hfl) [Htl Hti]] HK".
  iApply wp_call_bind; [exact Hargs | apply defines | reflexivity |]. iNext.
  iApply (wp_glibc_rwunlock_read with "Hl Hr Hcw Hsh Htl Hti"); first [reflexivity | eassumption | idtac].
  iNext. iIntros "Hl Hr Hcw Hsh Htl Hti". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  iApply ("HK" with "[$Hl $Hr $Hcw $Hsh $Hfl $Htl $Hti]").
Qed.
End rules.

(** ## Controls

    These examples check the proof against the captured code. The blocks
    that the proof steps through call only the runtime's thread query,
    while the blocks that wake a futex and the write unlock lie elsewhere. *)

(** This list names the blocks that the proof steps through. *)
Definition un_route : list string :=
  ["start"; "iw_2.start"; "iw_2.iw_1.L3"; "iw_2.iw_1.L4"; "iw_2.L9"; "iw_2.L16"; "iw_2.L24";
   "iw_2.L18"; "iw_2.L42"; "iw_2.L12"; "iw_2.L46"; "L7"].
Example rwunlock_route_calls :
  flat_map (fun l => blk_callees (rw_blk Unit_nptl_pthread_rwlock_unlock_os.fn____pthread_rwlock_unlock l)) un_route = [TAtom "zthread_self_cookie"].
Proof. vm_compute. reflexivity. Qed.
(** The writer-phase wake and the waiting-readers wake call the futex. *)
Example rwunlock_wake_calls :
  blk_callees (rw_blk Unit_nptl_pthread_rwlock_unlock_os.fn____pthread_rwlock_unlock "iw_2.iw_2.L30") = [TAtom "zsys_futex_wake"] /\
  blk_callees (rw_blk Unit_nptl_pthread_rwlock_unlock_os.fn____pthread_rwlock_unlock "iw_2.iw_3.L30") = [TAtom "zsys_futex_wake"].
Proof. vm_compute. split; reflexivity. Qed.
(** The reader route subtracts 8, and the last reader clears the
    waiting-readers flag with the mask ~4. *)
Example rwunlock_steps :
  hd_error (b_insts (rw_blk Unit_nptl_pthread_rwlock_unlock_os.fn____pthread_rwlock_unlock "iw_2.L9")) =
    Some (Let (TAtom "iw_2.v15") W Sub [Tmp (TAtom "iw_2.pr.2"); Const 8]) /\
  b_insts (rw_blk Unit_nptl_pthread_rwlock_unlock_os.fn____pthread_rwlock_unlock "iw_2.L24") =
    [Let (TAtom "iw_2.v32") W And [Tmp (TAtom "iw_2.pr.4"); Const 4294967291]].
Proof. vm_compute. split; reflexivity. Qed.
(** The name that gettext calls is an alias of the captured body. *)
Example rwunlock_alias :
  find_alias (TAtom "__GI___pthread_rwlock_unlock") rwunlock_module = Some (TAtom "___pthread_rwlock_unlock").
Proof. vm_compute. reflexivity. Qed.

(** The contract admits at least one reader with clear flags and rejects
    an empty count and each flag. *)
Definition un_free (r : Z) : bool := (r mod 8 =? 0) && (8 <=? r).
Example un_free_controls :
  map un_free [8; 16; 2 ^ 31 - 8] = [true; true; true] /\ map un_free [0; 9; 10; 12] = [false; false; false; false].
Proof. vm_compute. split; reflexivity. Qed.
