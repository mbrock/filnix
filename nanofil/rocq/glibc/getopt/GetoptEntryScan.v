(** A call of glibc's getopt that has no group of short options in
    progress first sets up its private object and then scans for the next
    argument. The proof of the setup blocks and the proof of the scanner
    were written separately, so their interfaces name the same values in
    different shapes. This file shows that what the setup blocks leave
    behind meets everything the scanner asks for, except the code
    bindings that the caller must still supply. It also shows that the
    scanner leaves the setup's facts about the environment intact, so the
    option parser can still use them after the scan. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Values Memory Runtime Pieces Heap Logic.
From Glibc Require Import FileInv GetoptState GetoptInitialize GetoptExchange GetoptReturn
  GetoptIdlePath GetoptScanEnd GetoptEntry.
Import ListNotations.
Open Scope Z_scope.

(** ## Names the scan must not overwrite

    The setup blocks compute fourteen values that later blocks read: the
    argument count and vector, the option string, the checked pointers
    into the private object, and a few flags. The scanner assigns names
    of its own, and none of them may be one of these fourteen. *)

(** These are the names that the setup's environment fact reads. *)
Definition entry_scan_keys : list name := List.map TAtom
  ["v0"; "v2"; "v6"; "v8"; "v10"; "v12"; "pr.1"; "pr.3"; "chk0"; "chk1"; "chk2"; "chk19"; "chk20"; "v80"]%string.

(** The scanner's tidying path and its decision never assign a name that
    the setup's environment fact reads. *)
Lemma entry_scan_keys_avoid : avoids entry_scan_keys idle_names = true /\ avoids entry_scan_keys scan_end_names = true.
Proof. split; vm_compute; reflexivity. Qed.

(** The scanner does assign the checked pointer chk100, so a caller
    could not carry an older value of it across the scan. *)
Lemma entry_scan_keys_ctl_chk100 : avoids [TAtom "chk100"] scan_end_names = false.
Proof. vm_compute. reflexivity. Qed.

(** ## The scanner's premises after setup

    The scanner may run only if its reads stay inside the argument
    vector and the private object. Its proof therefore asks for the
    index, the waiting block and the vector's size as separate facts.
    The setup proof ends with the same knowledge in another shape, and
    these lemmas convert it while keeping what a later session needs. *)

(** The environment fact contains the six lookups that the scanner
    reads: the argument count, the argument vector, the private object
    and three checked pointers into it. *)
Lemma entry_scan_env e n av p lo li lonly b pe :
  entry_env e n (mkPtr av (Obj av)) p lo li lonly b pe ->
  lookup (TAtom "v0") e = Some (WInt n) /\ lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) /\
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) /\
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) /\
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) /\
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))).
Proof. unfold entry_env. tauto. Qed.

(** A caller may reset the public index to 0 to restart parsing, and
    then the scan starts at 1; otherwise it starts where the caller
    left the index. In both cases the waiting block lies below the
    start, and the start lies at or below the count. The vector's region
    still reaches past its final null pointer. The scanner does not need
    that last fact, but the session after the scan does. The lemma also
    writes the object's state with its set-up flag as 1, which is the
    form that the session lemmas take. *)
Lemma entry_scan_nums n av ar i s' :
  0 <= i -> gs_initialized s' = 1 -> getopt_bounds n (gs_ind s') s' ->
  gs_ind s' = (if i =? 0 then 1 else i) -> av + 8 * (n + 1) <= r_end ar ->
  1 <= n < 2 ^ 31 /\ 1 <= gs_ind s' /\ (i <> 0 -> gs_ind s' = i) /\
  0 <= gs_first s' <= gs_last s' /\ gs_last s' <= n /\ gs_first s' <= gs_ind s' /\ gs_ind s' <= n /\
  av + 8 * n <= r_end ar /\ av + 8 * (n + 1) <= r_end ar /\
  s' = mkGetoptState (gs_ind s') (gs_err s') (gs_opt s') (gs_arg s') 1 (gs_next s') (gs_order s')
         (gs_first s') (gs_last s').
Proof.
  intros Hi Hin Hbd Hix Hav. unfold getopt_bounds in Hbd.
  destruct s' as [x1 x2 x3 x4 x5 x6 x7 x8 x9]; cbn in *. subst x5.
  destruct (Z.eqb_spec i 0); repeat split; first [reflexivity | lia].
Qed.

(** These controls check the start index from both sides. A caller that
    reset the index to 0 over one argument starts the scan at 1, which is
    already the count, and the fresh object's bounds hold there. *)
Lemma entry_scan_ctl_zero :
  gs_ind (init_state (mkGetoptState 0 1 0 null 1 null 0 0 0) 0) = (if 0 =? 0 then 1 else 0) /\
  getopt_bounds 1 1 (init_state (mkGetoptState 0 1 0 null 1 null 0 0 0) 0).
Proof. unfold getopt_bounds. cbn. split; [reflexivity | lia]. Qed.

(** A caller at index 3 of five words keeps index 3, and the waiting block
    from 1 to 2 lies below it, as the scanner requires. *)
Lemma entry_scan_ctl_pos :
  gs_ind (clear_arg (mkGetoptState 3 1 0 null 1 null 1 1 2)) = (if 3 =? 0 then 1 else 3) /\
  getopt_bounds 5 3 (clear_arg (mkGetoptState 3 1 0 null 1 null 1 1 2)).
Proof. unfold getopt_bounds. cbn. split; [reflexivity | lia]. Qed.

(** A waiting block that started after the index would break the order
    that the scanner needs, and the setup's bounds rule it out. *)
Lemma entry_scan_ctl_order : ~ getopt_bounds 5 1 (mkGetoptState 1 1 0 null 1 null 1 2 3).
Proof. unfold getopt_bounds. cbn. lia. Qed.

(** The scanner's bound on the vector is weaker than the session's. A
    two-word vector at 8 in a region ending at 24 meets the first but not
    the second, so the bridge keeps the session's bound separately. *)
Lemma entry_scan_ctl_sentinel : 8 + 8 * 2 <= 24 /\ ~ (8 + 8 * (2 + 1) <= 24).
Proof. lia. Qed.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptEntryScanOn (R : Runtime) (LG0 : LogicSig R).
(** The exchange module supplies the private fields and the kept-name relation. *)
Module X := GetoptExchangeOn R LG0.
Import X X.I X.I.S X.I.S.FI X.I.S.FI.ML X.I.S.FI.LG X.I.S.FI.L.

(** The scanner hands back a later environment that agrees with the old
    one on every kept name. When the kept names include the setup's
    fourteen, the setup's environment fact holds again afterwards, with
    the same values. *)
Lemma entry_env_keeps ks e e' n av p lo li lonly b pe :
  keeps ks e e' -> incl entry_scan_keys ks ->
  entry_env e n av p lo li lonly b pe -> entry_env e' n av p lo li lonly b pe.
Proof.
  intros Hk Hin Henv.
  assert (Hl : forall k, In k entry_scan_keys -> lookup k e' = lookup k e)
    by (intros k Hk'; exact (keeps_in ks k e e' Hk (Hin k Hk'))).
  unfold entry_env in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; (rewrite Hl; [assumption | unfold entry_scan_keys; cbn [List.map In]; intuition congruence]).
Qed.

Section entry_scan.
Context `{!gen_heapGS piece pval Σ}.

(** The scanner owns six of the object's nine fields while it runs, and
    the caller keeps the other four for the session after the scan. The
    setup leaves the argument field null and the set-up flag at 1. This
    lemma splits the fields that the setup hands over into the two
    groups, in the shapes that the scanner and the session lemmas use. *)
Lemma entry_scan_cells b r s' :
  gs_initialized s' = 1 -> gs_arg s' = null ->
  live b r -∗ int_cell b 0 (gs_ind s') -∗ int_cell b 4 (gs_err s') -∗ int_cell b 8 (gs_opt s') -∗
  pcell b 16 (gs_arg s') -∗ int_cell b 24 (gs_initialized s') -∗ pcell b 32 (gs_next s') -∗
  int_cell b 40 (gs_order s') -∗ int_cell b 44 (gs_first s') -∗ int_cell b 48 (gs_last s') -∗
  (live b r ∗ int_cell b 0 (gs_ind s') ∗ pcell b 16 null ∗ int_cell b 40 (gs_order s') ∗
     int_cell b 44 (gs_first s') ∗ int_cell b 48 (gs_last s')) ∗
  (int_cell b 4 (gs_err s') ∗ int_cell b 8 (gs_opt s') ∗ int_cell b 24 1 ∗ pcell b 32 (gs_next s')).
Proof.
  intros Hin Ha. rewrite Hin Ha.
  iIntros "Hl Hi He Ho Ha Hn Hc Hr Hf Hla". iFrame.
Qed.

End entry_scan.
End GetoptEntryScanOn.
