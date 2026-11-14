(** Before glibc's scanner parses an option argument, it stores the
    private cursor, which points into the argument just after its dashes.
    A cluster of short options and a long-only option store a cursor one
    byte in. This file proves those two stores safe: each block reads
    argument i only below the argument count and writes only the cursor
    field of the scanner's own state. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString GetoptModule GetoptState GetoptBytes
  GetoptInitialize GetoptEntry GetoptArgv GetoptExchange.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptExchange GetoptInitialize GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The short-option cursor block assigns these names. *)
Definition short_names : list name := Eval vm_compute in
  List.map TAtom ["v441"; "chk131"; "v444"; "v445"; "v446"; "v447"; "chk132"; "v448"; "v449"; "chk133"]%string.

(** The long-only cursor block assigns these names. *)
Definition long_cursor_names : list name := Eval vm_compute in
  List.map TAtom ["v413"; "chk128"; "v416"; "v417"; "v418"; "v419"; "chk129"; "v420"; "v421"; "chk130"]%string.

(** A long-only option with one dash calls the long-option parser here. *)
Definition long_only_call : list inst := Eval vm_compute in skipn 11 (b_insts (x_blk "L376")).
(** The jump after that call tests its result. *)
Definition long_only_jump : jump := Eval vm_compute in b_jump (x_blk "L376").

(** A byte that is not zero lies inside its string. *)
Lemma sbyte_in_len (s : list Z) k : sbyte s k <> 0 -> (k < List.length s)%nat.
Proof.
  unfold sbyte. intros H. destruct (Nat.lt_ge_cases k (List.length s)) as [Hk|Hk]; [exact Hk|].
  rewrite app_nth2 in H; [|exact Hk]. destruct (k - List.length s)%nat as [|m]; cbn in H; [congruence|].
  destruct m; cbn in H; congruence.
Qed.


(** The exchange module supplies the argument vector and its tactics. *)
Import GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

(** This tactic enters a block and evaluates its phi assignments. *)


(** This tactic loads an owned private integer field as a signed 32-bit value. *)


Section cursor.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance cursor_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance cursor_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A cluster of short options starts after the single dash. The block
    reads argument i, below the argument count n, and stores the private
    cursor one byte into it. *)
Lemma wp_getopt_short_cursor ks e fr i n c b r av ar ps Φ :
  avoids ks short_names = true ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  0 <= i < n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 i -∗ pcell b 32 c -∗ live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  (∀ e', ⌜keeps ks e e'⌝ -∗
     live b r -∗ int_cell b 0 i -∗ pcell b 32 (ptr_add (nth (Z.to_nat i) ps null) 1) -∗
     live av ar -∗ argv_cells av ps -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L75") (Some (TAtom "L338")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L338") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hv2 Hv12 Hc2 Hc20 Hi Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra.
  iIntros "Hl [%Hi0 Hib] Hcur Ha Hc #Hs HK".
  set (j := Z.to_nat i). assert (Hj : Z.of_nat j = i) by (unfold j; lia).
  destruct (lookup_lt_is_Some_2 ps j) as [q Hq]; [lia|].
  iDestruct (big_sepL_lookup with "Hs") as (s) "#Hws"; [exact Hq|].
  iDestruct (argv_str_cap with "Hws") as (rq) "[#Hcapq %Hq0]".
  iDestruct (ws_shape with "Hws") as %(Hch & Hqp & Hqe).
  step. step. check "Hl". load_s32_using ltac:(arith) "Hl Hib". step. step. step. idx i. check "Ha".
  iDestruct (big_sepL_lookup_acc with "Hc") as "[Hcj Hc]"; [exact Hq|].
  iApply (wp_raw_load_pointer_dq with "Ha Hcj Hcapq"); [reflexivity | vx | left; reflexivity | arith | arith | lia |].
  iNext. iIntros "Ha Hcj _". iSpecialize ("Hc" with "Hcj"). step. check "Hl".
  iApply (wp_raw_store_pointer with "Hl Hcur"); [vx | vx | reflexivity | arith | arith | wi_store |].
  iNext. iIntros "Hl Hcur".
  assert (Ha1 : (ptr_addr q mod 2 ^ 64 + 1 mod 2 ^ 64) mod 2 ^ 64 = ptr_addr q + 1)
    by (rewrite !(Z.mod_small _ (2 ^ 64)); lia).
  rewrite Ha1. step.
  iApply ("HK" with "[%] Hl [Hib] [Hcur] Ha Hc"); [xkeep | by iSplit |].
  unfold j in Hq. by rewrite (nth_lookup_Some _ _ _ _ Hq).
Qed.

(** A long-only option starts after the single dash too. The block stores
    the same cursor and stops just before it calls the long-option
    parser. *)
Lemma wp_getopt_long_cursor ks e fr i n c b r av ar ps Φ :
  avoids ks long_cursor_names = true ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  0 <= i < n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 i -∗ pcell b 32 c -∗ live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗
  (∀ e', ⌜keeps ks e e'⌝ -∗
     live b r -∗ int_cell b 0 i -∗ pcell b 32 (ptr_add (nth (Z.to_nat i) ps null) 1) -∗
     live av ar -∗ argv_cells av ps -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Exec (TAtom "L376") long_only_call long_only_jump))
           : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L376") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hv2 Hv12 Hc2 Hc20 Hi Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra.
  iIntros "Hl [%Hi0 Hib] Hcur Ha Hc #Hs HK".
  set (j := Z.to_nat i). assert (Hj : Z.of_nat j = i) by (unfold j; lia).
  destruct (lookup_lt_is_Some_2 ps j) as [q Hq]; [lia|].
  iDestruct (big_sepL_lookup with "Hs") as (s) "#Hws"; [exact Hq|].
  iDestruct (argv_str_cap with "Hws") as (rq) "[#Hcapq %Hq0]".
  iDestruct (ws_shape with "Hws") as %(Hch & Hqp & Hqe).
  step. step. check "Hl". load_s32_using ltac:(arith) "Hl Hib". step. step. step. idx i. check "Ha".
  iDestruct (big_sepL_lookup_acc with "Hc") as "[Hcj Hc]"; [exact Hq|].
  iApply (wp_raw_load_pointer_dq with "Ha Hcj Hcapq"); [reflexivity | vx | left; reflexivity | arith | arith | lia |].
  iNext. iIntros "Ha Hcj _". iSpecialize ("Hc" with "Hcj"). step. check "Hl".
  iApply (wp_raw_store_pointer with "Hl Hcur"); [vx | vx | reflexivity | arith | arith | wi_store |].
  iNext. iIntros "Hl Hcur".
  assert (Ha1 : (ptr_addr q mod 2 ^ 64 + 1 mod 2 ^ 64) mod 2 ^ 64 = ptr_addr q + 1)
    by (rewrite !(Z.mod_small _ (2 ^ 64)); lia).
  rewrite Ha1.
  iApply ("HK" with "[%] Hl [Hib] [Hcur] Ha Hc"); [xkeep | by iSplit |].
  unfold j in Hq. by rewrite (nth_lookup_Some _ _ _ _ Hq).
Qed.

End cursor.
