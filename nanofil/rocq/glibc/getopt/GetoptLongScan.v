From Glibc Require Import GlibcProgram.
(** A long option such as "--name=value" names its option before an
    equals sign, or before the end of the argument. glibc's long-option
    parser first measures that name. It walks a pointer from its private
    cursor until it reaches an equals sign or the terminator, and then
    computes the name's length as the distance from the cursor. This
    file proves that walk safe: it reads the cursor's string only up to
    the byte where it stops, and it writes nothing. *)

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
  GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor GetoptDiag GetoptReqTail.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptReqTail GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The name of a long option ends before its first equals sign, which
    is the byte 61, or at the end of the string. *)
Fixpoint eq_len (s : list Z) : nat :=
  match s with [] => O | c :: t => if c =? 61 then O else S (eq_len t) end.

(** The name lies inside its string. *)
Lemma eq_len_le s : (eq_len s <= List.length s)%nat.
Proof. induction s as [|c t IH]; cbn; [lia|]. destruct (c =? 61); lia. Qed.

(** Every byte of the name is neither the terminator nor an equals sign. *)
Lemma eq_len_go s j : Forall (fun c => 0 < c < 256) s -> (j < eq_len s)%nat -> sbyte s j <> 0 /\ sbyte s j <> 61.
Proof.
  revert j. induction s as [|c t IH]; intros j Hf Hj; cbn in Hj; [lia|].
  destruct (Z.eqb_spec c 61); [lia|]. apply Forall_cons_1 in Hf as [Hc Hf].
  destruct j as [|j]; unfold sbyte in *; cbn [app nth]; [lia|]. apply IH; [exact Hf | lia].
Qed.

(** The byte after the name is the terminator or an equals sign. *)
Lemma eq_len_stop s : sbyte s (eq_len s) = 0 \/ sbyte s (eq_len s) = 61.
Proof.
  induction s as [|c t IH]; [left; reflexivity|]. cbn [eq_len].
  destruct (Z.eqb_spec c 61) as [E | E]; unfold sbyte in *; cbn [app nth]; [right; exact E | exact IH].
Qed.

(** A walk that stops at a byte that ends the name stops at its end. *)
Lemma eq_len_at s j : Forall (fun c => 0 < c < 256) s -> (j <= eq_len s)%nat ->
  sbyte s j = 0 \/ sbyte s j = 61 -> j = eq_len s.
Proof.
  intros Hf Hj Hs. destruct (Nat.lt_ge_cases j (eq_len s)) as [Hlt | Hge]; [|lia].
  pose proof (eq_len_go s j Hf Hlt). lia.
Qed.

(** The name scan assigns these names. *)
Definition scan_names : list name := Eval vm_compute in
  List.map TAtom ["v25"; "chk0"; "v26"; "pr.1"; "chk1"; "v32"; "v36"; "v37"; "v39"; "v41"; "v44";
    "chk3"; "v45"; "v46"; "v47"; "v48"]%string.

(** This definition looks up a block of the long-option parser by its label. *)
Definition plo_blk (l : string) : block := Eval vm_compute in
  match find_block (TAtom l) (fn_blocks glibc_process_long_option) with
  | Some b => b | None => mkBlock (TAtom l) [] [] JUnreachable end.
(** The walk's test starts in this block. *)
Definition plo_blk27 : block := Eval vm_compute in plo_blk "L27".


(** The tail module supplies the string lemmas, a shared renewed read and the tactics. *)
Import GetoptReqTail GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

(** This tactic enters a block and evaluates its phi assignments. *)


Import ProgramAbbreviations.
Section scan.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the parser's safepoints. *)
Local Instance scan_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A read half check of a pointer into a shared object needs only a
    share of that object's lifetime. *)
Lemma wp_half_check_read_dq f e ls l d bd lo hi al args rest j classes p1 p b reg dq Φ :
  op_arg_classes (HalfCheck bd lo hi Read al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p1; WPtr p] ->
  ptr_cap p1 = ptr_cap p -> ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  b <= raw_address (ptr_addr p) lo -> raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg ->
  lo < hi -> r_end reg <= 2 ^ 63 -> raw_address (ptr_addr p) lo mod al = 0 ->
  liveq dq b reg -∗
  ▷ (liveq dq b reg -∗ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (HalfCheck bd lo hi Read al) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp1 Hp H1 H2 H3 H4 H5. apply (wp_read_dq registry (os_wi w0) ge dq _ _ _ []).
  intros m fuel (Hf & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E Lv] _].
  apply rule_let with (classes := classes) (xs := [WPtr p1; WPtr p]); [reflexivity | exact Hc | exact Hx |].
  exact (op_half_check_read _ _ _ _ _ _ _ _ _ Hp1 Hp E Lv H1 H2 H3 H4 H5).
Qed.

(** At the end of the name, the walk reads the cursor again and stores
    the name's length as the distance between the two pointers. *)
Lemma wp_long_scan_end ks e0 e fr cur s b r Φ :
  avoids ks scan_names = true -> keeps ks e0 e ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "pr.1") e = Some (WPtr (ptr_add cur (Z.of_nat (eq_len s)))) ->
  lookup (TAtom "chk1") e = Some (WPtr (ptr_add cur (Z.of_nat (eq_len s)))) ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  word_string DfracDiscarded cur s -∗ live b r -∗ pcell b 32 cur -∗
  (∀ e', ⌜keeps ks e0 e' /\ lookup (TAtom "pr.1") e' = Some (WPtr (ptr_add cur (Z.of_nat (eq_len s)))) /\
       lookup (TAtom "v48") e' = Some (WInt (Z.of_nat (eq_len s))) /\
       lookup (TAtom "chk0") e' = Some (WPtr (mkPtr (b + 32) (Obj b))) /\
       lookup (TAtom "chk1") e' = Some (WPtr (ptr_add cur (Z.of_nat (eq_len s))))⌝ -∗
     live b r -∗ pcell b 32 cur -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L50") (Some (TAtom "L30")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L30") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hk0 H12 Hc0 Hp1 Hc1 Hb Hal Hend Hr. iIntros "#Hws Hl Hcur HK".
  iDestruct (ws_shape with "Hws") as %(Hch & Hqp & Hqe).
  iDestruct (argv_str_cap with "Hws") as (rq) "[#Hcapq %Hq0]".
  pose proof (eq_len_le s) as Hle.
  step. step. check "Hl".
  load_pointer_dq "Hl Hcur Hcapq" by arith.
  iNext. iIntros "Hl Hcur _". step. step. step. step.
  iApply ("HK" with "[%] Hl Hcur"). split; [xkeep|].
  split; [lk_prove|]. split; [|split; lk_prove].
  match goal with |- lookup _ (put _ (WInt ?X) _) = _ => replace X with (Z.of_nat (eq_len s)); [lk_prove|] end.
  rewrite (Z.mod_small (ptr_addr cur + _)); [|lia]. rewrite (Z.mod_small (ptr_addr cur)); [|lia].
  rewrite Z.mod_small; lia.
Qed.

(** The walk stands j bytes into the name of the string s at the cursor
    cur. It reads one byte at a time and stops at the end of the name.
    Then it stores the name's length, measured from the cursor that it
    reads again. The names ks keep their values from the caller's
    environment e. *)
Lemma wp_long_scan_loop ks e (j : nat) cur s b r Φ :
  avoids ks scan_names = true ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "pr.1") e = Some (WPtr (ptr_add cur (Z.of_nat j))) ->
  (j <= eq_len s)%nat -> 0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  word_string DfracDiscarded cur s -∗ live b r -∗ pcell b 32 cur -∗
  (∀ e', ⌜keeps ks e e' /\ lookup (TAtom "pr.1") e' = Some (WPtr (ptr_add cur (Z.of_nat (eq_len s)))) /\
       lookup (TAtom "v48") e' = Some (WInt (Z.of_nat (eq_len s))) /\
       lookup (TAtom "chk0") e' = Some (WPtr (mkPtr (b + 32) (Obj b))) /\
       lookup (TAtom "chk1") e' = Some (WPtr (ptr_add cur (Z.of_nat (eq_len s))))⌝ -∗
     live b r -∗ pcell b 32 cur -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L50") (Some (TAtom "L30")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None
              (Exec (TAtom "L27") (b_insts plo_blk27) (b_jump plo_blk27))) : gexpr) {{ Φ }}.
Proof.
  intros Hks. remember (eq_len s - j)%nat as m eqn:Hm. revert e j Hm.
  induction m as [m IH] using (well_founded_induction lt_wf).
  intros e j Hm H12 Hc0 Hp1 Hj Hb Hal Hend Hr. iIntros "#Hws Hl Hcur HK".
  iDestruct (ws_shape with "Hws") as %(Hch & Hqp & Hqe).
  iDestruct (argv_str_cap with "Hws") as (rq) "[#Hcapq %Hq0]".
  pose proof (eq_len_le s) as Hle. pose proof (sbyte_range s j Hch) as Hxr.
  cbn [b_insts b_jump plo_blk27].
  iDestruct (ws_byte cur s j with "Hws") as (bb breg) "(%Hbb & #Hbl & #Hbt)"; [lia|].
  destruct Hbb as (Hcap & ? & ? & ? & ?).
  check_read_dq "Hbl" by rawa; iNext; iIntros "_".
  load_bytes_dq "Hbl Hbt" decode (apply extended_chr) by rawa.
  iNext; iIntros "_ _".
  iApply wp_branch; [vx | iNext].
  rewrite (Z.mod_small (chr_w _) (2 ^ 32)); [|apply chr_w_range]. rewrite chr_w_eqb; [|lia|lia].
  destruct (Z.eqb_spec (sbyte s j) 0) as [E0 | E0]; cbn [edge_label].
  { step. iApply wp_branch; [vx | iNext]. close_br.
    assert (Hje : j = eq_len s) by (apply eq_len_at; auto). subst j.
    iApply (wp_long_scan_end ks e with "Hws Hl Hcur HK");
      [exact Hks | xkeep | lk_prove | lk_prove | lk_prove | lk_prove | exact Hb | exact Hal | exact Hend | exact Hr]. }
  step.
  load_bytes_dq "Hbl Hbt" decode (apply extended_chr) by rawa.
  iNext; iIntros "_ _". step. step. step. iApply wp_branch; [vx | iNext].
  rewrite (Z.mod_small (chr_w _) (2 ^ 32)); [|apply chr_w_range]. change (61 mod 2 ^ 32) with 61.
  rewrite chr_w_eqb; [|lia|lia].
  destruct (Z.eqb_spec (sbyte s j) 61) as [E61 | E61]; first [close_br | cbn [edge_label]].
  { assert (Hje : j = eq_len s) by (apply eq_len_at; auto). subst j.
    iApply (wp_long_scan_end ks e with "Hws Hl Hcur HK");
      [exact Hks | xkeep | lk_prove | lk_prove | lk_prove | lk_prove | exact Hb | exact Hal | exact Hend | exact Hr]. }
  assert (Hlt : (j < eq_len s)%nat).
  { destruct (Nat.lt_ge_cases j (eq_len s)) as [Hq | Hq]; [exact Hq|].
    assert (j = eq_len s) as -> by lia. destruct (eq_len_stop s); lia. }
  step. step. step. iApply wp_enter; [reflexivity | reflexivity | iNext].
  iApply (IH (eq_len s - S j)%nat ltac:(lia) _ (S j) eq_refl with "Hws Hl Hcur [HK]");
    [lk_prove | lk_prove | | lia | exact Hb | exact Hal | exact Hend | exact Hr |].
  { match goal with |- lookup _ (put _ (WPtr ?X) _) = _ => replace X with (ptr_add cur (Z.of_nat (S j))); [lk_prove|] end.
    unfold ptr_add; cbn [ptr_addr ptr_cap]. f_equal. rewrite !(Z.mod_small _ (2 ^ 64)); lia. }
  iIntros (e' (Hk' & Hq1 & Hq2 & Hq3 & Hq4)) "Hl Hcur". iApply ("HK" with "[%] Hl Hcur").
  split; [eapply keeps_trans; [|exact Hk']; xkeep | auto].
Qed.

(** On entry the parser reads its private cursor cur, which points into
    the shared string s, and measures the name there. Its private state
    at d is unchanged. *)
Lemma wp_getopt_long_scan ks e cur s b r Φ :
  avoids ks scan_names = true ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  word_string DfracDiscarded cur s -∗ live b r -∗ pcell b 32 cur -∗
  (∀ e', ⌜keeps ks e e' /\ lookup (TAtom "pr.1") e' = Some (WPtr (ptr_add cur (Z.of_nat (eq_len s)))) /\
       lookup (TAtom "v48") e' = Some (WInt (Z.of_nat (eq_len s))) /\
       lookup (TAtom "chk0") e' = Some (WPtr (mkPtr (b + 32) (Obj b))) /\
       lookup (TAtom "chk1") e' = Some (WPtr (ptr_add cur (Z.of_nat (eq_len s))))⌝ -∗
     live b r -∗ pcell b 32 cur -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L50") (Some (TAtom "L30")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hks H12 Hb Hal Hend Hr. iIntros "#Hws Hl Hcur HK".
  iDestruct (argv_str_cap with "Hws") as (rq) "[#Hcapq %Hq0]".
  step. step. norm. check "Hl".
  load_pointer_dq "Hl Hcur Hcapq" by arith.
  iNext. iIntros "Hl Hcur _". step. iApply wp_enter; [reflexivity | reflexivity | iNext].
  iApply (wp_long_scan_loop ks _ 0 with "Hws Hl Hcur [HK]");
    [exact Hks | lk_prove | lk_prove | | lia | exact Hb | exact Hal | exact Hend | exact Hr |].
  { replace (ptr_add cur (Z.of_nat 0)) with cur; [lk_prove|]. destruct cur; unfold ptr_add; cbn; f_equal; lia. }
  iIntros (e' (Hk' & Hq1 & Hq2 & Hq3 & Hq4)) "Hl Hcur". iApply ("HK" with "[%] Hl Hcur").
  split; [eapply keeps_trans; [|exact Hk']; xkeep | auto].
Qed.

End scan.
