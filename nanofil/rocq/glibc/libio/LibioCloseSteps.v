(** What the proofs of the close, flush and exit path share
    (LibioUnlink.v to ExitRun.v): checks at a share of an object's
    life, as the read-only jump tables and `c: __libc_single_threaded`
    are owned (LibioLogic.v's [wp_check_read_dq]); the bounds every live object has
    ([wp_live_fit]); a stream's life, opened from FileInv.v's
    [file_inv] and closed again ([file_inv_live]); the cleanup buffer
    a fresh allocation holds ([obj32]); and the step tactics.

    Each is stated over the [os_world] of [OsWorld](../zsys/OsWorld.v),
    as the triples of SysWrappers.v are. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode FileInv LibioLogic SysWrappers.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** ## Rule application

    As stdlib/LeavesLogic.v does: a step rule applied as a plain
    entailment, not by [iApply] and [iNext], whose proof-mode searches
    cost most of a step. *)

(** Apply a step rule ⊢ ▷ P -∗ Q to the goal Q, leaving P. *)
Lemma step_wand {PROP : bi} (Δ : environments.envs PROP) (P Q : PROP) :
  (⊢ ▷ P -∗ Q) -> environments.envs_entails Δ P -> environments.envs_entails Δ Q.
Proof.
  rewrite environments.envs_entails_unseal. intros HW HΔ. etrans; [exact HΔ|].
  iIntros "H". iApply HW. iNext. iExact "H".
Qed.

(** Apply a step rule R -∗ ▷ (R' -∗ P) -∗ Q, over one resource, to
    the goal R -∗ Q, leaving R' -∗ P. *)
Lemma step_res1 {PROP : bi} (Δ : environments.envs PROP) (R R' P Q : PROP) :
  (⊢ R -∗ ▷ (R' -∗ P) -∗ Q) -> environments.envs_entails Δ (R' -∗ P) -> environments.envs_entails Δ (R -∗ Q).
Proof.
  rewrite environments.envs_entails_unseal. intros HW HΔ. etrans; [exact HΔ|].
  iIntros "H HR". iApply (HW with "HR"). iNext. iExact "H".
Qed.

(** [step_res1] over two resources. *)
Lemma step_res2 {PROP : bi} (Δ : environments.envs PROP) (R1 R2 R1' R2' P Q : PROP) :
  (⊢ R1 -∗ R2 -∗ ▷ (R1' -∗ R2' -∗ P) -∗ Q) ->
  environments.envs_entails Δ (R1' -∗ R2' -∗ P) -> environments.envs_entails Δ (R1 -∗ R2 -∗ Q).
Proof.
  rewrite environments.envs_entails_unseal. intros HW HΔ. etrans; [exact HΔ|].
  iIntros "H HR1 HR2". iApply (HW with "HR1 HR2"). iNext. iExact "H".
Qed.

(** [step_res1] over three resources. *)
Lemma step_res3 {PROP : bi} (Δ : environments.envs PROP) (R1 R2 R3 R1' R2' R3' P Q : PROP) :
  (⊢ R1 -∗ R2 -∗ R3 -∗ ▷ (R1' -∗ R2' -∗ R3' -∗ P) -∗ Q) ->
  environments.envs_entails Δ (R1' -∗ R2' -∗ R3' -∗ P) -> environments.envs_entails Δ (R1 -∗ R2 -∗ R3 -∗ Q).
Proof.
  rewrite environments.envs_entails_unseal. intros HW HΔ. etrans; [exact HΔ|].
  iIntros "H HR1 HR2 HR3". iApply (HW with "HR1 HR2 HR3"). iNext. iExact "H".
Qed.

(** Apply a rule over the resource H by the tactic t. *)
Ltac rule1 H t := iRevert H; eapply step_res1; [t |]; iIntros H.

(** Apply a rule over the resources H1 and H2 by the tactic t. *)
Ltac rule2 H1 H2 t := iRevert H2; iRevert H1; eapply step_res2; [t |]; iIntros H1; iIntros H2.

(** Apply a rule over the resources H1, H2 and H3 by the tactic t. *)
Ltac rule3 H1 H2 H3 t :=
  iRevert H3; iRevert H2; iRevert H1; eapply step_res3; [t |]; iIntros H1; iIntros H2; iIntros H3.

(** Drop each wrap to 64 or 32 bits of the goal that arithmetic shows
    the identity, as LibioLogic.v's [unwrap], without clearing
    hypotheses first. *)
Ltac unwrap2 :=
  repeat match goal with
    | |- context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2 ^ 64)); [|lia]
    | |- context [?x mod 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616); [|lia]
    | |- context [?x mod 2 ^ 32] => rewrite (Z.mod_small x (2 ^ 32)); [|lia]
    | |- context [?x mod 4294967296] => rewrite (Z.mod_small x 4294967296); [|lia]
    end.

(** The rules over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioCloseStepsOn (R : Runtime) (LG0 : LogicSig R).
Module SW := SysWrappersOn R LG0.
Import SW SW.FI.ML SW.FI.LG SW.FI.L SW.OW SW.FI SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance steps_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Every live object lies in the address space from 0 to 2^48
    (Runtime.v's [objects_fit]): owning its life at any share shows
    it, before a step. *)
Lemma wp_live_fit dq b reg fr Φ :
  liveq dq b reg -∗
  (⌜0 <= b /\ r_end reg <= 2 ^ 48⌝ -∗ liveq dq b reg -∗ WP (ERun fr : sexpr) {{ Φ }}) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  iIntros "Hl HK". rewrite !wp_unfold /wp_pre /=. iIntros (σ ns κ κs nt) "Hσ".
  iDestruct (ptsq_facts with "Hσ Hl") as %(Hag & _ & Hfit).
  cbn [all_agree agree_piece fst snd] in Hag. destruct Hag as [[Hreg _] _].
  destruct (Hfit b reg Hreg) as [H0 H48].
  iSpecialize ("HK" with "[%] Hl"); [lia|]. iApply ("HK" $! σ ns κ κs nt with "Hσ").
Qed.

(** [wp_live_fit] for a whole life token. *)
Lemma wp_live_fit1 b reg fr Φ :
  live b reg -∗
  (⌜0 <= b /\ r_end reg <= 2 ^ 48⌝ -∗ live b reg -∗ WP (ERun fr : sexpr) {{ Φ }}) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  iIntros "Hl HK". rewrite /live pts_ptsq. iApply (wp_live_fit with "Hl").
  iIntros (H) "Hl". rewrite -pts_ptsq. iApply ("HK" with "[//] Hl").
Qed.

(** [wp_raw_load_pointer] of a null pointer, whose capability needs
    no life. *)
Lemma wp_raw_load_null f e ls l d off args rest j classes p b reg o Φ :
  op_arg_classes (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) P = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o -> (b + o) mod 8 = 0 ->
  live b reg -∗ pcell b o null -∗
  ▷ (live b reg -∗ pcell b o null -∗
     WP (ERun (mkFrame f (put d (WPtr null) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec l (Let d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) args :: rest) j))
       : sexpr) {{ Φ }}.
Proof.
  iIntros (Hc Hx Hp Ha Hal) "Hl Hc HK".
  iApply (wp_raw_load_pointer with "Hl Hc [//]");
    [exact Hc | exact Hx | exact Hp | exact Ha | exact Hal | cbn; lia |].
  iNext. iIntros "Hl Hc _". iApply ("HK" with "Hl Hc").
  Unshelve. exact reg.
Qed.

End rules.

Section streams.
Context `{!gen_heapGS piece pval Σ}.

(** A stream's life, from its [file_inv], and the stream back from it:
    the stream is the 224-byte object gb, 8-aligned. *)
Lemma file_inv_live vb self g :
  file_inv vb self g ⊢
  ∃ gb greg, ⌜g = mkPtr gb (Obj gb) /\ 0 < gb /\ gb mod 8 = 0 /\ gb + file_size <= r_end greg /\
              r_end greg <= 2 ^ 63⌝ ∗ live gb greg ∗ (live gb greg -∗ file_inv vb self g).
Proof.
  iIntros "(%fb & %freg & %st & %nb & %vt & %held & %Hp & Hl & Hrest)".
  destruct Hp as (-> & Hal & Hfb & Hend & Hreg & Hp).
  iExists fb, freg. iFrame "Hl". iSplit; [iPureIntro; repeat split; assumption|]. iIntros "Hl".
  iExists fb, freg, st, nb, vt, held. iFrame. iPureIntro. exact (conj eq_refl (conj Hal (conj Hfb (conj Hend (conj Hreg Hp))))).
Qed.

(** Eight zero bytes and an empty slot are a null pointer's cell. *)
Lemma byte_ps_cell0 b o : byte_ps b o (replicate 8 0) = cell b o 0.
Proof. unfold byte_ps, cell, seqZ. rewrite Nat2Z.id. simpl. repeat (f_equal; try lia; try reflexivity). Qed.

(** A null pointer's cell, from an empty slot and eight zero bytes. *)
Lemma pcell_null_of b o : auxes b o [CNone] ∗ bytes b o (replicate 8 0) ⊢ pcell b o null.
Proof.
  rewrite /bytes byte_ps_cell0 /auxes /pcell /aux_ps /pts. cbn -[cell]. unfold seqZ. simpl. rewrite ?Z.add_0_l.
  iIntros "[[$ _] $]".
Qed.

(** A fresh 32-byte heap object, as libio's
    `c: _IO_cleanup_region_start_noarg` allocates its
    `c: struct _pthread_cleanup_buffer`: its life, the null pointers
    at 0 (`c: __routine`), 8 (`c: __arg`) and 24 (`c: __prev`), and
    the four zero bytes of `c: __canceltype` at 16. *)
Lemma obj32 b : obj b (heap_req 8 32) ⊢
  live b (mkRegion b (b + 32) Heap Live) ∗ pcell b 0 null ∗ pcell b 8 null ∗ bytes b 16 [0; 0; 0; 0] ∗
  pcell b 24 null.
Proof.
  rewrite obj_zero_block; [|vm_compute; congruence]. cbn [req_extent req_kind heap_req].
  replace ((32 + 15) / 16 * 16) with 32 by reflexivity.
  change (replicate (Z.to_nat 32) 0) with
    (replicate 8 0 ++ replicate 8 0 ++ ([0; 0; 0; 0] ++ [0; 0; 0; 0]) ++ replicate 8 0)%list.
  change (replicate (Z.to_nat 32) CNone) with
    ([CNone] ++ replicate 7 CNone ++ [CNone] ++ replicate 7 CNone ++ replicate 8 CNone ++ [CNone] ++
     replicate 7 CNone)%list.
  rewrite !bytes_app !auxes_app. cbn [length replicate].
  iIntros "($ & (H0 & H8 & (H16 & _) & H24) & (A0 & _ & A8 & _ & _ & A24 & _))".
  iSplitL "H0 A0"; [iApply pcell_null_of; iFrame|].
  iSplitL "H8 A8"; [iApply pcell_null_of; iFrame|].
  iSplitL "H16"; [iFrame|]. iApply pcell_null_of. iFrame.
Qed.

End streams.

(** ## Step tactics *)

(** A signed 32-bit load of an [int_cell]'s bytes, its life and bytes
    in H. *)
Ltac ldi H :=
  iApply (wp_raw_load_sub_bytes_dq with H);
    [reflexivity | vx | reflexivity | apply load_sw_int; assumption | left; reflexivity | ar |];
  iNext; iIntros H.

(** A one-byte load, its life and byte in H, at any shares. *)
Ltac ldb H :=
  iApply (wp_raw_load_sub_bytes_dq with H);
    [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | ar |];
  iNext; iIntros H.

(** A 32-bit store over the four bytes in H. *)
Ltac sti H :=
  iApply (wp_raw_store_w with H); [vx | vx | reflexivity | ar | reflexivity | wi_store |];
  iNext; iIntros H.

(** A pointer load, the base's life, the cell and the loaded
    capability's life in H. *)
Ltac ldp H :=
  iApply (wp_raw_load_pointer with H); [reflexivity | vx | reflexivity | ar | ar | cbn; lia |];
  iNext; iIntros H.

(** A pointer store, the base's life and the cell in H. *)
Ltac stp H :=
  iApply (wp_raw_store_pointer with H); [vx | vx | reflexivity | ar | ar | wi_store |];
  iNext; iIntros H.

(** A read check at a share of the object's life H. *)
Ltac chkq H :=
  iApply (wp_check_read_dq with H);
    [reflexivity | vx | first [left; reflexivity | right; reflexivity] | ar | ar | ar |];
  iNext; iIntros H.

(** [ldb] and [chkq] of persistent shares, handed back to the
    persistent context. *)
Ltac ldbp H :=
  iApply (wp_raw_load_sub_bytes_dq with H);
    [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | ar |];
  iNext; iIntros "_ _".
Ltac chkp H :=
  iApply (wp_check_read_dq with H);
    [reflexivity | vx | first [left; reflexivity | right; reflexivity] | ar | ar | ar |];
  iNext; iIntros "_".

(** Close the instance premise a rule's eapply leaves. *)
Ltac inst := lazymatch goal with |- SafepointStable _ => exact _ | _ => idtac end.

(** An address fact about FileInv.v's offsets, by arithmetic, as
    LibioLogic.v's [ar] without clearing hypotheses. *)
Ltac a2 := unfold off_cleanup, off_cleanup_jmp, off_cancelhandling, off_lk_lock, off_lk_cnt, off_lk_owner,
  off_flags, off_read_ptr, off_write_base, off_write_ptr, off_write_end, off_buf_base, off_buf_end,
  off_chain, off_fileno, off_flags2, off_lock, off_wide, off_prevchain, off_mode, off_vtable, off_ptr,
  off_old_offset, off_column, off_shortbuf, off_offset, off_codecvt, off_freeres_list, off_freeres_buf,
  off_total_written, vt_file, vt_wfile, slot_finish, slot_overflow, slot_xsputn, slot_doallocate, slot_write,
  slot_close, slot_stat;
  cbn [ptr_addr ptr_cap]; unfold raw_address; rewrite ?Z.add_0_r; unwrap2;
  first [lia | apply Z.mod_1_r | Z.div_mod_to_equations; lia].

(** One step whose premises reduce, applied as an entailment: a pure
    let, a flight, entering a block, or a goto. *)
Ltac fs :=
  let a := at_of in
  lazymatch a with
  | Exec _ (Let _ _ _ _ :: _) _ =>
      eapply step_wand; [eapply wp_let; inst; [reflexivity | reflexivity | vx | intros ?; cbn; reflexivity] |]
  | Exec _ (Flight _ _ _ _ :: _) _ => eapply step_wand; [eapply wp_flight; inst; [vx | reflexivity | vx] |]
  | Enter _ _ => eapply step_wand; [eapply wp_enter; inst; [reflexivity | vx] |]; cbn [b_insts b_jump]
  | Exec _ [] (JGoto _) => eapply step_wand; [eapply wp_goto; inst |]
  end.

(** A branch on a closed condition, computed. *)
Ltac fbr :=
  eapply step_wand; [eapply wp_branch; inst; vx |];
  lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
    let c' := vm_of c in change c with c' end; cbn [edge_label].

(** A branch whose condition is b, by [decide_ints]. *)
Ltac fbrv b :=
  eapply step_wand; [eapply wp_branch; inst; vx |];
  lazymatch goal with |- context [edge_label (if ?n =? 0 then _ else _)] =>
    let E := fresh "E" in assert (E : (n =? 0) = b) by decide_ints; rewrite E; clear E end;
  cbn [edge_label].

(** A check, half check or renew, over the object's life H. *)
Ltac fchk H :=
  let a := at_of in
  lazymatch a with
  | Exec _ (Let _ _ (Check _ _ _ _) _ :: _) _ =>
      rule1 H ltac:(eapply wp_check; inst; [reflexivity | vx | reflexivity | a2 | a2 | a2])
  | Exec _ (Let _ _ (HalfCheck _ _ _ _ _) _ :: _) _ =>
      rule1 H ltac:(eapply wp_half_check; inst; [reflexivity | vx | reflexivity | reflexivity | a2 | a2 | lia | a2 | a2])
  | Exec _ (Let _ _ (Renew _ _ _ _) _ :: _) _ =>
      rule1 H ltac:(eapply wp_renew; inst; [reflexivity | vx | reflexivity | reflexivity | a2 | a2 | a2])
  end.

(** A signed 32-bit load of an [int_cell]'s bytes Hb, the life Hl. *)
Ltac fldi Hl Hb :=
  rule2 Hl Hb ltac:(eapply wp_raw_load_sub_bytes_dq; inst;
    [reflexivity | vx | reflexivity | apply load_sw_int; assumption | left; reflexivity | a2]).

(** A 32-bit store over the four bytes Hb, the life Hl. *)
Ltac fsti Hl Hb :=
  rule2 Hl Hb ltac:(eapply wp_raw_store_w; inst; [vx | vx | reflexivity | a2 | reflexivity | wi_store]).

(** A pointer load: the base's life Hl, the cell Hc and the loaded
    capability's life Hk. *)
Ltac fldp Hl Hc Hk :=
  iRevert Hk; iRevert Hc; iRevert Hl;
  lazymatch goal with |- environments.envs_entails _ (_ -∗ pcell _ _ ?pv -∗ _) =>
    eapply step_res3; [eapply wp_raw_load_pointer with (x := pv); inst;
                       [reflexivity | vx | reflexivity | a2 | a2 | cbn; lia] |] end;
  iIntros Hl; iIntros Hc; iIntros Hk.

(** A load of a null pointer: the base's life Hl and the cell Hc. *)
Ltac fldn Hl Hc :=
  rule2 Hl Hc ltac:(eapply wp_raw_load_null; inst; [reflexivity | vx | reflexivity | a2 | a2]).

(** A pointer store: the base's life Hl and the cell Hc. *)
Ltac fstp Hl Hc :=
  rule2 Hl Hc ltac:(eapply wp_raw_store_pointer; inst; [vx | vx | reflexivity | a2 | a2 | wi_store]).

(** A side premise of a block lemma: a hypothesis, a lookup through
    the environment's [put]s, or arithmetic. *)
Ltac side := first [eassumption | lk_prove | unfold file_size; lia].

(** The rest of a caller after a callee's triple: resume it. *)
Ltac resume := iExists _; iSplit; [iPureIntro; reflexivity|]; iNext; cbn [fr_fn fr_env fr_locals fr_doomed fr_at].

End LibioCloseStepsOn.
