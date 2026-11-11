(** What the libio proofs share (SysWrappers.v, LibioRead.v): a store
    keeps OsWorld.v's [os_wi] when it writes back only the life token
    the program owned ([os_wi_store_life]), the lists of pieces that
    hold no life token ([no_life]), and the tactics that keep a
    symbolic run's addresses small.

    A store rule of Logic.v or MemLogic.v asks that the store keep the
    world interpretation, given that the old pieces, the object's life
    token first, are in the ghost heap: [os_wi_store] gives it when
    every life token written is the one the heap holds, and the new
    pieces of a store are the same life token and pieces with none
    ([wi_store]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From iris.program_logic Require Import language weakestpre.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  Pieces Heap Language Logic StringLogic MemLogic StepRules ExternalCalls ExternalMachine.
From Nanofil Require WordBits Symbolic.
From Glibc Require Import OsBlocks OsWorld FileInv.
Import ListNotations.
Open Scope Z_scope.

(** ## Pieces with no life token *)

(** No piece of ps is a life token. *)
Definition no_life (ps : list (piece * pval)) : Prop :=
  forall l v, (l, v) ∈ ps -> match l with PLive _ => False | _ => True end.

(** A long's cell has none. *)
Lemma no_life_cell b o x : no_life (cell b o x).
Proof.
  intros l v Hin. unfold cell in Hin. cbn in Hin.
  repeat (apply elem_of_cons in Hin as [Hin|Hin]; [injection Hin as -> _; exact I|]).
  by apply not_elem_of_nil in Hin.
Qed.

(** Bytes have none. *)
Lemma no_life_byte_ps b o xs : no_life (byte_ps b o xs).
Proof. intros l v Hin. apply byte_ps_elem in Hin as (i & x & _ & -> & _). exact I. Qed.

(** A pointer's cell, its aux slot and its bytes, has none. *)
Lemma no_life_pcell b o c a : no_life ((PAux b o, VAux c) :: cell b o a).
Proof.
  intros l v Hin. apply elem_of_cons in Hin as [[= -> _] | Hin]; [exact I|]. exact (no_life_cell _ _ _ _ _ Hin).
Qed.

(** One byte has none. *)
Lemma no_life_byte b o x : no_life [(PByte b o, VByte x)].
Proof. intros l v Hin. apply list_elem_of_singleton in Hin. injection Hin as -> _. exact I. Qed.

(** A store into the object b that keeps every region, whose new
    pieces are b's life token, as owned, and pieces with no life
    token, keeps [os_wi]. *)
Lemma os_wi_store_life w0 b reg ps ps' m m' wd h :
  m_regions m' = m_regions m -> no_life ps' ->
  (forall l v, (l, v) ∈ (PLive b, VLive reg) :: ps -> h !! l = Some v) -> os_wi w0 m wd h ->
  os_wi w0 m' wd (overwrite ((PLive b, VLive reg) :: ps') h).
Proof.
  intros Er Hn Hh Hw. apply (os_wi_store w0 m m' wd h); [exact Er | | exact Hw].
  intros l v Hin. apply elem_of_cons in Hin as [[= -> ->] | Hin].
  - apply Hh. left.
  - pose proof (Hn l v Hin) as H. destruct l; [contradiction | exact I | exact I | exact I].
Qed.

(** The premise of a store rule over [os_wi]: by [os_wi_store_life]. *)
Ltac wi_store :=
  let Hh := fresh "Hh" in let Hw := fresh "Hw" in
  intros ? ? ? Hh Hw; eapply os_wi_store_life; [reflexivity | | exact Hh | exact Hw];
  first [apply no_life_cell | apply no_life_byte_ps | apply no_life_pcell | apply no_life_byte].

(** ## A `c: int`'s bytes *)

(** The four bytes of an int below 2^32 read back as it. *)
Lemma of_bytes_int x : 0 <= x < 2 ^ 32 -> of_bytes (le_bytes x 4) = x.
Proof.
  intros Hx. transitivity (x mod 2 ^ (8 * (3 + 1))); [| apply Z.mod_small; exact Hx].
  rewrite WordBits.low_step; [|lia]. change (8 * 3) with (8 * (2 + 1)).
  rewrite WordBits.low_step; [|lia]. change (8 * 2) with (8 * (1 + 1)).
  rewrite WordBits.low_step; [|lia]. change (8 * 1) with (8 * (0 + 1)).
  rewrite WordBits.low_step; [|lia]. rewrite Z.mul_0_r Z.pow_0_r Z.mod_1_r. cbn -[byte_of].
  change (Z.of_nat 0) with 0. change (Z.of_nat 1) with 1. change (Z.of_nat 2) with 2. change (Z.of_nat 3) with 3. lia.
Qed.

(** A signed 32-bit load of an int's bytes, at class [W], is its bits. *)
Lemma load_sw_int x : 0 <= x < 2 ^ 32 -> extended Sw W (of_bytes (le_bytes x 4)) = Some (WInt x).
Proof.
  intros Hx. rewrite of_bytes_int; [|exact Hx]. cbn. f_equal. f_equal. unfold sign_extension.
  rewrite (Z.mod_small x); [|exact Hx]. destruct (2 ^ 31 <=? x) eqn:E.
  - apply Z.leb_le in E. rewrite Zminus_mod Z_mod_same_full Z.sub_0_r !Z.mod_mod; [|lia..].
    apply Z.mod_small. exact Hx.
  - apply Z.mod_small. exact Hx.
Qed.

(** A mask of a nonnegative integer by a 32-bit one is a 32-bit int. *)
Lemma land_lt32 a b : 0 <= a -> 0 <= b < 2 ^ 32 -> 0 <= Z.land a b < 2 ^ 32.
Proof.
  intros Ha Hb. split; [apply Z.land_nonneg; lia|].
  assert (Hl : Z.log2 b < 32).
  { destruct (Z.eq_dec b 0) as [->|Hne]; [reflexivity|]. apply Z.log2_lt_pow2; lia. }
  rewrite <- (Z.land_ones_low b 32); [|lia | exact Hl]. rewrite Z.land_assoc Z.land_ones; [|lia].
  apply Z.mod_pos_bound. lia.
Qed.

(** A test of bit k, below 24, of the 24-bit field `c: _flags2`: the
    4 bytes as loaded, sign-extended by a shift left and an arithmetic
    shift right by 8, then masked by M, 2^k, read bit k of the bytes.
    `c: _IO_ferror` tests `c: _IO_FLAGS2_NEED_LOCK` (bit 7) this way,
    `c: _IO_new_file_write` `c: _IO_FLAGS2_NOTCANCEL` (bit 1). *)
Lemma flags2_mask f2 M k : M = 2 ^ k -> 0 <= k < 24 -> 0 <= f2 < 2 ^ 32 ->
  Z.land (((sign_extension (2 ^ 32) (2 ^ 31)
              (((f2 mod 2 ^ 32 * 2 ^ ((8 mod 2 ^ 32) mod 32)) mod 2 ^ 32) mod 2 ^ 32) /
            2 ^ ((8 mod 2 ^ 32) mod 32)) mod 2 ^ 32) mod 2 ^ 32) (M mod 2 ^ 32) = Z.land f2 M.
Proof.
  intros -> Hk H. change ((8 mod 2 ^ 32) mod 32) with 8.
  rewrite (Z.mod_small (2 ^ k)); [|split; [lia | apply Z.pow_lt_mono_r; lia]].
  rewrite (Z.mod_small f2); [|lia..]. rewrite !Z.mod_mod; [|lia..].
  apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.eq_dec i k) as [->|Hne].
  - f_equal. rewrite Z.mod_pow2_bits_low; [|lia..].
    rewrite Z.div_pow2_bits; [|lia..]. unfold sign_extension. rewrite Z.mod_mod; [|lia..].
    assert (Hl : forall l, 0 <= l < 2 ^ 32 -> Z.testbit (l - 2 ^ 32) (k + 8) = Z.testbit l (k + 8)).
    { intros l Hl. rewrite <- (Z.mod_pow2_bits_low (l - 2 ^ 32) 32 (k + 8)); [|lia..].
      f_equal. rewrite Zminus_mod Z_mod_same_full Z.sub_0_r !Z.mod_mod; [|lia..]. apply Z.mod_small. exact Hl. }
    assert (Hb : 0 <= (f2 * 2 ^ 8) mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
    assert (Hm : Z.testbit ((f2 * 2 ^ 8) mod 2 ^ 32) (k + 8) = Z.testbit f2 k).
    { rewrite (Z.mod_pow2_bits_low _ 32 (k + 8)); [|lia]. rewrite (Z.mul_pow2_bits f2 8 (k + 8)); [|lia].
      f_equal. lia. }
    destruct (2 ^ 31 <=? _).
    + rewrite (Hl _ Hb). exact Hm.
    + exact Hm.
  - rewrite Z.pow2_bits_false; [|lia..]. rewrite !andb_false_r. reflexivity.
Qed.

(** The bitwise or of two 32-bit ints is one. *)
Lemma lor_lt32 a b : 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> 0 <= Z.lor a b < 2 ^ 32.
Proof.
  intros Ha Hb. assert (Hn : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
  split; [exact Hn|]. destruct (Z.eq_dec (Z.lor a b) 0) as [E|E]; [rewrite E; lia|].
  apply Z.log2_lt_pow2; [lia|]. rewrite Z.log2_lor; [|lia..].
  assert (Z.log2 a < 32) by (destruct (Z.eq_dec a 0) as [->|]; [reflexivity | apply Z.log2_lt_pow2; lia]).
  assert (Z.log2 b < 32) by (destruct (Z.eq_dec b 0) as [->|]; [reflexivity | apply Z.log2_lt_pow2; lia]).
  lia.
Qed.

(** `c: _IO_ferror`'s test of `c: _IO_FLAGS2_NEED_LOCK`: [flags2_mask]
    at bit 7. *)
Lemma flags2_bit7 f2 : 0 <= f2 < 2 ^ 32 ->
  Z.land (((sign_extension (2 ^ 32) (2 ^ 31)
              (((f2 mod 2 ^ 32 * 2 ^ ((8 mod 2 ^ 32) mod 32)) mod 2 ^ 32) mod 2 ^ 32) /
            2 ^ ((8 mod 2 ^ 32) mod 32)) mod 2 ^ 32) mod 2 ^ 32) (128 mod 2 ^ 32) = Z.land f2 128.
Proof. apply (flags2_mask f2 128 7); [reflexivity | lia]. Qed.

(** ## Arithmetic *)

(** Keep only arithmetic hypotheses, so lia does not read the rest. *)
Ltac clear_junk :=
  repeat match goal with
    H : ?T |- _ =>
      lazymatch T with
      | @eq Z _ _ => fail | Z.le _ _ => fail | Z.lt _ _ => fail | and (Z.le _ _) _ => fail
      | and (Z.lt _ _) _ => fail | not (@eq Z _ _) => fail
      | _ => clear H
      end
    end.

(** Drop each wrap to 64 or 32 bits of the goal that arithmetic shows
    the identity. *)
Ltac unwrap :=
  repeat match goal with
    | |- context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2 ^ 64)); [|clear_junk; lia]
    | |- context [?x mod 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616); [|clear_junk; lia]
    | |- context [?x mod 2 ^ 32] => rewrite (Z.mod_small x (2 ^ 32)); [|clear_junk; lia]
    | |- context [?x mod 4294967296] => rewrite (Z.mod_small x 4294967296); [|clear_junk; lia]
    end.

(** An address or integer fact, by arithmetic. *)
Ltac arith := cbn [ptr_addr ptr_cap]; unfold raw_address; unwrap; clear_junk;
  first [lia | Z.div_mod_to_equations; lia].

(** An address fact about FileInv.v's offsets, by arithmetic. *)
Ltac ar := unfold off_cleanup, off_cleanup_jmp, off_cancelhandling, off_lk_lock, off_lk_cnt, off_lk_owner,
  off_flags, off_read_ptr, off_write_base, off_write_ptr, off_write_end, off_buf_base, off_buf_end,
  off_chain, off_fileno, off_flags2, off_lock, off_wide, off_prevchain, off_mode, off_vtable, off_ptr,
  off_old_offset, off_column, off_shortbuf, off_offset, off_codecvt, off_freeres_list, off_freeres_buf,
  off_total_written, vt_file, vt_wfile, slot_finish, slot_overflow, slot_xsputn, slot_doallocate, slot_write,
  slot_close, slot_stat; arith.

(** Write each address of the goal's environment without wraps. *)
Ltac norm := cbn [ptr_addr ptr_cap]; unwrap.

(** The term X has a variable in it. *)
Ltac has_var X := match X with context [?v] => is_var v end.

(** Compute each closed integer of the goal's words: a value glibc
    computes from constants, such as a flag test of a field known to
    be 0, becomes its numeral. *)
Ltac closed_ints :=
  repeat match goal with
    |- context [WInt ?X] =>
      tryif has_var X then fail else
      let v := eval vm_compute in X in tryif constr_eq X v then fail else change X with v
    end.

(** The term X holds no integer test. *)
Ltac innermost X :=
  lazymatch X with context [_ =? _] => fail | context [_ <? _] => fail | context [_ <=? _] => fail | _ => idtac end.

(** Decide a goal of integer tests, such as a branch condition, by
    a case on each test and arithmetic. *)
Ltac decide_ints :=
  unfold sign_extension, vt_file, vt_wfile; cbv zeta; unwrap;
  repeat match goal with
    | |- context [?x =? ?y] => innermost x; innermost y; destruct (Z.eqb_spec x y); cbn [negb andb orb]
    | |- context [?x <? ?y] => innermost x; innermost y; destruct (Z.ltb_spec x y); cbn [negb andb orb]
    | |- context [?x <=? ?y] => innermost x; innermost y; destruct (Z.leb_spec x y); cbn [negb andb orb]
    end;
  first [reflexivity | exfalso; clear_junk; first [lia | Z.div_mod_to_equations; lia]].

(** ## Values of an environment with an unknown tail *)

(** A value premise of a step, such as `c: map2_option (value_x ge e)
    classes args = Some xs`: computed when e is known; when e is a
    run of [put]s over an unknown env, as at a loop's head, each
    [lookup] is taken through the [put]s ([Symbolic.lookup_after_put])
    and, past them, from a hypothesis `c: lookup k e = Some x`. *)
(** A lookup past a [put] of another name. *)
Lemma lookup_put_miss {A : Type} k k' (v : A) e r :
  name_eqb k k' = false -> lookup k e = r -> lookup k (put k' v e) = r.
Proof. intros H <-. apply Symbolic.lookup_after_put_other. exact H. Qed.

(** Prove `c: lookup k E = r`, r found: through E's [put]s, each of
    another name by computation, to the [put] of k or, past them, to a
    hypothesis. The proof applies one small lemma per [put], so its
    size does not grow with the goal's. *)
Ltac lk_prove :=
  first [ apply Symbolic.lookup_after_put_same
        | eapply lookup_put_miss; [vm_compute; reflexivity | lk_prove]
        | eassumption ].

Ltac vx :=
  first
    [ reflexivity
    | cbn -[put];
      repeat match goal with
        |- context [lookup ?k ?E] =>
          let H := fresh "Hlk" in assert (H : lookup k E = _) by lk_prove; rewrite H; clear H
        end;
      reflexivity ].

(** What `c: _IO_new_file_write` leaves: r of the n bytes written,
    all of them with the flags as they were, or fewer after a failed
    call, which set `c: _IO_ERR_SEEN`. *)
Definition fw_post (n fl r fl' : Z) : Prop :=
  (r = n /\ fl' = fl) \/ (0 <= r < n /\ fl' = Z.lor fl io_err_seen).

(** ## Functions of the genv *)

(** The genv ge defines the function gf as n, at the pointer its
    symbol n holds, whose capability is that function's. *)
Definition ge_fn (ge : genv) (n : string) (gf : func) : Prop :=
  exists a, lookup (TAtom n) (ge_globals ge) = Some (mkPtr a (Fn (TAtom n))) /\
            find_fn ge (TAtom n) = Some (Defined gf) /\ 0 <= a < 2 ^ 64.

(** Such a function's pointer passes `c: check_function`. *)
Lemma ge_fn_check ge n gf : ge_fn ge n gf -> function_check_res ge (sym_ptr ge n) = Some ok.
Proof.
  intros (a & Hl & _ & _). unfold sym_ptr, function_check_res. rewrite Hl. cbn. rewrite Hl. cbn.
  rewrite Z.eqb_refl. reflexivity.
Qed.

(** Its pointer's capability names it. *)
Lemma ge_fn_cap ge n gf : ge_fn ge n gf -> ptr_cap (FileInv.sym_ptr ge n) = Fn (TAtom n).
Proof. intros (a & Hl & _ & _). unfold sym_ptr. rewrite Hl. reflexivity. Qed.

(** Its pointer is a canonical address. *)
Lemma ge_fn_addr ge n gf : ge_fn ge n gf -> 0 <= ptr_addr (sym_ptr ge n) < 2 ^ 64.
Proof. intros (a & Hl & _ & Ha). unfold sym_ptr. rewrite Hl. exact Ha. Qed.

(** It is the function [find_fn] finds. *)
Lemma ge_fn_find ge n gf : ge_fn ge n gf -> find_fn ge (TAtom n) = Some (Defined gf).
Proof. intros (a & _ & Hf & _). exact Hf. Qed.

(** ## Steps over a Logic instance *)

(** The step tactics over the [[runtime]] R and [LogicSig] LG0: each
    takes one instruction of a run whose values are symbolic, by its
    rule from Logic.v, every premise computed or shown by arithmetic. *)
Module LibioStepOn (R : Runtime) (LG0 : LogicSig R).
Import LG0.

(** The point of the frame the goal's weakest precondition runs, given
    to the tactic k: the hypotheses, which may hold other frames, are
    not looked at. *)
Ltac with_at k :=
  lazymatch goal with |- environments.envs_entails _ (wp _ _ (_ (mkFrame _ _ _ _ ?a)) _) => k a end.

(** Enter the start block of a frame. *)
Ltac enter := iApply wp_enter; [reflexivity | vx | iNext; cbn [b_insts b_jump]].

(** A check, its bounds by arithmetic, with the object's life H. *)
Ltac chk H :=
  with_at ltac:(fun a => lazymatch a with
  | Exec _ (Let _ _ (Check _ _ _ _) _ :: _) _ =>
      iApply (wp_check with H); [reflexivity | vx | reflexivity | ar | ar | ar |]
  | Exec _ (Let _ _ (HalfCheck _ _ _ _ _) _ :: _) _ =>
      iApply (wp_half_check with H);
        [reflexivity | vx | reflexivity | reflexivity | ar | ar | lia | ar | ar |]
  | Exec _ (Let _ _ (Renew _ _ _ _) _ :: _) _ =>
      iApply (wp_renew with H); [reflexivity | vx | reflexivity | reflexivity | ar | ar | ar |]
  end);
  iNext; iIntros H.

(** A branch on a closed condition: computed. *)
Ltac br :=
  iApply wp_branch; [vx | iNext];
  lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
    let c' := eval vm_compute in c in change c with c' end; cbn [edge_label].

(** A branch on an unknown condition: both ways, as two goals. *)
Ltac brc :=
  iApply wp_branch; [vx | iNext];
  lazymatch goal with |- context [edge_label (if ?n =? 0 then _ else _)] => destruct (n =? 0) end;
  cbn [edge_label].

(** A branch whose condition is b, by [decide_ints]. *)
Ltac brv b :=
  iApply wp_branch; [vx | iNext];
  lazymatch goal with |- context [edge_label (if ?n =? 0 then _ else _)] =>
    let E := fresh "E" in assert (E : (n =? 0) = b) by decide_ints; rewrite E; clear E end;
  cbn [edge_label].

(** One step whose premises reduce: a pure let, a flight, entering a
    block, or a goto. The values stay symbolic. *)
Ltac st :=
  with_at ltac:(fun a => lazymatch a with
  | Exec _ (Let _ _ _ _ :: _) _ =>
      iApply wp_let; [reflexivity | reflexivity | vx | intros ?; cbn; reflexivity | iNext]
  | Exec _ (Flight _ _ _ _ :: _) _ => iApply wp_flight; [vx | reflexivity | vx | iNext]
  | Enter _ _ => iApply wp_enter; [reflexivity | vx | iNext; cbn [b_insts b_jump]]
  | Exec _ [] (JGoto _) => iApply wp_goto; iNext
  end).

(** ## A check at a share *)

Import LG0.L.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

Local Instance step_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** [wp_check_read] at a share: a [[check]] for reading of the pointer
    p, through a read-write or read-only capability for the object b of
    which a share of the life is owned. *)
Lemma wp_check_read_dq f e ls l d lo hi al args rest j classes p b reg dq Φ :
  op_arg_classes (Check lo hi Read al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b -> b <= raw_address (ptr_addr p) lo ->
  raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg -> raw_address (ptr_addr p) lo mod al = 0 ->
  liveq dq b reg -∗
  ▷ (liveq dq b reg -∗ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (Check lo hi Read al) args :: rest) j)) : sexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp H1 H2 H3. apply (wp_read_dq registry wi ge dq _ _ _ []).
  intros m fuel (Hf & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E _] _].
  apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
  apply op_check. exact (access_read _ _ _ _ _ _ _ Hp E H1 H2 H3).
Qed.

End rules.
End LibioStepOn.
