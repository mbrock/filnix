(** This file holds the shared pieces of the `c: _IO_new_file_overflow` proofs
    (LibioDoWriteCode.v). The function is called when a narrow stream
    has no room to put a byte: it allocates a buffer on the first call,
    switches the stream to putting, flushes a full buffer, and stores
    the byte, flushing again when the stream is unbuffered or is
    line-buffered and the byte is a newline.

    [ovf_state] is the put area of a stream that is putting into a heap
    buffer, [ovf_fixed] is the fields the function leaves alone, and
    [ovf_ret] is its result. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers.
Import ListNotations.
Open Scope Z_scope.

(** A byte returned as an `c: unsigned char` widened to `c: int` is
    itself. *)
Lemma ret_byte ch : 0 <= ch < 256 -> (((ch mod 2 ^ 32) mod 256) mod 2 ^ 32) mod 2 ^ 32 = ch.
Proof.
  intros H. rewrite (Z.mod_small ch (2 ^ 32)); [|lia]. rewrite (Z.mod_small ch 256); [|lia].
  rewrite (Z.mod_small ch (2 ^ 32)); [|lia]. apply Z.mod_small. lia.
Qed.

(** A byte stored through a `c: char` is itself. *)
Lemma sb_byte ch : 0 <= ch < 256 -> ((sign_extension 256 128 ch mod 2 ^ 32) mod 2 ^ 32) mod 256 = ch.
Proof.
  intros H. unfold sign_extension. rewrite (Z.mod_small ch 256); [|lia].
  destruct (Z.leb_spec 128 ch); Z.div_mod_to_equations; lia.
Qed.

(** What `c: _IO_new_file_overflow(f, ch)` returns: `c: EOF` after a
    failed flush, or else ch itself, or 0 when ch is `c: EOF` and the
    flush succeeded. *)
Definition ovf_ret (ch r : Z) : Prop := r = 2 ^ 32 - 1 \/ r = (if ch =? 2 ^ 32 - 1 then 0 else ch).

(** Setting bits c that miss the mask m leaves the masked bits as they
    were. *)
Lemma land_lor_const fl c m : Z.land c m = 0 -> Z.land (Z.lor fl c) m = Z.land fl m.
Proof. intros H. rewrite Z.land_lor_distr_l H Z.lor_0_r. reflexivity. Qed.

(** Setting `c: _IO_ERR_SEEN` twice is setting it once. *)
Lemma lor_err_twice fl : Z.lor (Z.lor fl 32) 32 = Z.lor fl 32.
Proof. rewrite -Z.lor_assoc Z.lor_diag. reflexivity. Qed.

(** The definitions over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioOverflowBaseOn (R : Runtime) (LG0 : LogicSig R).
Module SW := SysWrappersOn R LG0.
Import SW SW.FI.ML SW.FI.LG SW.FI.L SW.OW SW.FI SW.ST.

(** A branch on the signed test `c: fp->_mode <= 0` of a narrow
    stream, whose mode H says is 0 or -1: the test holds. *)
Ltac brm H :=
  iApply wp_branch; [vx | iNext];
  lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
    let E := fresh "E" in
    first [ assert (E : c = true) by (destruct H as [-> | ->]; vm_compute; reflexivity)
          | assert (E : c = false) by (destruct H as [-> | ->]; vm_compute; reflexivity) ];
    rewrite E; clear E end;
  cbn [edge_label].

(** One step over a pure let, a flight, a jump or an entry, or over a
    check of the stream's object, whose life is "Hl". *)
Ltac adv1 :=
  let a := at_of in
  lazymatch a with
  | Exec _ (Let _ _ (Check _ _ _ _) _ :: _) _ => norm; chk "Hl"
  | Exec _ (Let _ _ (HalfCheck _ _ _ _ _) _ :: _) _ => norm; chk "Hl"
  | Exec _ (Let _ _ (Renew _ _ _ _) _ :: _) _ => norm; chk "Hl"
  | Exec _ (Let _ _ (RawLoad _ _) _ :: _) _ => fail
  | Exec _ (Let _ _ (RawLoadPointer _ _) _ :: _) _ => fail
  | _ => st
  end.

(** Steps of [adv1] up to the next load, store, call or branch. *)
Ltac adv := repeat adv1.

Section defs.
Context `{!gen_heapGS piece pval Σ}.

(** A stream putting into the heap buffer bb of sz bytes xs, k of them
    pending: the read pointers and write base at bb, the write pointer
    at bb + k, the write end we inside the buffer, and the flags fl. *)
Definition ovf_state (fb bb : Z) (breg : region) (sz k : Z) (we : ptr) (xs : list Z) (fl tw off : Z) : iProp Σ :=
  ⌜0 < bb /\ bb + sz <= r_end breg /\ r_end breg <= 2 ^ 63 /\ 0 < sz /\ 0 <= k <= sz /\
   length xs = Z.to_nat sz /\ Forall (fun x => 0 <= x < 256) xs /\
   ptr_cap we = Obj bb /\ bb <= ptr_addr we <= bb + sz⌝ ∗
  live bb breg ∗ bytes bb 0 xs ∗
  int_cell fb off_flags fl ∗ icell fb off_total_written tw ∗ icell fb off_offset off ∗
  pcell fb off_read_ptr (mkPtr bb (Obj bb)) ∗ pcell fb 16 (mkPtr bb (Obj bb)) ∗ pcell fb 24 (mkPtr bb (Obj bb)) ∗
  pcell fb off_write_base (mkPtr bb (Obj bb)) ∗ pcell fb off_write_ptr (mkPtr (bb + k) (Obj bb)) ∗
  pcell fb off_write_end we ∗ pcell fb off_buf_base (mkPtr bb (Obj bb)) ∗
  pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)).

(** The fields `c: _IO_new_file_overflow` and the flush it calls leave
    alone: `c: _flags2`, the descriptor, errno, `c: _cur_column`,
    `c: _mode` and the jump table. *)
Definition ovf_fixed (fb f2 fd eb mode vb : Z) : iProp Σ :=
  int_cell fb off_flags2 f2 ∗ int_cell fb off_fileno fd ∗ errno_any eb ∗ bytes fb off_column [0; 0] ∗
  int_cell fb off_mode mode ∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)).

(** [ovf_state] from its parts, the flags as bytes. *)
Lemma ovf_state_intro fb bb breg sz k we xs fl tw off :
  0 < bb -> bb + sz <= r_end breg -> r_end breg <= 2 ^ 63 -> 0 < sz -> 0 <= k <= sz -> length xs = Z.to_nat sz ->
  Forall (fun x => 0 <= x < 256) xs -> ptr_cap we = Obj bb -> bb <= ptr_addr we <= bb + sz -> 0 <= fl < 2 ^ 32 ->
  live bb breg -∗ bytes bb 0 xs -∗ bytes fb off_flags (int_bytes fl) -∗ icell fb off_total_written tw -∗
  icell fb off_offset off -∗ pcell fb off_read_ptr (mkPtr bb (Obj bb)) -∗ pcell fb 16 (mkPtr bb (Obj bb)) -∗
  pcell fb 24 (mkPtr bb (Obj bb)) -∗ pcell fb off_write_base (mkPtr bb (Obj bb)) -∗
  pcell fb off_write_ptr (mkPtr (bb + k) (Obj bb)) -∗ pcell fb off_write_end we -∗
  pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗ pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗
  ovf_state fb bb breg sz k we xs fl tw off.
Proof.
  iIntros (Hb Hbe Hbr Hsz Hk Hxl Hxr Hwc Hwa Hfl) "Hbl Hxs Hfl Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend".
  rewrite /ovf_state /int_cell. iFrame. iPureIntro. repeat split; try assumption; lia.
Qed.

(** [ovf_state] with nothing pending, from its parts. *)
Lemma ovf_state_base fb bb breg sz we xs fl tw off :
  0 < bb -> bb + sz <= r_end breg -> r_end breg <= 2 ^ 63 -> 0 < sz -> length xs = Z.to_nat sz ->
  Forall (fun x => 0 <= x < 256) xs -> ptr_cap we = Obj bb -> bb <= ptr_addr we <= bb + sz ->
  live bb breg -∗ bytes bb 0 xs -∗ int_cell fb off_flags fl -∗ icell fb off_total_written tw -∗
  icell fb off_offset off -∗ pcell fb off_read_ptr (mkPtr bb (Obj bb)) -∗ pcell fb 16 (mkPtr bb (Obj bb)) -∗
  pcell fb 24 (mkPtr bb (Obj bb)) -∗ pcell fb off_write_base (mkPtr bb (Obj bb)) -∗
  pcell fb off_write_ptr (mkPtr bb (Obj bb)) -∗ pcell fb off_write_end we -∗
  pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗ pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗
  ovf_state fb bb breg sz 0 we xs fl tw off.
Proof.
  iIntros (Hb Hbe Hbr Hsz Hxl Hxr Hwc Hwa) "Hbl Hxs Hfl Htw Hoff Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend".
  rewrite /ovf_state Z.add_0_r. iFrame. iPureIntro. repeat split; try assumption; lia.
Qed.

(** One byte as a list is that byte. *)
Lemma bytes_ibyte b o x : bytes b o [x] ⊣⊢ ibyte b o x.
Proof. rewrite /bytes /ibyte /byte_ps. cbn. done. Qed.

(** The bytes xs split around byte k. *)
Lemma bytes_focus b xs k : (k < length xs)%nat ->
  bytes b 0 xs ⊣⊢ bytes b 0 (take k xs) ∗ ibyte b (Z.of_nat k) (nth k xs 0) ∗ bytes b (Z.of_nat k + 1) (drop (S k) xs).
Proof.
  intros Hk. rewrite (bytes_take_drop b 0 xs k); [|lia]. rewrite Z.add_0_l.
  rewrite (bytes_take_drop b (Z.of_nat k) (drop k xs) 1); [|rewrite length_drop; lia].
  rewrite drop_drop -bytes_ibyte. replace (k + 1)%nat with (S k) by lia.
  assert (E : forall (l : list Z) n, (n < length l)%nat -> take 1 (drop n l) = [nth n l 0]).
  { induction l as [|y l IH]; intros [|n] Hn; cbn in *; [lia | lia | reflexivity | apply IH; lia]. }
  rewrite (E xs k Hk). done.
Qed.

(** The bytes split around byte k, with y in its place, are xs with y
    at k. *)
Lemma bytes_unfocus b xs k y : (k < length xs)%nat ->
  bytes b 0 (take k xs) -∗ ibyte b (Z.of_nat k) y -∗ bytes b (Z.of_nat k + 1) (drop (S k) xs) -∗
  bytes b 0 (<[k := y]> xs).
Proof.
  iIntros (Hk) "H0 H1 H2". rewrite (bytes_focus b (<[k:=y]> xs) k); [|rewrite length_insert; lia].
  rewrite take_insert_ge; [|lia]. rewrite drop_insert_lt; [|lia].
  rewrite nth_lookup list_lookup_insert_eq; [|lia]. cbn. iFrame.
Qed.

End defs.
End LibioOverflowBaseOn.
