(** The triple of `c: _IO_setb` (LibioReadCode.v), which sets a
    stream's buffer: it frees the old one when the stream owns it,
    stores the new base and end, and sets `c: _IO_USER_BUF` when the
    caller keeps the new buffer.

    The old base is null, as when `c: _IO_doallocbuf` or
    `c: _IO_file_doallocate` installs a first buffer, or a heap buffer
    the stream owns, `c: _IO_USER_BUF` clear, as when
    `c: _IO_new_file_close_it` drops it: [old_base]. `c: free` is the
    model's free of a heap object ([heap_fns]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode FileInv LibioLogic
  SysWrappers.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The genv ge leaves `c: malloc` and `c: free` to the model: neither
    is defined or held as data, and its free frees heap objects. *)
Definition heap_fns (ge : genv) : Prop :=
  frees_heap (ge_free ge) /\ find_fn ge (TAtom "free") = None /\ lookup (TAtom "free") (ge_globals ge) = None /\
  find_fn ge (TAtom "malloc") = None /\ lookup (TAtom "malloc") (ge_globals ge) = None.

(** `c: _flags` after `c: _IO_setb(fp, b, eb, a)`: `c: _IO_USER_BUF`
    clear when a is nonzero, the stream owning the buffer, else set. *)
Definition setb_flags (fl a : Z) : Z := if a =? 0 then Z.lor fl io_user_buf else Z.land fl 4294967294.

(** A 32-bit int with bit 0 set is a 32-bit int. *)
Lemma lor1_lt32 fl : 0 <= fl < 2 ^ 32 -> 0 <= Z.lor fl 1 < 2 ^ 32.
Proof.
  intros H. assert (Hn : 0 <= Z.lor fl 1) by (apply Z.lor_nonneg; lia).
  assert (Hp : 0 < Z.lor fl 1).
  { destruct (Z.eq_dec (Z.lor fl 1) 0) as [E|E]; [apply Z.lor_eq_0_iff in E; lia | lia]. }
  split; [exact Hn|]. apply Z.log2_lt_pow2; [exact Hp|]. rewrite Z.log2_lor; try lia.
  destruct (Z.eq_dec fl 0) as [->|Hne]; [reflexivity|].
  assert (Z.log2 fl < 32) by (apply Z.log2_lt_pow2; lia). change (Z.log2 1) with 0. lia.
Qed.

(** The new flags are a 32-bit int. *)
Lemma setb_flags_range fl a : 0 <= fl < 2 ^ 32 -> 0 <= setb_flags fl a < 2 ^ 32.
Proof.
  intros H. unfold setb_flags, io_user_buf. destruct (a =? 0); [apply lor1_lt32; exact H|].
  apply land_lt32; lia.
Qed.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioSetbOn (R : Runtime) (LG0 : LogicSig R).
Module SW := SysWrappersOn R LG0.
Import SW SW.FI.ML SW.FI.LG SW.FI.L SW.OW SW.FI SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hheap : heap_fns ge).

Local Instance setb_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** [old_base] fl ob: the old base ob is null, or a live heap buffer
    the stream owns, `c: _IO_USER_BUF` clear in fl. *)
Definition old_base (fl : Z) (ob : ptr) : iProp Σ :=
  ⌜ob = null⌝ ∨ ∃ bb breg, ⌜ob = mkPtr bb (Obj bb) /\ r_kind breg = Heap /\ 0 < bb /\ bb < 2 ^ 64 /\
                            Z.land fl io_user_buf = 0⌝ ∗ live bb breg.

(** Bytes of equal values. *)
Lemma bytes_le_eq b o x y n : x = y -> bytes b o (le_bytes x n) -∗ bytes b o (le_bytes y n).
Proof. intros ->. auto. Qed.

(** A signed 32-bit load of an owned [int_cell]'s bytes. *)
Ltac load_int H :=
  iApply (wp_raw_load_sub_bytes_dq with H);
    [reflexivity | reflexivity | reflexivity | apply load_sw_int; assumption | left; reflexivity | ar |];
  iNext; iIntros H.

(** The stores of `c: _IO_setb`'s new base, end and flags, from block
    `c: L10` to the return. *)
Ltac setb_tail a fl :=
  st; norm; chk "Hl";
  iApply (wp_raw_store_pointer with "Hl Hb"); [reflexivity | reflexivity | reflexivity | ar | ar | wi_store |];
  iNext; iIntros "Hl Hb"; st; norm; chk "Hl";
  iApply (wp_raw_store_pointer with "Hl He"); [reflexivity | reflexivity | reflexivity | ar | ar | wi_store |];
  iNext; iIntros "Hl He";
  destruct (Z.eq_dec a 0) as [-> | Ha0];
  [ brv true; st; chk "Hl"; load_int "Hl Hfl"; st; chk "Hl"; 
    iApply (wp_raw_store_w with "Hl Hfl"); [reflexivity | reflexivity | reflexivity | ar | reflexivity | wi_store |];
    iNext; iIntros "Hl Hfl"; st; st; iApply wp_ret_void; iNext; 
    iApply ("HK" with "Hl [Hfl] Hb He"); iSplit; [iPureIntro; apply setb_flags_range; assumption|];
    unfold setb_flags, io_user_buf, int_bytes; cbn [Z.eqb];
    iApply (bytes_le_eq with "Hfl"); change (1 mod 2 ^ 32) with 1; repeat (rewrite (Z.mod_small fl); [|lia]);
    apply Z.mod_small, lor1_lt32; lia
  | brv false; st; chk "Hl"; load_int "Hl Hfl"; st; chk "Hl";
    iApply (wp_raw_store_w with "Hl Hfl"); [reflexivity | reflexivity | reflexivity | ar | reflexivity | wi_store |];
    iNext; iIntros "Hl Hfl"; st; st; iApply wp_ret_void; iNext;
    iApply ("HK" with "Hl [Hfl] Hb He"); iSplit; [iPureIntro; apply setb_flags_range; assumption|];
    unfold setb_flags, io_user_buf, int_bytes; replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; assumption);
    iApply (bytes_le_eq with "Hfl"); change (4294967294 mod 2 ^ 32) with 4294967294;
    repeat (rewrite (Z.mod_small fl); [|lia]); apply Z.mod_small, land_lt32; lia ].

Lemma wp_glibc__IO_setb fr fb freg fl ob oe nb ne a Φ :
  call_frame glibc__IO_setb [WPtr (mkPtr fb (Obj fb)); WPtr nb; WPtr ne; WInt a] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 <= a < 2 ^ 32 ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base ob -∗ pcell fb off_buf_end oe -∗
  old_base fl ob -∗
  ▷ (live fb freg -∗ int_cell fb off_flags (setb_flags fl a) -∗ pcell fb off_buf_base nb -∗
     pcell fb off_buf_end ne -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfb Hal Hend Hfreg Ha. injection Hfr as <-.
  iIntros "Hl [%Hf Hfl] Hb He Hob HK". unfold file_size in Hend. enter. st. norm. chk "Hl".
  iDestruct "Hob" as "[-> | (%bb & %breg & %Hbb & Hbl)]".
  - iApply (wp_raw_load_pointer with "Hl Hb [//]"); [reflexivity | reflexivity | reflexivity | ar | ar | cbn; lia |].
    iNext. iIntros "Hl Hb _". st. st. br. st. br. st. setb_tail a fl.
  all: fail.
  - destruct Hbb as (-> & Hk & Hb0 & Hb64 & Huser).
    iApply (wp_raw_load_pointer with "Hl Hb Hbl"); [reflexivity | reflexivity | reflexivity | ar | ar | cbn; lia |].
    iNext. iIntros "Hl Hb Hbl". st. st. brv false. st. chk "Hl". load_int "Hl Hfl". st. st. st.
    unfold io_user_buf in Huser. st. brv false. st. st.
    iApply (wp_raw_load_pointer with "Hl Hb Hbl"); [reflexivity | reflexivity | reflexivity | ar | ar | cbn; lia |].
    iNext. iIntros "Hl Hb Hbl". destruct Hheap as (Hfh & Hff & Hfd & _).
    iApply (wp_free_sym _ _ _ (TAtom "free") with "Hbl"); [reflexivity | exact Hfh | exact Hff | exact Hfd | reflexivity |
      exact Hk | lia | |].
    { intros m wd h rs Hh Hrs Hw. exact (os_wi_free w0 m wd h bb breg rs Hk Hh Hrs Hw). }
    iNext. st. st. setb_tail a fl.
  Unshelve. exact freg.
Qed.

End rules.
End LibioSetbOn.
