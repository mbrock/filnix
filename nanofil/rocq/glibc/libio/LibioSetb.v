From Glibc Require Import GlibcProgram.
(** `c: _IO_setb` (LibioReadCode.v) sets a stream's buffer. It frees
    the old buffer when the stream owns it, stores the new base and
    end, and sets `c: _IO_USER_BUF` when the caller keeps the new
    buffer.

    The proof covers two kinds of old buffer. Either the old base is
    null, as when a stream gets its first buffer, or it is a heap
    buffer that the stream owns, as when a stream is closed
    ([old_base]). The call of `c: free` is assumed as a rule,
    [free_rule]. [heap_free_rule] proves the rule when `c: free` is
    the model's own ([heap_fns]); a program that links glibc's
    `c: free` proves it from that function's triple. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode FileInv LibioLogic
  SysWrappers.
From Glibc Require FileInv LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
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
  split; [exact Hn|]. apply Z.log2_lt_pow2; [exact Hp|]. rewrite Z.log2_lor; [|lia|lia].
  destruct (Z.eq_dec fl 0) as [->|Hne]; [reflexivity|].
  assert (Z.log2 fl < 32) by (apply Z.log2_lt_pow2; lia). change (Z.log2 1) with 0. lia.
Qed.

(** The new flags are a 32-bit int. *)
Lemma setb_flags_range fl a : 0 <= fl < 2 ^ 32 -> 0 <= setb_flags fl a < 2 ^ 32.
Proof.
  intros H. unfold setb_flags, io_user_buf. destruct (a =? 0); [apply lor1_lt32; exact H|].
  apply land_lt32; lia.
Qed.


Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules_values.
Context {hlc : has_lc}
  {Σ : gFunctors}
  {invGS_gen0 : invGS_gen hlc Σ}
  {gen_heapGS0 : gen_heapGS piece pval Σ}
  (w0 : os_world)
  (registry : name -> option (contract os_world))
  (ge : genv).
Existing Instance invGS_gen0.
Existing Instance gen_heapGS0.
Local Instance setb_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Definition free_rule : Prop := forall f e ls l v rest j b reg Φ,
  arg_x ge e (Arg P v) = Some (WPtr (mkPtr b (Obj b))) -> r_kind reg = Heap -> 0 < b < 2 ^ 64 ->
  live b reg -∗ ▷ WP (ERun (mkFrame f e ls None (Exec l rest j)) : sexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call CVoid (Global (TAtom "free")) [Arg P v] :: rest) j)) : sexpr)
    {{ Φ }}.
Definition old_base (fl : Z) (ob : ptr) : iProp Σ :=
  ⌜ob = null⌝ ∨ ∃ bb breg, ⌜ob = mkPtr bb (Obj bb) /\ r_kind breg = Heap /\ 0 < bb /\ bb < 2 ^ 64 /\
                            Z.land fl io_user_buf = 0⌝ ∗ live bb breg.
Lemma bytes_le_eq b o x y n : x = y -> bytes b o (le_bytes x n) -∗ bytes b o (le_bytes y n).
Proof. intros ->. auto. Qed.
End rules_values.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The call `c: free(p)` at any call site, p the own pointer of the
    live heap object b: b's life is given up and the rest of the block
    runs. *)

(** Where `c: free` is the model's free of a heap object, [free_rule]
    holds: the model frees b, and [os_wi] keeps no piece of a heap
    object. *)
Lemma heap_free_rule : heap_fns ge -> (free_rule w0 registry ge).
Proof.
  intros (Hfh & Hff & Hfd & _) f e ls l v rest j b reg Φ Hx Hk Hb. iIntros "Hbl HK".
  iApply (wp_free_sym _ _ _ (TAtom "free") with "Hbl"); [reflexivity | exact Hfh | exact Hff | exact Hfd | exact Hx |
    exact Hk | lia | |].
  { intros m wd h rs Hh Hrs Hw. exact (os_wi_free w0 m wd h b reg rs Hk Hh Hrs Hw). }
  iExact "HK".
Qed.

(** The call of `c: free` is [free_rule]'s. *)
Context (Hfree : (free_rule w0 registry ge)).

(** [old_base] fl ob: the old base ob is null, or a live heap buffer
    the stream owns, `c: _IO_USER_BUF` clear in fl. *)

(** Bytes of equal values. *)

(** A signed 32-bit load of an owned [int_cell]'s bytes. *)


(** The stores of `c: _IO_setb`'s new base, end and flags, from block
    `c: L10` to the return. *)
Ltac setb_tail a fl :=
  step; norm; check "Hl";
  iApply (wp_raw_store_pointer with "Hl Hb"); [vx | vx | reflexivity | ar | ar | wi_store |];
  iNext; iIntros "Hl Hb"; step; norm; check "Hl";
  iApply (wp_raw_store_pointer with "Hl He"); [vx | vx | reflexivity | ar | ar | wi_store |];
  iNext; iIntros "Hl He";
  destruct (Z.eq_dec a 0) as [-> | Ha0];
  [ branch_as true; step; check "Hl"; load_s32_group "Hl Hfl"; step; check "Hl"; 
    iApply (wp_raw_store_w with "Hl Hfl"); [vx | vx | reflexivity | ar | reflexivity | wi_store |];
    iNext; iIntros "Hl Hfl"; step; step; iApply wp_ret_void; iNext; 
    iApply ("HK" with "Hl [Hfl] Hb He"); iSplit; [iPureIntro; apply setb_flags_range; assumption|];
    unfold setb_flags, io_user_buf, int_bytes; cbn [Z.eqb];
    iApply (bytes_le_eq with "Hfl"); change (1 mod 2 ^ 32) with 1; repeat (rewrite (Z.mod_small fl); [|lia]);
    apply Z.mod_small, lor1_lt32; lia
  | branch_as false; step; check "Hl"; load_s32_group "Hl Hfl"; step; check "Hl";
    iApply (wp_raw_store_w with "Hl Hfl"); [vx | vx | reflexivity | ar | reflexivity | wi_store |];
    iNext; iIntros "Hl Hfl"; step; step; iApply wp_ret_void; iNext;
    iApply ("HK" with "Hl [Hfl] Hb He"); iSplit; [iPureIntro; apply setb_flags_range; assumption|];
    unfold setb_flags, io_user_buf, int_bytes; replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; assumption);
    iApply (bytes_le_eq with "Hfl"); change (4294967294 mod 2 ^ 32) with 4294967294;
    repeat (rewrite (Z.mod_small fl); [|lia]); apply Z.mod_small, land_lt32; lia ].

(** Block `c: L10` of `c: _IO_setb` to its return, the old base freed
    or null: the new base and end stored, and `c: _IO_USER_BUF` set or
    cleared by a. *)
Lemma wp_setb_tail fb freg fl ob oe nb ne a e from Φ :
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 <= a < 2 ^ 32 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (fb + off_buf_base) (Obj fb))) ->
  lookup (TAtom "v2") e = Some (WPtr nb) -> lookup (TAtom "v4") e = Some (WPtr ne) ->
  lookup (TAtom "v6") e = Some (WInt a) ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base ob -∗ pcell fb off_buf_end oe -∗
  ▷ (live fb freg -∗ int_cell fb off_flags (setb_flags fl a) -∗ pcell fb off_buf_base nb -∗
     pcell fb off_buf_end ne -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc__IO_setb e [] None (Enter (TAtom "L10") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Ha Hv0 Hc0 Hv2 Hv4 Hv6.
  iIntros "Hl [%Hf Hfl] Hb He HK". step. setb_tail a fl.
Qed.

(** `c: _IO_setb(fp, b, eb, a)`, the old base [old_base]: the old
    buffer freed if the stream owned it, the new base and end stored,
    and the flags [setb_flags]. *)
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
  iIntros "Hl [%Hf Hfl] Hb He Hob HK". unfold file_size in Hend. step. step. norm. check "Hl".
  iDestruct "Hob" as "[-> | (%bb & %breg & %Hbb & Hbl)]".
  - load_pointer "Hl Hb [//]" by ar.
    iNext. iIntros "Hl Hb _". step. step. branch. step. branch.
    iApply (wp_setb_tail with "Hl [$Hfl //] Hb He HK"); try libio_side.
  - destruct Hbb as (-> & Hk & Hb0 & Hb64 & Huser).
    load_pointer "Hl Hb Hbl" by ar.
    iNext. iIntros "Hl Hb Hbl". step. step. branch_as false. step. check "Hl". load_s32_group "Hl Hfl". step. step. step.
    unfold io_user_buf in Huser. step. branch_as false. step. step.
    load_pointer "Hl Hb Hbl" by ar.
    iNext. iIntros "Hl Hb Hbl".
    iApply (Hfree with "Hbl"); [reflexivity | exact Hk | lia |].
    iNext. step.
    iApply (wp_setb_tail with "Hl [$Hfl //] Hb He HK"); try libio_side.
  Unshelve. exact freg.
Qed.

End rules.
