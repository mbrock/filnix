(** A wide stream keeps its wide characters in a second buffer, and
    `c: _IO_wsetb` is the one function that installs that buffer. It
    frees the old wide buffer when the stream owns it, stores the new
    base and end in the wide data object, and records in `c: _flags2`
    whether the stream owns the new buffer. This file proves the
    function for every kind of old buffer: none, the one-character
    short buffer inside the wide data object, and a heap buffer.

    A caller runs this function in the middle of a write, when the
    stream as a whole is between two consistent states. The contract
    therefore asks only for the fields that the function touches, and
    the caller keeps the rest of the stream. The proof of the narrow
    function in [LibioSetb](LibioSetb.v) is stated the same way. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers LibioSetb LibioPutsInv
  LibioWIdle LibioWAllocCode FxprintfStream.
From Glibc Require FileInv LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

(** ## The owner bit

    Bit 8 of `c: _flags2` is `c: _IO_FLAGS2_USER_WBUF`. The stream owns
    its wide buffer exactly when the bit is clear. *)

(** The function [wbuf_base] gives the base pointer that the wide data
    object holds for the wide buffer w. *)
Definition wbuf_base (wd : Z) (w : wbuf) : ptr :=
  match w with
  | WbNone => null
  | WbShort => mkPtr (wd + woff_shortbuf) (Obj wd)
  | WbHeap wb _ => mkPtr wb (Obj wb)
  end.

(** After `c: _IO_wsetb (fp, b, eb, a)` the owner bit is clear when a
    is nonzero and set when a is zero. The function [wsetb_flags2]
    gives the new value of `c: _flags2`. *)
Definition wsetb_flags2 (f2 a : Z) : Z := if a =? 0 then Z.lor f2 8 else Z.land f2 4294967287.

(** The new flags are a 32-bit number. *)
Lemma wsetb_flags2_range f2 a : 0 <= f2 < 2 ^ 32 -> 0 <= wsetb_flags2 f2 a < 2 ^ 32.
Proof.
  intros H. unfold wsetb_flags2. destruct (a =? 0); [apply lor_lt32; lia | apply fx_land_lt32; lia].
Qed.

(** A number has bit 8 either clear or set. *)
Lemma land8_cases x : Z.land x 8 = 0 \/ Z.land x 8 = 8.
Proof.
  change 8 with (2 ^ 3). destruct (Z.testbit x 3) eqn:H; [right | left].
  all: apply Z.bits_inj; intro i; rewrite Z.land_spec Z.pow2_bits_eqb; [|lia].
  all: rewrite ?Z.pow2_bits_eqb ?Z.bits_0; [|lia..].
  all: destruct (Z.eqb_spec 3 i) as [<-|]; [rewrite H | destruct (Z.testbit x i)]; reflexivity.
Qed.

(** The owner bit of the new flags depends only on a. *)
Lemma wsetb_flags2_bit f2 a : Z.land (wsetb_flags2 f2 a) 8 = if a =? 0 then 8 else 0.
Proof.
  unfold wsetb_flags2. destruct (a =? 0).
  - rewrite Z.land_lor_distr_l. change (Z.land 8 8) with 8. destruct (land8_cases f2) as [-> | ->]; reflexivity.
  - rewrite -Z.land_assoc. change (Z.land 4294967287 8) with 0. apply Z.land_0_r.
Qed.

(** The field `c: _flags2` is a bitfield of 24 bits under one byte of
    other data. The compiled code reads the word, extends the
    bitfield's sign, changes the bit, and stores the bitfield back
    under the byte it kept. These two lemmas say that the stored word
    is the old word with bit 8 set or cleared. *)
Lemma wf2_set x : 0 <= x < 2 ^ 32 ->
  Z.lor (Z.land x 4278190080) (Z.land (Z.lor (fx_field x) 8) 16777215) = Z.lor x 8.
Proof.
  intros Hx. rewrite Z.land_lor_distr_l (fx_field_low x Hx).
  change (Z.land 8 16777215) with 8. rewrite Z.lor_assoc (fx_split x Hx). reflexivity.
Qed.

Lemma wf2_clear x : 0 <= x < 2 ^ 32 ->
  Z.lor (Z.land x 4278190080) (Z.land (Z.land (fx_field x) 4294967287) 16777215) = Z.land x 4294967287.
Proof.
  intros Hx. rewrite -(Z.land_assoc (fx_field x)) (Z.land_comm 4294967287) Z.land_assoc (fx_field_low x Hx).
  replace (Z.land x 4278190080) with (Z.land (Z.land x 4278190080) 4294967287)
    by (rewrite -Z.land_assoc; reflexivity).
  rewrite -Z.land_lor_distr_l (fx_split x Hx). reflexivity.
Qed.

(** The test of the owner bit on the extended bitfield is the test on
    the word itself. *)
Lemma wf2_bit x : 0 <= x < 2 ^ 32 -> Z.land (fx_field x) 8 = Z.land x 8.
Proof.
  intros Hx. change 8 with (Z.land 16777215 8) at 1. rewrite Z.land_assoc (fx_field_low x Hx).
  rewrite -Z.land_assoc. reflexivity.
Qed.

(** The compiled code computes the new word in several 32-bit steps.
    These two lemmas follow the steps of each store. *)
Lemma wf2_set_ops x y z a b c d : 0 <= x < 2 ^ 32 ->
  y = (x mod 2 ^ 32 * 2 ^ ((8 mod 2 ^ 32) mod 32)) mod 2 ^ 32 ->
  z = (sign_extension (2 ^ 32) (2 ^ 31) (y mod 2 ^ 32) / 2 ^ ((8 mod 2 ^ 32) mod 32)) mod 2 ^ 32 ->
  a = Z.lor (z mod 2 ^ 32) (8 mod 2 ^ 32) ->
  b = Z.land (x mod 2 ^ 32) (4278190080 mod 2 ^ 32) ->
  c = Z.land (a mod 2 ^ 32) (16777215 mod 2 ^ 32) ->
  d = Z.lor (b mod 2 ^ 32) (c mod 2 ^ 32) -> d mod 2 ^ 32 = Z.lor x 8.
Proof.
  intros Hx Hy Hz -> -> -> ->. rewrite (fx_shift_field x y z Hx Hy Hz). pose proof (fx_field_range x) as Hf.
  change (8 mod 2 ^ 32) with 8. change (4278190080 mod 2 ^ 32) with 4278190080.
  change (16777215 mod 2 ^ 32) with 16777215.
  rewrite (Z.mod_small (fx_field x)); [|lia]. rewrite (Z.mod_small x); [|lia].
  assert (Ha : 0 <= Z.lor (fx_field x) 8 < 2 ^ 32) by (apply lor_lt32; lia).
  rewrite (Z.mod_small (Z.lor (fx_field x) 8)); [|lia].
  rewrite (Z.mod_small (Z.land x 4278190080)); [|apply fx_land_lt32; lia].
  rewrite (Z.mod_small (Z.land (Z.lor (fx_field x) 8) 16777215)); [|apply fx_land_lt32; lia].
  rewrite (wf2_set x Hx). apply Z.mod_small, lor_lt32; lia.
Qed.

Lemma wf2_clear_ops x y z a b c d : 0 <= x < 2 ^ 32 ->
  y = (x mod 2 ^ 32 * 2 ^ ((8 mod 2 ^ 32) mod 32)) mod 2 ^ 32 ->
  z = (sign_extension (2 ^ 32) (2 ^ 31) (y mod 2 ^ 32) / 2 ^ ((8 mod 2 ^ 32) mod 32)) mod 2 ^ 32 ->
  a = Z.land (z mod 2 ^ 32) (4294967287 mod 2 ^ 32) ->
  b = Z.land (x mod 2 ^ 32) (4278190080 mod 2 ^ 32) ->
  c = Z.land (a mod 2 ^ 32) (16777215 mod 2 ^ 32) ->
  d = Z.lor (b mod 2 ^ 32) (c mod 2 ^ 32) -> d mod 2 ^ 32 = Z.land x 4294967287.
Proof.
  intros Hx Hy Hz -> -> -> ->. rewrite (fx_shift_field x y z Hx Hy Hz). pose proof (fx_field_range x) as Hf.
  change (4294967287 mod 2 ^ 32) with 4294967287. change (4278190080 mod 2 ^ 32) with 4278190080.
  change (16777215 mod 2 ^ 32) with 16777215.
  rewrite (Z.mod_small (fx_field x)); [|lia]. rewrite (Z.mod_small x); [|lia].
  assert (Ha : 0 <= Z.land (fx_field x) 4294967287 < 2 ^ 32) by (apply fx_land_lt32; lia).
  rewrite (Z.mod_small (Z.land (fx_field x) 4294967287)); [|lia].
  rewrite (Z.mod_small (Z.land x 4278190080)); [|apply fx_land_lt32; lia].
  rewrite (Z.mod_small (Z.land (Z.land (fx_field x) 4294967287) 16777215)); [|apply fx_land_lt32; lia].
  rewrite (wf2_clear x Hx). apply Z.mod_small, fx_land_lt32; lia.
Qed.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The function frees a heap buffer with `c: free`. The proof assumes
    that a call of `c: free` on a live heap object ends that object's
    life and returns, which [free_rule] of [LibioSetb](LibioSetb.v)
    states. *)
Context (Hfree : free_rule w0 registry ge).

(** The last block of the function stores the new base and the new
    end and updates the owner bit. This lemma runs that block to the
    return, for any old base, because the block does not read the old
    base. *)
Lemma wp_wsetb_tail fb freg f2 wd wreg ob oe nb ne a e from Φ :
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 -> 0 <= a < 2 ^ 32 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (fb + off_wide) (Obj fb))) ->
  lookup (TAtom "v2") e = Some (WPtr nb) -> lookup (TAtom "v4") e = Some (WPtr ne) ->
  lookup (TAtom "v6") e = Some (WInt a) ->
  live fb freg -∗ int_cell fb off_flags2 f2 -∗ pcell fb off_wide (mkPtr wd (Obj wd)) -∗
  live wd wreg -∗ pcell wd 48 ob -∗ pcell wd 56 oe -∗
  ▷ (live fb freg -∗ int_cell fb off_flags2 (wsetb_flags2 f2 a) -∗ pcell fb off_wide (mkPtr wd (Obj wd)) -∗
     live wd wreg -∗ pcell wd 48 nb -∗ pcell wd 56 ne -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc__IO_wsetb e [] None (Enter (TAtom "L10") (Some from))) : sexpr) {{ Φ }}.
Proof using Type.
  intros Hfb Hal Hend Hfreg Hwd Hwal Hwend Hwreg Ha Hv0 Hc0 Hv2 Hv4 Hv6.
  iIntros "Hl [%Hf Hfl] Hw Hwl Hb He HK".
  step. step. norm. check "Hl". load_pointer "Hl Hw Hwl" by ar. iNext. iIntros "Hl Hw Hwl". step. norm. check "Hwl".
  iApply (wp_raw_store_pointer with "Hwl Hb"); [vx | vx | reflexivity | ar | ar | wi_store |]. iNext. iIntros "Hwl Hb".
  check "Hl". load_pointer "Hl Hw Hwl" by ar. iNext. iIntros "Hl Hw Hwl". step. norm. check "Hwl".
  iApply (wp_raw_store_pointer with "Hwl He"); [vx | vx | reflexivity | ar | ar | wi_store |]. iNext. iIntros "Hwl He".
  destruct (Z.eq_dec a 0) as [-> | Ha0].
  - branch. step. step. check "Hl". load_s32_group "Hl Hfl". step_named. step_named. step_named.
    load_s32_group "Hl Hfl". step_named. step_named. step_named. check "Hl".
    iApply (wp_raw_store_w with "Hl Hfl"); [vx | vx | reflexivity | ar | reflexivity | wi_store |].
    iNext. iIntros "Hl Hfl". step. step. iApply wp_ret_void. iNext.
    iApply ("HK" with "Hl [Hfl] Hw Hwl Hb He"). iSplit; [iPureIntro; apply wsetb_flags2_range; assumption|].
    iApply (bytes_le_eq with "Hfl"). exact (wf2_set_ops f2 x x0 x1 x2 x3 x4 Hf E E0 E1 E2 E3 E4).
  - branch_as false. step. step. check "Hl". load_s32_group "Hl Hfl". step_named. step_named. step_named.
    load_s32_group "Hl Hfl". step_named. step_named. step_named. check "Hl".
    iApply (wp_raw_store_w with "Hl Hfl"); [vx | vx | reflexivity | ar | reflexivity | wi_store |].
    iNext. iIntros "Hl Hfl". step. step. iApply wp_ret_void. iNext.
    iApply ("HK" with "Hl [Hfl] Hw Hwl Hb He"). iSplit; [iPureIntro; apply wsetb_flags2_range; assumption|].
    unfold wsetb_flags2. replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; assumption).
    iApply (bytes_le_eq with "Hfl"). exact (wf2_clear_ops f2 x x0 x1 x2 x3 x4 Hf E E0 E1 E2 E3 E4).
Qed.

(** `c: _IO_wsetb (fp, b, eb, a)` replaces the wide buffer w of the
    stream by the buffer from b to eb. The caller owns the stream's
    `c: _flags2` and its pointer to the wide data object, and in that
    object the base and the end of the wide buffer. The old buffer is
    freed exactly when it is a heap buffer, because [wbuf_user_ok] ties
    the owner bit to the kind of buffer. The function gives back the
    same fields with the new base, the new end and the new owner
    bit. *)
Lemma wp_glibc__IO_wsetb fr fb freg f2 wd wreg w oe nb ne a Φ :
  call_frame glibc__IO_wsetb [WPtr (mkPtr fb (Obj fb)); WPtr nb; WPtr ne; WInt a] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 -> 0 <= a < 2 ^ 32 ->
  wbuf_user_ok w f2 ->
  live fb freg -∗ int_cell fb off_flags2 f2 -∗ pcell fb off_wide (mkPtr wd (Obj wd)) -∗
  live wd wreg -∗ pcell wd 48 (wbuf_base wd w) -∗ pcell wd 56 oe -∗ wbuf_idle w -∗
  ▷ (live fb freg -∗ int_cell fb off_flags2 (wsetb_flags2 f2 a) -∗ pcell fb off_wide (mkPtr wd (Obj wd)) -∗
     live wd wreg -∗ pcell wd 48 nb -∗ pcell wd 56 ne -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hfb Hal Hend Hfreg Hwd Hwal Hwend Hwreg Ha Hu. injection Hfr as <-.
  iIntros "Hl Hfl Hw Hwl Hb He Hold HK". unfold file_size in Hend.
  step. step. norm. check "Hl". load_pointer "Hl Hw Hwl" by ar. iNext. iIntros "Hl Hw Hwl".
  step. norm. check "Hwl".
  destruct w as [| |wb wsz]; cbn [wbuf_base wbuf_idle wbuf_user_ok] in *.
  - load_pointer "Hwl Hb [//]" by ar. iNext. iIntros "Hwl Hb _". step. step. branch. step. branch.
    iApply (wp_wsetb_tail with "Hl Hfl Hw Hwl Hb He HK"); try libio_side.
  - unfold woff_shortbuf. iDestruct (live_halves with "Hwl") as "[Hwl Hwl2]".
    iApply (wp_raw_load_pointer_dq with "Hwl Hb Hwl2"); [reflexivity | vx | left; reflexivity | ar | ar | cbn [ptr_addr]; lia |].
    iNext. iIntros "Hwl Hb Hwl2". iDestruct (live_halves with "[$Hwl $Hwl2]") as "Hwl".
    step. step. branch_as false. step. step. check "Hl". iDestruct "Hfl" as "[%Hf Hfl]". load_s32_group "Hl Hfl".
    step_named. step_named. step_named.
    assert (Hx1 : x1 = Z.land f2 8).
    { rewrite E1 (fx_shift_field f2 x x0 Hf E E0) (Z.mod_small (fx_field f2)); [|apply fx_field_range].
      change (8 mod 2 ^ 32) with 8. apply wf2_bit. exact Hf. }
    rewrite Hu in Hx1. clear E E0 E1. subst x1. step. step. step. branch.
    iApply (wp_wsetb_tail with "Hl [$Hfl //] Hw Hwl Hb He HK"); try libio_side.
  - iDestruct "Hold" as (hreg xs cs Hh) "(Hhl & _ & _)".
    destruct Hh as (Hk & Hhend & Hhreg & Hwb0 & _ & Hsz0 & _).
    load_pointer "Hwl Hb Hhl" by ar. iNext. iIntros "Hwl Hb Hhl".
    step. step. branch_as false. step. step. check "Hl". iDestruct "Hfl" as "[%Hf Hfl]". load_s32_group "Hl Hfl".
    step_named. step_named. step_named.
    assert (Hx1 : x1 = Z.land f2 8).
    { rewrite E1 (fx_shift_field f2 x x0 Hf E E0) (Z.mod_small (fx_field f2)); [|apply fx_field_range].
      change (8 mod 2 ^ 32) with 8. apply wf2_bit. exact Hf. }
    rewrite Hu in Hx1. clear E E0 E1. subst x1. step. step. step. branch.
    step. step. load_pointer "Hl Hw Hwl" by ar. iNext. iIntros "Hl Hw Hwl". step. norm. check "Hwl".
    load_pointer "Hwl Hb Hhl" by ar. iNext. iIntros "Hwl Hb Hhl".
    iApply (Hfree with "Hhl"); [reflexivity | exact Hk | lia |]. iNext. step.
    iApply (wp_wsetb_tail with "Hl [$Hfl //] Hw Hwl Hb He HK"); try libio_side.
  Unshelve. exact freg.
Qed.

(** A stream that has no wide buffer yet holds a null base, so the
    function frees nothing. The first wide write of a stream calls
    `c: _IO_wsetb` in this state. *)
Lemma wp_glibc__IO_wsetb_null fr fb freg f2 wd wreg oe nb ne a Φ :
  call_frame glibc__IO_wsetb [WPtr (mkPtr fb (Obj fb)); WPtr nb; WPtr ne; WInt a] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 -> 0 <= a < 2 ^ 32 ->
  live fb freg -∗ int_cell fb off_flags2 f2 -∗ pcell fb off_wide (mkPtr wd (Obj wd)) -∗
  live wd wreg -∗ pcell wd 48 null -∗ pcell wd 56 oe -∗
  ▷ (live fb freg -∗ int_cell fb off_flags2 (wsetb_flags2 f2 a) -∗ pcell fb off_wide (mkPtr wd (Obj wd)) -∗
     live wd wreg -∗ pcell wd 48 nb -∗ pcell wd 56 ne -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hfb Hal Hend Hfreg Hwd Hwal Hwend Hwreg Ha. iIntros "Hl Hfl Hw Hwl Hb He HK".
  iApply (wp_glibc__IO_wsetb fr fb freg f2 wd wreg WbNone with "Hl Hfl Hw Hwl Hb He [//] HK"); done.
Qed.

End rules.
