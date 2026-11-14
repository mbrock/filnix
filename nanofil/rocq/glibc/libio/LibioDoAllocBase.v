From Glibc Require Import GlibcProgram.
(** This file holds the shared pieces of the `c: _IO_file_doallocate` proofs
    (LibioReadCode.v). The function asks the jump table's stat for the
    stream's descriptor, makes a terminal line-buffered, and installs a
    fresh `c: malloc` buffer of `c: st_blksize` bytes, or of
    `c: BUFSIZ` when the stat fails or gives no usable size.

    The allocator needs to distinguish terminal devices before choosing its buffer.
    The shared proofs extract the device's major number and read the kernel's size hint. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode FileInv LibioLogic SysWrappers LibioSetb.
From Glibc Require FileInv LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
From Glibc Require Import GlibcSpec LibioSpecs.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The device query joins bits 8 through 19 and 32 through 63 into the major number. *)
Definition dev_major (d : Z) : Z :=
  LibioSpecs.dev_major d.

(** Reducing the left operand of an or to 32 bits does not change the
    or's low 32 bits. *)
Lemma lor_mod32 x y : 0 <= x -> 0 <= y -> Z.lor (x mod 2 ^ 32) y mod 2 ^ 32 = Z.lor x y mod 2 ^ 32.
Proof.
  intros Hx Hy. apply Z.bits_inj'. intros i Hi. destruct (Z.ltb_spec i 32).
  - rewrite !Z.mod_pow2_bits_low; [|lia|lia]. rewrite !Z.lor_spec Z.mod_pow2_bits_low; [reflexivity | lia].
  - rewrite !Z.mod_pow2_bits_high; [reflexivity | lia | lia].
Qed.

(** Masking a 64-bit word gives a 64-bit word. *)
Lemma land_lt64 a b : 0 <= a < 2 ^ 64 -> 0 <= b -> 0 <= Z.land a b < 2 ^ 64.
Proof.
  intros Ha Hb. assert (H0 : 0 <= Z.land a b) by (apply Z.land_nonneg; lia). split; [exact H0|].
  destruct (Z.eq_dec (Z.land a b) 0) as [->|Hne]; [lia|].
  apply Z.log2_lt_pow2; [lia|]. pose proof (Z.log2_land a b ltac:(lia) Hb).
  assert (Z.log2 a < 64) by (apply Z.log2_lt_pow2; [destruct (Z.eq_dec a 0) as [->|]; [rewrite Z.land_0_l in Hne; lia | lia] | lia]).
  lia.
Qed.

(** The helper's shifts and masks compute the specified major number for every 64-bit input. *)
Lemma dev_major_eq d : 0 <= d < 2 ^ 64 ->
  (Z.lor
     ((((((Z.land (d mod 2 ^ 64) (1048320 mod 2 ^ 64) mod 2 ^ 64 / 2 ^ ((8 mod 2 ^ 32) mod 64))
            mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 64) mod 2 ^ 64)
     ((Z.land (d mod 2 ^ 64) (18446726481523507200 mod 2 ^ 64) mod 2 ^ 64 / 2 ^ ((32 mod 2 ^ 32) mod 64))
        mod 2 ^ 64) mod 2 ^ 32) mod 2 ^ 32 = dev_major d.
Proof.
  intros Hd. unfold dev_major, LibioSpecs.dev_major.
  change (1048320 mod 2 ^ 64) with 1048320. change (18446726481523507200 mod 2 ^ 64) with 18446726481523507200.
  change ((8 mod 2 ^ 32) mod 64) with 8. change ((32 mod 2 ^ 32) mod 64) with 32.
  rewrite (Z.mod_small d); [|lia].
  assert (H1 : 0 <= Z.land d 1048320 < 2 ^ 64) by (apply land_lt64; lia).
  assert (H2 : 0 <= Z.land d 18446726481523507200 < 2 ^ 64) by (apply land_lt64; lia).
  rewrite (Z.mod_small (Z.land d 1048320)); [|lia]. rewrite (Z.mod_small (Z.land d 18446726481523507200)); [|lia].
  assert (H3 : 0 <= Z.land d 1048320 / 2 ^ 8 < 2 ^ 64) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  assert (H4 : 0 <= Z.land d 18446726481523507200 / 2 ^ 32 < 2 ^ 64) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite !Z.mod_mod; try lia.
  assert (H5 : 0 <= (Z.land d 1048320 / 2 ^ 8) mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  rewrite (Z.mod_small ((Z.land d 1048320 / 2 ^ 8) mod 2 ^ 32)); [|lia].
  rewrite (Z.mod_small (Z.land d 18446726481523507200 / 2 ^ 32)); [|lia].
  apply lor_mod32; lia.
Qed.

(** A word that is signed above 0 and below 8192 is between them as an
    unsigned word too. *)
Lemma blksize_range x :
  (sign_extension (2 ^ 64) (2 ^ 63) (0 mod 2 ^ 64) <? sign_extension (2 ^ 64) (2 ^ 63) (x mod 2 ^ 64)) = true ->
  (sign_extension (2 ^ 64) (2 ^ 63) (x mod 2 ^ 64) <? sign_extension (2 ^ 64) (2 ^ 63) (8192 mod 2 ^ 64)) = true ->
  0 < x mod 2 ^ 64 < 8192.
Proof.
  intros E1 E2. apply Z.ltb_lt in E1, E2. unfold sign_extension in E1, E2.
  change ((0 mod 2 ^ 64) mod 2 ^ 64) with 0 in E1. change ((8192 mod 2 ^ 64) mod 2 ^ 64) with 8192 in E2.
  change (2 ^ 63 <=? 0) with false in E1. change (2 ^ 63 <=? 8192) with false in E2.
  assert (Hm : (x mod 2 ^ 64) mod 2 ^ 64 = x mod 2 ^ 64) by (apply Z.mod_mod; lia).
  rewrite Hm in E1, E2. pose proof (Z.mod_pos_bound x (2 ^ 64) ltac:(lia)).
  destruct (Z.leb_spec (2 ^ 63) (x mod 2 ^ 64)); lia.
Qed.


Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

(** The evaluator computes a concrete value before a branch is chosen. *)
Ltac vm_of x := eval vm_compute in x.

(** A branch on an unknown test produces two proof goals.
    Each goal records which test result led to that branch. *)
Ltac brk E :=
  iApply wp_branch; [vx | iNext];
  lazymatch goal with |- context [edge_label (if ?n =? 0 then _ else _)] =>
    lazymatch n with context [if ?c then 1 else 0] => destruct c eqn:E end end;
  lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
    let c' := vm_of c in change c with c' end; cbn [edge_label].

Import ProgramAbbreviations.
Section rules_values.
Context {Σ : gFunctors}
  {gen_heapGS0 : gen_heapGS piece pval Σ}.
Existing Instance gen_heapGS0.
Definition new_buf (bb sz : Z) : iProp Σ :=
  ∃ breg, ⌜r_kind breg = Heap /\ bb + sz <= r_end breg /\ r_end breg <= 2 ^ 48 /\ bb mod 16 = 0⌝ ∗
    live bb breg ∗ bytes bb 0 (replicate (Z.to_nat sz) 0) ∗ auxes bb 0 (replicate (Z.to_nat sz) CNone).
Definition doalloc_k (Mres : iProp Σ) (fb : Z) (freg : region) (fl fd eb : Z) (Φ : outcome -> iProp Σ) : iProp Σ :=
  ∀ fl1 bb sz, ⌜(fl1 = fl \/ fl1 = Z.lor fl io_line_buf) /\ 0 < sz <= 8192 /\ 0 < bb /\ bb + sz <= 2 ^ 48⌝ -∗
    live fb freg -∗ int_cell fb off_flags (setb_flags fl1 1) -∗ int_cell fb off_fileno fd -∗
    pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗ pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗
    new_buf bb sz -∗ errno_any eb -∗ Mres -∗ Φ (Ret (WInt 1)).
End rules_values.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** A fresh heap object starts at a 16-byte-aligned address and holds
    at least sz zero bytes with no capabilities stored in it. *)

(** The allocator installs a fresh buffer between one and 8192 bytes.
    It clears the user-buffer flag and returns one, preserving the descriptor and errno. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** `c: __gnu_dev_major(d)` returns [dev_major] d. *)
Lemma wp_glibc___gnu_dev_major fr d Φ :
  call_frame glibc___gnu_dev_major [WInt d] = Some fr -> 0 <= d < 2 ^ 64 ->
  ▷ Φ (Ret (WInt (dev_major d))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hd. injection Hfr as <-. iIntros "HK". step. step. step. step. step. step. step. step. step.
  iApply wp_ret; [reflexivity | vx |]. iNext. rewrite dev_major_eq; [iExact "HK" | exact Hd].
Qed.

(** The linked device-number helper establishes its pure result contract. *)
#[global] Instance major_has_spec n `{!Defines ge n glibc___gnu_dev_major} :
  HasSpec registry (os_wi w0) ge (TAtom n) major_spec.
Proof.
  intros d. exists glibc___gnu_dev_major. split; [apply defines|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr.
  cbn [fs_pre fs_post major_spec]. iIntros "%Hd HK".
  iApply (wp_glibc___gnu_dev_major fr d); [exact Hfr | exact Hd |].
  iNext. iApply "HK". done.
Qed.

(** A 64-bit load of eight owned bytes bs reads [of_bytes] bs. *)
Lemma wp_raw_load_bytes8 f e ls l d k off args rest j classes p b reg o bs Φ :
  op_arg_classes (RawLoad LdL off) k = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  length bs = 8%nat -> ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o ->
  live b reg -∗ bytes b o bs -∗
  ▷ (live b reg -∗ bytes b o bs -∗
     WP (ERun (mkFrame f (put d (WInt (of_bytes bs)) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k (RawLoad LdL off) args :: rest) j)) : sexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hlen Hp Ha. iIntros "Hl Hb HK".
  iApply (wp_read_with _ _ _ (live b reg ∗ bytes b o bs)
            (fun m => live_at m b reg /\ all_agree m (byte_ps b o bs)) _ _ [] with "[$Hl $Hb] [HK]").
  - iIntros (σ) "Hσ [Hl Hb]".
    iDestruct (pts_facts with "Hσ Hl") as %([Hlv _] & _).
    iDestruct (pts_facts with "Hσ Hb") as %(Hbs & _). iPureIntro. auto.
  - intros m fuel (Hlv & Hbs).
    destruct (lookup_lt_is_Some_2 bs 0 ltac:(lia)) as [x0 H0].
    destruct (lookup_lt_is_Some_2 bs (length bs - 1) ltac:(lia)) as [x1 H1].
    destruct (byte_ps_agree _ _ _ _ _ _ _ Hlv Hbs H0) as (_ & Hlo & _).
    destruct (byte_ps_agree _ _ _ _ _ _ _ Hlv Hbs H1) as (_ & _ & Hhi).
    apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
    rewrite (op_raw_load m k p off).
    + rewrite Ha. replace 8 with (Z.of_nat (length bs)) by (rewrite Hlen; reflexivity).
      rewrite (bytes_load m b reg o bs Hlv Hbs). reflexivity.
    + rewrite Ha Hp. apply (access_obj _ b reg); [exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r].
  - iNext. iIntros "[Hl Hb]". iApply ("HK" with "Hl Hb").
Qed.

End rules.
