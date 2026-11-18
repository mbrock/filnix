(** Glibc gives the C locale's ASCII converter room for one wide
    character. The converter consumes one ASCII byte, even when that
    byte is NUL. A high byte stops conversion without moving either
    cursor, so gnulib can recover the byte from the input. *)

From Glibc Require Import HelloImageTypedGC.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic HelloLeaf.
From Glibc Require Import CodePrelude OsWorld FileInv LibioLogic Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic.
Open Scope Z_scope.

(** This is the function stored in the conversion table of Hello's
    linked image. The captured block list includes the paths for other
    callers as well as the final-step path used here. *)
Definition glibc_ascii_internal := hello_image_fn___gconv_transform_ascii_internal.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

Section ascii.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Local Notation heap b n := (mkRegion b (b + n) Heap Live).
Local Notation objp b := (mkPtr b (Obj b)).

(** The caller supplies a nonempty input window and exactly four
    output bytes. An ASCII byte exhausts either the input (status 4)
    or the output (status 5). For a high byte the converter instead
    returns the illegal-input status, 6. *)
Lemma wp_ascii_internal step_ptr d i count sb sr sa sc ob or oa n x xs Φ :
  0 < d -> d mod 16 = 0 -> d + 48 <= 2 ^ 48 ->
  0 < i -> i mod 16 = 0 -> i + 16 <= 2 ^ 48 ->
  0 < count -> count + 16 <= 2 ^ 48 ->
  sc = Obj sb \/ sc = Ro sb -> 0 < sb -> sb <= sa -> 1 <= n -> sa + n <= r_end sr -> r_end sr <= 2 ^ 48 ->
  0 < ob -> ob <= oa -> oa + 4 <= r_end or -> r_end or <= 2 ^ 48 ->
  0 <= x < 256 -> length xs = 4%nat ->
  live d (heap d 48) -∗ pcell d 0 (mkPtr oa (Obj ob)) -∗ pcell d 8 (mkPtr (oa + 4) (Obj ob)) -∗
  bytes d 16 (le_bytes 1 4) -∗ bytes d 20 (le_bytes 0 4) -∗
  live i (heap i 16) -∗ pcell i 0 (mkPtr sa sc) -∗ live count (heap count 16) -∗ icell count 0 0 -∗
  liveq DfracDiscarded sb sr -∗ bytesq DfracDiscarded sb (sa - sb) [x] -∗
  live ob or -∗ bytes ob (oa - ob) xs -∗
  ▷ (let good := x <? 128 in
     live d (heap d 48) -∗ pcell d 0 (mkPtr (if good then oa + 4 else oa) (Obj ob)) -∗
     live i (heap i 16) -∗ pcell i 0 (mkPtr (if good then sa + 1 else sa) sc) -∗
     live ob or -∗ bytes ob (oa - ob) (if good then le_bytes x 4 else xs) -∗
     Φ (Ret (WInt (if good then if n =? 1 then 4 else 5 else 6)))) -∗
  WP (ERun (invocation glibc_ascii_internal [WPtr step_ptr; WPtr (objp d); WPtr (objp i);
    WPtr (mkPtr (sa + n) sc); WPtr null; WPtr (objp count); WInt 0; WInt 1]) : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hd Hd16 Hde Hi Hi16 Hie Hcount Hce Hsc Hsb Hsa Hn Hse Hsr Hob Hoa Hoe Hor Hx Hxs.
  iIntros "Hdl Hout Hend Hflags Hcalls Hil Hin Hcl Hcount #Hsl #Hbyte Hol Hbytes HK".
  iAssert (live_capq DfracDiscarded sc sr) as "Hsk". { destruct Hsc as [->| ->]; iExact "Hsl". }
  lazymatch goal with |- context [invocation ?f ?xs] => change (invocation f xs) with
    (mkFrame f [(TAtom "v14", WInt 1); (TAtom "v12", WInt 0); (TAtom "v10", WPtr (objp count));
     (TAtom "v8", WPtr null); (TAtom "v6", WPtr (mkPtr (sa+n) sc)); (TAtom "v4", WPtr (objp i));
     (TAtom "v2", WPtr (objp d)); (TAtom "v0", WPtr step_ptr)] [] None (Enter (TAtom "start") None)) end.
  step. iApply wp_alloc; [reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (t Ht) "Ht". change (0 < t /\ t mod 16 = 0 /\ t + 16 <= 2 ^ 48) in Ht.
  destruct Ht as (Ht & Ht16 & Hte). iDestruct (obj_zero_block with "Ht") as "(Htl & Htx & _)"; [vm_compute; congruence|].
  iDestruct (bytes_take_drop _ _ _ 8 with "Htx") as "[Htx _]"; [vm_compute; lia|].
  iAssert (icell t 0 0) with "Htx" as "Ht0". iAssert (live t (heap t 16)) with "Htl" as "Htl".
  iApply wp_alloc; [reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |]. iNext. iIntros (? _) "_".
  do 3 step. check "Hdl". load_bytes_dq "Hdl Hflags" decode reflexivity by a2. iNext. iIntros "Hdl Hflags".
  step. branch. step. step. step. branch. step. check "Hil". load_pointer_dq "Hil Hin Hsk" by a2.
  iNext. iIntros "Hil Hin _". step. step. step. branch. step. check "Hdl". load_pointer_dq "Hdl Hout Hol" by a2.
  iNext. iIntros "Hdl Hout Hol". step. step. step. check "Hdl". load_pointer_dq "Hdl Hend Hol" by a2.
  iNext. iIntros "Hdl Hend Hol". check "Htl". store_long "Htl" "Ht0".
  step. step. branch_as false. step. branch. step. branch. step. branch. step. check "Hil".
  load_pointer_dq "Hil Hin Hsk" by a2. iNext. iIntros "Hil Hin _". check "Htl".
  iApply (wp_raw_load with "Htl Ht0"); [reflexivity | vx | reflexivity | a2 |]. iNext. iIntros "Htl Ht0".
  branch_as false. step. check "Hcl". iApply (wp_raw_load with "Hcl Hcount"); [reflexivity | vx | reflexivity | a2 |].
  iNext. iIntros "Hcl Hcount". do 4 step. check "Hdl". load_bytes_dq "Hdl Hflags" decode reflexivity by a2.
  iNext. iIntros "Hdl Hflags". load_pointer_dq "Hil Hin Hsk" by a2. iNext. iIntros "Hil Hin _".
  do 5 step. branch_as false. do 5 step. branch_as true. do 3 step. branch. step.
  check_read_dq "Hsl" by a2. iNext. iIntros "_".
  assert (Ex : extended Ub W (of_bytes [x]) = Some (WInt x)).
  { change (Some (WInt (((x + 256 * 0) mod 256) mod 2 ^ 32)) = Some (WInt x)).
    rewrite Z.mul_0_r Z.add_0_r !Z.mod_small; lia || reflexivity. }
  load_bytes_dq "Hsl Hbyte" decode (exact Ex) by a2. iNext. iIntros "_ _". step_symbolic.
  destruct (Z.ltb_spec x 128) as [Hlo|Hhi].
  1: { branch_as true. step. step. load_bytes_dq "Hsl Hbyte" decode (exact Ex) by a2. iNext. iIntros "_ _".
    check "Hol". iApply (wp_raw_store_w with "Hol Hbytes"); [vx | vx | reflexivity | a2 | exact Hxs | wi_store |].
    iNext. iIntros "Hol Hbytes". do 6 step. destruct (Z.eqb_spec n 1) as [En|En];
      [branch_as true | branch_as false; do 5 step; branch_as false; step; branch]; shelve. }
  branch_as false. step. step. check "Hdl". load_bytes_dq "Hdl Hflags" decode reflexivity by a2.
  iNext. iIntros "Hdl Hflags". step. check "Hdl". store_int "Hdl" "Hflags".
  step. step. branch_as false. do 5 step. branch.
  Unshelve.
  all: step; check "Hil"; store "Hil" "Hin"; step; branch; step; step; check "Hdl";
    load_bytes_dq "Hdl Hcalls" decode reflexivity by a2; iNext; iIntros "Hdl Hcalls"; step;
    check "Hdl"; store_int "Hdl" "Hcalls"; step; check "Hdl"; load_bytes_dq "Hdl Hflags" decode reflexivity by a2;
    iNext; iIntros "Hdl Hflags"; step; branch; step; check "Hdl"; store "Hdl" "Hout";
    check "Hcl"; iApply (wp_raw_load with "Hcl Hcount"); [reflexivity | vx | reflexivity | a2 |];
    iNext; iIntros "Hcl Hcount"; check "Htl"; iApply (wp_raw_load with "Htl Ht0"); [reflexivity | vx | reflexivity | a2 |];
    iNext; iIntros "Htl Ht0"; step; check "Hcl"; store_long "Hcl" "Hcount";
    step; step; branch; step; branch; step; branch; step; iApply wp_ret; [reflexivity | vx |]; iNext.
  all: cbn [ptr_addr ptr_cap]; rewrite ?(Z.mod_small x (2^32)) ?(Z.mod_small sa (2^64)) ?(Z.mod_small oa (2^64))
    ?(Z.mod_small 4 (2^64)) ?(Z.mod_small 1 (2^64)) ?(Z.mod_small (oa+4) (2^64)) ?(Z.mod_small (sa+1) (2^64));
    try lia; iApply ("HK" with "Hdl Hout Hil Hin Hol Hbytes").
Qed.
End ascii.
