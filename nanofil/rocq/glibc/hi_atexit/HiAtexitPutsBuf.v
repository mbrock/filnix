(** Puts can store its newline directly when stdout's buffer has
    room. These rules retain the buffer's bytes, capability slots
    and heap origin through the pointer loads and byte store. The
    close proof needs all three even after output has failed. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioDefaultXsputnBuf HiAtexitBase HiAtexitGe HiAtexitOutputState.
Import ListNotations.
Open Scope Z_scope.
Import HXS.XE.XL.XU.XW.XD.XC.XR.XF.XS.
Import XB XB.DX.RM.SM.TL.BY.BF XB.DX.RM.SM.TL.BY.BF.CP
  XB.DX.RM.SM.TL.BY.BF.CP.CS XB.DX.RM.SM.TL.BY.BF.CP.CS.SW
  XB.DX.RM.SM.TL.BY.BF.CP.CS.SW.FI.ML XB.DX.RM.SM.TL.BY.BF.CP.CS.SW.FI.LG
  XB.DX.RM.SM.TL.BY.BF.CP.CS.SW.FI.L XB.DX.RM.SM.TL.BY.BF.CP.CS.SW.OW
  XB.DX.RM.SM.TL.BY.BF.CP.CS.SW.FI XB.DX.RM.SM.TL.BY.BF.CP.CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world).

(** These memory operations run in the linked program. *)
Local Instance hi_puts_buf_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry hge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) hge.
Local Notation sexpr := (language.expr (nanofil_lang glibc_os_registry hge)).

(** Both pointers lie within the address space, whether the buffer
    is absent or allocated. The owned pieces remain available. *)
Lemma hi_room_bounds nb wp we :
  wroom nb wp we ⊢ ⌜0 <= ptr_addr wp <= 2 ^ 63 /\ 0 <= ptr_addr we <= 2 ^ 63⌝ ∗ wroom nb wp we.
Proof.
  destruct nb as [[b sz]|].
  - iIntros "(%reg & %xs & %cs & %Hp & Hl & Hxs & Hcs)".
    iSplitR; [iPureIntro; unfold room_ok, in_buf in Hp; lia|].
    iExists reg, xs, cs. iFrame. done.
  - iIntros "%Hp". destruct Hp as [-> ->].
    iSplit; [iPureIntro; cbn [null ptr_addr]; lia | done].
Qed.

(** Loading a buffer pointer borrows the buffer's life without
    forgetting its byte values or capability slots. *)
Lemma hi_load_bufptr f e ls l d off args rest j classes p fb freg o nb wp we x Φ :
  op_arg_classes (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) P = Some classes ->
  map2_option (value_x hge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj fb -> raw_address (ptr_addr p) off = fb + o -> (fb + o) mod 8 = 0 ->
  (x = wp \/ x = we) ->
  live fb freg -∗ pcell fb o x -∗ wroom nb wp we -∗
  ▷ (live fb freg -∗ pcell fb o x -∗ wroom nb wp we -∗
     WP (ERun (mkFrame f (put d (WPtr x) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Let d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) args :: rest) j)) : sexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp Ha Hal Hwhich. iIntros "Hl Hpc Hb HK".
  destruct nb as [[b sz]|].
  - iDestruct "Hb" as (reg xs cs Hroom) "(Hbl & Hxs & Hcs)".
    assert (Hcap : ptr_cap x = Obj b) by (destruct Hwhich as [->| ->]; unfold room_ok, in_buf in Hroom; tauto).
    assert (Hr : 0 <= ptr_addr x < 2 ^ 64) by (destruct Hwhich as [->| ->]; unfold room_ok, in_buf in Hroom; lia).
    iApply (wp_raw_load_pointer with "Hl Hpc [Hbl]"); try eassumption.
    { rewrite Hcap. iExact "Hbl". }
    iNext. iIntros "Hl Hpc Hbl". iApply ("HK" with "Hl Hpc [Hbl Hxs Hcs]").
    iExists reg, xs, cs. rewrite Hcap. iFrame. done.
  - iDestruct "Hb" as %[Hwp Hwe].
    assert (Hx0 : x = null) by (destruct Hwhich as [->| ->]; assumption). subst x.
    iApply (wp_raw_load_null w0 glibc_os_registry hge with "Hl Hpc"); try eassumption.
    iNext. iIntros "Hl Hpc". iApply ("HK" with "Hl Hpc []"). done.
Qed.

(** The direct newline store replaces one byte, advances the write
    pointer and leaves every capability slot unchanged. *)
Lemma hi_buf_putc f e ls l d v rest j nb wp we Φ :
  map2_option (value_x hge e) [P] [v] = Some [WPtr wp] -> ptr_addr wp < ptr_addr we ->
  wroom nb wp we -∗
  ▷ (wroom nb (mkPtr (ptr_addr wp + 1) (ptr_cap wp)) we -∗
     WP (ERun (mkFrame f (put d (WPtr wp) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Let d A (Check 0 1 Write 1) [v] :: RawStore Wb 0 (Const 10) (Tmp d) :: rest) j)) : sexpr) {{ Φ }}.
Proof.
  intros Hv Hlt. iIntros "Hb HK". destruct nb as [[b sz]|].
  - iDestruct "Hb" as (reg xs cs Hp) "(Hbl & Hxs & Hcs)".
    destruct Hp as (Hb & Hal & Hsz & Hend & Hreg & Hlx & Hlc & Hxs & Hwp & Hwe & Hheap).
    destruct Hwp as [Hcap Hwp]. destruct Hwe as [Hec Hwe].
    set (k := Z.to_nat (ptr_addr wp - b)).
    assert (Hk : Z.of_nat k = ptr_addr wp - b) by (unfold k; lia).
    destruct (lookup_lt_is_Some_2 xs k ltac:(lia)) as [x Hx].
    iEval (rewrite (bytes_at b xs k x Hx)) in "Hxs". iDestruct "Hxs" as "(Ht & Hx & Hd)".
    iApply (wp_check with "Hbl"); [reflexivity | exact Hv | exact Hcap
      | cbn; unfold raw_address; unwrap2; lia | cbn; unfold raw_address; unwrap2; lia | apply Z.mod_1_r |].
    iNext. iIntros "Hbl".
    iApply (wp_raw_store_byte with "Hbl Hx");
      [reflexivity | vx | exact Hcap | cbn; unfold raw_address; unwrap2; lia | wi_store |].
    iNext. iIntros "Hbl Hx".
    iDestruct (bytes_put with "[$Ht $Hx $Hd]") as "Hxs"; [lia|].
    iApply ("HK" with "[Hbl Hxs Hcs]"). iExists reg, (<[k := 10 mod 256]> xs), cs. iFrame.
    iPureIntro. unfold room_ok, in_buf. cbn [ptr_addr ptr_cap]. rewrite length_insert.
    split_and!; try assumption; try lia.
    apply Forall_insert; [exact Hxs | change (0 <= 10 < 256); lia].
  - iDestruct "Hb" as %[-> ->]. cbn [ptr_addr] in Hlt. lia.
Qed.

End rules.
