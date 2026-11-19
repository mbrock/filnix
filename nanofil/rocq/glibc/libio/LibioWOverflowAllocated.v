(** After glibc gives a stream its buffers, overflow sets the read
    pointers before the write pointers. A narrow buffer allocated by
    the first call still has null read pointers. The second call then
    finds the narrow buffer already installed. *)

From Glibc Require Import Unit_libio_genops_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import Fix FileInv FileIdle LibioLogic LibioCloseSteps LibioPutsInv LibioWIdle LibioWXsputnWindow
  LibioWAllocBuf LibioWOverflowDispatch LibioWOverflowPut LibioWOverflowWrite LibioWOverflowSetp LibioWOverflowSetWide
  LibioWOverflowState LibioWOverflowLoan LibioWOverflowReady LibioWOverflowAllocateSteps CBlocks.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Abbreviation objp b := (mkPtr b (Obj b)).

Definition wo_alloc_ok fb st nb fl f2 w b stop := wo_storage fb nb fl b stop /\ 0 <= fl < 2^32 /\
  (forall m, Z.land 513 m = 0 -> Z.land fl m = Z.land (fs_flags st) m) /\
  (forall m, (m = 2 \/ m = 32 \/ m = io_need_lock) -> Z.land f2 m = Z.land (fs_flags2 st) m) /\
  wbuf_user_ok w f2 /\ window_bound w /\ 0 < window_size w.

Section allocated.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (vb : Z) (self : ptr) (E : iProp Σ).
Context `{!Defines ge "__GI__IO_wdo_write" wdo_write_fn} (Hwrite : wdo_pending_spec vb self 1 E).
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation block e l := (ERun (mkFrame wfile_overflow_fn e [] None (body_at wfile_overflow_fn l)) : sexpr).

Lemma wo_alloc_setg e fb fr ch st nb fl f2 wd wr w b rb wb wp we stop Φ :
  0 <= ch < 2^32 -> wo_setup_regs e fb ch ->
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 -> wo_alloc_ok fb st nb fl f2 w b stop ->
  wo_cells vb fb fr fl f2 nb wd wr w (wo_ptrs_before b rb wb wp we stop) (wo_new_wide wd w) -∗
  wo_close ge vb self fb fr st wd wr -∗ E -∗ wo_post vb self E fb ch Φ -∗ WP (block e "L49") {{ Φ }}.
Proof using Type*.
  intros Ch G Fb Fa Fe Fr Wd Wa We Wr (S & F & Bits & B2 & U & B & Room).
  iIntros "(Hf & Hfl & Hf2 & Hfd & Hm & Hvt & Hwd & Hp & Hnb & Hl & Hw & Hwvt & Hb) Hclose HE HK".
  iDestruct "Hw" as "(W0 & W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & _)".
  iApply (wp_wo_setg e fb fr ch wd wr w null null null null null null with "[Hf Hwd Hl Hb] [W0 W1 W2 W3 W4 W5 W6 W7] [-]");
    try assumption; [rewrite /wo_lives; by iFrame|rewrite /wo_wide_cursors; by iFrame|].
  iIntros (ee Ge) "(Hf & Hwd & Hl & Hb) (W0 & W1 & W2 & W3 & W4 & W5 & W6 & W7)".
  iApply (wp_wo_ready vb self E Hwrite ee fb fr ch st nb fl f2 wd wr w b rb wb wp we stop null null null with "[-Hclose HE HK] Hclose HE HK");
    try assumption. rewrite /wo_cells /wo_wide_before /=. by iFrame.
Qed.

Context `{!Defines ge "__GI__IO_doallocbuf" Unit_libio_genops_os.fn___GI__IO_doallocbuf}.

(** The wide allocator has already provided both heap buffers. The
    narrow allocator reads the nonnull base and returns without
    changing either allocation. *)
Lemma wo_alloc_have e fb fr ch st fl f2 wd wr w bb sz Φ :
  0 <= ch < 2^32 -> wo_setup_regs e fb ch ->
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 ->
  0 < wd -> wd mod 8 = 0 -> wd+232 <= r_end wr -> r_end wr <= 2^63 ->
  wo_alloc_ok fb st (NbHeap bb sz) fl f2 w (objp bb) (mkPtr (bb+sz) (Obj bb)) ->
  wo_cells vb fb fr fl f2 (NbHeap bb sz) wd wr w [null;null;null;null;null;null;objp bb;mkPtr (bb+sz) (Obj bb)] (wo_new_wide wd w) -∗
  wo_close ge vb self fb fr st wd wr -∗ E -∗ wo_post vb self E fb ch Φ -∗ WP (block e "L47") {{ Φ }}.
Proof using Type*.
  intros Ch G Fb Fa Fe Fr Wd Wa We Wr Ok. pose proof G as (Hfp & Hch & Hck & H7).
  iIntros "(Hf & Hfl & Hf2 & Hfd & Hm & Hvt & Hwd & Hp & Hnb & Hl & Hw & Hwvt & Hb) Hclose HE HK".
  iDestruct "Hnb" as (br xs cs N) "(Hbl & Hx & Ha)". iDestruct "Hp" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & _)".
  body_start wfile_overflow_fn "L47"%string. iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext.
  iApply (wp_glibc__IO_doallocbuf_have _ fb fr (objp bb) br (DfracOwn 1) (DfracOwn 1) with "Hf P6 Hbl");
    try assumption; try reflexivity; try (unfold file_size; cbn [ptr_addr]; lia).
  iNext. iIntros "Hf P6 Hbl". resume. iAssert (buf_idle (NbHeap bb sz)) with "[Hbl Hx Ha]" as "Hnb"; [iExists br, xs, cs; by iFrame|].
  iApply (wp_wo_after_alloc e ch vb fb fr fl f2 (NbHeap bb sz) wd wr w (objp bb) (mkPtr (bb+sz) (Obj bb)) with "[-Hclose HE HK] [-]");
    try assumption; [cbn; split; [done|lia]|rewrite /wo_cells /=; by iFrame|].
  iIntros (ee Ge) "HC". iApply (wo_alloc_setg ee fb fr ch st (NbHeap bb sz) fl f2 wd wr w (objp bb) (objp bb) null null null (mkPtr (bb+sz) (Obj bb)) with "HC Hclose HE HK"); assumption.
Qed.
End allocated.
