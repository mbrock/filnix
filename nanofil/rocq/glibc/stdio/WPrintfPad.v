(** The compiled formatter can request padding even with a field width of
    zero: it tests the low 32 bits of the width minus the string length,
    which can represent a positive signed int. The padding loop fills only the free part of its array.
    If more padding remains, it flushes the full array and tries again. *)

From Glibc Require Import Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os Unit_stdioZ2dcommon_wprintf_buffer_pad_1_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import CodePrelude Fix OsWorld FileInv LibioLogic
  LibioCloseSteps LibioPutsInv LibioWIdle CBlocks PrintfOut WPrintfFileFlush WPrintfDispatch WPrintfFill.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Definition wprintf_pad_fn := Unit_stdioZ2dcommon_wprintf_buffer_pad_1_os.fn___wprintf_buffer_pad_1.
Definition wprintf_pad_inline_fn := Unit_stdioZ2dcommon_vfwprintfZ2dinternal_os.fn_glibc_vfwprintf_internal'23__wprintf_buffer_pad.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.
Local Abbreviation bp b o := (mkPtr (b+o) (Obj b)).
Local Abbreviation obj b := (mkPtr b (Obj b)).
Local Abbreviation nchar cs := (Z.of_nat (length cs)).
Local Abbreviation reg e s v := (lookup (TAtom s) e = Some v).

(** The loop saves the buffer, the padding character and its remaining
    count. The first mode check also survives the loop's back edge. *)
Local Definition pad_regs e bb c n :=
  reg e "v0" (WPtr (obj bb)) /\ reg e "v2" (WInt c) /\
  reg e "pr.1" (WInt n) /\ reg e "chk0" (WPtr (bp bb 32)).

Section pad.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation at_pad e l := (ERun (mkFrame wprintf_pad_fn e [] None (body_at wprintf_pad_fn l)) : sexpr).
Context (Hfill : find_fn ge (TAtom "__GI___wmemset") = Some (Defined wprintf_fill_fn)).

(** After a chunk the loop either returns or enters the next round with a
    smaller count. Both continuations receive the updated array. *)
Local Definition pad_next bb br fp c Φ : iProp Σ :=
  ∀ cs written, wide_stage bb br fp cs written true -∗
    (Φ RetVoid ∧ ∀ e n, ⌜pad_regs e bb c n /\ 0 < n < 2^64⌝ -∗ WP (at_pad e "L15") {{ Φ }}).

Local Ltac open_stage := iDestruct "Hs" as "(%tail & %slots & (%Hbb & %Hal & %Hend & %Hreg & %Hwr & %Hvalid & %Hlen & %Hslots & %Htail) & Hl & Hbase & Hcur & Hstop & Hw & Hm & Hfp & Hbs & Ha)".

(** One chunk appends exactly k copies to the staged prefix. Its write
    does not touch the remaining free bytes or any shadow slots. *)
Local Lemma pad_chunk e bb br fp cs written c n k Φ :
  pad_regs e bb c n -> reg e "chk1" (WPtr (bp bb 8)) -> reg e "chk6" (WPtr (bp bb 8)) ->
  reg e "pr.2" (WInt (Z.of_nat k)) -> 0 <= c < 2^32 -> 0 < Z.of_nat k <= n ->
  n < 2^64 -> (length cs + k <= 128)%nat ->
  wide_stage bb br fp cs written true -∗ pad_next bb br fp c Φ -∗ WP (at_pad e "L67") {{ Φ }}.
Proof using Type*.
  intros (Hb & Hc & Hn & Hck) H1 H6 Hk Hch Hkn Hn64 Hroom.
  iIntros "Hs HK". open_stage. assert (Hcs : 0 <= nchar cs <= 128) by lia. body_start wprintf_pad_fn "L67"%string. step.
  load_self_using wp_raw_load_pointer_self "Hl Hcur".
  iEval (rewrite bytes_app stage_bytes_length) in "Hbs". iDestruct "Hbs" as "[Hpre Htail]".
  iDestruct (bytes_take_drop _ _ _ (4*k) with "Htail") as "[Hdst Hrest]"; [lia|].
  set (off := 48 + 4*nchar cs). replace (48 + Z.of_nat (4*length cs)) with off by (unfold off; lia).
  iApply wp_call_bind; [vx | exact Hfill | reflexivity |]. iNext. norm.
  replace (bb+48+4*nchar cs) with (bb+off) by (unfold off; lia).
  iApply (wp_wprintf_fill _ bb br off k c with "Hl Hdst"); try assumption;
    [reflexivity | unfold off; lia | unfold off; lia | rewrite length_take; lia |].
  iNext. iIntros "Hl Hnew". resume. check "Hl". load_self_using wp_raw_load_pointer_self "Hl Hcur".
  step. step. check "Hl". store "Hl" "Hcur". step. step. norm. unwrap2.
  iAssert (wide_stage bb br fp (cs ++ replicate k c) written true) with "[-HK]" as "Hs".
  { iExists (drop (4*k) tail), slots. rewrite length_app length_replicate.
    iSplit; [iPureIntro; repeat split; try assumption; try lia; try (rewrite length_drop; lia);
      [apply Forall_app; split; [assumption|apply Forall_replicate; assumption] | by apply Forall_drop] |].
    rewrite /stage_bytes flat_map_app -app_assoc bytes_app. fold (stage_bytes cs) (stage_bytes (replicate k c)).
    rewrite stage_bytes_length. replace (48 + Z.of_nat (4*length cs)) with off by (unfold off; lia).
    rewrite bytes_app stage_bytes_length length_replicate. iFrame.
    iEval (change (2 ^ (2 mod 64)) with 4; unfold off; unwrap2) in "Hcur".
    replace (bb+48+4*Z.of_nat (length cs+k)) with (bb+(48+4*nchar cs) + Z.of_nat k * 4) by lia. iExact "Hcur". }
  iDestruct ("HK" with "Hs") as "HK". destruct (Z.eq_dec n (Z.of_nat k)) as [->|Hneq].
  - branch_as true. step. iApply wp_ret_void. iNext. by iDestruct "HK" as "[$ _]".
  - branch_as false. step. iDestruct "HK" as "[_ HK]". iApply ("HK" $! _ (n-Z.of_nat k)). iPureIntro. split; [|lia].
    unfold pad_regs. repeat split; try lk_prove. lookups. unwrap2. reflexivity.
Qed.

(** The formatter compares the remaining count with the number of free
    characters, not the number of free bytes. The smaller count determines
    how much of the array the next call to wide memset may overwrite. *)
Local Lemma pad_room e bb br fp cs written c n Φ :
  pad_regs e bb c n -> reg e "chk1" (WPtr (bp bb 8)) -> reg e "chk2" (WPtr (bp bb 16)) ->
  0 <= c < 2^32 -> 0 < n < 2^64 -> nchar cs < 128 ->
  wide_stage bb br fp cs written true -∗ pad_next bb br fp c Φ -∗ WP (at_pad e "L20") {{ Φ }}.
Proof using Type*.
  intros (Hb & Hc & Hn & Hck) H1 H2 Hch Hn64 Hroom. iIntros "Hs HK". open_stage.
  body_start wprintf_pad_fn "L20"%string. step. check "Hl". load_self_using wp_raw_load_pointer_self "Hl Hcur".
  step. check "Hl". load_self_using wp_raw_load_pointer_self "Hl Hstop". do 3 step. branch_as false. step.
  step. check "Hl". load_self_using wp_raw_load_pointer_self "Hl Hstop".
  step. check "Hl". load_self_using wp_raw_load_pointer_self "Hl Hcur". do 4 step. norm.
  set (room := 128 - nchar cs). assert (Hr : 0 < room <= 128) by (unfold room; lia).
  replace (bb+560 - (bb+48+4*nchar cs)) with (room*4) by (unfold room; lia).
  change (sign_extension (2^64) (2^63) 4) with 4. unfold sign_extension. change (4 =? 0) with false.
  rewrite (Z.mod_small (room*4) (2^64)); [|lia]. rewrite (proj2 (Z.leb_gt (2^63) (room*4)) ltac:(lia)).
  rewrite Z.quot_mul; [|lia]. norm. step.
  iAssert (wide_stage bb br fp cs written true) with "[-HK]" as "Hs"; [iExists tail, slots; iFrame; done|].
  destruct (Z_lt_le_dec n room) as [Hlt|Hle].
  - branch_as false. step. iApply (pad_chunk _ bb br fp cs written c n (Z.to_nat n) with "Hs HK");
      try assumption; try (unfold pad_regs; repeat split; lk_prove); try lk_prove; try (unfold room in *; lia).
    lookups. unwrap2. rewrite Z2Nat.id; [reflexivity|lia].
  - branch_as true. do 3 step. iApply (pad_chunk _ bb br fp cs written c n (Z.to_nat room) with "Hs HK");
      try assumption; try (unfold pad_regs; repeat split; lk_prove); try lk_prove; try (unfold room in *; lia).
    lookups. unwrap2. rewrite Z2Nat.id; [reflexivity|lia].
Qed.

Context (vb : Z) (self : ptr) (E : iProp Σ)
  (Hfn : ge_fn ge "__GI__IO_wfile_xsputn" wprintf_xsputn_fn)
  (Hcall : wprintf_xsputn_call_spec vb self E)
  (Hbackend : find_fn ge (TAtom "__wprintf_buffer_flush_to_file") = Some (Defined wprintf_file_flush_fn))
  (Hflush : find_fn ge (TAtom "__wprintf_buffer_flush") = Some (Defined wprintf_dispatch_fn)).

Local Lemma pad_loop bb br fp vreg c Φ : 0 <= c < 2^32 ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗ ∀ e cs written n,
  ⌜pad_regs e bb c n /\ 0 < n < 2^64⌝ -∗
  file_wide ge vb self fp 1 -∗ E -∗ wide_stage bb br fp cs written true -∗
  (∀ cs' written' active', file_wide ge vb self fp 1 -∗ E -∗ wide_stage bb br fp cs' written' active' -∗ Φ RetVoid) -∗
  WP (at_pad e "L15") {{ Φ }}.
Proof using Type*.
  intros Hch. iIntros "#Hvt #Hwv". iLöb as "IH". iIntros (e cs written n ((Hb & Hc & Hn & Hck) & Hpos)) "HF HE Hs HK".
  open_stage. assert (Hcs : 0 <= nchar cs <= 128) by lia. body_start wprintf_pad_fn "L15"%string.
  step. check "Hl". load_self_using wp_raw_load_pointer_self "Hl Hcur".
  step. check "Hl". load_self_using wp_raw_load_pointer_self "Hl Hstop". do 3 step.
  iAssert (wide_stage bb br fp cs written true) with "[Hl Hbase Hcur Hstop Hw Hm Hfp Hbs Ha]" as "Hs"; [iExists tail, slots; iFrame; done|].
  Local Ltac next_round := iIntros (cs' written') "Hs'"; iSplit;
    [by iApply ("HK" with "HF HE Hs'") | iIntros (e' n' Hreg') ""; by iApply ("IH" with "[%] HF HE Hs' HK")].
  destruct (Z.eq_dec (nchar cs) 128) as [Hfull|Hfree].
  - branch_as false. step. iApply wp_call_bind; [vx | exact Hflush | reflexivity |]. iNext.
    iApply (wp_wprintf_dispatch vb self E Hfn Hcall Hbackend with "Hvt Hwv HF HE Hs"); [reflexivity|].
    iNext. iIntros (ok) "HF HE Hs". resume. destruct ok; do 4 step; branch; step.
    + iApply (pad_room _ bb br fp [] _ c n with "Hs [-]");
        try (unfold pad_regs; repeat split; lk_prove); try lk_prove; try assumption;
        try (lookups; cbn [ptr_addr ptr_cap length]; unwrap2; reflexivity). next_round.
    + iApply wp_ret_void. iNext. by iApply ("HK" with "HF HE Hs").
  - branch_as true. step. branch. step. iApply (pad_room _ bb br fp cs written c n with "Hs [-]");
      try (unfold pad_regs; repeat split; lk_prove); try lk_prove; try assumption;
      try (lookups; cbn [ptr_addr ptr_cap]; unwrap2; reflexivity); [lia|next_round].
Qed.

(** A positive padding request may span arbitrarily many flushes within
    the machine's count range. A short write stops the loop and leaves
    the stream and the failed stage available to the caller. *)
Lemma wp_wprintf_pad fr bb br fp vreg cs written active n c Φ :
  call_frame wprintf_pad_fn [WPtr (obj bb); WInt c; WInt n] = Some fr ->
  0 < n < 2^64 -> 0 <= c < 2^32 ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗ file_wide ge vb self fp 1 -∗ E -∗ wide_stage bb br fp cs written active -∗
  ▷ (∀ cs' written' active', file_wide ge vb self fp 1 -∗ E -∗ wide_stage bb br fp cs' written' active' -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hn Hc. injection Hfr as <-. iIntros "#Hvt #Hwv HF HE Hs HK". open_stage.
  step. step. check "Hl". load_mode "Hl" "Hm". step. destruct active; branch; step.
  - iApply (pad_loop bb br fp vreg c Φ Hc with "Hvt Hwv [%] HF HE [-HK] HK"); [|iExists tail, slots; iFrame; done].
    split; [|exact Hn]. unfold pad_regs; repeat split; lookups; cbn [ptr_addr ptr_cap]; unwrap2; reflexivity.
  - iApply wp_ret_void. iNext. iApply ("HK" $! cs written false with "HF HE [-]"). iExists tail, slots. iFrame. done.
Qed.

(** The wrapper pads a string conversion with spaces only if the signed
    count is positive. Zero and negative counts leave the array untouched. *)
Lemma wp_wprintf_pad_spaces fr bb br fp vreg cs written active n Φ :
  find_fn ge (TAtom "__wprintf_buffer_pad_1") = Some (Defined wprintf_pad_fn) ->
  call_frame wprintf_pad_inline_fn [WPtr (obj bb); WInt 32; WInt n] = Some fr -> 0 <= n < 2^64 ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗ file_wide ge vb self fp 1 -∗ E -∗ wide_stage bb br fp cs written active -∗
  ▷ (∀ cs' written' active', file_wide ge vb self fp 1 -∗ E -∗ wide_stage bb br fp cs' written' active' -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hpad Hfr Hn. injection Hfr as <-. iIntros "#Hvt #Hwv HF HE Hs HK". step. step.
  destruct (decide (0 < n < 2^63)) as [Hpos|Hneg].
  - branch_as false. step. step. iApply wp_call_bind; [vx | exact Hpad | reflexivity |]. iNext.
    rewrite (Z.mod_small n (2^64) Hn). iApply (wp_wprintf_pad _ bb br fp vreg cs written active n 32 with "Hvt Hwv HF HE Hs"); [reflexivity|lia|lia|].
    iNext. iIntros (cs' written' ok) "HF HE Hs". resume. step. step. iApply wp_ret_void. iNext. by iApply ("HK" with "HF HE Hs").
  - assert (n = 0 \/ 2^63 <= n) as [->|Hhi] by lia; [branch|branch_as true]; step; iApply wp_ret_void; iNext; by iApply ("HK" with "HF HE Hs").
Qed.
End pad.
