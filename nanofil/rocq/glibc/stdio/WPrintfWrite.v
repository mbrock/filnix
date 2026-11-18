(** The counted wide write copies as many characters as the staging array
    can hold. It advances the source by four bytes per character and
    starts another round on the unread suffix. A failed flush stops the
    write and gives the caller back the entire source, including any
    characters already copied. *)

From Glibc Require Import HelloImageTypedWP.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import CodePrelude Fix OsWorld OsRegistry FileInv LibioLogic
  LibioCloseSteps LibioPutsInv LibioWIdle CBlocks PrintfOut MemFwdCode WPrintfFileFlush WPrintfDispatch WPrintfCopy.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps OsWorld.
Open Scope Z_scope.

Definition wprintf_write_fn := hello_image_fn___wprintf_buffer_write.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.
Local Abbreviation bp b o := (mkPtr (b+o) (Obj b)).
Local Abbreviation obj b := (mkPtr b (Obj b)).
Local Abbreviation nchar cs := (Z.of_nat (length cs)).
Local Abbreviation reg e s v := (lookup (TAtom s) e = Some v).
Local Definition write_regs e bb p (ys : list Z) := reg e "v0" (WPtr (obj bb)) /\ reg e "chk0" (WPtr (bp bb 32)) /\
  reg e "pr.1" (WPtr p) /\ reg e "pr.2" (WInt (nchar ys)).

Section write.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).
Local Abbreviation at_write e l := (ERun (mkFrame wprintf_write_fn e [] None (body_at wprintf_write_fn l)) : sexpr).
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None)
  (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None)
  (Hmemcpy : find_fn ge (TAtom "__GI_memcpy") = Some (Defined glibc_memcpy))
  (Hcopy : find_fn ge (TAtom "__wmemcpy") = Some (Defined wprintf_copy_fn)).

Local Ltac open_stage := iDestruct "Hs" as "(%tail & %slots & (%Hbb & %Hal & %Hend & %Hreg & %Hwr & %Hvalid & %Hlen & %Hslots & %Htail) & Hl & Hbase & Hcur & Hstop & Hw & Hm & Hfp & Hbs & Ha)".

Local Lemma source_split dq sb so ys k : (k <= length ys)%nat ->
  bytesq dq sb so (stage_bytes ys) ⊣⊢ bytesq dq sb so (stage_bytes (take k ys)) ∗
    bytesq dq sb (so + 4 * Z.of_nat k) (stage_bytes (drop k ys)).
Proof using Type.
  intros Hk. rewrite -{1}(take_drop k ys) /stage_bytes flat_map_app /bytesq byte_ps_app ptsq_app.
  fold (stage_bytes (take k ys)). rewrite stage_bytes_length length_take_le; [|done].
  by replace (Z.of_nat (4*k)) with (4*Z.of_nat k) by lia.
Qed.

(** The next iteration needs only the unread suffix. The caller retains
    the consumed prefix and joins it back to the suffix on return. *)
Local Definition write_next bb br fp dq sb sr so sc ys Φ : iProp Σ :=
  ∀ k, ⌜(k <= length ys)%nat⌝ -∗ ∀ e' cs' written',
    ⌜write_regs e' bb (mkPtr (sb + (so + 4*Z.of_nat k)) sc) (drop k ys)⌝ -∗
    wide_stage bb br fp cs' written' true -∗ liveq dq sb sr -∗ bytesq dq sb so (stage_bytes ys) -∗
    WP (at_write e' "L15") {{ Φ }}.

Local Lemma write_chunk e bb br fp cs written dq sb sr so sc ys k Φ :
  write_regs e bb (mkPtr (sb+so) sc) ys -> reg e "chk1" (WPtr (bp bb 8)) -> reg e "chk6" (WPtr (bp bb 8)) ->
  reg e "pr.3" (WInt (Z.of_nat k)) -> (k <= length ys)%nat -> (length cs + k <= 128)%nat ->
  0 < sb -> sb mod 8 = 0 -> 0 <= so -> sb+so+4*nchar ys <= r_end sr -> r_end sr <= 2^63 ->
  sc = Obj sb \/ sc = Ro sb -> Forall (fun c => 0 <= c < 2^32) ys ->
  wide_stage bb br fp cs written true -∗ liveq dq sb sr -∗ bytesq dq sb so (stage_bytes ys) -∗
  write_next bb br fp dq sb sr so sc ys Φ -∗ WP (at_write e "L69") {{ Φ }}.
Proof using Type*.
  intros (Hb & Hck & Hp & Hn) H1 H6 Hk Hky Hfit Hb0 Hsa Hso Hse Hsr Hsc Vys.
  iIntros "Hs Hsl Hy HK". open_stage. assert (Hcs : 0 <= nchar cs <= 128) by lia.
  body_start wprintf_write_fn "L69"%string. step. load_self_using wp_raw_load_pointer_self "Hl Hcur".
  iDestruct (source_split dq sb so ys k Hky with "Hy") as "[Hpart Hrest]".
  assert (Lk : length (take k ys) = k) by (apply length_take_le; done).
  iApply wp_call_bind; [vx | exact Hcopy | reflexivity |]. iNext. norm. unwrap2.
  iApply (wp_wprintf_copy Hmove Hmove_fn Hmove_sym Hmemcpy _ bb br cs tail slots dq sb sr so sc (take k ys)
    with "Hl Hbs Ha Hsl Hpart"); try assumption; try (rewrite Lk; lia).
  { rewrite Lk. replace (bb+(48+4*nchar cs)) with (bb+48+4*nchar cs) by lia. reflexivity. }
  iNext. iIntros (tl sl (L & Ls & V)) "Hl Hbs Ha Hsl Hpart". resume. check "Hl".
  load_self_using wp_raw_load_pointer_self "Hl Hcur". step. step. check "Hl". store "Hl" "Hcur".
  do 3 step. norm. unwrap2. step. iSpecialize ("HK" $! k with "[%]"); [done|].
  iApply ("HK" $! _ (cs ++ take k ys)%list written with "[%] [Hl Hbase Hcur Hstop Hw Hm Hfp Hbs Ha] Hsl [Hpart Hrest]").
  - unfold write_regs. repeat split; try lk_prove; lookups; cbn [ptr_addr ptr_cap]; change (2 ^ (2 mod 64)) with 4; unwrap2;
      rewrite ?length_drop.
    + replace (sb+so+Z.of_nat k*4) with (sb+(so+4*Z.of_nat k)) by lia. done.
    + rewrite Nat2Z.inj_sub; [done|lia].
  - iExists tl, sl. iSplit; [iPureIntro; split_and!; try assumption; try lia; apply Forall_app; split; [done|by apply Forall_take]|].
    iFrame. iEval (change (2 ^ (2 mod 64)) with 4; unwrap2) in "Hcur".
    rewrite length_app Lk. replace (bb+48+4*Z.of_nat (length cs+k)) with (bb+48+4*nchar cs+Z.of_nat k*4) by lia. iExact "Hcur".
  - rewrite (source_split _ _ _ _ k Hky). iFrame.
Qed.

(** Once space is available, the smaller of the source length and the
    free character count fits both arrays. The equality case fills the
    array exactly and leaves no unread characters. *)
Local Lemma write_room e bb br fp cs written dq sb sr so sc ys Φ :
  write_regs e bb (mkPtr (sb+so) sc) ys -> reg e "chk1" (WPtr (bp bb 8)) -> reg e "chk2" (WPtr (bp bb 16)) ->
  nchar cs < 128 -> 0 < sb -> sb mod 8 = 0 -> 0 <= so -> sb+so+4*nchar ys <= r_end sr -> r_end sr <= 2^63 ->
  sc = Obj sb \/ sc = Ro sb -> Forall (fun c => 0 <= c < 2^32) ys ->
  wide_stage bb br fp cs written true -∗ liveq dq sb sr -∗ bytesq dq sb so (stage_bytes ys) -∗
  write_next bb br fp dq sb sr so sc ys Φ -∗ WP (at_write e "L22") {{ Φ }}.
Proof using Type*.
  intros (Hb & Hck & Hp & Hn) H1 H2 Hroom Hb0 Hsa Hso Hse Hsr Hsc Vys. iIntros "Hs Hsl Hy HK". open_stage.
  body_start wprintf_write_fn "L22"%string. step. check "Hl". load_self_using wp_raw_load_pointer_self "Hl Hcur".
  step. check "Hl". load_self_using wp_raw_load_pointer_self "Hl Hstop". do 3 step. branch_as false. step.
  step. check "Hl". load_self_using wp_raw_load_pointer_self "Hl Hstop".
  step. check "Hl". load_self_using wp_raw_load_pointer_self "Hl Hcur". do 4 step. norm.
  set (room := 128 - nchar cs). assert (Hr : 0 < room <= 128) by (unfold room; lia).
  replace (bb+560 - (bb+48+4*nchar cs)) with (room*4) by (unfold room; lia).
  change (sign_extension (2^64) (2^63) 4) with 4. unfold sign_extension. change (4 =? 0) with false.
  rewrite (Z.mod_small (room*4) (2^64)); [|lia]. rewrite (proj2 (Z.leb_gt (2^63) (room*4)) ltac:(lia)).
  rewrite Z.quot_mul; [|lia]. norm. step.
  iAssert (wide_stage bb br fp cs written true) with "[-Hsl Hy HK]" as "Hs"; [iExists tail, slots; iFrame; done|].
  destruct (Z_lt_le_dec (nchar ys) room) as [Hlt|Hle].
  - branch_as false. step. iApply (write_chunk _ bb br fp cs written dq sb sr so sc ys (length ys) with "Hs Hsl Hy HK");
      try assumption; try (unfold write_regs; repeat split; lk_prove); try lk_prove; try (unfold room in *; lia).
    lookups. unwrap2. done.
  - branch_as true. do 3 step. iApply (write_chunk _ bb br fp cs written dq sb sr so sc ys (Z.to_nat room) with "Hs Hsl Hy HK");
      try assumption; try (unfold write_regs; repeat split; lk_prove); try lk_prove; try (unfold room in *; lia).
    lookups. unwrap2. by rewrite Z2Nat.id; [|lia].
Qed.

Context (vb : Z) (self : ptr) (E : iProp Σ)
  (Hfn : ge_fn ge "__GI__IO_wfile_xsputn" wprintf_xsputn_fn)
  (Hcall : wprintf_xsputn_call_spec vb self E)
  (Hbackend : find_fn ge (TAtom "__wprintf_buffer_flush_to_file") = Some (Defined wprintf_file_flush_fn))
  (Hflush : find_fn ge (TAtom "__wprintf_buffer_flush") = Some (Defined wprintf_dispatch_fn)).

Local Lemma write_loop bb br fp dq sb sr sc vreg Φ :
  0 < sb -> sb mod 8 = 0 -> r_end sr <= 2^63 -> sc = Obj sb \/ sc = Ro sb ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗ ∀ e cs written so ys,
  ⌜write_regs e bb (mkPtr (sb+so) sc) ys /\ 0 <= so /\ sb+so+4*nchar ys <= r_end sr /\ Forall (fun c => 0 <= c < 2^32) ys⌝ -∗
  file_wide ge vb self fp 1 -∗ E -∗ wide_stage bb br fp cs written true -∗ liveq dq sb sr -∗ bytesq dq sb so (stage_bytes ys) -∗
  (∀ cs' written' ok, file_wide ge vb self fp 1 -∗ E -∗ wide_stage bb br fp cs' written' ok -∗
    liveq dq sb sr -∗ bytesq dq sb so (stage_bytes ys) -∗ Φ RetVoid) -∗ WP (at_write e "L15") {{ Φ }}.
Proof using Type*.
  intros Hb0 Hsa Hsr Hsc. iIntros "#Hvt #Hwv". iLöb as "IH".
  iIntros (e cs written so ys ((Hb & Hck & Hp & Hn) & Hso & Hse & Vys)) "HF HE Hs Hsl Hy HK".
  body_start wprintf_write_fn "L15"%string. step. destruct (Nat.eq_dec (length ys) 0) as [Hz|Hnz].
  { norm. rewrite Hz. branch. step. iApply wp_ret_void. iNext. by iApply ("HK" with "HF HE Hs Hsl Hy"). }
  norm. unwrap2. assert (Hypos : (0 <? nchar ys) = true) by (apply Z.ltb_lt; lia). rewrite Hypos.
  branch. step. open_stage. assert (Hcs : 0 <= nchar cs <= 128) by lia.
  step. check "Hl". load_self_using wp_raw_load_pointer_self "Hl Hcur".
  step. check "Hl". load_self_using wp_raw_load_pointer_self "Hl Hstop". do 3 step.
  iAssert (wide_stage bb br fp cs written true) with "[Hl Hbase Hcur Hstop Hw Hm Hfp Hbs Ha]" as "Hs"; [iExists tail, slots; iFrame; done|].
  Local Ltac next_chunk ys := let k := fresh "k" in let Hk := fresh "Hk" in let Hregs := fresh "Hregs" in
    let e1 := fresh "env" in let cs1 := fresh "cs1" in let w1 := fresh "w1" in iIntros (k Hk e1 cs1 w1 Hregs) "Hs Hsl Hy";
    iDestruct (source_split _ _ _ _ k Hk with "Hy") as "[Hpre Hsuffix]";
    iApply ("IH" $! e1 cs1 w1 _ (drop k ys) with "[%] HF HE Hs Hsl Hsuffix [-]");
    [split; [exact Hregs|]; split; [lia|]; split; [rewrite length_drop; lia|by apply Forall_drop] |
     iIntros (cs'' wr ok) "HF HE Hs Hsl Hsuffix"; iApply ("HK" with "HF HE Hs Hsl [-]");
     rewrite (source_split _ _ _ _ k Hk); iFrame].
  destruct (Z.eq_dec (nchar cs) 128) as [Hfull|Hfree].
  - branch_as false. step. iApply wp_call_bind; [vx | exact Hflush | reflexivity |]. iNext.
    iApply (wp_wprintf_dispatch vb self E Hfn Hcall Hbackend with "Hvt Hwv HF HE Hs"); [reflexivity|].
    iNext. iIntros (ok) "HF HE Hs". resume. destruct ok; do 4 step; branch; step.
    + iApply (write_room _ bb br fp [] _ dq sb sr so sc ys with "Hs Hsl Hy [-]");
        try (unfold write_regs; repeat split; lk_prove); try lk_prove; try assumption;
        try (lookups; cbn [ptr_addr ptr_cap length]; unwrap2; reflexivity). next_chunk ys.
    + iApply wp_ret_void. iNext. by iApply ("HK" with "HF HE Hs Hsl Hy").
  - branch_as true. step. branch. step. iApply (write_room _ bb br fp cs written dq sb sr so sc ys with "Hs Hsl Hy [-]");
      try (unfold write_regs; repeat split; lk_prove); try lk_prove; try assumption;
      try (lookups; cbn [ptr_addr ptr_cap]; unwrap2; reflexivity); [lia|next_chunk ys].
Qed.

(** The counted write borrows either a mutable wide argument or a
    read-only literal. Both zero-length writes and writes to a failed
    stage return the loan without reading the source. *)
Lemma wp_wprintf_write fr bb br fp cs written ok dq sb sr so sc ys vreg Φ :
  call_frame wprintf_write_fn [WPtr (obj bb); WPtr (mkPtr (sb+so) sc); WInt (nchar ys)] = Some fr ->
  0 < sb -> sb mod 8 = 0 -> 0 <= so -> sb+so+4*nchar ys <= r_end sr -> r_end sr <= 2^63 ->
  sc = Obj sb \/ sc = Ro sb -> Forall (fun c => 0 <= c < 2^32) ys ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗ file_wide ge vb self fp 1 -∗ E -∗ wide_stage bb br fp cs written ok -∗
  liveq dq sb sr -∗ bytesq dq sb so (stage_bytes ys) -∗
  ▷ (∀ cs' written' ok', file_wide ge vb self fp 1 -∗ E -∗ wide_stage bb br fp cs' written' ok' -∗
    liveq dq sb sr -∗ bytesq dq sb so (stage_bytes ys) -∗ Φ RetVoid) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hfr Hb0 Hsa Hso Hse Hsr Hsc Vys. injection Hfr as <-. iIntros "#Hvt #Hwv HF HE Hs Hsl Hy HK".
  open_stage. step. step. check "Hl". load_mode "Hl" "Hm". step. destruct ok; branch; step.
  - iApply (write_loop bb br fp dq sb sr sc vreg Φ Hb0 Hsa Hsr Hsc with "Hvt Hwv [%] HF HE [-Hsl Hy HK] Hsl Hy HK");
      [|iExists tail, slots; iFrame; done]. split_and!; try assumption. unfold write_regs.
    repeat split; lookups; cbn [ptr_addr ptr_cap]; unwrap2; reflexivity.
  - iApply wp_ret_void. iNext. iApply ("HK" $! cs written false with "HF HE [-Hsl Hy] Hsl Hy"). iExists tail, slots. iFrame. done.
Qed.
End write.
