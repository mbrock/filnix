(** A file-backed printf buffer stages bytes when the stream has no room.
    Its full staging array goes to the stream's bulk write function, but
    its one-byte window goes to overflow only when that byte is used.
    Either stream call may fail. This proof returns the window on failure
    and hands it to buffer selection on success. *)

From Glibc Require Import Unit_libio_fileops_os Unit_libio_genops_os Unit_stdioZ2dcommon_printf_buffer_to_file_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules WordBits Heap ContractFrame Language Logic MemLogic.
From Glibc Require Import Fix OsWorld FileInv FileTidy LibioLogic CStruct PrintfLayout PrintfOut
  PrintfBufferFileNames PrintfBufferFlushEmpty
  PrintfBufferXsputnCall PrintfBufferXsputnStaging PrintfBufferOverflowCall PrintfBufferOverflowStaging.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic.
Import PrintfBufferFileNames.fn___printf_buffer_flush_to_file.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

(** The count field holds eight bytes. Reducing the count modulo 2^64
    leaves each byte unchanged, even when the caller described the field
    by a negative number. *)
Lemma flush_count_repr b o n : cell b o (n mod 2^64) = cell b o n.
Proof. unfold cell. cbn [List.map]. rewrite !WordBits.byte_of_mod64 //; lia. Qed.

Section loans.
Context `{!gen_heapGS piece pval Σ}.

(** The stream call reads only the pending prefix of the staging window.
    The caller keeps the suffix and all capability slots while it lends
    the prefix, including when that prefix is empty. *)
Lemma flush_stage_prefix b hi n : 0 <= n <= hi - (b+48) ->
  win_own b (b+48) hi ⊢ ∃ xs, ⌜Z.of_nat (length xs) = n /\ Forall (fun y => 0 <= y < 256) xs⌝ ∗
    bytes b 48 xs ∗ (bytes b 48 xs -∗ win_own b (b+48) hi).
Proof using Type.
  intros Hn. iIntros "(%ys & %cs & (%Hlen & %Hcs & %Hys) & Hys & Hcs)".
  replace (b+48-b) with 48 by lia. rewrite -{1}(take_drop (Z.to_nat n) ys).
  iDestruct (bytes_app with "Hys") as "[Hp Hs]". iExists (take (Z.to_nat n) ys).
  iSplit; [iPureIntro; split; [rewrite length_take; lia | by apply Forall_take]|].
  iFrame "Hp". iIntros "Hp". iExists ys, cs. iSplit; [done|].
  replace (b+48-b) with 48 by lia. iFrame "Hcs".
  iEval (rewrite -{1}(take_drop (Z.to_nat n) ys) bytes_app). iFrame.
Qed.

(** The bulk write loads a function through the stream's vtable. Lending
    that field and the stream's lifetime leaves the lock, buffer and all
    idle facts untouched. *)
Lemma flush_vtable vb self fb fd flags2 held :
  file_tidy vb self (mkPtr fb (Obj fb)) fd flags2 held ⊢ ∃ fr dq,
    ⌜fb + 224 <= r_end fr /\ r_end fr <= 2^63⌝ ∗ liveq dq fb fr ∗
    pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) ∗
    (liveq dq fb fr -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
      file_tidy vb self (mkPtr fb (Obj fb)) fd flags2 held).
Proof using Type.
  iIntros "(%fb' & %fr & %st & %nb & %H & Hl & Hf & Hrest)".
  pose proof H as (Hfp & _ & _ & He & Hr & _ & _ & _ & Hvt & _). injection Hfp as <-.
  iDestruct "Hf" as "(%Hlen & Ha & Hb & Hc & Hd & He & %Hcol & Hf & Hg & Hh & Hi & Hj & Hk & Hm & Hn & Ho & Hv)".
  iExists fr, (DfracOwn 1%Qp). iSplit; [done|]. rewrite -Hvt. iFrame "Hl Hv".
  iIntros "Hl Hv". iExists _, fr, st, nb. iSplit; [done|]. iFrame "Hl Hrest".
  rewrite /file_fields. iFrame. done.
Qed.
End loans.

(** The window contains n staged bytes and has room for cap bytes. Both
    supported capacities start at the same field of the wrapper. *)
Definition staged (bb : Z) (br : region) (n cap : Z) :=
  PWin bb br (bb+48) (bb+48+n) (bb+48+cap).

Section staging.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (vb : Z) (self : ptr) (fd flags2 : Z) (held : option Z) (E : iProp Σ).
Let F fp := file_tidy vb self fp fd flags2 held.
Context (Hfn : ge_fn ge "_IO_new_file_xsputn" Unit_libio_fileops_os.fn__IO_new_file_xsputn).
Context `{!Defines ge "__GI___overflow" Unit_libio_genops_os.fn___GI___overflow}.
Context (Hbulk : printf_xsputn_call_spec w0 registry ge F E)
        (Hchar : printf_overflow_call_spec w0 registry ge F E).
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

Local Lemma bulk_frame X : printf_xsputn_call_spec w0 registry ge F (E ∗ X).
Proof using Type*.
  intros fr fp b reg dq xs Φ Hb Ha Hn He Hr Hxs Hfr. iIntros "HF [HE HX] Hl Hxs HK".
  iApply (Hbulk with "HF HE Hl Hxs"); try assumption. iNext. iIntros (r Hr') "HF HE Hl Hxs".
  iApply ("HK" $! r with "[%] HF [HE HX] Hl Hxs"); [done|iFrame].
Qed.

Local Lemma char_frame X : printf_overflow_call_spec w0 registry ge F (E ∗ X).
Proof using Type*.
  intros fr fp ch Φ Hch Hfr. iIntros "HF [HE HX] HK".
  iApply (Hchar fr fp ch with "HF HE"); try assumption. iNext. iIntros (r Hr) "HF HE".
  iApply ("HK" $! r with "[%] HF [HE HX]"); [done|iFrame].
Qed.

Local Ltac pack_stage bb Hlo :=
  iSplit; [done|]; iSplitL "Hl"; [iEval (struct_sizes); iSplit; [done|iExact "Hl"]|];
  iSplitR "Hwl Hwin"; [iEval (struct_cells)|iFrame "Hwl"; rewrite Hlo];
  cbn [staged pw_obj pw_base pw_ptr pw_end]; try rewrite Z.add_0_r;
  try replace (bb+48+1) with (bb+49) by lia; try replace (bb+48+128) with (bb+176) by lia; iFrame.

(** The printf buffer keeps its stage on all paths up to the switch.
    The switch may select a different window, so the caller receives
    control at that block rather than a promise that the stage stays
    selected. *)
Lemma wp_flush_staged fr bb br fb vr n cap written Φ :
  call_frame Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_flush_to_file [WPtr (mkPtr bb (Obj bb))] = Some fr ->
  bb+176 <= r_end br -> cap = 1 \/ cap = 128 ->
  let w := staged bb br n cap in
  let state m count := (printf_buf bb br w count m ∗ pcell bb 40 (mkPtr fb (Obj fb)) ∗ F (mkPtr fb (Obj fb)) ∗ E)%I in
  let count := (written+n) mod 2^64 in
  vtables_ro ge vb vr -∗ state 4 written -∗
  ((∀ m, ⌜m = mode_failed \/ (m = 4 /\ n = 0 /\ cap = 1)⌝ -∗ state m count -∗ Φ RetVoid) ∧
  (∀ l from e, ⌜(l = "L40" \/ l = "L88") /\ lookup ‹buf› e = Some (WPtr (mkPtr bb (Obj bb)))⌝ -∗
    state 4 count -∗ WP (ERun (mkFrame Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_flush_to_file e [] None (Enter (TAtom l) from)) : sexpr) {{ Φ }})) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  cbn zeta. intros Hfr Hsize Hcap. iIntros "#Hvt (Hbuf & Hfp & HF & HE) HK".
  buf_open "Hbuf". pose proof Hw as Hord. unfold pwin_ok, staged in Hord.
  cbn [pw_obj pw_reg pw_base pw_ptr pw_end] in Hord.
  assert (Hlo : pw_lo (staged bb br n cap) = bb+48).
  { unfold pw_lo, staged. cbn [pw_base]. rewrite Z.add_mod //. destruct Hord as (_ & -> & _). rewrite Z.sub_0_r //. }
  rewrite Hlo. cbn [staged pw_obj pw_reg pw_base pw_ptr pw_end].
  iEval (rewrite /icell -flush_count_repr -/icell) in "Hwr".
  set (v := written mod 2^64). assert (Hv : 0 <= v < 2^64) by (apply Z.mod_pos_bound; lia).
  assert (Hcount : (written+n) mod 2^64 = (v+n) mod 2^64) by (unfold v; by rewrite Z.add_mod_idemp_l).
  rewrite Hcount. fold v.
  iDestruct (flush_stage_prefix bb _ n with "Hwin") as (xs (Hxs & Hrange)) "[Hxs Hback]"; [lia|].
  iDestruct "HF" as (fb' freg st nb Hp) "Hfields". pose proof Hp as (Haddr & Hal & Hpos & Hfe & Hfrg & _).
  injection Haddr as <-. iAssert (F (mkPtr fb (Obj fb))) with "[Hfields]" as "HF"; [iExists _, freg, st, nb; iFrame; done|].
  destruct Hcap as [-> | ->].
  - destruct (Z.eq_dec n 0) as [->|Hnz].
    + iDestruct ("Hback" with "Hxs") as "Hwin". rewrite !Z.add_0_r (Z.mod_small v _ Hv).
      replace (bb+48+1) with (bb+49) by lia.
      iApply (wp_printf_buffer_flush_empty fr bb br v with "Hl Hbase Hptr Hend Hwr"); try assumption; try lia.
      iNext. iIntros "Hl Hbase Hptr Hend Hwr". iDestruct "HK" as "[Hret _]". iApply ("Hret" $! 4 with "[%]"); [tauto|].
      iFrame "Hfp HF HE". pack_stage bb Hlo.
    + unfold file_size in Hfe. replace n with 1 in * by lia. destruct xs as [|ch [|z zs]]; cbn [length] in Hxs; try lia.
      rewrite Forall_singleton in Hrange. replace (bb+48+1) with (bb+49) by lia.
      iCombine "Hback Hwl HK" as "HX". let X := lazymatch iTypeOf "HX" with Some (_, ?P) => P end in
      iApply (wp_printf_overflow_staging F _ (char_frame X) fr bb br _ ch 4 v
        with "Hl Hbase Hptr Hend Hwr Hfp Hxs Hmode HF [HE HX] [] []"); try assumption; try lia.
      * iIntros "HF". iDestruct (file_tidy_live with "HF") as (b reg (Haddr & _)) "[Hl Hback]".
        injection Haddr as <-. iExists reg, (DfracOwn 1%Qp). iFrame.
      * iFrame.
      * iIntros "Hl Hbase Hptr Hend Hwr Hfp Hxs Hmode HF (HE & Hback & Hwl & [Hret _])". iDestruct ("Hback" with "Hxs") as "Hwin".
        iApply ("Hret" $! 0 with "[%]"); [by left|]. iFrame "Hfp HF HE". pack_stage bb Hlo.
      * iIntros (e Hv0) "Hl Hbase Hptr Hend Hwr Hfp Hxs Hmode HF (HE & Hback & Hwl & [_ Hsel])". iDestruct ("Hback" with "Hxs") as "Hwin".
        iApply ("Hsel" $! "L88" _ e with "[%]"); [tauto|]. iFrame "Hfp HF HE". pack_stage bb Hlo.
  - subst n. replace (bb+48+128) with (bb+176) by lia.
    iCombine "Hback Hwl HK" as "HX". let X := lazymatch iTypeOf "HX" with Some (_, ?P) => P end in
    iApply (wp_printf_xsputn_staging F _ Hfn (bulk_frame X) fr bb br _ vb vr xs 4 v
      with "Hvt Hl Hbase Hptr Hend Hwr Hfp Hxs Hmode HF [HE HX] [] []"); try assumption; try lia.
    + apply flush_vtable.
    + iFrame.
    + iIntros "Hl Hbase Hptr Hend Hwr Hfp Hxs Hmode HF (HE & Hback & Hwl & [Hret _])". iDestruct ("Hback" with "Hxs") as "Hwin".
      iApply ("Hret" $! 0 with "[%]"); [by left|]. iFrame "Hfp HF HE". pack_stage bb Hlo.
    + iIntros (e Hv0) "Hl Hbase Hptr Hend Hwr Hfp Hxs Hmode HF (HE & Hback & Hwl & [_ Hsel])". iDestruct ("Hback" with "Hxs") as "Hwin".
      iApply ("Hsel" $! "L40" _ e with "[%]"); [tauto|]. iFrame "Hfp HF HE". pack_stage bb Hlo.
Qed.

End staging.
