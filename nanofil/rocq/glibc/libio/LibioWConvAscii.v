(** Hello prints its greeting through a wide stream, and the stream
    must turn its wide characters into bytes. In the C locale an ASCII
    step does that: it writes one byte for each character below 128.
    For a larger character it asks transliteration for a replacement,
    such as "(C)" for a copyright sign, and converts the replacement
    with the same step. That second call stops at the first character
    that it cannot convert, so it never asks for a replacement itself.

    This file proves the step as transliteration calls it. The step's
    loop reads whole characters from its input and writes bytes into
    its output window. It stops when the input ends, when the window
    fills, or when it meets a character that it cannot convert. The C
    functions are `c: __gconv_transform_internal_ascii` and
    `c: __gconv_transliterate`. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic AbsInfer.
From Glibc Require Import CodePrelude HelloImageCode47 HelloImageCode70 HelloImageLoad HelloImageMbsObjs
  HelloImageWFwideObjs HelloImageWConvObjs OsWorld FileInv LibioLogic LibioDefaultXsputnBuf LibioWIdle Mbrtowc CBlocks Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation objp b := (mkPtr b (Obj b)).
Local Abbreviation rop b := (mkPtr b (Ro b)).

(** This definition is the ASCII step as Hello's image holds it. *)
Definition glibc_internal_ascii := Eval vm_compute in
  code_function (code_module (TApp "module" [TList hello_image_items_47])) "__gconv_transform_internal_ascii".

(** When a character has no byte of its own, the step calls this function to find a replacement. *)
Definition glibc_translit := Eval vm_compute in
  code_function (code_module (TApp "module" [TList hello_image_items_70])) "__GI___gconv_transliterate".

(** The loop changes only its own temporaries, so a proof of it can
    keep every other value of the caller. The compiler copied the loop
    into the step twice, and only one copy runs for the C locale: its
    blocks start with `c: iw_3.`. This list holds the names that the
    copy defines. *)
Definition ia_loop_names : list name := Eval vm_compute in
  flat_map (fun b => app (map (fun p => match p with Phi d _ _ => d end) (b_phis b)) (flat_map inst_defs (b_insts b)))
    (filter (fun b => match b_label b with TAtom s => String.prefix "iw_3."%string s | _ => false end)
      (fn_blocks glibc_internal_ascii)).

(** ## What the conversion reads

    The conversion reads constant tables of the C locale and the
    thread's locale pointer. Startup holds the constants as read-only
    shares, and a caller lends the locale cells for the call. *)

Section objects.
Context `{!gen_heapGS piece pval Σ}.

(** The conversion reads these read-only objects. They include the
    converter path that `c: mbrtowc` reads and the output step's
    handle. They also include the transliteration tables, the zero
    word after each table of strings, and the words that lead to the
    tables. *)
Definition wconv_ro : iProp Σ :=
  mbr_tables ∗ ptsq DfracDiscarded hello_wfwide_ps ∗ ptsq DfracDiscarded hello_wc_tables_ps ∗
  ptsq DfracDiscarded hello_wc_words_ps ∗ ptsq DfracDiscarded hello_wc_tails_ps.

Global Instance wconv_ro_persistent : Persistent wconv_ro.
Proof using Type. unfold wconv_ro, mbr_tables, liveq, pcellq. apply _. Qed.

(** Transliteration finds the C locale through the thread's locale
    pointer, as `c: mbrtowc` does, so it borrows the same cells. *)
Definition wlocale (dq : dfrac) : iProp Σ := mbr_locale dq.

(** The flags of the output step say that it is the last step and that
    it transliterates. A failed conversion may also have set bit 30. *)
Definition wflags_ok (fl : Z) : Prop :=
  fl = Z.lor gconv_is_last gconv_translit \/ fl = Z.lor (Z.lor gconv_is_last gconv_translit) gconv_illegal_seen.

End objects.

(** ## The conversion loop *)

Section loop.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** The tactic [ia_branch] takes a jump whose condition the step
    computes from constants. *)
Local Ltac ia_branch :=
  iStartProof; eapply step_wand; [eapply wp_branch; inst; vx |];
  repeat match goal with |- context [if ?c then To ?a else To ?b] =>
    let v := eval vm_compute in c in
    lazymatch v with true => idtac | false => idtac end; change c with v; cbn [edge_label] end.

(** The tactic [keep] carries a lookup across a loop that leaves the
    name alone. *)
Local Ltac keep Hs x := let L := fresh "L" in pose proof (Hs (TAtom x) eq_refl) as L; cbn in L.

(** The tactic [ia_cell] allocates one pointer cell, which starts null. *)
Local Ltac ia_cell b H L C :=
  iApply wp_alloc; [reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |]; iNext; iIntros (b H) "Hob";
  change (0 < b /\ b mod 16 = 0 /\ b + 16 <= 2^48) in H;
  iDestruct (obj_zero_block with "Hob") as "(Hobl & Hobb & Hoba)"; [vm_compute; congruence|];
  iDestruct (Mbrtowc.MbVL.zero_cell_prefix b 0 8 with "Hobb Hoba") as "(Hobc & _ & _)";
  iAssert (live b (mkRegion b (b + 16) Heap Live)) with "Hobl" as L; iRename "Hobc" into C.

(** The step takes a pointer to its count of irreversible
    conversions. The pointer is null when transliteration calls the
    step, and it names a local counter otherwise. *)
Definition irr_ptr (irr : option Z) : ptr := match irr with Some lb => objp lb | None => null end.

(** The flags have the bits that the step tests: it is the last step
    and transliterates, and it does not ignore errors. *)
Lemma wflags_bits fl : wflags_ok fl ->
  0 <= fl < 2 ^ 31 /\ Z.land fl 1 = 1 /\ Z.land fl 8 = 8 /\ Z.land fl 2 = 0.
Proof using Type. intros [-> | ->]; vm_compute; split_and!; congruence. Qed.

(** A 16-byte aligned address is 8-byte aligned. *)
Lemma mod16_mod8 b : b mod 16 = 0 -> b mod 8 = 0.
Proof using Type.
  intros H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|]. destruct H as [q ->]. exists (2 * q). lia.
Qed.

(** An unsigned 32-bit load of a character's bytes is the character. *)
Lemma load_uw_char x : 0 <= x < 2 ^ 32 -> extended Uw W (of_bytes (le_bytes x 4)) = Some (WInt x).
Proof using Type. intros Hx. rewrite of_bytes_int; [|exact Hx]. cbn. by rewrite !(Z.mod_small x (2 ^ 32)). Qed.

(** Each character takes four bytes. *)
Lemma le_words_length cs : length (le_words cs) = (4 * length cs)%nat.
Proof using Type.
  induction cs as [|c cs IH]; [reflexivity|]. rewrite /le_words. cbn [flat_map]. rewrite length_app.
  fold (le_words cs). rewrite IH. unfold le_bytes. rewrite length_fmap length_seq. cbn [length]. lia.
Qed.

(** The loop reads one whole character at a time. *)
Lemma wchar_at dq b o cs (k : nat) x : cs !! k = Some x ->
  bytesq dq b o (le_words cs) ⊢ bytesq dq b (o + 4 * Z.of_nat k) (le_bytes x 4) ∗
    (bytesq dq b (o + 4 * Z.of_nat k) (le_bytes x 4) -∗ bytesq dq b o (le_words cs)).
Proof using Type.
  intros Hk. rewrite -{1 2}(take_drop_middle cs k x Hk) /le_words flat_map_app. cbn [flat_map].
  rewrite /bytesq byte_ps_app byte_ps_app !ptsq_app.
  assert (Hl : length (flat_map (fun c => le_bytes c 4) (take k cs)) = (4 * k)%nat).
  { fold (le_words (take k cs)). rewrite le_words_length length_take_le; [lia|]. apply lookup_lt_Some in Hk. lia. }
  rewrite Hl. replace (Z.of_nat (4 * k)) with (4 * Z.of_nat k) by lia.
  iIntros "(Hp & Hc & Hs)". iFrame "Hc". iIntros "Hc". iFrame.
Qed.

(** The loop writes one byte of its output window at a time. *)
Lemma bytes_split_at b o xs (k : nat) x : xs !! k = Some x ->
  bytes b o xs ⊣⊢ bytes b o (take k xs) ∗ ibyte b (o + Z.of_nat k) x ∗ bytes b (o + Z.of_nat k + 1) (drop (S k) xs).
Proof using Type.
  intros Hk. rewrite -{1}(take_drop_middle xs k x Hk) bytes_app.
  rewrite length_take_le; [|apply lookup_lt_Some in Hk; lia].
  rewrite /bytes byte_ps_cons /ibyte /pts !big_sepL_cons big_sepL_nil.
  iSplit; [iIntros "($ & $ & $)" | iIntros "($ & [$ _] & $)"].
Qed.

Lemma bytes_put_at b o xs (k : nat) y : (k < length xs)%nat ->
  bytes b o (take k xs) ∗ ibyte b (o + Z.of_nat k) y ∗ bytes b (o + Z.of_nat k + 1) (drop (S k) xs) ⊢
  bytes b o (<[k := y]> xs).
Proof using Type.
  intros Hk. rewrite (bytes_split_at b o (<[k := y]> xs) k y); [|apply list_lookup_insert_eq; lia].
  rewrite take_insert_ge; [|lia]. rewrite drop_insert_lt; [|lia]. done.
Qed.

(** A pointer cell keeps its pointer when the address is rewritten. *)
Lemma pcell_congr b o x y c : x = y -> pcell b o (mkPtr x c) ⊢ pcell b o (mkPtr y c).
Proof using Type. intros ->. done. Qed.

(** Both callers copy ASCII characters and skip tags the same way.
    The loop either reaches its exit with a status or stops at a character
    for which the outer caller must try transliteration. The inner caller
    has no irreversible counter and returns an error at that character. *)
Lemma ia_loop ib ireg di dqb ic io ws tb treg to ip ipreg op opreg (irr : option Z) Φ :
  let n := Z.of_nat (length ws) in
  ic = Obj ib \/ ic = Ro ib -> 0 < ib -> 0 <= io -> ib + io + 4 * n <= r_end ireg -> r_end ireg <= 2 ^ 63 ->
  Forall (fun c => 0 <= c < 2 ^ 32) ws ->
  0 < tb -> 0 <= to -> r_end treg <= 2 ^ 63 ->
  0 < ip -> ip mod 8 = 0 -> ip + 8 <= r_end ipreg -> r_end ipreg <= 2 ^ 63 ->
  0 < op -> op mod 8 = 0 -> op + 8 <= r_end opreg -> r_end opreg <= 2 ^ 63 ->
  ⊢ ∀ e st k j zs, ⌜let m := Z.of_nat (length zs) in
      lookup (TAtom "v6") e = Some (WPtr (mkPtr (ib + io + 4 * n) ic)) /\
      lookup (TAtom "iw_3.v19") e = Some (WPtr (objp ip)) /\ lookup (TAtom "chk87") e = Some (WPtr (objp ip)) /\
      lookup (TAtom "iw_3.v22") e = Some (WPtr (objp op)) /\ lookup (TAtom "chk88") e = Some (WPtr (objp op)) /\
      lookup (TAtom "v101") e = Some (WPtr (mkPtr (tb + to + m) (Obj tb))) /\
      lookup (TAtom "v111") e = Some (WPtr (irr_ptr irr)) /\ lookup (TAtom "v89") e = Some (WInt 0) /\
      lookup (TAtom "iw_3.pr.2") e = Some (WInt st) /\
      0 <= st < 2 ^ 32 /\ 0 <= k <= n /\ 0 <= j <= m /\ tb + to + m <= r_end treg /\
      Forall (fun z => 0 <= z < 256) zs⌝ -∗
    liveq di ib ireg -∗ bytesq dqb ib io (le_words ws) -∗ live tb treg -∗ bytes tb to zs -∗
    live ip ipreg -∗ pcell ip 0 (mkPtr (ib + io + 4 * k) ic) -∗ live op opreg -∗ pcell op 0 (mkPtr (tb + to + j) (Obj tb)) -∗
    ▷ (∀ e' (st' : option Z) k' j' zs', ⌜same_out ia_loop_names e e' /\
         (match st' with Some r => lookup (TAtom "iw_3.pr.3") e' = Some (WInt r) | None => irr <> None /\ k' < n end) /\
         k <= k' <= n /\ j <= j' <= Z.of_nat (length zs) /\ length zs' = length zs /\
         Forall (fun z => 0 <= z < 256) zs'⌝ -∗
       liveq di ib ireg -∗ bytesq dqb ib io (le_words ws) -∗ live tb treg -∗ bytes tb to zs' -∗
       live ip ipreg -∗ pcell ip 0 (mkPtr (ib + io + 4 * k') ic) -∗
       live op opreg -∗ pcell op 0 (mkPtr (tb + to + j') (Obj tb)) -∗
       WP (ERun (mkFrame glibc_internal_ascii e' [] None (body_at glibc_internal_ascii
         (if st' then "iw_3.L27" else "iw_3.L93"))) : sexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame glibc_internal_ascii e [] None (body_at glibc_internal_ascii "iw_3.L25")) : sexpr) {{ Φ }}.
Proof using Type*.
  intros n Hic Hib Hio Hie Hir Hws Htb Hto Htr Hip Hip8 Hipe Hipr Hop Hop8 Hope Hopr.
  iLöb as "IH". iIntros (e st k j zs Hlk) "Hil Hin Htl Hzs Hipl Hip Hopl Hop HK".
  destruct Hlk as (Hv6 & Hv19 & Hc87 & Hv22 & Hc88 & Hv101 & Hv111 & Hv89 & Hst & Hst32 & Hk & Hj & Hte & Hzs).
  assert (Hlc : forall dq, live_capq dq ic ireg = liveq dq ib ireg) by (intros; destruct Hic as [-> | ->]; reflexivity).
  assert (Hn0 : 0 <= n) by lia.
  body_start glibc_internal_ascii "iw_3.L25".
  check "Hipl". iEval (rewrite -Hlc) in "Hil". load_pointer_dq "Hipl Hip Hil" by a2. iNext. iIntros "Hipl Hip Hil".
  iEval (rewrite Hlc) in "Hil". step. step. step.
  Local Ltac exit_side := split_and!; try same_tac; try lia; try assumption;
    rewrite Symbolic.lookup_after_put_same; do 2 f_equal; first [apply Z.mod_small; lia | reflexivity].
  destruct (Z.eq_dec k n) as [-> | Hkn].
  { branch_as true. step. iApply ("HK" $! _ (Some st) n j zs with "[%] Hil Hin Htl Hzs Hipl Hip Hopl Hop"). exit_side. }
  branch_as false. step. iEval (rewrite -Hlc) in "Hil". load_pointer_dq "Hipl Hip Hil" by a2. iNext. iIntros "Hipl Hip Hil".
  iEval (rewrite Hlc) in "Hil". step. step. step. branch_as true. step.
  set (m := Z.of_nat (length zs)) in *. check "Hopl". load_pointer_dq "Hopl Hop Htl" by a2. iNext. iIntros "Hopl Hop Htl".
  step. step. step. destruct (Z.eq_dec j m) as [-> | Hjm].
  { branch_as false. step. iApply ("HK" $! _ (Some 5) k m zs with "[%] Hil Hin Htl Hzs Hipl Hip Hopl Hop"). exit_side. }
  branch_as true. step.
  destruct (lookup_lt_is_Some_2 ws (Z.to_nat k) ltac:(lia)) as [c Hc].
  assert (Hc32 : 0 <= c < 2 ^ 32) by exact (Forall_lookup_1 _ _ _ _ Hws Hc).
  iEval (rewrite -Hlc) in "Hil". load_pointer_dq "Hipl Hip Hil" by a2. iNext. iIntros "Hipl Hip Hil".
  iEval (rewrite Hlc) in "Hil". check_read_dq "Hil" by a2. iNext. iIntros "Hil".
  iDestruct (wchar_at _ _ _ _ _ c Hc with "Hin") as "[Hc Hin]".
  assert (Ek : Z.of_nat (Z.to_nat k) = k) by lia. iEval (rewrite Ek) in "Hc". iEval (rewrite Ek) in "Hin".
  load_bytes_dq "Hil Hc" decode (apply load_uw_char; lia) by a2. iNext. iIntros "Hil Hc".
  iDestruct ("Hin" with "Hc") as "Hin". step.
  destruct (Z.leb_spec c 127) as [Hasc | Hhigh].
  - (* An ASCII character becomes one byte. *)
    branch_as true. step. load_pointer_dq "Hopl Hop Htl" by a2. iNext. iIntros "Hopl Hop Htl".
    step. check "Hopl". store "Hopl" "Hop". check "Hipl".
    iEval (rewrite -Hlc) in "Hil". load_pointer_dq "Hipl Hip Hil" by a2. iNext. iIntros "Hipl Hip Hil".
    iEval (rewrite Hlc) in "Hil". check_read_dq "Hil" by a2. iNext. iIntros "Hil".
    iDestruct (wchar_at _ _ _ _ _ c Hc with "Hin") as "[Hc Hin]". iEval (rewrite Ek) in "Hc". iEval (rewrite Ek) in "Hin".
    load_bytes_dq "Hil Hc" decode (apply load_uw_char; lia) by a2. iNext. iIntros "Hil Hc".
    iDestruct ("Hin" with "Hc") as "Hin". step. check "Htl".
    destruct (lookup_lt_is_Some_2 zs (Z.to_nat j) ltac:(lia)) as [z Hz].
    iEval (rewrite (bytes_split_at tb to zs (Z.to_nat j) z Hz)) in "Hzs". iDestruct "Hzs" as "(Hz1 & Hzb & Hz2)".
    assert (Ej : Z.of_nat (Z.to_nat j) = j) by lia. rewrite !Ej.
    iApply (wp_raw_store_byte with "Htl Hzb"); [vx | vx | reflexivity | cbn; unfold raw_address; unwrap2; lia | wi_store |].
    iNext. iIntros "Htl Hzb".
    assert (Eb : ((((c mod 2 ^ 32) mod 256) mod 2 ^ 32) mod 2 ^ 32) mod 256 = c).
    { rewrite (Z.mod_small c (2 ^ 32)); [|lia]. rewrite (Z.mod_small c 256); [|lia].
      rewrite (Z.mod_small c (2 ^ 32)); [|lia]. rewrite (Z.mod_small c (2 ^ 32)); [|lia]. apply Z.mod_small; lia. }
    iEval (rewrite Eb) in "Hzb".
    iDestruct (bytes_put_at tb to zs (Z.to_nat j) c with "[Hz1 Hzb Hz2]") as "Hzs"; [lia | rewrite Ej; iFrame |].
    iEval (rewrite -Hlc) in "Hil". load_pointer_dq "Hipl Hip Hil" by a2. iNext. iIntros "Hipl Hip Hil".
    iEval (rewrite Hlc) in "Hil". step. check "Hipl". store "Hipl" "Hip". step. step.
    iApply ("IH" $! _ st (k + 1) (j + 1) (<[Z.to_nat j := c]> zs) with "[%] Hil Hin Htl Hzs Hipl [Hip] Hopl [Hop] [HK]").
    + rewrite length_insert. split_and!; try (repeat (rewrite Symbolic.lookup_after_put_other; [|reflexivity]); assumption);
        try lia; try assumption.
      * rewrite Symbolic.lookup_after_put_same Z.mod_small; [reflexivity | lia].
      * apply Forall_insert; [assumption | lia].
    + iApply (pcell_congr with "Hip"). cbn [ptr_addr]. unwrap2. lia.
    + iApply (pcell_congr with "Hop"). cbn [ptr_addr]. unwrap2. lia.
    + iNext. iIntros (e' st' k' j' zs' (Hs & Hp3 & Hk' & Hj' & Hl' & Hz')).
      rewrite length_insert in Hj' Hl'.
      iIntros "Hil Hin Htl Hzs Hipl Hip Hopl Hop".
      iApply ("HK" $! e' st' k' j' zs' with "[%] Hil Hin Htl Hzs Hipl Hip Hopl Hop").
      split_and!; try lia; try assumption. eapply same_out_trans; [|exact Hs]. same_tac.
  - (* A character above 127 is skipped when it is a tag character and
       otherwise ends the loop, because this caller has no counter of
       irreversible conversions. *)
    branch_as false. step.
    iEval (rewrite -Hlc) in "Hil". load_pointer_dq "Hipl Hip Hil" by a2. iNext. iIntros "Hipl Hip Hil".
    iEval (rewrite Hlc) in "Hil". check_read_dq "Hil" by a2. iNext. iIntros "Hil".
    iDestruct (wchar_at _ _ _ _ _ c Hc with "Hin") as "[Hc Hin]". iEval (rewrite Ek) in "Hc". iEval (rewrite Ek) in "Hin".
    load_bytes_dq "Hil Hc" decode (apply load_uw_char; lia) by a2. iNext. iIntros "Hil Hc".
    iDestruct ("Hin" with "Hc") as "Hin". step. step.
    change (2 ^ ((7 mod 2 ^ 32) mod 32)) with 128. rewrite !(Z.mod_small c (2 ^ 32)); [|lia..].
    assert (Hcq : 0 <= c / 128 < 2 ^ 32) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    rewrite !(Z.mod_small (c / 128) (2 ^ 32)); [|lia..].
    destruct (Z.eq_dec (c / 128) 7168) as [Htag | Hntag].
    + branch_as false. step.
      iEval (rewrite -Hlc) in "Hil". load_pointer_dq "Hipl Hip Hil" by a2. iNext. iIntros "Hipl Hip Hil".
      iEval (rewrite Hlc) in "Hil". step. check "Hipl". store "Hipl" "Hip". step. step.
      iApply ("IH" $! _ st (k + 1) j zs with "[%] Hil Hin Htl Hzs Hipl [Hip] Hopl Hop [HK]").
      * split_and!; try (repeat (rewrite Symbolic.lookup_after_put_other; [|reflexivity]); assumption); try lia; try assumption.
        rewrite Symbolic.lookup_after_put_same Z.mod_small; [reflexivity | lia].
      * iApply (pcell_congr with "Hip"). cbn [ptr_addr]. unwrap2. lia.
      * iNext. iIntros (e2 st2 k2 j2 zs2 (Hs & Hp3 & Hk2 & Hj2 & Hl2 & Hz2)) "Hil Hin Htl Hzs Hipl Hip Hopl Hop".
        iApply ("HK" $! e2 st2 k2 j2 zs2 with "[%] Hil Hin Htl Hzs Hipl Hip Hopl Hop").
        split_and!; try lia; try assumption. eapply same_out_trans; [|exact Hs]. same_tac.
    + branch_as true. step. destruct irr as [lb|].
      * iApply ("HK" $! _ None k j zs with "[%] Hil Hin Htl Hzs Hipl Hip Hopl Hop"). split_and!; first [same_tac | congruence | lia | assumption].
      * step. step. branch_as false. step.
        iApply ("HK" $! _ (Some 6) k j zs with "[%] Hil Hin Htl Hzs Hipl Hip Hopl Hop"). exit_side.
Qed.
(** Transliteration runs the step on one replacement, with no counter
    of irreversible conversions and with its own cells for the input
    and output positions. The step converts a prefix of the
    replacement and moves both positions past what it converted.
    It leaves the stream's flags unchanged even when it rejects a character. *)
Lemma wp_ia_inner fr stp wd wreg ib ireg di dqb ic io ws tb treg to zs j fl pi pireg po poreg Φ :
  let n := Z.of_nat (length ws) in let m := Z.of_nat (length zs) in
  call_frame glibc_internal_ascii [WPtr stp; WPtr (mkPtr (wd + 168) (Obj wd)); WPtr (objp pi);
    WPtr (mkPtr (ib + io + 4 * n) ic); WPtr (objp po); WPtr null; WInt 0; WInt 0] = Some fr ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 ->
  ic = Obj ib \/ ic = Ro ib -> 0 < ib -> 0 <= io -> ib + io + 4 * n <= r_end ireg -> r_end ireg <= 2 ^ 63 ->
  Forall (fun c => 0 <= c < 2 ^ 32) ws ->
  0 < tb -> 0 <= to -> tb + to + m <= r_end treg -> r_end treg <= 2 ^ 63 -> 0 <= j <= m ->
  Forall (fun z => 0 <= z < 256) zs ->
  0 < pi -> pi mod 8 = 0 -> pi + 8 <= r_end pireg -> r_end pireg <= 2 ^ 63 ->
  0 < po -> po mod 8 = 0 -> po + 8 <= r_end poreg -> r_end poreg <= 2 ^ 63 -> wflags_ok fl ->
  live wd wreg -∗ pcell wd 176 (mkPtr (tb + to + m) (Obj tb)) -∗ bytes wd 184 (int_bytes fl) -∗
  liveq di ib ireg -∗ bytesq dqb ib io (le_words ws) -∗ live tb treg -∗ bytes tb to zs -∗
  live pi pireg -∗ pcell pi 0 (mkPtr (ib + io) ic) -∗ live po poreg -∗ pcell po 0 (mkPtr (tb + to + j) (Obj tb)) -∗
  ▷ (∀ st k' j' zs' fl', ⌜0 <= k' <= n /\ j <= j' <= m /\ length zs' = length zs /\
       Forall (fun z => 0 <= z < 256) zs' /\ fl' = fl⌝ -∗
     live wd wreg -∗ pcell wd 176 (mkPtr (tb + to + m) (Obj tb)) -∗ bytes wd 184 (int_bytes fl') -∗
     liveq di ib ireg -∗ bytesq dqb ib io (le_words ws) -∗ live tb treg -∗ bytes tb to zs' -∗
     live pi pireg -∗ pcell pi 0 (mkPtr (ib + io + 4 * k') ic) -∗
     live po poreg -∗ pcell po 0 (mkPtr (tb + to + j') (Obj tb)) -∗ Φ (Ret (WInt st))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros n m Hfr Hwd Hwd8 Hwe Hwr Hic Hib Hio Hie Hir Hws Htb Hto Hte Htr Hj Hzs Hpi Hpi8 Hpie Hpir Hpo Hpo8 Hpoe Hpor Hfl.
  iIntros "Hwl Hoe Hfl Hil Hin Htl Hzs Hpil Hpi Hpol Hpo HK".
  injection Hfr as <-. destruct (wflags_bits fl Hfl) as (Hfl31 & Hb1 & Hb8 & Hb2).
  assert (Hlc : forall dq, live_capq dq ic ireg = liveq dq ib ireg) by (intros; destruct Hic as [-> | ->]; reflexivity).
  step. iApply wp_alloc; [reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |]; iNext. iIntros (lb Hlb) "Hlb".
  change (0 < lb /\ lb mod 16 = 0 /\ lb + 16 <= 2^48) in Hlb. destruct Hlb as (Hlb & Hlb16 & Hlbe).
  iDestruct (obj_zero_block with "Hlb") as "(Hlbl & Hlbx & _)"; [vm_compute; congruence|].
  iDestruct (bytes_take_drop _ _ _ 8 with "Hlbx") as "[Hlbx _]"; [vm_compute; lia|].
  iAssert (icell lb 0 0) with "Hlbx" as "Hlb0". iAssert (live lb (mkRegion lb (lb + 16) Heap Live)) with "Hlbl" as "Hlbl".
  iApply wp_alloc; [reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |]; iNext. iIntros (? _) "_".
  do 3 step. check "Hwl".
  load_bytes_dq "Hwl Hfl" decode (apply load_sw_int; lia) by a2. iNext. iIntros "Hwl Hfl". step.
  iStartProof; eapply step_wand; [eapply wp_branch; inst; vx |]. rewrite !(Z.mod_small fl (2^32)); [|lia..].
  change (1 mod 2^32) with 1. rewrite Hb1. change (1 mod 2^32 =? 0) with false. cbn [edge_label]. do 3 step.
  branch_as true. step. check "Hpil". iEval (rewrite -Hlc) in "Hil". load_pointer_dq "Hpil Hpi Hil" by a2.
  iNext. iIntros "Hpil Hpi Hil". iEval (rewrite Hlc) in "Hil". do 3 step. branch_as true. step.
  check "Hpol". load_pointer_dq "Hpol Hpo Htl" by a2. iNext. iIntros "Hpol Hpo Htl". do 3 step.
  check "Hwl". load_pointer_dq "Hwl Hoe Htl" by a2. iNext. iIntros "Hwl Hoe Htl".
  check "Hlbl". store_long "Hlbl" "Hlb0". do 2 step. ia_branch. do 4 step. ia_branch. step. ia_branch. step.
  check "Hpil". iEval (rewrite -Hlc) in "Hil". load_pointer_dq "Hpil Hpi Hil" by a2. iNext. iIntros "Hpil Hpi Hil".
  iEval (rewrite Hlc) in "Hil". check "Hlbl".
  iApply (wp_raw_load with "Hlbl Hlb0"); [reflexivity | vx | reflexivity | a2 |]. iNext. iIntros "Hlbl Hlb0".
  ia_branch. do 2 step. ia_cell ip Hip "Hipl" "Hip". ia_cell oq Hoq "Hopl" "Hop". step.
  check "Hwl". load_bytes_dq "Hwl Hfl" decode (apply load_sw_int; lia) by a2. iNext. iIntros "Hwl Hfl".
  check "Hpil". iEval (rewrite -Hlc) in "Hil". load_pointer_dq "Hpil Hpi Hil" by a2. iNext. iIntros "Hpil Hpi Hil".
  iEval (rewrite Hlc) in "Hil". check "Hipl". store "Hipl" "Hip". check "Hopl". store "Hopl" "Hop". step.
  cbn [edge_label]. iApply wp_enter; [reflexivity | vx | iNext; cbn [b_insts b_jump]].
  destruct Hip as (Hip & Hip16 & Hipe). destruct Hoq as (Hoq & Hoq16 & Hoqe).
  iApply (ia_loop ib ireg di dqb ic io ws tb treg to ip _ oq _ None Φ with "[%] Hil Hin Htl Hzs Hipl [Hip] Hopl Hop");
    try solve [cbn [r_end]; lia | assumption | reflexivity | apply mod16_mod8; assumption].
  { split_and!; try solve [reflexivity | lia | assumption | vm_compute; congruence]. }
  { iApply (pcell_congr with "Hip"). lia. }
  iNext. iIntros (e2 [st2|] k2 j2 zs2 (Hs & Hp3 & Hk2 & Hj2 & Hl2 & Hz2)) "Hil Hin Htl Hzs Hipl Hip Hopl Hop"; [|tauto].
  keep Hs "chk87". keep Hs "iw_3.v19". keep Hs "chk6". keep Hs "v4". keep Hs "chk88". keep Hs "iw_3.v22".
  keep Hs "v88". keep Hs "v89". keep Hs "v8". clear Hs.
  body_start glibc_internal_ascii "iw_3.L27". check "Hipl". iEval (rewrite -Hlc) in "Hil".
  load_pointer_dq "Hipl Hip Hil" by a2. iNext. iIntros "Hipl Hip Hil". iEval (rewrite Hlc) in "Hil".
  check "Hpil". store "Hpil" "Hpi". check "Hopl". load_pointer_dq "Hopl Hop Htl" by a2. iNext. iIntros "Hopl Hop Htl".
  step. branch_as false. step. check "Hpol". store "Hpol" "Hpo". iApply wp_ret; [reflexivity | vx |]. iNext.
  iApply ("HK" $! (st2 mod 2 ^ 32) k2 j2 zs2 fl with "[%] Hwl Hoe Hfl Hil Hin Htl Hzs Hpil [Hpi] Hpol [Hpo]").
  - split_and!; try lia; assumption.
  - iApply (pcell_congr with "Hpi"). unwrap2. lia.
  - iApply (pcell_congr with "Hpo"). unwrap2. lia.
Qed.

End loop.
