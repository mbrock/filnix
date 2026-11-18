(** The function `c: __vfprintf_internal (fp, fmt, ap, 0)` is what
    `c: fprintf` and `c: printf` call. It checks the stream, sets up a
    buffer that prints to the stream, runs the formatter on that
    buffer, and finishes the buffer. This module proves that the
    compiled function meets [vfprintf_spec] of
    [PrintfSpec](PrintfSpec.v).

    The function calls three others. The first sets the buffer up, the
    formatter fills it, and the last finishes it. The proof needs a
    contract for each call. The contract of the first call is proved in
    [PrintfFileInit](PrintfFileInit.v). The contracts of the other two
    calls are hypotheses of this module, and each speaks of a buffer
    that prints to a stream. *)

From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  VariadicLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv FileIdle FileTidy LibioLogic LibioFputsSpec AllocRo WordString FxprintfStream
  NarrowFormat NarrowArgs DcigettextExit FormatterCode FormatterSrc FormatterNames
  CFrame CStruct CBlocks PrintfLayout PrintfOut PrintfSpec PrintfBufferFileCode PrintfFileInit PrintfFileOut
  PrintfFlushChoice PrintfFlush PrintfDone PrintfFileEntry.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Module S := FormatterSrc.fn___vfprintf_internal.
Import FormatterNames.fn___vfprintf_internal.

(** The function allocates its local variables on the heap when it
    starts. The tactic [alloc_keep] runs one allocation and names the
    new object, and the tactic [alloc_drop] runs one whose object the
    proof never uses. *)
Local Ltac alloc_keep b H :=
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |];
  iNext; iIntros (b H) "Hobj".
Local Ltac alloc_drop :=
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |];
  iNext; iIntros (? _) "_".

Section vfprintf.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{!Defines ge "__printf_buffer_to_file_init" glibc___printf_buffer_to_file_init}.
Context `{!Defines ge "__printf_buffer_to_file_switch" glibc___printf_buffer_to_file_switch}.
(** The formatter and the function that finishes the buffer both write
    to the stream. A write needs the stream's descriptor to be open,
    and it needs errno to belong to the running thread. This section
    assumes the contracts of the two functions for every stream that
    has those properties, and other modules prove them. The predicate
    [fout_ok] collects the properties. *)
Context (Hformat : forall a, fout_ok a ->
  HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer") (printf_buffer_spec 4 (file_R a))).
Context (Hdone : forall a, fout_ok a ->
  HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer_to_file_done") (file_done_spec (file_R a))).
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The function compares the format with the null pointer. A pointer
    to a string is never null, because the string lies in an object,
    and no object starts at the address 0. *)
Lemma word_string_addr dq p s : word_string dq p s ⊢ ⌜0 < ptr_addr p < 2 ^ 64⌝.
Proof using Type.
  iIntros "(%b & %reg & %ws & %Hsh & _)". iPureIntro. destruct Hsh as [_ Hb _ Hst Hfit Hsp Hlen _ _ _].
  unfold wstart in Hfit. pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)).
  assert (1 <= Z.of_nat (length ws)) by (rewrite Hlen; apply Z.div_le_lower_bound; lia). lia.
Qed.

(** When the function starts, its live variables are its four
    arguments: the stream, the format, the argument list and the mode
    flags. The mode flags are 0, because `c: fprintf` passes none. *)
Definition vfp_sig : cut_sig := Eval vm_compute in cut_at S.temp_keys S.live_in "start".

Definition vfp_vals (x : vfp_in) : list (string * word) :=
  [("s", WPtr (vi_fp x)); ("format", WPtr (vi_fmt x)); ("ap", WPtr (vi_ap x)); ("mode_flags", WInt 0)].

(** The entry block reads the stream's orientation and makes an
    unoriented stream narrow. Both of its paths meet at the block
    `L28`, where the stream is narrow. The record [vfp_mid] is the
    logical state at that block. It adds to the function's input the
    stream's object, the region of that object, the stream's flags, and
    the three objects that the entry block allocates for local
    variables. *)
Record vfp_mid : Type := VfpMid {
  vm_in : vfp_in; vm_fb : Z; vm_freg : region; vm_fl : Z; vm_bb : Z; vm_b2 : Z; vm_b3 : Z
}.

(** After the entry block the function still holds its four
    arguments. It has also allocated three objects for its local
    variables, and it holds a pointer to each of them. *)
Definition mid_sig : cut_sig := Eval vm_compute in cut_at S.temp_keys S.live_in "L28".

Definition mid_vals (m : vfp_mid) : list (string * word) :=
  [("s", WPtr (mkPtr (vm_fb m) (Obj (vm_fb m)))); ("&wrap", WPtr (mkPtr (vm_bb m) (Obj (vm_bb m))));
   ("&_buffer", WPtr (mkPtr (vm_b2 m) (Obj (vm_b2 m)))); ("format", WPtr (vi_fmt (vm_in m)));
   ("&wrap@v290", WPtr (mkPtr (vm_b3 m) (Obj (vm_b3 m)))); ("ap", WPtr (vi_ap (vm_in m)));
   ("mode_flags", WInt 0)].

(** The function next tests whether the stream can be written, and it
    sets the stream's error flag when it cannot. To follow those steps
    the proof must own the fields that they touch. So it owns the
    stream's two flag words and its orientation, which is narrow, and
    it owns the stream's lifetime. It can put the stream together again
    with the flags as they are or with the error flag set. The proof
    also owns a fresh object of 176 zero bytes, which becomes the
    buffer, and everything else that the caller gave the function. *)
Definition mid_pre (m : vfp_mid) : iProp Σ :=
  let x := vm_in m in let fb := vm_fb m in let bb := vm_bb m in
  (⌜vfp_fits x /\ vi_fp x = mkPtr fb (Obj fb) /\ fb mod 8 = 0 /\ 0 < fb /\ fb + file_size <= r_end (vm_freg m) /\
    r_end (vm_freg m) <= 2 ^ 63 /\ 0 <= vm_fl m < 2 ^ 32 /\ Z.land (vi_flags2 x) io_need_lock = 0 /\
    (vi_fd x <> 0 -> has (vm_fl m) io_no_writes = false) /\ 0 < bb /\ bb mod 16 = 0 /\ bb + 176 <= 2 ^ 48⌝ ∗
   live fb (vm_freg m) ∗ int_cell fb off_flags (vm_fl m) ∗ int_cell fb off_flags2 (vi_flags2 x) ∗
   int_cell fb off_mode (2 ^ 32 - 1) ∗
   (∀ fl', ⌜fl' = vm_fl m \/ fl' = Z.lor (vm_fl m) io_err_seen⌝ -∗ live fb (vm_freg m) -∗
      int_cell fb off_flags fl' -∗ int_cell fb off_flags2 (vi_flags2 x) -∗ int_cell fb off_mode (2 ^ 32 - 1) -∗
      file_tidy (vi_vb x) (ow_self w0) (vi_fp x) (vi_fd x) (vi_flags2 x) (vi_held x)) ∗
   live bb (mkRegion bb (bb + 176) Heap Live) ∗ bytes bb 0 (replicate 176 0) ∗ auxes bb 0 (replicate 176 CNone) ∗
   word_string (vi_dq x) (vi_fmt x) (vi_bytes x) ∗ va_at (vi_ap x) (vi_skip x) (vi_xs x) ∗
   ([∗ list] a ∈ skipn (Z.to_nat (vi_skip x / 8)) (vi_xs x), str_arg a) ∗ errno_any (vi_eb x) ∗
   printf_ro ∗ fputs_ro (vi_vb x) ∗ malloc_ro)%I.

(** The function has two parts: the first settles the stream's
    orientation, and the second prints. Each part has a contract. The
    first part has the function's own contract. The second part starts
    from the state described above, and it promises what the function
    promises. *)
Definition vfp_blocks : list bspec :=
  [BSpec "start" None vfp_sig vfp_in vfp_vals (fs_pre vfprintf_spec) (fs_post vfprintf_spec);
   BSpec "L28" None mid_sig vfp_mid mid_vals mid_pre (fun m => fs_post vfprintf_spec (vm_in m))].

(** The entry block allocates the local variables and settles the
    stream's orientation. *)
Lemma vfp_start_row :
  ▷ blocks_hold glibc_vfprintf_internal vfp_blocks ⊢ block_triple glibc_vfprintf_internal
    (BSpec "start" None vfp_sig vfp_in vfp_vals (fs_pre vfprintf_spec) (fs_post vfprintf_spec)).
Proof using Type.
  iIntros "#IH". iModIntro.
  iIntros ([vb [fa fc] fd flags2 held [ma mc] dq fbs ds ap skip xs rest eb] e from Φ) "_ %He H HK".
  cbn [bs_sig bs_vals bs_label bs_pre bs_post fs_pre fs_post vfprintf_spec vfp_vals vi_vb vi_fp vi_fd vi_flags2 vi_held
    vi_fmt vi_dq vi_bytes vi_ds vi_ap vi_skip vi_xs vi_rest vi_eb] in *. c_env_open He.
  iDestruct "H" as "((%Hp & %Hfit & %Hs0 & %Hs8 & %Herr & %Hfd & %Hge) & Htidy & Hs & Hva & Hargs & Herrno & #Hpro & #Hfro & #Hmro)".
  iDestruct (file_tidy_entry with "Htidy") as (fb freg fl md) "((%Hfp & %A1 & %A2 & %A3 & %A4 & %Hflr & %Hmd & %Hneed & %Hnw) & Hl & Hflg & Hfl2 & Hmode & Hback)".
  injection Hfp as -> ->.
  block_enter.
  alloc_keep bb Hbb. change (0 < bb /\ bb mod 16 = 0 /\ bb + 176 <= 2 ^ 48) in Hbb.
  iDestruct (obj_zero_block with "Hobj") as "(Hbl & Hbx & Hbc)"; [compute; discriminate|].
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |]; iNext; iIntros (b2 _) "_".
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |]; iNext; iIntros (b3 _) "_".
  assert (Hmdr : 0 <= md < 2 ^ 32) by (destruct Hmd as [-> | ->]; lia).
  unfold file_size in A3. step. check "Hl". iDestruct "Hmode" as "[_ Hmode]". load_s32 "Hl" "Hmode". step.
  set (x := VfpIn vb (mkPtr fb (Obj fb)) fd flags2 held (mkPtr ma mc) dq fbs ds ap skip xs rest eb).
  iAssert (∀ m, ⌜m = 2 ^ 32 - 1⌝ -∗ bytes fb off_mode (int_bytes m) -∗ live fb freg -∗ mid_pre (VfpMid x fb freg fl bb b2 b3))%I
    with "[Hs Hva Hargs Herrno Hflg Hfl2 Hback Hbl Hbx Hbc]" as "Hmid".
  { iIntros (m ->) "Hmode Hl". unfold mid_pre. cbn [vm_in vm_fb vm_freg vm_fl vm_bb vm_b2 vm_b3 x vi_vb vi_fp vi_fd vi_flags2 vi_held
      vi_fmt vi_dq vi_bytes vi_ds vi_ap vi_skip vi_xs vi_rest vi_eb].
    iFrame "Hl Hflg Hfl2 Hbl Hs Hva Hargs Herrno Hpro Hfro Hmro". iSplit.
    { iPureIntro. unfold file_size. split; [unfold vfp_fits; cbn; tauto|].
      split_and!; first [assumption | reflexivity | lia]. }
    iSplitL "Hmode"; [iSplit; [iPureIntro; lia|iExact "Hmode"]|]. iSplitL "Hback"; [|iFrame "Hbx Hbc"].
    iIntros (fl' Hfl') "Hl Hflg Hfl2 Hmode". iApply ("Hback" $! fl' (2 ^ 32 - 1) with "[%] Hl Hflg Hfl2 Hmode"). split; [exact Hfl' | by right]. }
  destruct Hmd as [-> | ->]; branch.
  - step. step. check "Hl". store_int "Hl" "Hmode". step.
    goto_block "IH" "HK" 1%nat with (VfpMid x fb freg fl bb b2 b3). iApply ("Hmid" with "[%] Hmode Hl"). reflexivity.
  - goto_block "IH" "HK" 1%nat with (VfpMid x fb freg fl bb b2 b3). iApply ("Hmid" with "[%] Hmode Hl"). reflexivity.
Qed.

(** From the block `L28` on, the function checks that the stream can
    be written and that the format is not null. It then sets the
    buffer up, runs the formatter and finishes the buffer. *)
Lemma vfp_mid_row :
  ▷ blocks_hold glibc_vfprintf_internal vfp_blocks ⊢ block_triple glibc_vfprintf_internal
    (BSpec "L28" None mid_sig vfp_mid mid_vals mid_pre (fun m => fs_post vfprintf_spec (vm_in m))).
Proof using Type*.
  iIntros "#IH". iModIntro.
  iIntros ([[vb fp fd flags2 held [ma mc] dq fbs ds ap skip xs rest eb] fb freg fl bb b2 b3] e from Φ) "_ %He H HK".
  cbn [bs_sig bs_vals bs_label bs_pre bs_post fs_pre fs_post vfprintf_spec mid_vals mid_pre vm_in vm_fb vm_freg vm_fl vm_bb
    vm_b2 vm_b3 vi_vb vi_fp vi_fd vi_flags2 vi_held vi_fmt vi_dq vi_bytes vi_ds vi_ap vi_skip vi_xs vi_rest vi_eb] in *.
  c_env_open He.
  iDestruct "H" as "((%Hfits & %Hfp & %A1 & %A2 & %A3 & %A4 & %Hflr & %Hneed & %Hnw & %B1 & %B2 & %B3) & Hl & Hflg & Hfl2 & Hmode & Hback & Hbl & Hbx & Hbc & Hs & Hva & Hargs & Herrno & #Hpro & #Hfro & #Hmro)".
  cbn [vm_in vm_fb vm_freg vm_fl vm_bb vm_b2 vm_b3 vi_vb vi_fp vi_fd vi_flags2 vi_held vi_fmt vi_dq vi_bytes vi_ds vi_ap vi_skip vi_xs vi_rest vi_eb] in *.
  subst fp. unfold file_size in A3. pose proof Hfits as (Hp & Hfit & Hs0 & Hs8 & Herr & Hfd & Hge).
  cbn [vi_bytes vi_ds vi_skip vi_xs vi_rest vi_eb vi_fd] in Hp, Hfit, Hs0, Hs8, Herr, Hfd, Hge.
  block_enter. step. iDestruct "Hmode" as "[%Hmdr Hmode]". load_s32 "Hl" "Hmode". step. branch.
  step. check "Hl". iDestruct "Hflg" as "[_ Hflg]". load_s32 "Hl" "Hflg". step.
  branch_symbolic. rewrite (Z.mod_small fl); [|lia]. change (8 mod 2 ^ 32) with 8. rewrite (Z.mod_small (Z.land fl 8)); [|apply fx_land_lt32; lia]. destruct (Z.land fl 8 =? 0) eqn:Enw; cbn [edge_label]; last first.
  - step. load_s32 "Hl" "Hflg". step. check "Hl". store_int "Hl" "Hflg". step_global Hge.
    iApply (wp_dci_errno_check eb Herr); [vx|]. iNext.
    iDestruct "Herrno" as (ebs ecs [Hebs Hecs]) "Hp". iEval (rewrite pts_app) in "Hp". iDestruct "Hp" as "[Heb Hea]".
    iApply (wp_dci_errno_store eb Herr with "Heb"); [vx | vx | exact Hebs|]. iNext. iIntros "Heb".
    iApply wp_ret; [reflexivity | vx |]. iNext. iApply "HK". iExists 4294967295.
    iSplit; [iPureIntro; split; [reflexivity|lia]|].
    assert (Hor : 0 <= Z.lor fl 32 < 2 ^ 32) by (apply lor_lt32; lia).
    iEval (rewrite (Z.mod_small fl); [|lia]; change (32 mod 2 ^ 32) with 32; rewrite (Z.mod_small (Z.lor fl 32)); [|lia]) in "Hflg".
    iFrame "Hs". iSplitR "Heb Hea"; [|iExists (le_bytes (9 mod 2 ^ 32) 4), ecs; iSplit; [iPureIntro; split; [reflexivity|exact Hecs]|]; rewrite pts_app; iFrame].
    iApply ("Hback" $! (Z.lor fl 32) with "[%] Hl [Hflg] Hfl2 [Hmode]"); [by right | iSplit; [done|iExact "Hflg"] | iSplit; [done|iExact "Hmode"]].
  - step. step_named. step_named. step.
    iDestruct (word_string_addr with "Hs") as %Hma. cbn [ptr_addr] in Hma, E, E0. subst x x0.
    branch_symbolic. rewrite (Z.mod_small ma); [|lia]. change ((0 mod 2 ^ 64) mod 2 ^ 64) with 0.
    destruct (Z.eqb_spec ma 0) as [Hz|_]; [lia|]. cbn [edge_label].
    step. step. load_s32 "Hl" "Hmode". step. branch. step. step. load_s32 "Hl" "Hmode". step. branch.
    step. step. iDestruct "Hfl2" as "[%Hf2r Hfl2]". load_s32 "Hl" "Hfl2". step_named. step_named. step_named. step.
    assert (Hx0 : x0 = fx_field flags2) by exact (fx_shift_field flags2 x x0 Hf2r E E0).
    assert (Hx1 : x1 = 0).
    { rewrite E1 Hx0 (Z.mod_small (fx_field flags2)); [|apply fx_field_range]. change (128 mod 2 ^ 32) with 128.
      change 128 with (Z.land 16777215 128) at 1. rewrite Z.land_assoc fx_field_low; [|exact Hf2r].
      rewrite -Z.land_assoc. exact Hneed. }
    clear E E0 E1 Hx0. subst x1. branch.
  iDestruct ("Hback" $! fl with "[%] Hl [Hflg] [Hfl2] [Hmode]") as "Htidy";
    [by left | iSplit; [done|iExact "Hflg"] | iSplit; [done|iExact "Hfl2"] | iSplit; [done|iExact "Hmode"] |].
  set (a := FOut vb (ow_self w0) fb fd flags2 held eb).
  assert (Hok : fout_ok a) by (unfold fout_ok; cbn [a fo_self fo_eb fo_fd]; tauto).
  pose proof (Hformat a Hok) as Hformat_a. pose proof (Hdone a Hok) as Hdone_a.
  set (br := mkRegion bb (bb + 176) Heap Live).
  iDestruct (fresh_file_buffer bb with "[$Hbl $Hbx $Hbc]") as "(Hbl & Hfp & Hb & Hstage)"; [lia | Z.div_mod_to_equations; lia | lia|].
  step.
  iApply (wp_file_choice _ a bb br with "Hbl Hstage Htidy"). iIntros (freg' dqf cs) "Hbl Hstream Hchoice". cbn zeta.
  set (i := FWinIn bb br (fo_fb a) freg' dqf cs).
  iAssert (fs_pre file_init_spec i) with "[Hstream Hbl Hfp Hb]" as "Hpre".
  { cbn [fs_pre file_init_spec fi_buf fi_breg i]. iFrame "Hstream Hbl". iSplitL "Hfp"; [iExists null; iExact "Hfp"|].
    iExists null, null, null, 0, 0. iExact "Hb". }
  assert (Hsw : Callees [(TAtom "__printf_buffer_to_file_switch", switch_spec)])
    by (apply List.Forall_cons; [apply switch_has_spec | apply List.Forall_nil]).
  pose proof (file_init_has_spec (Callees0 := Hsw)) as Hinit.
  call_callee with i giving "Hpre"; first iExact "Hpre".
  iDestruct "Hpost" as "(-> & Hstream & Hbl & Hfp & Hb)". block_resume.
  iDestruct ("Hchoice" with "Hstream") as "(%Hw & Hwl & Hwin & HR)".
  iDestruct ("HR" with "Hfp Herrno Hfro Hmro") as "HR". struct_live_open "Hbl" as "[%Hbbf Hbl]".
  iAssert (printf_out 4 (file_R a) bb) with "[Hbl Hb Hwl Hwin HR]" as "Hout".
  { iExists br, (fwin_choice i), 0, 4. iFrame "HR Hb Hwl Hwin". iSplit; [iPureIntro; by right|]. iSplit; [done|].
    iEval (struct_sizes). iSplit; [iPureIntro; revert Hbbf; unfold i; cbn [fi_buf fi_breg]; unfold br; cbn [r_end]; lia | iExact "Hbl"]. }
  iPoseProof (file_R_lends_errno a bb) as "#Hlend".
  set (pb := PbIn bb (mkPtr ma mc) dq fbs ds ap skip xs rest eb).
  iAssert (fs_pre (printf_buffer_spec 4 (file_R a)) pb) with "[Hout Hs Hva Hargs]" as "Hpre".
  { cbn [fs_pre printf_buffer_spec pb pb_buf pb_fmt pb_dq pb_bytes pb_ds pb_ap pb_skip pb_xs pb_rest pb_eb].
    iFrame "Hout Hs Hva Hargs Hlend Hpro". iPureIntro. tauto. }
  call_callee with pb giving "Hpre"; first iExact "Hpre".
  iDestruct "Hpost" as "(-> & Hout & Hs)". cbn [pb pb_buf pb_fmt pb_dq pb_bytes]. block_resume.
  iAssert (fs_pre (file_done_spec (file_R a)) (bb, eb)) with "[Hout]" as "Hpre".
  { cbn [fs_pre file_done_spec fst snd]. iFrame "Hout Hlend". iPureIntro. tauto. }
  call_callee with (bb, eb) giving "Hpre"; first iExact "Hpre".
  iDestruct "Hpost" as (n) "((-> & %Hn) & Hout)". cbn [fst snd]. block_resume.
  iDestruct (file_out_close with "Hout") as "[Htidy Herrno]".
  iApply wp_ret; [reflexivity | vx |]. iNext. iApply "HK". iExists n. iFrame "Htidy Hs Herrno".
  iPureIntro. rewrite Z.mod_mod; [|lia]. rewrite Z.mod_small; [done|lia].
Qed.

(** The two rows together prove the table. *)
Lemma vfp_table : ⊢ blocks_hold glibc_vfprintf_internal vfp_blocks.
Proof using Type*.
  apply blocks_close. iIntros "#IH". iSplit; [iApply (vfp_start_row with "IH")|].
  iSplit; [iApply (vfp_mid_row with "IH")|done].
Qed.

(** A call of `c: __vfprintf_internal` on a tidy stream returns an int
    and gives the stream back tidy, with the format and errno. The
    compiled function meets this contract, because the entry block's
    contract in the table is the same one. *)
Lemma vfprintf_has_spec `{!Defines ge "__vfprintf_internal" glibc_vfprintf_internal} :
  HasSpec registry (os_wi w0) ge (TAtom "__vfprintf_internal") vfprintf_spec.
Proof using Type*.
  eapply (blocks_has_spec _ _ _ vfp_blocks); [exact defines | reflexivity | reflexivity | | exact vfp_table].
  intros x. eexists _, x. split; [reflexivity|]. split.
  { destruct x as [vb [fa fc] fd flags2 held [ma mc] dq bytes ds [ca cc] skip xs rest eb]. c_env_close. }
  cbn [bs_pre bs_post]. iIntros "$". iIntros (r) "$".
Qed.

End vfprintf.
