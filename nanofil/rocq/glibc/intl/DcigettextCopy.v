From Glibc Require Import GlibcProgram.
(** After glibc's `c: __dcigettext` has allocated the buffer for the name
    of the catalog file, it writes that name into the buffer and copies
    the locale name. This module proves that block of the C-locale route.
    The block writes the category name, a slash, the domain and the
    suffix ".mo" one after another. It then measures the locale name and
    asks malloc for a buffer that holds it and its terminator.

    In the C locale nothing reads the file name, because the locale test
    returns before any catalog is opened. So the proof only has to show
    that the copies stay inside the buffer, and it forgets what they
    write. When the second malloc fails, the lookup returns the message
    unchanged.

    The block copies the domain with mempcpy and the other names with
    stpcpy. This proof reuses the proof of mempcpy, and it lets the
    caller say how stpcpy and malloc behave. Another module proves that
    behaviour of stpcpy from glibc's code. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv LibioLogic LibioSetb WordString StrlenLogic StrlenWord.
From Glibc Require Import MemFwdCode MemFwdLogic LibioDefaultXsputnCopy.
From Glibc Require Import GetoptLongPfxAlloc DcigettextCode DcigettextFree DcigettextExit DcigettextPreRules DcigettextFail.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Import FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance dci_copy_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).

(** ## The rule for stpcpy *)

(** The lookup copies strings with __GI_stpcpy. The first rule below is
    the one this proof originally assumed. A caller states what a call
    does to an owned buffer b:
    it copies the string s and its terminator to address a inside the
    buffer, returns the address of the copied terminator, and leaves the
    buffer's bytes valid. The rule says nothing about which bytes end up
    in the buffer, because the C route never reads them. *)
Definition dci_stpcpy_rule : Prop :=
  forall f e ls l d args rest j a b reg xs cs dq q s Φ,
    map_option (arg_x ge e) args = Some [WPtr (mkPtr a (Obj b)); WPtr q] ->
    b <= a -> a - b + Z.of_nat (length s) + 1 <= Z.of_nat (length xs) -> b + Z.of_nat (length xs) <= r_end reg ->
    length cs = length xs ->
    ⊢ live b reg -∗ bytes b 0 xs -∗ auxes b 0 cs -∗ word_string dq q s -∗
      ▷ (live b reg -∗ buf_after b (length xs) -∗ word_string dq q s -∗
         WP (ERun (mkFrame f (put d (WPtr (mkPtr (a + Z.of_nat (length s)) (Obj b))) e) ls None (Exec l rest j)) : gexpr)
           {{ Φ }}) -∗
      WP (ERun (mkFrame f e ls None
        (Exec l (Call (CResult d P) (Global (TAtom "__GI_stpcpy")) args :: rest) j)) : gexpr) {{ Φ }}.

(** The real stpcpy cannot meet the old rule, so this rule adds one
    premise. The old rule promises that every byte of the buffer is a valid byte
    afterwards, but the copy leaves the bytes outside the string as they
    were, and owning a byte does not bound its value. So the rule proved
    from the body asks that the buffer hold valid bytes before the call.
    Every call in the lookup passes a buffer of fresh zeros or one that
    an earlier copy left valid. *)
Definition dci_stpcpy_rule_r : Prop :=
  forall f e ls l d args rest j a b reg xs cs dq q s Φ,
    map_option (arg_x ge e) args = Some [WPtr (mkPtr a (Obj b)); WPtr q] ->
    b <= a -> a - b + Z.of_nat (length s) + 1 <= Z.of_nat (length xs) -> b + Z.of_nat (length xs) <= r_end reg ->
    length cs = length xs -> Forall (fun x => 0 <= x < 256) xs ->
    ⊢ live b reg -∗ bytes b 0 xs -∗ auxes b 0 cs -∗ word_string dq q s -∗
      ▷ (live b reg -∗ buf_after b (length xs) -∗ word_string dq q s -∗
         WP (ERun (mkFrame f (put d (WPtr (mkPtr (a + Z.of_nat (length s)) (Obj b))) e) ls None (Exec l rest j)) : gexpr)
           {{ Φ }}) -∗
      WP (ERun (mkFrame f e ls None
        (Exec l (Call (CResult d P) (Global (TAtom "__GI_stpcpy")) args :: rest) j)) : gexpr) {{ Φ }}.

(** The old rule gives the new one, which only adds a premise. *)
Lemma dci_stpcpy_rule_r_of : dci_stpcpy_rule -> dci_stpcpy_rule_r.
Proof. intros H f e ls l d args rest j a b reg xs cs dq q s Φ Ha H1 H2 H3 H4 _. exact (H f e ls l d args rest j a b reg xs cs dq q s Φ Ha H1 H2 H3 H4). Qed.

(** This tactic proves the argument list of the mempcpy call, whose
    length argument is reduced modulo 2^64. *)
Ltac vx_len n :=
  cbn -[put]; repeat match goal with |- context [lookup ?k ?E] =>
    let L := fresh "Hlk" in assert (L : lookup k E = _) by lk_prove; rewrite L; clear L end;
  cbn -[put]; rewrite (Z.mod_small n (2 ^ 64)); [reflexivity | lia].

(** ## From the file-name buffer to the copied locale name *)

(** Filling the file-name buffer must stay inside it, and copying the
    locale name needs a second buffer. The lookup starts with the fresh
    buffer xd and borrows the category name at cp, the domain, the locale
    name cv that reads "C" and the two literals of the file name. If the
    second malloc fails, the left continuation receives the exit
    resources. Otherwise the right continuation receives both buffers: xd
    with valid bytes and the sixteen-byte buffer sl, which is aligned to
    16 and holds zeros. *)
Lemma wp_dci_copy_w_fr e xs xreg rl sb dom msgid cv s cp cat dqc ds dqd xd p276 p277 lk1 lk2 U1 U1' U2 U2' bs M Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy} :
  registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)) ->
  find_fn ge (TAtom "zmemmove") = None -> lookup (TAtom "zmemmove") (ge_globals ge) = None ->
  dci_stpcpy_rule_r ->
  dci_pre_env e xs rl sb dom msgid cv s -> lookup (TAtom "v224") e = Some (WPtr cv) ->
  lookup (TAtom "iw_2.v9") e = Some (WPtr cp) -> lookup (TAtom "v226") e = Some (WInt (Z.of_nat (length ds))) ->
  lookup (TAtom "v232") e = Some (WPtr (mkPtr xd (Obj xd))) ->
  0 < xd -> xd mod 16 = 0 -> xd + req_extent (heap_req 16 (Z.of_nat (length cat + length ds) + 5)) <= 2 ^ 48 ->
  0 <= s < 2 ^ 32 -> 0 < xs -> xs mod 8 = 0 -> xs + 8 <= r_end xreg -> r_end xreg <= 2 ^ 48 ->
  dci_free_rule -> getopt_malloc_rule w0 registry ge M ->
  lookup (TAtom "glibc_dcigettext#str.276") (ge_globals ge) = Some p276 ->
  lookup (TAtom "glibc_dcigettext#str.277") (ge_globals ge) = Some p277 ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "_nl_state_lock") (ge_globals ge) = Some lk1 ->
  lookup (TAtom "__libc_setlocale_lock") (ge_globals ge) = Some lk2 ->
  dci_unlock_rule lk1 U1 U1' -> dci_unlock_rule lk2 U2 U2' ->
  obj xd (heap_req 16 (Z.of_nat (length cat + length ds) + 5)) -∗
  word_string dqc cp cat -∗ word_string dqd dom ds -∗ word_string DfracDiscarded cv [67] -∗
  word_string DfracDiscarded p276 [47] -∗ word_string DfracDiscarded p277 [46; 109; 111] -∗ M -∗
  live xs xreg -∗ pcell xs 0 null -∗ U1 -∗ U2 -∗ errno_own eb bs -∗
  ▷ ((live xs xreg -∗ pcell xs 0 null -∗ U1' -∗ U2' -∗ errno_own eb (le_bytes s 4) -∗
      word_string dqc cp cat -∗ word_string dqd dom ds -∗ M -∗ Φ (Ret (WPtr msgid))) ∧
     (∀ e' sl, ⌜dci_pre_env e' xs rl sb dom msgid cv s /\ lookup (TAtom "v224") e' = Some (WPtr cv) /\
         lookup (TAtom "v232") e' = Some (WPtr (mkPtr xd (Obj xd))) /\
         lookup (TAtom "v254") e' = Some (WPtr (mkPtr sl (Obj sl))) /\ 0 < sl /\ sl + 16 <= 2 ^ 48 /\ sl mod 16 = 0⌝ -∗
      live xd (mkRegion xd (xd + req_extent (heap_req 16 (Z.of_nat (length cat + length ds) + 5))) Heap Live) -∗
      live sl (mkRegion sl (sl + 16) Heap Live) -∗ ibyte sl 0 0 -∗ ibyte sl 1 0 -∗ bytes sl 2 (replicate 14 0) -∗
      word_string dqc cp cat -∗ word_string dqd dom ds -∗ M -∗
      live xs xreg -∗ pcell xs 0 null -∗ U1 -∗ U2 -∗ errno_own eb bs -∗
      WP (ERun (mkFrame glibc_dcigettext e' [] None (Enter (TAtom "L263") (Some (TAtom "L235")))) : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_dcigettext e [] None (Enter (TAtom "L235") (Some (TAtom "iw_3.join")))) : gexpr) {{ Φ }}.
Proof.
  intros Hmv Hmvf Hmvs Hcpy Henv Hv224 Hv9 Hv226 Hv232 Hxd0 Hxd16 Hxdend Hs Hxs0 Hxs8 Hxsend Hxsr Hheap Hmal
    H276 H277 Hge Hlk1 Hlk2 Hu1 Hu2.
  pose proof Henv as (Hv17 & Hc0 & Hv21 & Hv23 & Hpr1 & Hv2 & Hv6 & Hv10 & Hv32 & Hv69 & Hv90).
  destruct dom as [da dc].
  iIntros "Ho Hcat Hdom #Hcv #H276 #H277 HM Hxl Hxc HU1 HU2 Herr HK".
  set (n := Z.of_nat (length cat + length ds) + 5) in *.
  set (N := req_extent (heap_req 16 n)) in *.
  assert (HN : n <= N) by (subst N n; cbn; Z.div_mod_to_equations; lia).
  rewrite obj_zero_block; [|lia]. iDestruct "Ho" as "(Hdl & Hdb & Hda)". fold N.
  set (xr := mkRegion xd (xd + N) Heap Live).
  step.
  iApply (Hcpy _ _ _ _ _ _ _ _ xd xd xr with "Hdl Hdb Hda Hcat");
    [vx | lia | rewrite length_replicate; lia | cbn [xr r_end]; rewrite length_replicate; lia |
     rewrite !length_replicate; reflexivity | apply Forall_replicate; lia |].
  iNext. iIntros "Hdl Hbuf Hcat". iDestruct "Hbuf" as (xs1 cs1 (Hl1 & Hc1 & Hf1)) "[Hdb Hda]".
  rewrite length_replicate in Hl1 Hc1 |- *.
  step_global H276.
  iApply (Hcpy _ _ _ _ _ _ _ _ (xd + Z.of_nat (length cat)) xd xr with "Hdl Hdb Hda H276");
    [vx | lia | cbn [length]; lia | cbn [xr r_end]; lia | lia | exact Hf1 |].
  iNext. iIntros "Hdl Hbuf _". iDestruct "Hbuf" as (xs2 cs2 (Hl2 & Hc2 & Hf2)) "[Hdb Hda]".
  change (Z.of_nat (length [47])) with 1.
  replace (xd + Z.of_nat (length cat) + 1) with (xd + (Z.of_nat (length cat) + 1)) by lia.
  iDestruct (word_string_bytes with "Hdom") as (bd rd wsd Hsd) "(Hdl' & Hdy & Hdw)".
  pose proof Hsd as [Hdc Hbd0 Hbd8 Hdst Hdfit Hdsp Hdlen Hdr Hdby Hdch]. unfold wstart in Hdfit. cbn [ptr_addr ptr_cap] in *.
  pose proof (Z.div_mod (da mod 8 + Z.of_nat (length ds) + 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (da mod 8 + Z.of_nat (length ds) + 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound da 8 ltac:(lia)).
  assert (Hxd8 : xd mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (Hdf : Forall (fun y => 0 <= y < 256) ds) by (eapply Forall_impl; [|exact Hdch]; cbn; lia).
  iEval (unfold MemFwdLogic.ML.bytesq; rewrite byte_ps_app ptsq_app) in "Hdy". iDestruct "Hdy" as "[Hds Hd0]".
  replace da with (bd + (da - bd)) in Hpr1 by lia.
  iApply (wp_call_mempcpy_in Hmv Hmvf Hmvs _ _ _ _ _ _ _ _ _ xd xr xs2 cs2 (Z.of_nat (length cat) + 1) dqd bd rd (da - bd) dc ds
    with "Hdl Hdb Hda Hdl' Hds").
  all: try first [apply defines | vx | vx_len (Z.of_nat (length ds)) | reflexivity | exact Hdc | assumption | lia | exact Hf2 | exact Hdf |
    (unfold xr; cbn [r_end]; lia)].
  iNext. iIntros "Hdl Hbuf Hdl' Hds". iDestruct "Hbuf" as (xs3 cs3 (Hl3 & Hc3 & Hf3)) "[Hdb Hda]".
  iDestruct ("Hdw" with "Hdl' [Hds Hd0]") as "Hdom".
  { unfold MemFwdLogic.ML.bytesq. rewrite byte_ps_app ptsq_app. iFrame. }
  step_global H277.
  iApply (Hcpy _ _ _ _ _ _ _ _ (xd + (Z.of_nat (length cat) + 1) + Z.of_nat (length ds)) xd xr with "Hdl Hdb Hda H277");
    [vx | lia | cbn [length]; lia | cbn [xr r_end]; lia | lia | exact Hf3 |].
  iNext. iIntros "Hdl _ _".
  iApply (wp_call_glibc_strlen registry (os_wi w0) ge with "Hcv"); [vx | apply defines | reflexivity |].
  iNext. iIntros "_". cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. step.
  iApply (Hmal _ _ _ _ _ _ _ _ 2 with "HM"); [vx | lia |].
  iNext. iIntros (p) "HM [-> | (%sl & %Hsl & Hso)]".
  - step. step. branch.
    iApply (wp_dci_fail_name_fr eb Herr _ xs xreg xd xr with "Hxl Hxc Hdl HU1 HU2 Herr");
      try first [exact Hheap | exact Hge | exact Hlk1 | exact Hlk2 | exact Hu1 | exact Hu2 | exact Hs | reflexivity |
        lia | lk_prove].
    iNext. iIntros "Hxl Hxc HU1 HU2 Herr". iDestruct "HK" as "[HK _]".
    iApply ("HK" with "Hxl Hxc HU1 HU2 Herr Hcat Hdom HM").
  - destruct Hsl as (-> & Hsl0 & Hsl16 & Hslend). change (req_extent (heap_req 16 2)) with 16 in Hslend.
    rewrite obj_zero_block; [|vm_compute; discriminate].
    change (req_extent (heap_req 16 2)) with 16. change (req_kind (heap_req 16 2)) with Heap.
    change (replicate (Z.to_nat 16) 0) with ([0] ++ [0] ++ replicate 14 0)%list.
    rewrite !bytes_app. iDestruct "Hso" as "(Hsl & (Hb0 & Hb1 & Hbs) & _)".
    step. step.
    assert (Hnn : ((if ptr_addr (mkPtr sl (Obj sl)) mod 2 ^ 64 =? 0 mod 2 ^ 64 mod 2 ^ 64 then 1 else 0) mod 2 ^ 32 =? 0) = true).
    { cbn [ptr_addr]. change (0 mod 2 ^ 64 mod 2 ^ 64) with 0. rewrite (Z.mod_small sl); [|lia].
      destruct (Z.eqb_spec sl 0); [lia | reflexivity]. }
    branch_symbolic. rewrite Hnn. cbn [edge_label].
    iDestruct "HK" as "[_ HK]".
    iApply ("HK" with "[%] Hdl Hsl Hb0 Hb1 Hbs Hcat Hdom HM Hxl Hxc HU1 HU2 Herr").
    replace (bd + (da - bd)) with da in Hpr1 by lia.
    unfold dci_pre_env. split_and!; try lk_prove; lia.
Qed.

(** The older statement drops the bytes that the locale test does not
    read when the flag is zero. *)
Lemma wp_dci_copy_r_fr e xs xreg rl sb dom msgid cv s cp cat dqc ds dqd xd p276 p277 lk1 lk2 U1 U1' U2 U2' bs M Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy} :
  registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)) ->
  find_fn ge (TAtom "zmemmove") = None -> lookup (TAtom "zmemmove") (ge_globals ge) = None ->
  dci_stpcpy_rule_r ->
  dci_pre_env e xs rl sb dom msgid cv s -> lookup (TAtom "v224") e = Some (WPtr cv) ->
  lookup (TAtom "iw_2.v9") e = Some (WPtr cp) -> lookup (TAtom "v226") e = Some (WInt (Z.of_nat (length ds))) ->
  lookup (TAtom "v232") e = Some (WPtr (mkPtr xd (Obj xd))) ->
  0 < xd -> xd mod 16 = 0 -> xd + req_extent (heap_req 16 (Z.of_nat (length cat + length ds) + 5)) <= 2 ^ 48 ->
  0 <= s < 2 ^ 32 -> 0 < xs -> xs mod 8 = 0 -> xs + 8 <= r_end xreg -> r_end xreg <= 2 ^ 48 ->
  dci_free_rule -> getopt_malloc_rule w0 registry ge M ->
  lookup (TAtom "glibc_dcigettext#str.276") (ge_globals ge) = Some p276 ->
  lookup (TAtom "glibc_dcigettext#str.277") (ge_globals ge) = Some p277 ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "_nl_state_lock") (ge_globals ge) = Some lk1 ->
  lookup (TAtom "__libc_setlocale_lock") (ge_globals ge) = Some lk2 ->
  dci_unlock_rule lk1 U1 U1' -> dci_unlock_rule lk2 U2 U2' ->
  obj xd (heap_req 16 (Z.of_nat (length cat + length ds) + 5)) -∗
  word_string dqc cp cat -∗ word_string dqd dom ds -∗ word_string DfracDiscarded cv [67] -∗
  word_string DfracDiscarded p276 [47] -∗ word_string DfracDiscarded p277 [46; 109; 111] -∗ M -∗
  live xs xreg -∗ pcell xs 0 null -∗ U1 -∗ U2 -∗ errno_own eb bs -∗
  ▷ ((live xs xreg -∗ pcell xs 0 null -∗ U1' -∗ U2' -∗ errno_own eb (le_bytes s 4) -∗
      word_string dqc cp cat -∗ word_string dqd dom ds -∗ M -∗ Φ (Ret (WPtr msgid))) ∧
     (∀ e' sl, ⌜dci_pre_env e' xs rl sb dom msgid cv s /\ lookup (TAtom "v224") e' = Some (WPtr cv) /\
         lookup (TAtom "v232") e' = Some (WPtr (mkPtr xd (Obj xd))) /\
         lookup (TAtom "v254") e' = Some (WPtr (mkPtr sl (Obj sl))) /\ 0 < sl /\ sl + 16 <= 2 ^ 48⌝ -∗
      live xd (mkRegion xd (xd + req_extent (heap_req 16 (Z.of_nat (length cat + length ds) + 5))) Heap Live) -∗
      live sl (mkRegion sl (sl + 16) Heap Live) -∗ ibyte sl 0 0 -∗ ibyte sl 1 0 -∗
      word_string dqc cp cat -∗ word_string dqd dom ds -∗ M -∗
      live xs xreg -∗ pcell xs 0 null -∗ U1 -∗ U2 -∗ errno_own eb bs -∗
      WP (ERun (mkFrame glibc_dcigettext e' [] None (Enter (TAtom "L263") (Some (TAtom "L235")))) : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_dcigettext e [] None (Enter (TAtom "L235") (Some (TAtom "iw_3.join")))) : gexpr) {{ Φ }}.
Proof.
  intros. iIntros "Ho Hcat Hdom Hcv H276 H277 HM Hxl Hxc HU1 HU2 Herr HK".
  iApply (wp_dci_copy_w_fr with "Ho Hcat Hdom Hcv H276 H277 HM Hxl Hxc HU1 HU2 Herr"); try eassumption.
  iNext. iSplit; [iDestruct "HK" as "[HK _]"; iExact "HK" |].
  iIntros (e' sl (Hq1 & Hq2 & Hq3 & Hq4 & Hq5 & Hq6 & _)) "Hdl Hsl Hb0 Hb1 _". iDestruct "HK" as "[_ HK]".
  iApply ("HK" with "[%] Hdl Hsl Hb0 Hb1"). split_and!; assumption.
Qed.

(** The older statement takes the model's free, which meets the rule. *)
Lemma wp_dci_copy_r e xs xreg rl sb dom msgid cv s cp cat dqc ds dqd xd p276 p277 lk1 lk2 U1 U1' U2 U2' bs M Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy} :
  registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)) ->
  find_fn ge (TAtom "zmemmove") = None -> lookup (TAtom "zmemmove") (ge_globals ge) = None ->
  dci_stpcpy_rule_r ->
  dci_pre_env e xs rl sb dom msgid cv s -> lookup (TAtom "v224") e = Some (WPtr cv) ->
  lookup (TAtom "iw_2.v9") e = Some (WPtr cp) -> lookup (TAtom "v226") e = Some (WInt (Z.of_nat (length ds))) ->
  lookup (TAtom "v232") e = Some (WPtr (mkPtr xd (Obj xd))) ->
  0 < xd -> xd mod 16 = 0 -> xd + req_extent (heap_req 16 (Z.of_nat (length cat + length ds) + 5)) <= 2 ^ 48 ->
  0 <= s < 2 ^ 32 -> 0 < xs -> xs mod 8 = 0 -> xs + 8 <= r_end xreg -> r_end xreg <= 2 ^ 48 ->
  heap_fns ge -> getopt_malloc_rule w0 registry ge M ->
  lookup (TAtom "glibc_dcigettext#str.276") (ge_globals ge) = Some p276 ->
  lookup (TAtom "glibc_dcigettext#str.277") (ge_globals ge) = Some p277 ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "_nl_state_lock") (ge_globals ge) = Some lk1 ->
  lookup (TAtom "__libc_setlocale_lock") (ge_globals ge) = Some lk2 ->
  dci_unlock_rule lk1 U1 U1' -> dci_unlock_rule lk2 U2 U2' ->
  obj xd (heap_req 16 (Z.of_nat (length cat + length ds) + 5)) -∗
  word_string dqc cp cat -∗ word_string dqd dom ds -∗ word_string DfracDiscarded cv [67] -∗
  word_string DfracDiscarded p276 [47] -∗ word_string DfracDiscarded p277 [46; 109; 111] -∗ M -∗
  live xs xreg -∗ pcell xs 0 null -∗ U1 -∗ U2 -∗ errno_own eb bs -∗
  ▷ ((live xs xreg -∗ pcell xs 0 null -∗ U1' -∗ U2' -∗ errno_own eb (le_bytes s 4) -∗
      word_string dqc cp cat -∗ word_string dqd dom ds -∗ M -∗ Φ (Ret (WPtr msgid))) ∧
     (∀ e' sl, ⌜dci_pre_env e' xs rl sb dom msgid cv s /\ lookup (TAtom "v224") e' = Some (WPtr cv) /\
         lookup (TAtom "v232") e' = Some (WPtr (mkPtr xd (Obj xd))) /\
         lookup (TAtom "v254") e' = Some (WPtr (mkPtr sl (Obj sl))) /\ 0 < sl /\ sl + 16 <= 2 ^ 48⌝ -∗
      live xd (mkRegion xd (xd + req_extent (heap_req 16 (Z.of_nat (length cat + length ds) + 5))) Heap Live) -∗
      live sl (mkRegion sl (sl + 16) Heap Live) -∗ ibyte sl 0 0 -∗ ibyte sl 1 0 -∗
      word_string dqc cp cat -∗ word_string dqd dom ds -∗ M -∗
      live xs xreg -∗ pcell xs 0 null -∗ U1 -∗ U2 -∗ errno_own eb bs -∗
      WP (ERun (mkFrame glibc_dcigettext e' [] None (Enter (TAtom "L263") (Some (TAtom "L235")))) : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_dcigettext e [] None (Enter (TAtom "L235") (Some (TAtom "iw_3.join")))) : gexpr) {{ Φ }}.
Proof using Type*. intros. eapply wp_dci_copy_r_fr; eauto using dci_free_rule_heap. Qed.

(** Callers written against the old stpcpy rule still get the same
    statement of the copy block. *)
Lemma wp_dci_copy e xs xreg rl sb dom msgid cv s cp cat dqc ds dqd xd p276 p277 lk1 lk2 U1 U1' U2 U2' bs M Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy} :
  registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)) ->
  find_fn ge (TAtom "zmemmove") = None -> lookup (TAtom "zmemmove") (ge_globals ge) = None ->
  dci_stpcpy_rule ->
  dci_pre_env e xs rl sb dom msgid cv s -> lookup (TAtom "v224") e = Some (WPtr cv) ->
  lookup (TAtom "iw_2.v9") e = Some (WPtr cp) -> lookup (TAtom "v226") e = Some (WInt (Z.of_nat (length ds))) ->
  lookup (TAtom "v232") e = Some (WPtr (mkPtr xd (Obj xd))) ->
  0 < xd -> xd mod 16 = 0 -> xd + req_extent (heap_req 16 (Z.of_nat (length cat + length ds) + 5)) <= 2 ^ 48 ->
  0 <= s < 2 ^ 32 -> 0 < xs -> xs mod 8 = 0 -> xs + 8 <= r_end xreg -> r_end xreg <= 2 ^ 48 ->
  heap_fns ge -> getopt_malloc_rule w0 registry ge M ->
  lookup (TAtom "glibc_dcigettext#str.276") (ge_globals ge) = Some p276 ->
  lookup (TAtom "glibc_dcigettext#str.277") (ge_globals ge) = Some p277 ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "_nl_state_lock") (ge_globals ge) = Some lk1 ->
  lookup (TAtom "__libc_setlocale_lock") (ge_globals ge) = Some lk2 ->
  dci_unlock_rule lk1 U1 U1' -> dci_unlock_rule lk2 U2 U2' ->
  obj xd (heap_req 16 (Z.of_nat (length cat + length ds) + 5)) -∗
  word_string dqc cp cat -∗ word_string dqd dom ds -∗ word_string DfracDiscarded cv [67] -∗
  word_string DfracDiscarded p276 [47] -∗ word_string DfracDiscarded p277 [46; 109; 111] -∗ M -∗
  live xs xreg -∗ pcell xs 0 null -∗ U1 -∗ U2 -∗ errno_own eb bs -∗
  ▷ ((live xs xreg -∗ pcell xs 0 null -∗ U1' -∗ U2' -∗ errno_own eb (le_bytes s 4) -∗
      word_string dqc cp cat -∗ word_string dqd dom ds -∗ M -∗ Φ (Ret (WPtr msgid))) ∧
     (∀ e' sl, ⌜dci_pre_env e' xs rl sb dom msgid cv s /\ lookup (TAtom "v224") e' = Some (WPtr cv) /\
         lookup (TAtom "v232") e' = Some (WPtr (mkPtr xd (Obj xd))) /\
         lookup (TAtom "v254") e' = Some (WPtr (mkPtr sl (Obj sl))) /\ 0 < sl /\ sl + 16 <= 2 ^ 48⌝ -∗
      live xd (mkRegion xd (xd + req_extent (heap_req 16 (Z.of_nat (length cat + length ds) + 5))) Heap Live) -∗
      live sl (mkRegion sl (sl + 16) Heap Live) -∗ ibyte sl 0 0 -∗ ibyte sl 1 0 -∗
      word_string dqc cp cat -∗ word_string dqd dom ds -∗ M -∗
      live xs xreg -∗ pcell xs 0 null -∗ U1 -∗ U2 -∗ errno_own eb bs -∗
      WP (ERun (mkFrame glibc_dcigettext e' [] None (Enter (TAtom "L263") (Some (TAtom "L235")))) : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_dcigettext e [] None (Enter (TAtom "L235") (Some (TAtom "iw_3.join")))) : gexpr) {{ Φ }}.
Proof using Type*. intros Hmv Hmvf Hmvs Hcpy. apply wp_dci_copy_r; try assumption. exact (dci_stpcpy_rule_r_of Hcpy). Qed.
End rules.
