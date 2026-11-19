(** When printf pads a field with spaces, the first space need not fall
    on an eight-byte boundary. Writing it can clear the pointer tag for
    the eight bytes around it. The formatter owns that tag as part of
    its window, so memset leaves the separate buffer header alone. *)
From Glibc Require Import Unit_string_memset_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import Fix OsWorld OsRegistry FileInv LibioLogic MemFwdLogic
  PrintfStagingCopy PrintfOut.
Import ListNotations ProgramAbbreviations OsWorld Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic.
Open Scope Z_scope.

(** A fill inside the window changes no bytes or slots outside it. The
    caller gets valid bytes throughout, including in the part it did not fill. *)
Local Lemma fill_inside m m' b reg lo xs cs a c n :
  live_disjoint m -> live_at m b reg -> b mod 8 = 0 -> lo mod 8 = 0 ->
  b <= lo <= a -> 0 <= n -> a+n <= lo + Z.of_nat (length xs) -> lo + Z.of_nat (length xs) <= r_end reg ->
  length cs = length xs -> Forall (fun y => 0 <= y < 256) xs ->
  all_agree m (byte_ps b (lo-b) xs ++ aux_ps b (lo-b) cs) ->
  memset_result m (mkPtr a (Obj b)) c n m' ->
  let ys := window_bytes m' b (lo-b) (length xs) in let ds := aux_now m' b (lo-b) (length xs) in
  all_agree m' (byte_ps b (lo-b) ys ++ aux_ps b (lo-b) ds) /\ Forall (fun y => 0 <= y < 256) ys /\
  frame_ok (byte_ps b (lo-b) xs ++ aux_ps b (lo-b) cs).*1 m m'.
Proof.
  intros Hd Hl Hb8 Hl8 Ha Hn Hlim Hend Hlen Hvalid Hold ((Hr & Hbytes & Haux) & Hfill & _).
  cbn zeta. pose proof Hl as [E0 L0].
  assert (Hreg : registered m' b) by (unfold registered; rewrite Hr E0; discriminate).
  split; [|split].
  - apply all_agree_app. split; apply all_agree_intro; intros l v Hin;
      [apply byte_ps_elem in Hin | apply aux_ps_elem in Hin]; destruct Hin as (i & y & Hyi & -> & ->);
      unfold window_bytes, aux_now in Hyi; change (map ?f ?l) with (f <$> l) in Hyi;
      apply list_lookup_fmap_Some in Hyi as (k & -> & Hk); pose proof (lookup_lt_Some _ _ _ Hk) as Hi;
      rewrite length_seq in Hi; (rewrite lookup_seq_lt in Hk; [|exact Hi]); injection Hk as <-;
      cbn [agree_piece]; (split; [exact Hreg|]); intros reg' E L; rewrite Hr E0 in E; injection E as <-;
      (split; [lia|]); (split; [lia|]); first [reflexivity | left; reflexivity].
  - apply Forall_forall. intros y Hy. unfold window_bytes in Hy. apply in_map_iff in Hy as (i & <- & Hi). apply in_seq in Hi.
    destruct (decide (a <= b + (lo-b + Z.of_nat i) < a+n)) as [Hin|Hout].
    + rewrite Hfill; [apply Z.mod_pos_bound; lia | exact Hin].
    + rewrite Hbytes; [|exact Hout]. destruct (lookup_lt_is_Some_2 xs i ltac:(lia)) as [x Hx].
      apply all_agree_app in Hold as [Hx0 _]. destruct (byte_ps_agree _ _ _ _ _ _ _ Hl Hx0 Hx) as (-> & _).
      exact (Forall_lookup_1 _ _ _ _ Hvalid Hx).
  - eapply block_frame; [exact Hd | exact Hl | exact Hb8 | Z.div_mod_to_equations; lia | exact Hlen | exact Hold |].
    split; [exact Hr|]. split.
    + intros p Hp. apply Hbytes. contradict Hp. unfold span_contains in *. cbn in *. lia.
    + intros p Hp. apply Haux. destruct (memset_touched (mkPtr a (Obj b)) n p) eqn:Ht; [|reflexivity]. exfalso.
      apply memset_touched_spec in Ht. assert (memset_touched (mkPtr (b+(lo-b)) (Obj b)) (Z.of_nat (length xs)) p = true).
      { apply memset_touched_spec. cbn [ptr_addr] in *. lia. } congruence.
Qed.

Section fill.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hset : registry (TAtom "zmemset") = Some (void_only (memset_contract os_world)))
  (Hfn : find_fn ge (TAtom "zmemset") = None) (Hsym : lookup (TAtom "zmemset") (ge_globals ge) = None).

(** The padding loop lends the whole aligned window but asks memset to
    fill only the bytes from a to a+n. The return value is a itself. *)
Definition win_fill_spec : fspec Σ :=
  FSpec (Z * region * Z * Z * Z * Z * Z)
    (fun '(b, _, _, _, a, c, n) => [WPtr (mkPtr a (Obj b)); WInt c; WInt n])
    (fun '(b, reg, lo, hi, a, c, n) =>
       ⌜b mod 8 = 0 /\ lo mod 8 = 0 /\ b <= lo <= a /\ a+n <= hi /\ hi <= r_end reg /\
         0 <= c < 2^32 /\ 0 <= n < 2^64⌝ ∗ live b reg ∗ win_own b lo hi)%I
    (fun '(b, reg, lo, hi, a, _, _) v => ⌜v = Ret (WPtr (mkPtr a (Obj b)))⌝ ∗ live b reg ∗ win_own b lo hi)%I.

(** The compiled glibc wrapper calls the runtime fill once. Its result
    supplies both the updated ownership and the unchanged frame. *)
Lemma memset_window_has_spec `{!Defines ge "__GI_memset" Unit_string_memset_os.fn___GI_memset} :
  HasSpec registry (os_wi w0) ge (TAtom "__GI_memset") win_fill_spec.
Proof using Type*.
  intros [[[[[[b reg] lo] hi] a] c] n]. exists Unit_string_memset_os.fn___GI_memset. split; [exact defines|]. split; [eexists; reflexivity|].
  intros fr Φ Hcall. injection Hcall as <-. cbn [fs_pre fs_post win_fill_spec].
  iIntros "((%Hb8 & %Hl8 & %Ha & %Hlim & %Hend & %Hc & %Hn) & Hl & Hwin) HK".
  iDestruct "Hwin" as (xs cs) "((%Hx & %Hlen & %Hvalid) & Hbytes & Haux)".
  iDestruct (block_pts b reg (lo-b) xs cs with "[$Hl $Hbytes $Haux]") as "Hps".
  iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (void_only (memset_contract os_world))
      [WPtr (mkPtr a (Obj b)); WInt c; WInt n] (pts (block_ps b reg (lo-b) xs cs)) with "Hps [HK]");
    [exact Hfn | exact Hsym | reflexivity | exact Hset | cbn; rewrite !Z.mod_small; [done|lia..] | | |].
  - split; [reflexivity|]. split; [left; reflexivity | do 3 eexists; reflexivity].
  - iIntros (σ) "Hσ Hps". iDestruct (pts_facts with "Hσ Hps") as %([Hl _] & _ & Hfit).
    destruct Hl as [E L]. cbn [fst snd] in E,L. destruct (Hfit b reg E). iPureIntro.
    eexists _, c, _. split; [reflexivity|]. split; [exact Hc|]. split; [lia|]. split.
    + unfold writable_span. cbn [span_ptr span_size ptr_addr ptr_cap]. split; [lia|]. exists b,reg.
      split; [done|]. split; [done|]. split; [done|]. apply (access_obj _ _ reg); [done | lia | lia | apply Z.mod_1_r].
    + right. exists b. auto.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) Hps". destruct Hf as (Hagree & Hd & Hr & Hw).
    destruct (M.E.memset_invocation _ _ _ _ _ _ _ _ _ _ _ _ (invoke_void_only _ _ _ _ _ _ _ _ _ _ _ _ Hinv))
      as (_ & -> & p & c' & n' & Hargs & _ & Hres & He). injection Hargs as <- <- <-. injection He as ->.
    iDestruct (pts_lookup with "Hh Hps") as %Hlk.
    assert (Hold : all_agree (ls_mem σ) (block_ps b reg (lo-b) xs cs)).
    { apply all_agree_intro. intros l v Hin. exact (Hagree _ _ (Hlk _ _ Hin)). }
    destruct Hold as [Hl Hold]. cbn [agree_piece fst snd] in Hl.
    destruct (fill_inside _ m' b reg lo xs cs a c n Hd Hl Hb8 Hl8 Ha ltac:(lia) ltac:(lia) ltac:(lia) Hlen Hvalid Hold Hres)
      as (Hnew & Hy & Hfr).
    destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (born & Hpre).
    destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hpre Hr) as [Hr' _]. pose proof Hres as ((Hregs & _) & _).
    set (ys := window_bytes m' b (lo-b) (length xs)). set (ds := aux_now m' b (lo-b) (length xs)).
    assert (Hkeys : (block_ps b reg (lo-b) ys ds).*1 = (block_ps b reg (lo-b) xs cs).*1).
    { apply block_ps_keys; [apply length_window_bytes | unfold ds; rewrite length_aux_now; lia]. }
    iMod (pts_update _ _ (block_ps b reg (lo-b) ys ds) with "Hh Hps") as "[Hh Hps]"; [exact Hkeys|].
    iModIntro. iExists _. iSplit; [done|]. iSplitL "Hh".
    + iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world]. split; [|split; [|split]].
      * intros l v Hv. destruct (lookup_overwrite _ _ _ _ Hv) as [Hin|[Hnk Hlk']].
        -- apply elem_of_cons in Hin as [Hin|Hin]; [injection Hin as -> ->; eapply live_at_regions; eassumption | exact (all_agree_elem _ _ _ _ Hnew Hin)].
        -- apply Hfr; [|exact (Hagree _ _ Hlk')]. intros Hkey. apply Hnk. rewrite Hkeys. right. exact Hkey.
      * exact (live_disjoint_regions _ _ Hregs Hd).
      * exact Hr'.
      * exact (os_wi_block _ _ _ _ _ _ _ _ _ _ _ _ Hregs Hlk Hw).
    + rewrite block_pts. iDestruct "Hps" as "(Hl & Hbytes & Haux)". iApply wp_ret; [reflexivity | reflexivity |]. iNext.
      iApply "HK". iFrame "Hl". iSplit; [done|]. iExists ys, ds. iFrame "Hbytes Haux". iPureIntro.
      unfold ys,ds. rewrite length_window_bytes length_aux_now. auto.
Qed.
End fill.
