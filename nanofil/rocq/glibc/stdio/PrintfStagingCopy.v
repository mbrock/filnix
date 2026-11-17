(** A printf staging array shares its allocation with the buffer header.
    A string can leave the write pointer between aligned addresses. Copying
    there changes capability slots before the pointer, but not before the
    aligned staging array. This module keeps ownership of that array while
    preserving the separate header and the single allocation lifetime. *)
From Glibc Require Import GlibcProgram GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import MemFwdLogic LibioDefaultXsputnCopy.
Import ListNotations.
Open Scope Z_scope.

(** The replacement bytes cover the same owned window after the copy. *)
Definition window_bytes (m : mem) (b lo : Z) (n : nat) : list Z :=
  map (fun i => m_bytes m (b + (lo + Z.of_nat i))) (seq 0 n).

(** Reading the window preserves its length. *)
Lemma length_window_bytes m b lo n : length (window_bytes m b lo n) = n.
Proof. unfold window_bytes. by rewrite length_map length_seq. Qed.

(** A copy may start anywhere inside the aligned owned window. Its frame
    preserves every piece outside that window, including the buffer header. *)
Lemma copy_window_after m m' b reg lo xs cs o b' reg' o' ys c' :
  live_disjoint m -> live_at m b reg -> live_at m b' reg' ->
  b mod 8 = 0 -> lo mod 8 = 0 -> length cs = length xs ->
  0 <= lo -> lo <= o -> o + Z.of_nat (length ys) <= lo + Z.of_nat (length xs) ->
  Forall (fun x => 0 <= x < 256) xs -> Forall (fun y => 0 <= y < 256) ys ->
  all_agree m (byte_ps b lo xs ++ aux_ps b lo cs) -> all_agree m (byte_ps b' o' ys) ->
  copy_result m (mkPtr (b + o) (Obj b)) (mkPtr (b' + o') c') (Z.of_nat (length ys)) m' ->
  all_agree m' (byte_ps b lo (window_bytes m' b lo (length xs)) ++
    aux_ps b lo (aux_now m' b lo (length xs))) /\
  Forall (fun x => 0 <= x < 256) (window_bytes m' b lo (length xs)) /\
  frame_ok (byte_ps b lo xs ++ aux_ps b lo cs).*1 m m'.
Proof.
  intros Hd Hl Hl' Hb8 Hlo8 Hlc Hlo Ho Hon Hx Hy Hdst Hsrc Hres.
  pose proof Hres as (Hfr & _ & _). pose proof Hfr as (Hr & Hbo & Hao).
  apply all_agree_app in Hdst as [Hxa Hca]. destruct Hl as [E0 L0].
  assert (Hreg : registered m' b) by (unfold registered; rewrite Hr E0; discriminate).
  assert (Hbyte : forall i, (i < length xs)%nat -> b + (lo + Z.of_nat i) < r_end reg).
  { intros i Hi. destruct (lookup_lt_is_Some_2 xs i Hi) as [x Hxi].
    destruct (byte_ps_agree _ _ _ _ _ _ _ (conj E0 L0) Hxa Hxi) as (_ & H1 & H2). lia. }
  assert (Hnow : forall i, (i < length xs)%nat -> 0 <= m_bytes m' (b + (lo + Z.of_nat i)) < 256).
  { intros i Hi. destruct (copy_result_cells _ _ _ _ _ (b + (lo + Z.of_nat i)) Hres) as [Hc _]. rewrite Hc.
    cbn [ptr_addr].
    destruct ((b + o <=? b + (lo + Z.of_nat i)) &&
      (b + (lo + Z.of_nat i) <? b + o + Z.of_nat (length ys))) eqn:Hin.
    - apply andb_true_iff in Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      destruct (lookup_lt_is_Some_2 ys (Z.to_nat (lo + Z.of_nat i - o)) ltac:(lia)) as [y Hyk].
      destruct (byte_ps_agree _ _ _ _ _ _ _ Hl' Hsrc Hyk) as (Hv & _ & _).
      replace (b' + o' + (b + (lo + Z.of_nat i) - (b + o)))
        with (b' + (o' + Z.of_nat (Z.to_nat (lo + Z.of_nat i - o)))) by lia.
      rewrite Hv. exact (Forall_lookup_1 _ _ _ _ Hy Hyk).
    - destruct (lookup_lt_is_Some_2 xs i Hi) as [x Hxi].
      destruct (byte_ps_agree _ _ _ _ _ _ _ (conj E0 L0) Hxa Hxi) as (Hv & _ & _).
      rewrite Hv. exact (Forall_lookup_1 _ _ _ _ Hx Hxi). }
  split; [|split].
  - apply all_agree_app. split; apply all_agree_intro; intros l v Hin.
    + apply byte_ps_elem in Hin as (i & y & Hyi & -> & ->). unfold window_bytes in Hyi.
      apply list_lookup_fmap_Some in Hyi as (k & -> & Hk).
      pose proof (lookup_lt_Some _ _ _ Hk) as Hi. rewrite length_seq in Hi.
      rewrite lookup_seq_lt in Hk; [injection Hk as <- | exact Hi]. cbn [agree_piece]. split; [exact Hreg|].
      intros reg0 E L. rewrite Hr E0 in E. injection E as <-. specialize (Hbyte i Hi). lia.
    + apply aux_ps_elem in Hin as (i & c & Hci & -> & ->).
      unfold aux_now in Hci. change (map ?f ?l) with (f <$> l) in Hci.
      apply list_lookup_fmap_Some in Hci as (k & -> & Hk).
      pose proof (lookup_lt_Some _ _ _ Hk) as Hi. rewrite length_seq in Hi.
      rewrite lookup_seq_lt in Hk; [injection Hk as <- | exact Hi]. cbn [agree_piece]. split; [exact Hreg|].
      intros reg0 E L. rewrite Hr E0 in E. injection E as <-. specialize (Hbyte i Hi).
      split; [lia|]. split; [lia|]. left. reflexivity.
  - apply Forall_forall. intros x Hin. unfold window_bytes in Hin. apply in_map_iff in Hin as (i & <- & Hi).
    apply in_seq in Hi. apply Hnow. lia.
  - apply (frame_within _ _ _ b reg); [exact Hr | exact Hd | exact (conj E0 L0) | |].
    + intros a H. apply Hbo. intros Hs. unfold span_contains in Hs. cbn in Hs.
      assert (Hlt : (Z.to_nat (a - b - lo) < length xs)%nat) by lia.
      apply H; [split; [lia|]; specialize (Hbyte _ Hlt); lia|]. rewrite fmap_app. apply elem_of_app. left.
      replace (a - b) with (lo + (a - b - lo)) by lia. apply byte_ps_key. lia.
    + intros a H. apply Hao. destruct (memset_touched _ _ _) eqn:Ht; [|reflexivity]. exfalso.
      apply memset_touched_spec in Ht as (Hn & Ha8 & Hhi & Hlo'). cbn [ptr_addr] in Hhi, Hlo'.
      assert (Hab : b + lo <= a).
      { pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.div_mod b 8 ltac:(lia)).
        pose proof (Z.div_mod lo 8 ltac:(lia)). lia. }
      assert (Hlt : (Z.to_nat (a - b - lo) < length xs)%nat) by lia.
      apply H; [split; [lia|]; specialize (Hbyte _ Hlt); lia|]. rewrite fmap_app. apply elem_of_app. right.
      replace (a - b) with (lo + (a - b - lo)) by lia. apply aux_ps_key. lia.
Qed.

(** Every copied source byte appears at its destination offset in the
    returned window, including copies that begin between aligned slots. *)
Lemma window_copy_lookup m m' b lo n o b' reg' o' ys c' :
  live_at m b' reg' -> all_agree m (byte_ps b' o' ys) ->
  lo <= o -> o + Z.of_nat (length ys) <= lo + Z.of_nat n ->
  copy_result m (mkPtr (b + o) (Obj b)) (mkPtr (b' + o') c') (Z.of_nat (length ys)) m' ->
  forall i y, ys !! i = Some y ->
    window_bytes m' b lo n !! (Z.to_nat (o - lo) + i)%nat = Some y.
Proof.
  intros Hl Hsrc Ho Hn Hres i y Hyi.
  pose proof (lookup_lt_Some _ _ _ Hyi) as Hi.
  unfold window_bytes. rewrite list_lookup_fmap lookup_seq_lt; [|lia].
  cbn. replace (lo + Z.of_nat (Z.to_nat (o - lo) + i)) with (o + Z.of_nat i) by lia.
  destruct Hres as (_ & Hcopy & _). rewrite Hcopy; [|unfold span_contains; cbn; lia].
  cbn [ptr_addr]. replace (b' + o' + (b + (o + Z.of_nat i) - (b + o)))
    with (b' + (o' + Z.of_nat i)) by lia.
  destruct (byte_ps_agree _ _ _ _ _ _ _ Hl Hsrc Hyi) as (Hv & _).
  by rewrite Hv.
Qed.

(** Bytes before and after the copy retain their values. In particular,
    appending a string does not forget an earlier formatted prefix. *)
Lemma window_copy_outside m m' b reg lo xs o b' o' (ys : list Z) c' :
  live_at m b reg -> all_agree m (byte_ps b lo xs) ->
  copy_result m (mkPtr (b + o) (Obj b)) (mkPtr (b' + o') c') (Z.of_nat (length ys)) m' ->
  forall i x, xs !! i = Some x ->
    lo + Z.of_nat i < o \/ o + Z.of_nat (length ys) <= lo + Z.of_nat i ->
    window_bytes m' b lo (length xs) !! i = Some x.
Proof.
  intros Hl Hdst Hres i x Hxi Hout.
  pose proof (lookup_lt_Some _ _ _ Hxi) as Hi.
  unfold window_bytes. rewrite list_lookup_fmap lookup_seq_lt; [|exact Hi]. cbn.
  destruct Hres as ((Hr & Hbytes & _) & _).
  rewrite Hbytes; [|unfold span_contains; cbn; lia].
  destruct (byte_ps_agree _ _ _ _ _ _ _ Hl Hdst Hxi) as (Hv & _). by rewrite Hv.
Qed.

From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps MemFwdCode Fix GlibcSpec.
Import LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic
  ProgramAbbreviations.

(** ## Owned staging windows *)

(** The caller lends the staging array and its single allocation lifetime
    to the runtime copy. The header stays in the caller's [[frame]], and
    the returned array records the copied bytes at their actual offsets. *)
Section values.
Context {Σ : gFunctors} {gen_heapGS0 : gen_heapGS piece pval Σ}.
Existing Instance gen_heapGS0.
(** The returned array retains its size, valid bytes and auxiliary slots.
    The pure lookup fact identifies each copied byte inside that array. *)
Definition window_after (b lo : Z) (xs : list Z) (o : Z) (ys : list Z) : iProp Σ :=
  ∃ xs' cs', ⌜length xs' = length xs /\ length cs' = length xs /\ Forall (fun x => 0 <= x < 256) xs' /\
    (forall i y, ys !! i = Some y -> xs' !! (Z.to_nat (o - lo) + i)%nat = Some y) /\
    (forall i x, xs !! i = Some x ->
      lo + Z.of_nat i < o \/ o + Z.of_nat (length ys) <= lo + Z.of_nat i -> xs' !! i = Some x)⌝ ∗
    bytes b lo xs' ∗ auxes b lo cs'.
End values.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None)
  (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None).
Local Instance window_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The real runtime move preserves the source share and returns the
    destination window without borrowing any bytes of the buffer header. *)
Lemma wp_zmemmove_window f e ls lab vd vs vn rest j b reg lo xs cs o dq b' reg' o' c' ys Φ :
  arg_x ge e (Arg P vd) = Some (WPtr (mkPtr (b + o) (Obj b))) ->
  arg_x ge e (Arg P vs) = Some (WPtr (mkPtr (b' + o') c')) -> c' = Obj b' \/ c' = Ro b' ->
  arg_x ge e (Arg L vn) = Some (WInt (Z.of_nat (length ys))) ->
  b mod 8 = 0 -> lo mod 8 = 0 -> b' mod 8 = 0 -> 0 <= lo -> lo <= o -> 0 <= o' ->
  o + Z.of_nat (length ys) <= lo + Z.of_nat (length xs) ->
  b + lo + Z.of_nat (length xs) <= r_end reg -> b' + o' + Z.of_nat (length ys) <= r_end reg' ->
  length cs = length xs -> Forall (fun x => 0 <= x < 256) xs -> Forall (fun y => 0 <= y < 256) ys ->
  live b reg -∗ bytes b lo xs -∗ auxes b lo cs -∗ liveq dq b' reg' -∗ bytesq dq b' o' ys -∗
  ▷ (live b reg -∗ window_after b lo xs o ys -∗ liveq dq b' reg' -∗ bytesq dq b' o' ys -∗
     WP (ERun (mkFrame f e ls None (Exec lab rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call CVoid (Global (TAtom "zmemmove")) [Arg P vd; Arg P vs; Arg L vn] :: rest) j))
        : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hpd Hps Hc' Hn Hb8 Hlo8 Hb8' Hlo Ho Ho' Hon Hend Hend' Hlc Hx Hy.
  iIntros "Hl Hx Hcs Hl' Hy HK".
  iAssert (⌜b <> b'⌝)%I as %Hne.
  { rewrite /live /liveq /pts /ptsq !big_sepL_singleton. cbn [fst snd].
    iDestruct (pointsto_ne with "Hl Hl'") as %Hne. iPureIntro. intros <-. apply Hne. reflexivity. }
  iDestruct (block_pts b reg lo xs cs with "[$Hl $Hx $Hcs]") as "Hdst".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (void_only (memmove_contract os_world))
            [WPtr (mkPtr (b + o) (Obj b)); WPtr (mkPtr (b' + o') c'); WInt (Z.of_nat (length ys))]
            (pts (block_ps b reg lo xs cs) ∗ liveq dq b' reg' ∗ bytesq dq b' o' ys) with "[$Hdst $Hl' $Hy] [HK]");
    [exact Hmove_fn | exact Hmove_sym | reflexivity | exact Hmove | cbn [map_option]; rewrite Hpd Hps Hn; done | | |].
  - split; [reflexivity|]. split; [left; reflexivity | exists vd, vs, vn; reflexivity].
  - iIntros (σ) "Hσ (Hdst & Hl' & Hy)". iDestruct (pts_facts with "Hσ Hdst") as %(Ha & Hd & Hfit).
    iDestruct (ptsq_facts with "Hσ Hl'") as %([[E' L'] _] & _).
    iDestruct (ptsq_facts with "Hσ Hy") as %(Hys & _). iPureIntro.
    destruct Ha as [[E L] _]. cbn [fst snd] in E, L.
    destruct (Hfit b reg E) as [Hb0 Hfit']. destruct (Hfit b' reg' E') as [Hb0' Hfit''].
    eexists _, _, _. split; [reflexivity|]. split; [|split; [|split]].
    + split; [lia|]. split; [lia|]. split.
      * unfold writable_span. cbn [span_ptr span_size ptr_addr ptr_cap].
        split; [lia|]. exists b, reg. split; [reflexivity|]. split; [exact E|]. split; [exact L|].
        apply (access_obj _ _ reg); [exact E | lia | lia | apply Z.mod_1_r].
      * right. exists b. auto.
    + split; [lia|]. split; [exists b', reg'; auto|]. split.
      * apply (access_read _ b' reg'); [exact Hc' | exact E' | cbn; lia | cbn; lia | apply Z.mod_1_r].
      * intros i Hi. cbn [ptr_addr]. destruct (lookup_lt_is_Some_2 ys (Z.to_nat i) ltac:(lia)) as [y Hyi].
        destruct (byte_ps_agree _ _ _ _ _ _ _ (conj E' L') Hys Hyi) as (Hv & _ & _).
        replace (b' + o' + i) with (b' + (o' + Z.of_nat (Z.to_nat i))) by lia. rewrite Hv.
        exact (Forall_lookup_1 _ _ _ _ Hy Hyi).
    + right. exists b'. auto.
    + left. reflexivity.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) (Hdst & Hl' & Hy)".
    destruct Hf as (Ha & Hd & Hr & Hw).
    destruct (M.E.copy_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ (invoke_void _ _ _ _ _ _ _ _ _ _ _ _ Hinv))
      as (_ & -> & d' & s0 & n' & Hxs & _ & Hres & He).
    injection Hxs as <- <- <-. injection He as ->.
    iDestruct (pts_lookup with "Hh Hdst") as %Hlk.
    iDestruct (ptsq_lookup with "Hh Hl'") as %Hlk1. iDestruct (ptsq_lookup with "Hh Hy") as %Hlk2.
    assert (Hold : all_agree (ls_mem σ) (block_ps b reg lo xs cs)).
    { apply all_agree_intro. intros l v Hin. exact (Ha l v (Hlk l v Hin)). }
    assert (Hold' : all_agree (ls_mem σ) (byte_ps b' o' ys)).
    { apply all_agree_intro. intros l v Hin. exact (Ha l v (Hlk2 l v Hin)). }
    assert (Hlv' : live_at (ls_mem σ) b' reg').
    { exact (Ha _ _ (Hlk1 _ _ ltac:(apply elem_of_cons; by left))). }
    destruct Hold as [Hlv Hold]. cbn [agree_piece fst snd] in Hlv.
    destruct (copy_window_after (ls_mem σ) m' b reg lo xs cs o b' reg' o' ys c'
                Hd Hlv Hlv' Hb8 Hlo8 Hlc Hlo Ho Hon Hx Hy Hold Hold' Hres) as (Hnew & Hby & Hfr).
    destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (born & Hpre).
    destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hpre Hr) as [Hr' _].
    pose proof Hres as ((Hregs & _) & _).
    set (xs' := window_bytes m' b lo (length xs)). set (cs' := aux_now m' b lo (length xs)).
    assert (Hk : (block_ps b reg lo xs' cs').*1 = (block_ps b reg lo xs cs).*1).
    { apply block_ps_keys; [unfold xs'; apply length_window_bytes | unfold cs'; rewrite length_aux_now; lia]. }
    iMod (pts_update _ _ (block_ps b reg lo xs' cs') with "Hh Hdst") as "[Hh Hdst]"; [exact Hk|].
    iModIntro. iExists _. iSplit; [iPureIntro; reflexivity|].
    iSplitL "Hh".
    + iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world]. split; [|split; [|split]].
      * intros l v Hl'. destruct (lookup_overwrite _ _ _ _ Hl') as [Hin | [Hnk Hh]].
        -- apply elem_of_cons in Hin as [Hin|Hin].
           ++ injection Hin as -> ->. cbn [agree_piece]. exact (live_at_regions _ _ _ _ Hregs Hlv).
           ++ exact (all_agree_elem _ _ _ _ Hnew Hin).
        -- apply Hfr; [|exact (Ha l v Hh)]. intros Hk'. apply Hnk. rewrite Hk.
           cbn [fmap list_fmap fst block_ps]. right. exact Hk'.
      * exact (live_disjoint_regions _ _ Hregs Hd).
      * exact Hr'.
      * exact (os_wi_block _ _ _ _ _ _ _ _ _ _ _ _ Hregs Hlk Hw).
    + rewrite block_pts. iDestruct "Hdst" as "(Hl & Hx & Hcs)".
      iApply ("HK" with "Hl [Hx Hcs] Hl' Hy"). iExists xs', cs'. iFrame "Hx Hcs". iPureIntro.
      split; [apply length_window_bytes|]. split; [unfold cs'; apply length_aux_now |].
      split; [exact Hby|]. split.
      * eapply window_copy_lookup; eassumption.
      * eapply window_copy_outside; [exact Hlv | apply all_agree_app in Hold; exact (proj1 Hold) | exact Hres].
Qed.

(** This memcpy contract owns only an aligned window of the destination
    allocation. The write pointer itself need not be aligned. *)
Definition window_copy_spec : fspec Σ :=
  FSpec (Z * region * Z * list Z * list cap * Z * dfrac * Z * region * Z * cap * list Z)
    (fun '(b, _, _, _, _, o, _, b', _, o', c', ys) =>
      [WPtr (mkPtr (b + o) (Obj b)); WPtr (mkPtr (b' + o') c'); WInt (Z.of_nat (length ys))])
    (fun '(b, reg, lo, xs, cs, o, dq, b', reg', o', c', ys) =>
      ⌜(c' = Obj b' \/ c' = Ro b') /\ Z.of_nat (length ys) < 2 ^ 64 /\
        b mod 8 = 0 /\ lo mod 8 = 0 /\ b' mod 8 = 0 /\ 0 <= lo /\ lo <= o /\ 0 <= o' /\
        o + Z.of_nat (length ys) <= lo + Z.of_nat (length xs) /\
        b + lo + Z.of_nat (length xs) <= r_end reg /\ b' + o' + Z.of_nat (length ys) <= r_end reg' /\
        length cs = length xs /\ Forall (fun x => 0 <= x < 256) xs /\ Forall (fun y => 0 <= y < 256) ys⌝ ∗
      live b reg ∗ bytes b lo xs ∗ auxes b lo cs ∗ liveq dq b' reg' ∗ bytesq dq b' o' ys)%I
    (fun '(b, reg, lo, xs, cs, o, dq, b', reg', o', c', ys) v =>
      ⌜v = Ret (WPtr (mkPtr (b + o) (Obj b)))⌝ ∗
      live b reg ∗ window_after b lo xs o ys ∗ liveq dq b' reg' ∗ bytesq dq b' o' ys)%I.

(** The captured memcpy body invokes the runtime move and returns its
    original destination pointer, with the owned window updated. *)
Lemma memcpy_window_spec_valid g : find_fn ge g = Some (Defined glibc_memcpy) ->
  HasSpec registry (os_wi w0) ge g window_copy_spec.
Proof using Type*.
  intros Hg [[[[[[[[[[[b reg] lo] xs] cs] o] dq] b'] reg'] o'] c'] ys].
  exists glibc_memcpy. split; [exact Hg|]. split; [eexists; reflexivity|].
  intros fr Φ Hfr. cbn in Hfr. injection Hfr as <-. cbn [fs_pre fs_post window_copy_spec].
  iIntros "(%Hp & Hl & Hx & Hcs & Hl' & Hy) HK".
  destruct Hp as (Hc' & Hn & Hb8 & Hlo8 & Hb8' & Hlo & Ho & Ho' & Hon & Hend & Hend' & Hlc & Hx & Hy).
  iApply wp_enter; [reflexivity | reflexivity |]. iNext. cbn [b_insts b_jump].
  iApply (wp_zmemmove_window with "Hl Hx Hcs Hl' Hy");
    [reflexivity | reflexivity | exact Hc' | cbn; rewrite Z.mod_small; [reflexivity | lia]
    | exact Hb8 | exact Hlo8 | exact Hb8' | exact Hlo | exact Ho | exact Ho' | exact Hon
    | exact Hend | exact Hend' | exact Hlc | exact Hx | exact Hy |].
  iNext. iIntros "Hl Hx Hl' Hy". iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  iApply "HK". by iFrame.
Qed.

(** A caller resumes after the concrete memcpy call with the same source
    share and allocation lifetime, and the updated staging window. *)
Lemma wp_call_memcpy_window f e ls lab r g args rest j b reg lo xs cs o dq b' reg' o' c' ys cf' Φ :
  map_option (arg_x ge e) args =
    Some [WPtr (mkPtr (b + o) (Obj b)); WPtr (mkPtr (b' + o') c'); WInt (Z.of_nat (length ys))] ->
  find_fn ge g = Some (Defined glibc_memcpy) ->
  resume (mkFrame f e ls None (Exec lab rest j)) (mkPending r None) (Ret (WPtr (mkPtr (b + o) (Obj b))))
    = Some cf' ->
  c' = Obj b' \/ c' = Ro b' -> Z.of_nat (length ys) < 2 ^ 64 ->
  b mod 8 = 0 -> lo mod 8 = 0 -> b' mod 8 = 0 -> 0 <= lo -> lo <= o -> 0 <= o' ->
  o + Z.of_nat (length ys) <= lo + Z.of_nat (length xs) ->
  b + lo + Z.of_nat (length xs) <= r_end reg -> b' + o' + Z.of_nat (length ys) <= r_end reg' ->
  length cs = length xs -> Forall (fun x => 0 <= x < 256) xs -> Forall (fun y => 0 <= y < 256) ys ->
  live b reg -∗ bytes b lo xs -∗ auxes b lo cs -∗ liveq dq b' reg' -∗ bytesq dq b' o' ys -∗
  ▷ (live b reg -∗ window_after b lo xs o ys -∗ liveq dq b' reg' -∗ bytesq dq b' o' ys -∗
     WP (ERun cf' : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call r (Global g) args :: rest) j)) : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hxa Hg Hres Hc' Hn Hb8 Hlo8 Hb8' Hlo Ho Ho' Hon Hend Hend' Hlc Hx Hy.
  iIntros "Hl Hx Hcs Hl' Hy HK".
  pose proof (memcpy_window_spec_valid g Hg) as Hspec.
  call_spec with (b, reg, lo, xs, cs, o, dq, b', reg', o', c', ys).
  { repeat split; assumption. }
  iDestruct "Hpost" as "(-> & Hl & Hx & Hl' & Hy)".
  iExists cf'. iSplit; [done|]. iNext. iApply ("HK" with "Hl Hx Hl' Hy").
Qed.
End rules.
