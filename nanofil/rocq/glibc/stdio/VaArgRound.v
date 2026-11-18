(** A variadic function reads its arguments through a cursor, and
    `c: va_arg` rounds the cursor up to a multiple of 8 before it reads.
    After a 32-bit argument the cursor stands 4 bytes past a slot, so
    the next read starts from an address that is not a multiple of 8.
    The formatter does this whenever a `%d` or a `%c` comes before
    another conversion. The rule for a pointer argument in
    [VariadicLogic](../../theories/logic/VariadicLogic.v) asks for a
    cursor that already stands at a slot. This module proves the rule
    for a cursor that stands anywhere up to 7 bytes before the slot. It
    also restates the rule for a 32-bit argument over the world of a
    glibc program. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic VariadicLogic.
From Glibc Require Import OsWorld FileInv LibioLogic Fix WordString FormatterStringArg.
Import StringVL ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L LibioLogic.
Open Scope Z_scope.

(** Reading a pointer argument loads the cursor, rounds it up to the
    slot a, moves the cursor to the slot after a, and returns the
    pointer that the slot a holds. *)
Lemma va_arg_pointer_round m p cur c a m' x :
  access_res m (ptr_addr p) (ptr_cap p) 8 Read 8 = Some ok ->
  load_bytes m (ptr_addr p) 8 = cur -> aux_at m (ptr_addr p) = c ->
  (cur + 8 - 1) / 8 * 8 = a -> access_res m a c 8 Read 8 = Some ok ->
  store_res Wl m (ptr_addr p) (ptr_cap p) (WInt (a + 8)) = Some (ok, m') ->
  load_bytes m' a 8 = ptr_addr x -> aux_at m' a = ptr_cap x ->
  va_arg_res P p m = Some (RVal (WPtr x), m').
Proof.
  intros Hp Ha Hc Hr Hcell Hstore Haddr Hcap.
  unfold va_arg_res. rewrite Hp Ha Hc. cbn [va_cell class_width width_bytes ptr_addr ptr_cap].
  rewrite Hr Hcell Hstore Haddr Hcap. destruct x. reflexivity.
Qed.

Section round.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Moving the cursor writes only the cursor's own cell, so the world
    of the program stays as it was. *)
Lemma cursor_store_wi cb cr sb cur next m w h :
  (forall k v, (k, v) ∈ va_cursor_ps cb cr (mkPtr cur (Ro sb)) -> h !! k = Some v) ->
  os_wi w0 m w h -> os_wi w0 (store_bytes m cb 8 next) w (overwrite (va_cursor_ps cb cr (mkPtr next (Ro sb))) h).
Proof using Type.
  intros Hown Hw. eapply os_wi_store; [reflexivity | | exact Hw].
  intros k v Hin. destruct k; try done. apply Hown. unfold va_cursor_ps, cell in *. simpl in *. set_solver.
Qed.

(** The cursor stands at the address cur, and the next slot is at the
    offset off of the argument copy. The rule reads the pointer x from
    that slot and leaves the cursor at the slot after it. The pointer
    is null, or the caller lends a share of the lifetime of its
    object. *)
Lemma wp_va_arg_ptr f e ls l d args rest j cb cr cur sb sr off x dq ps Φ :
  map2_option (value_x ge e) [P] args = Some [WPtr (mkPtr cb (Obj cb))] ->
  cb mod 8 = 0 -> 0 < sb -> 0 <= off -> sb + off + 8 <= r_end sr -> r_end sr <= 2 ^ 48 ->
  0 <= cur -> (cur + 8 - 1) / 8 * 8 = sb + off -> 0 <= ptr_addr x < 2 ^ 64 ->
  (ptr_cap x = CNone \/ exists xb xr, (ptr_cap x = Obj xb \/ ptr_cap x = Ro xb) /\ (PLive xb, VLive xr) ∈ ps) ->
  pts (va_cursor_ps cb cr (mkPtr cur (Ro sb))) -∗ live sb sr -∗ pcell sb off x -∗ ptsq dq ps -∗
  ▷ (pts (va_cursor_ps cb cr (mkPtr (sb + off + 8) (Ro sb))) -∗ live sb sr -∗ pcell sb off x -∗ ptsq dq ps -∗
     WP (ERun (mkFrame f (put d (WPtr x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d P VaArg args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hargs Hcb Hsb Hoff Hsend Hsmax Hcur0 Hround Hrange Htarget.
  assert (Hal : (sb + off) mod 8 = 0) by (rewrite -Hround; apply Z.mod_mul; lia).
  assert (Hle : cur <= sb + off).
  { pose proof (Z.div_mod (cur + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (cur + 8 - 1) 8 ltac:(lia)).
    lia. }
  set (before := va_cursor_ps cb cr (mkPtr cur (Ro sb))).
  set (after := va_cursor_ps cb cr (mkPtr (sb + off + 8) (Ro sb))).
  set (reads := [(PLive sb, VLive sr); (PAux sb off, VAux (ptr_cap x))] ++ cell sb off (ptr_addr x)).
  iIntros "Hcursor Hsl Hsc Hps HK".
  iAssert (pts (before ++ reads)) with "[Hcursor Hsl Hsc]" as "Hpieces".
  { rewrite pts_app. iFrame "Hcursor".
    replace reads with ([(PLive sb, VLive sr)] ++ ((PAux sb off, VAux (ptr_cap x)) :: cell sb off (ptr_addr x)))
      by reflexivity.
    rewrite !pts_app. iFrame "Hsl Hsc". }
  iDestruct (pts_keys_nodup with "Hpieces") as %Hnd.
  rewrite fmap_app in Hnd. apply list.NoDup_app in Hnd as (_ & Hseparate & _).
  iApply (wp_write_with registry (os_wi w0) ge (ptsq dq ps) (fun m => all_agree m ps)
    (before ++ reads) (after ++ reads) _ _ [] (fun m => store_bytes m cb 8 (sb + off + 8)) with "Hpieces Hps [HK]").
  - rewrite !fmap_app. unfold before, after, va_cursor_ps, cell. reflexivity.
  - iIntros (σ) "Hσ Hps". iDestruct (ptsq_facts with "Hσ Hps") as %(Hagree & _). done.
  - intros m fuel (Hagree & Hd & _) Hps.
    apply all_agree_app in Hagree as [Hcur Hreads].
    unfold before, va_cursor_ps in Hcur. cbn [all_agree fst snd] in Hcur. destruct Hcur as (Hclive & Hcaux & Hcbytes).
    unfold reads in Hreads. cbn [all_agree fst snd] in Hreads. destruct Hreads as (Hslive & Hsaux & Hsbytes).
    destruct (cell_bounds _ _ _ _ _ Hclive Hcbytes) as [Hc0 Hcend].
    destruct (cell_store_ok m cb cr 0 cb (sb + off + 8) Hd Hclive Hc0 ltac:(lia) ltac:(lia)) as [Hnew Hframe].
    assert (Hframe_reads : all_agree (store_bytes m cb 8 (sb + off + 8)) reads).
    { apply all_agree_intro. intros k v Hin. apply Hframe.
      - intros Hkey. apply (Hseparate k).
        + unfold before, va_cursor_ps. rewrite fmap_app. apply elem_of_app. right. exact Hkey.
        + exact (list_elem_of_fmap_2 fst _ _ Hin).
      - apply (all_agree_elem _ reads k v); [|exact Hin].
        unfold reads. cbn [all_agree fst snd]. split; [exact Hslive|]. split; [exact Hsaux | exact Hsbytes]. }
    pose proof Hframe_reads as (Hslive' & Hsaux' & Hsbytes').
    assert (Hcursor : load_bytes m cb 8 = cur).
    { replace cb with (cb + 0) at 1 by lia.
      rewrite (cell_load m cb cr 0 cur (cb + 0) Hclive Hcbytes eq_refl). apply Z.mod_small. lia. }
    assert (Hcursor_cap : aux_at m cb = Ro sb).
    { unfold aux_at. replace cb with (cb + 0) at 1 by lia. apply (aux_holds_ro m (cb + 0) sb sr); [|exact Hslive].
      exact (aux_piece_holds _ _ _ _ _ Hclive Hcaux). }
    assert (Hresult_cap : aux_at (store_bytes m cb 8 (sb + off + 8)) (sb + off) = ptr_cap x).
    { unfold aux_at. pose proof (aux_piece_holds _ _ _ _ _ Hslive' Hsaux') as Haux.
      destruct Htarget as [Hnull | (xb & xr & [Hobj | Hro] & Hmember)].
      - apply aux_holds_live; [exact Haux | auto].
      - apply aux_holds_live; [exact Haux|]. right. exists xb, xr. split; [exact Hobj|].
        exact (all_agree_elem _ _ _ _ Hps Hmember).
      - rewrite Hro in Haux |- *. apply (aux_holds_ro _ _ _ xr Haux). exact (all_agree_elem _ _ _ _ Hps Hmember). }
    split.
    + eapply rule_va_arg; [exact Hargs|].
      apply (va_arg_pointer_round m (mkPtr cb (Obj cb)) cur (Ro sb) (sb + off) (store_bytes m cb 8 (sb + off + 8)) x).
      * cbn [ptr_addr ptr_cap]. apply (access_obj _ _ cr); [exact (proj1 Hclive) | lia | lia | exact Hcb].
      * exact Hcursor.
      * exact Hcursor_cap.
      * exact Hround.
      * apply (access_ro_read _ _ sr); [exact (proj1 Hslive) | lia | exact Hsend | exact Hal].
      * apply store_res_long. cbn [ptr_addr ptr_cap].
        apply (access_obj _ _ cr); [exact (proj1 Hclive) | lia | lia | apply Z.mod_1_r].
      * rewrite (cell_load _ sb sr off (ptr_addr x) (sb + off) Hslive' Hsbytes' eq_refl). apply Z.mod_small. exact Hrange.
      * exact Hresult_cap.
    + split; [reflexivity|]. split.
      * apply store_bytes_kept. exact (in_object_live _ _ _ cb Hclive ltac:(lia) ltac:(lia)).
      * split.
        -- apply all_agree_app. split; [|exact Hframe_reads].
           unfold after, va_cursor_ps. cbn [all_agree fst snd]. split; [exact Hclive|]. split; [exact Hcaux | exact Hnew].
        -- eapply frame_ok_mono; [|exact Hframe]. intros k Hin.
           rewrite fmap_app. apply elem_of_app. left.
           unfold after, va_cursor_ps. rewrite fmap_app. apply elem_of_app. right. exact Hin.
  - intros m w h Hown Hw. rewrite overwrite_app. rewrite (overwrite_id reads h).
    + apply (cursor_store_wi cb cr sb cur); [|exact Hw]. intros k v Hin. apply Hown. apply elem_of_app. left. exact Hin.
    + intros k v Hin. apply Hown. apply elem_of_app. right. exact Hin.
  - iNext. iIntros "Hpieces Hps". iEval (rewrite pts_app) in "Hpieces". iDestruct "Hpieces" as "[Hcursor Hreads]".
    iEval (rewrite /reads; rewrite pts_app) in "Hreads". iDestruct "Hreads" as "[Hhead Hsc]".
    iEval (rewrite /pts !big_sepL_cons) in "Hhead". iDestruct "Hhead" as "(Hsl & Hsa & _)".
    iApply ("HK" with "Hcursor [Hsl] [Hsa Hsc] Hps"); rewrite /live /pcell /pts; iFrame; done.
Qed.

(** The rule for a 32-bit argument reads the integer v from the next
    slot and leaves the cursor 4 bytes into that slot. *)
Lemma wp_va_arg_w f e ls l d args rest j cb cr cur sb sr off v Φ :
  map2_option (value_x ge e) [P] args = Some [WPtr (mkPtr cb (Obj cb))] ->
  cb mod 8 = 0 -> 0 < sb -> 0 <= off -> sb + off + 8 <= r_end sr -> r_end sr <= 2 ^ 48 ->
  0 <= cur -> (cur + 8 - 1) / 8 * 8 = sb + off ->
  pts (va_cursor_ps cb cr (mkPtr cur (Ro sb))) -∗ live sb sr -∗ icell sb off v -∗
  ▷ (pts (va_cursor_ps cb cr (mkPtr (sb + off + 4) (Ro sb))) -∗ live sb sr -∗ icell sb off v -∗
     WP (ERun (mkFrame f (put d (WInt (v mod 2 ^ 32)) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d W VaArg args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hargs Hcb Hsb Hoff Hsend Hsmax Hcur0 Hround. iIntros "Hcursor Hsl Hsc HK".
  iApply (wp_va_arg_int registry (os_wi w0) ge f e ls l d W 4 args rest j cb cr cur sb sr off v
    with "Hcursor Hsl Hsc HK"); [left; split; reflexivity | exact Hargs | exact Hcb | exact Hsb | exact Hoff | exact Hsend |
    exact Hsmax | exact Hcur0 | exact Hround |].
  intros m wd h Hown Hw. exact (cursor_store_wi cb cr sb cur (sb + off + 4) m wd h Hown Hw).
Qed.

(** A `%s` reads a pointer into a string that the caller shares. The
    string owns a share of the lifetime of its object, and the rule
    for a pointer argument asks for that share. This rule lends the
    share for the read and gives the string back whole. *)
Lemma wp_va_arg_str f e ls l d args rest j cb cr cur sb sr off p dq s Φ :
  map2_option (value_x ge e) [P] args = Some [WPtr (mkPtr cb (Obj cb))] ->
  cb mod 8 = 0 -> 0 < sb -> 0 <= off -> sb + off + 8 <= r_end sr -> r_end sr <= 2 ^ 48 ->
  0 <= cur -> (cur + 8 - 1) / 8 * 8 = sb + off -> 0 <= ptr_addr p < 2 ^ 64 ->
  pts (va_cursor_ps cb cr (mkPtr cur (Ro sb))) -∗ live sb sr -∗ pcell sb off p -∗ word_string dq p s -∗
  ▷ (pts (va_cursor_ps cb cr (mkPtr (sb + off + 8) (Ro sb))) -∗ live sb sr -∗ pcell sb off p -∗ word_string dq p s -∗
     WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d P VaArg args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hargs Hcb Hsb Hoff Hsend Hsmax Hcur0 Hround Hrange. iIntros "Hcursor Hsl Hsc Hs HK".
  iDestruct "Hs" as (b reg ws) "[%Hshape [Htarget Hwords]]".
  iApply (wp_va_arg_ptr _ _ _ _ _ _ _ _ cb cr cur sb sr off p dq [(PLive b, VLive reg)]
    with "Hcursor Hsl Hsc Htarget"); [exact Hargs | exact Hcb | exact Hsb | exact Hoff | exact Hsend | exact Hsmax |
    exact Hcur0 | exact Hround | exact Hrange | |].
  { right. exists b, reg. split; [exact (ss_cap _ _ _ _ _ Hshape) | by left]. }
  iNext. iIntros "Hcursor Hsl Hsc Htarget". iApply ("HK" with "Hcursor Hsl Hsc"). iExists b, reg, ws.
  iSplit; [done|]. iFrame.
Qed.

End round.
