(** GNU Hello's closeout helpers through the [[separation logic]].
    Module statics and the four errno bytes are owned pieces. Stream
    operations are premise triples, including their frame obligations;
    the null file name excludes the named-file diagnostic. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run StepRules Symbolic
  ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic MemLogic
  HelloModule HelloLeaf.
Open Scope Z_scope.
Open Scope list_scope.

(** Keep unknown arithmetic folded in computed instruction premises. *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** The stream-closing helper from the linked IR. *)
Definition close_stream_fn : func := Eval vm_compute in hello_fn "close_stream".
(** The exit callback from the linked IR. *)
Definition close_stdout_fn : func := Eval vm_compute in hello_fn "close_stdout".
(** A close_stream block. *)
Definition cs_block (s : String.string) : block := hblk close_stream_fn s.
(** A close_stdout block. *)
Definition co_block (s : String.string) : block := hblk close_stdout_fn s.

(** The canonical W loaded from four owned bytes, signed or unsigned. *)
Definition close_w (xs : list Z) : Z :=
  match xs with
  | [a; b; c; d] => extension Sw (((d * 256 + c) * 256 + b) * 256 + a) mod 2 ^ 32
  | _ => 0
  end.

(** A canonical W value fits its return channel. *)
Lemma close_w_range xs : 0 <= close_w xs < 2 ^ 32.
Proof.
  unfold close_w. destruct xs as [|a [|b [|c [|d [|u xs]]]]]; try (cbn; lia).
  apply Z.mod_pos_bound. lia.
Qed.

(** close_stream binds its stream argument. *)
Lemma close_stream_entry p : invocation close_stream_fn [WPtr p] =
  mkFrame close_stream_fn [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** The stream helper over any [[runtime]]. *)
Module HelloCloseOn (R : Runtime) (LG0 : LogicSig R).
Module HL := HelloLeafOn R LG0.
Module ML := HL.ML.
Module SL := ML.SL.
Module LG := ML.LG.
Module L := LG.L.
Import L LG SL ML HL.

Section close.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The instance used by all closeout triples. *)
Local Instance close_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.
(** Expressions in the linked program. *)
Local Notation cexpr := (language.expr (nanofil_lang registry ge)).

(** The represented errno cell is fixed in this thread. *)
Context (eb eo : Z) (er : region) (cell : world -> ptr) (rep : mem -> world -> Prop)
  (Herrno : registry (TAtom "__errno_location") = Some (errno_location_contract world cell rep))
  (Hlinked : hello_linked ge)
  (Hcell : forall m w h, wi m w h -> cell w = mkPtr (eb + eo) (Obj eb))
  (Hrep : forall m w h, wi m w h -> rep m w /\ errno_cell m (cell w)).

(** The errno pointer used in the IR. *)
Let ep := mkPtr (eb + eo) (Obj eb).

(** Errno lookup exports the represented cell without changing any pieces.
    Local rule for promotion to a libc logic module. *)
Lemma wp_close_errno f e ls lab d rest j Φ :
  ▷ WP (ERun (mkFrame f (put d (WPtr ep) e) ls None (Exec lab rest j)) : cexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec lab
    (Call (CResult d P) (Global (TAtom "__errno_location")) [] :: rest) j)) : cexpr) {{ Φ }}.
Proof.
  iIntros "HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (errno_location_contract world cell rep) [] True%I
    with "[] [HK]").
  - apply linked_outside; [exact Hlinked | reflexivity].
  - apply linked_unbound; [exact Hlinked | reflexivity].
  - reflexivity.
  - exact Herrno.
  - reflexivity.
  - split; [right; eexists; reflexivity | reflexivity].
  - iIntros (σ) "Hσ _". iDestruct "Hσ" as (h) "[_ %Hσ]".
    iPureIntro. split; [reflexivity|]. apply Hrep with h. exact (proj2 (proj2 (proj2 Hσ))).
  - done.
  - iNext. iIntros (σ tr vs s' m' w' Hi) "Hσ _".
    destruct (M.E.errno_location_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi)
      as (_ & _ & _ & _ & _ & -> & -> & -> & He).
    injection He as ->.
    iDestruct "Hσ" as (h) "[Hh %Hσ]".
    pose proof (Hcell _ _ _ (proj2 (proj2 (proj2 Hσ)))) as Ec.
    iModIntro. iExists _. iSplit.
    + iPureIntro. cbn [external_env external_outcome contract_returns site_result returned_env].
      rewrite Ec. reflexivity.
    + iSplitL "Hh"; [iExists h; iFrame; done|]. iExact "HK".
Qed.

(** A four-byte load from owned memory. Local rule for promotion to
    MemLogic.v; it needs neither a world fact nor eight-byte ownership. *)
Lemma wp_close_load_w f e ls lab d v rest j b reg o xs Φ :
  value_x ge e A v = Some (WPtr (mkPtr (b + o) (Obj b))) ->
  0 <= b + o < 2 ^ 64 -> length xs = 4%nat ->
  live b reg -∗ bytes b o xs -∗
  ▷ (live b reg -∗ bytes b o xs -∗
    WP (ERun (mkFrame f (put d (WInt (close_w xs)) e) ls None (Exec lab rest j)) : cexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab
    (Let d W (RawLoad (LdNarrow Sw) 0) [v] :: rest) j)) : cexpr) {{ Φ }}.
Proof.
  intros Hv Ha Hlen. iIntros "Hl Hx HK".
  iApply (wp_read _ _ _ ((PLive b, VLive reg) :: byte_ps b o xs) _ _ [] with "[Hl Hx] [HK]").
  - intros m fuel (Hag & _). destruct Hag as [Hl Hx].
    cbn [agree_piece fst snd] in Hl.
    destruct xs as [|a [|c [|dd [|z [|u xs]]]]]; try discriminate Hlen.
    pose proof (byte_ps_agree _ _ _ _ _ 0%nat a Hl Hx eq_refl) as (E0 & H0 & _).
    pose proof (byte_ps_agree _ _ _ _ _ 1%nat c Hl Hx eq_refl) as (E1 & _).
    pose proof (byte_ps_agree _ _ _ _ _ 2%nat dd Hl Hx eq_refl) as (E2 & _).
    pose proof (byte_ps_agree _ _ _ _ _ 3%nat z Hl Hx eq_refl) as (E3 & _ & H3).
    apply rule_let with (classes := [A]) (xs := [WPtr (mkPtr (b + o) (Obj b))])
      (w := WInt (close_w [a; c; dd; z]));
      [reflexivity | reflexivity | cbn [map2_option]; rewrite Hv; reflexivity |].
    assert (Er : raw_address (b + o) 0 = b + o) by (unfold raw_address; rewrite Z.add_0_r; apply Z.mod_small; exact Ha).
    assert (Ea : access_res m (b + o) (Obj b) 4 Read 1 = Some ok).
    { apply (access_obj _ _ reg); [exact (proj1 Hl)|lia|cbn in H3; lia|apply Z.mod_1_r]. }
    cbn - [access_res raw_address load_bytes extension]. rewrite Er.
    unfold int_load_res. cbn - [access_res load_bytes extension]. rewrite Ea.
    change (Some (OpRes (RVal (WInt (extension Sw (load_bytes m (b + o) 4) mod 2 ^ 32))) m) =
      Some (OpRes (RVal (WInt (close_w [a; c; dd; z]))) m)).
    change (Some (OpRes (RVal (WInt (extension Sw
      (((m_bytes m (b + o + 3) * 256 + m_bytes m (b + o + 2)) * 256 +
        m_bytes m (b + o + 1)) * 256 + m_bytes m (b + o + 0)) mod 2 ^ 32))) m) =
      Some (OpRes (RVal (WInt (close_w [a; c; dd; z]))) m)).
    replace (b + o + 0) with (b + (o + 0)) by lia.
    replace (b + o + 1) with (b + (o + 1)) by lia.
    replace (b + o + 2) with (b + (o + 2)) by lia.
    replace (b + o + 3) with (b + (o + 3)) by lia.
    cbn [Z.of_nat] in E0, E1, E2, E3. rewrite E0 E1 E2 E3. reflexivity.
  - rewrite /live /bytes /pts big_sepL_cons big_sepL_nil. iDestruct "Hl" as "[$ _]". iExact "Hx".
  - iNext. iIntros "H". iDestruct (pts_app [(PLive b, VLive reg)] (byte_ps b o xs) with "H") as "[Hl Hx]".
    iApply ("HK" with "Hl Hx").
Qed.

(** An invocation frame, promoted locally to an Iris call rule. The
    pure endpoint premise describes the whole authoritative heap after
    the call, including updates to pieces the caller handed over.
    Local bridge for promotion to Logic.v. *)
Lemma wp_close_contract f e ls lab d k g args rest j spec xs ps
    (after : list Z -> list (piece * pval)) (good : Z -> list Z -> Prop) Φ :
  find_fn ge g = None -> lookup g (ge_globals ge) = None -> is_free_name g = false ->
  registry g = Some spec -> contract_returns spec = RClass k ->
  (k = W \/ k = L) -> map_option (arg_x ge e) args = Some xs ->
  contract_abi spec (CResult d k) args ->
  (forall m w h, wi m w h -> (forall l v, (l,v) ∈ ps -> h !! l = Some v) ->
    contract_pre spec xs m w) ->
  (forall s m w h tr vs s' m' w', agrees m h -> live_disjoint m -> R.ready s m -> wi m w h ->
    (forall l v, (l,v) ∈ ps -> h !! l = Some v) ->
    M.E.invoke spec (CResult d k) args xs s m w tr (CallReturn vs) s' m' w' ->
    exists n ys, vs = [WInt n] /\ 0 <= n < 2 ^ (if class_eqb k W then 32 else 64) /\
      good n ys /\ (after ys).*1 = ps.*1 /\
      agrees m' (overwrite (after ys) h) /\ live_disjoint m' /\ R.ready s' m' /\
      wi m' w' (overwrite (after ys) h)) ->
  pts ps -∗ ▷ (∀ n ys, ⌜good n ys⌝ -∗ pts (after ys) -∗
    WP (ERun (mkFrame f (put d (WInt n) e) ls None (Exec lab rest j)) : cexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab
    (Call (CResult d k) (Global g) args :: rest) j)) : cexpr) {{ Φ }}.
Proof.
  intros Hfn Hg Hfree Hreg Hret Hk Hargs Habi Hpre Hpost. iIntros "Hps HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ spec xs (pts ps) with "Hps [HK]");
    [exact Hfn|exact Hg|exact Hfree|exact Hreg|exact Hargs|exact Habi| |].
  - iIntros (σ) "Hσ Hps". iDestruct "Hσ" as (h) "[Hh %Hσ]".
    iDestruct (pts_lookup with "Hh Hps") as %Hl. iPureIntro.
    apply (Hpre _ _ h (proj2 (proj2 (proj2 Hσ))) Hl).
  - iNext. iIntros (σ tr vs s' m' w' Hi) "Hσ Hps".
    iDestruct "Hσ" as (h) "[Hh %Hσ]". destruct Hσ as (Ha & Hd & Hr & Hw).
    iDestruct (pts_lookup with "Hh Hps") as %Hl.
    destruct (Hpost _ _ _ _ _ _ _ _ _ Ha Hd Hr Hw Hl Hi)
      as (n & ys & -> & Hn & Hgood & Hkeys & Ha' & Hd' & Hr' & Hw').
    iMod (pts_update with "Hh Hps") as "[Hh Hps]"; [exact Hkeys|].
    iModIntro. iExists _. iSplit.
    + iPureIntro. unfold external_env. rewrite Hret.
      destruct Hk as [-> | ->]; cbn [external_outcome returned_env site_result word_at_class modulus];
        rewrite Z.mod_small; [reflexivity|exact Hn|reflexivity|exact Hn].
    + iSplitL "Hh"; [iExists (overwrite (after ys) h); iFrame; iPureIntro; auto|].
      iApply ("HK" $! n ys with "[%] Hps"). exact Hgood.
Qed.

(** Stream admission and consumption are represented by ghost pieces;
    fclose replaces their values with closed-state pieces of the same
    keys, rather than restoring usability of the stream. *)
Context (stream_ps closed_ps : ptr -> list (piece * pval)).
(** Ownership of a usable stream's represented pieces. *)
Let stream p : iProp Σ := pts (stream_ps p).

(** Query specs, including their exact ABI and pure frame obligations.
    The query preserves the original owned pieces and libc world. *)
Context (query_spec : name -> contract world)
  (Hquery_reg : forall g k, (g = TAtom "__fpending" /\ k = L) \/ (g = TAtom "ferror" /\ k = W) ->
    registry g = Some (query_spec g))
  (Hquery_ret : forall g k, (g = TAtom "__fpending" /\ k = L) \/ (g = TAtom "ferror" /\ k = W) ->
    contract_returns (query_spec g) = RClass k)
  (Hquery_abi : forall g k d v, (g = TAtom "__fpending" /\ k = L) \/ (g = TAtom "ferror" /\ k = W) ->
    contract_abi (query_spec g) (CResult d k) [Arg P v])
  (Hquery_pre : forall g k p xs m w h,
    (g = TAtom "__fpending" /\ k = L) \/ (g = TAtom "ferror" /\ k = W) ->
    wi m w h -> (forall l v, (l,v) ∈ stream_ps p ++ byte_ps eb eo xs -> h !! l = Some v) ->
    length xs = 4%nat -> contract_pre (query_spec g) [WPtr p] m w)
  (Hquery_post : forall g k d v p xs s m w h tr vs s' m' w',
    (g = TAtom "__fpending" /\ k = L) \/ (g = TAtom "ferror" /\ k = W) ->
    agrees m h -> live_disjoint m -> R.ready s m -> wi m w h ->
    (forall l v, (l,v) ∈ stream_ps p ++ byte_ps eb eo xs -> h !! l = Some v) ->
    M.E.invoke (query_spec g) (CResult d k) [Arg P v] [WPtr p] s m w tr (CallReturn vs) s' m' w' ->
    exists n, vs = [WInt n] /\ 0 <= n < 2 ^ (if class_eqb k W then 32 else 64) /\
      agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ wi m' w' h).

(** fclose's spec consumes usable stream pieces, returning closed pieces
    and arbitrary four-byte errno contents. Its frame premise includes
    readiness, separation and libc's world, not just the returned value. *)
Context (fclose_spec : contract world)
  (Hfclose_reg : registry (TAtom "fclose") = Some fclose_spec)
  (Hfclose_ret : contract_returns fclose_spec = RClass W)
  (Hfclose_abi : forall d v, contract_abi fclose_spec (CResult d W) [Arg P v])
  (Hfclose_pre : forall p xs m w h, wi m w h ->
    (forall l v, (l,v) ∈ stream_ps p ++ byte_ps eb eo xs -> h !! l = Some v) ->
    length xs = 4%nat -> contract_pre fclose_spec [WPtr p] m w)
  (Hfclose_post : forall d v p xs s m w h tr vs s' m' w',
    agrees m h -> live_disjoint m -> R.ready s m -> wi m w h ->
    (forall l v, (l,v) ∈ stream_ps p ++ byte_ps eb eo xs -> h !! l = Some v) ->
    M.E.invoke fclose_spec (CResult d W) [Arg P v] [WPtr p] s m w tr (CallReturn vs) s' m' w' ->
    exists n ys, vs = [WInt n] /\ 0 <= n < 2 ^ 32 /\ length ys = 4%nat /\
      (closed_ps p ++ byte_ps eb eo ys).*1 = (stream_ps p ++ byte_ps eb eo xs).*1 /\
      agrees m' (overwrite (closed_ps p ++ byte_ps eb eo ys) h) /\ live_disjoint m' /\ R.ready s' m' /\
      wi m' w' (overwrite (closed_ps p ++ byte_ps eb eo ys) h)).

(** Derive the two query call-site triples from their raw contracts. *)
Lemma Hquery g k : (g = TAtom "__fpending" /\ k = L) \/ (g = TAtom "ferror" /\ k = W) ->
    forall f e ls lab d v rest j p xs Φ,
    arg_x ge e (Arg P v) = Some (WPtr p) -> length xs = 4%nat ->
    stream p -∗ bytes eb eo xs -∗
    ▷ (∀ n, ⌜0 <= n < 2 ^ (if class_eqb k W then 32 else 64)⌝ -∗ stream p -∗ bytes eb eo xs -∗
      WP (ERun (mkFrame f (put d (WInt n) e) ls None (Exec lab rest j)) : cexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame f e ls None (Exec lab
      (Call (CResult d k) (Global g) [Arg P v] :: rest) j)) : cexpr) {{ Φ }}.
Proof.
  intros Hwhich f e ls lab d v rest j p xs Φ Hv Hlen. iIntros "Hs Hx HK".
  iApply (wp_close_contract _ _ _ _ _ k g _ _ _ (query_spec g) [WPtr p]
    (stream_ps p ++ byte_ps eb eo xs) (fun _ => stream_ps p ++ byte_ps eb eo xs)
    (fun n _ => 0 <= n < 2 ^ (if class_eqb k W then 32 else 64)) with "[Hs Hx] [HK]").
  - destruct Hwhich as [[-> ->]|[-> ->]]; apply linked_outside; [exact Hlinked|reflexivity|exact Hlinked|reflexivity].
  - destruct Hwhich as [[-> ->]|[-> ->]]; apply linked_unbound; [exact Hlinked|reflexivity|exact Hlinked|reflexivity].
  - destruct Hwhich as [[-> ->]|[-> ->]]; reflexivity.
  - apply Hquery_reg with k. exact Hwhich.
  - apply Hquery_ret. exact Hwhich.
  - destruct Hwhich as [[_ ->]|[_ ->]]; auto.
  - cbn [map_option]. rewrite Hv. reflexivity.
  - apply Hquery_abi. exact Hwhich.
  - intros m w h Hw Hl. exact (Hquery_pre _ _ _ _ _ _ _ Hwhich Hw Hl Hlen).
  - intros s m w h tr vs s' m' w' Ha Hd Hr Hw Hl Hi.
    destruct (Hquery_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hwhich Ha Hd Hr Hw Hl Hi)
      as (n & Hvs & Hn & Ha' & Hd' & Hr' & Hw').
    exists n, xs. rewrite (overwrite_id _ h Hl). repeat split; try assumption; try reflexivity; tauto.
  - rewrite pts_app. iFrame.
  - iNext. iIntros (n ys Hn) "H". rewrite pts_app. iDestruct "H" as "[Hs Hx]".
    iApply ("HK" $! n with "[%] Hs Hx"). exact Hn.
Qed.

(** Derive the consuming close call-site triple from its raw contract. *)
Lemma Hfclose : forall f e ls lab d v rest j p xs Φ,
    arg_x ge e (Arg P v) = Some (WPtr p) -> length xs = 4%nat ->
    stream p -∗ bytes eb eo xs -∗
    ▷ (∀ n ys, ⌜0 <= n < 2 ^ 32 /\ length ys = 4%nat⌝ -∗ bytes eb eo ys -∗
      WP (ERun (mkFrame f (put d (WInt n) e) ls None (Exec lab rest j)) : cexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame f e ls None (Exec lab
      (Call (CResult d W) (Global (TAtom "fclose")) [Arg P v] :: rest) j)) : cexpr) {{ Φ }}.
Proof.
  intros f e ls lab d v rest j p xs Φ Hv Hlen. iIntros "Hs Hx HK".
  iApply (wp_close_contract _ _ _ _ _ W (TAtom "fclose") _ _ _ fclose_spec [WPtr p]
    (stream_ps p ++ byte_ps eb eo xs) (fun ys => closed_ps p ++ byte_ps eb eo ys)
    (fun n ys => 0 <= n < 2 ^ 32 /\ length ys = 4%nat) with "[Hs Hx] [HK]").
  - apply linked_outside; [exact Hlinked|reflexivity].
  - apply linked_unbound; [exact Hlinked|reflexivity].
  - reflexivity.
  - exact Hfclose_reg.
  - exact Hfclose_ret.
  - auto.
  - cbn [map_option]. rewrite Hv. reflexivity.
  - apply Hfclose_abi.
  - intros m w h Hw Hl. exact (Hfclose_pre _ _ _ _ _ Hw Hl Hlen).
  - intros s m w h tr vs s' m' w' Ha Hd Hr Hw Hl Hi.
    destruct (Hfclose_post _ _ _ _ _ _ _ _ _ _ _ _ _ Ha Hd Hr Hw Hl Hi)
      as (n & ys & Hvs & Hn & Hys & Hkeys & Ha' & Hd' & Hr' & Hw').
    exists n, ys. cbn [class_eqb]. repeat split; try assumption; try reflexivity; tauto.
  - rewrite pts_app. iFrame.
  - iNext. iIntros (n ys Hn) "H". rewrite pts_app. iDestruct "H" as "[_ Hx]".
    iApply ("HK" $! n ys with "[%] Hx"). exact Hn.
Qed.

(** Storing zero into owned errno preserves libc's world interpretation. *)
Context (Kerrno : forall xs m w h,
  (forall l v, (l, v) ∈ (PLive eb, VLive er) :: byte_ps eb eo xs -> h !! l = Some v) ->
  wi m w h -> wi (store_bytes m (eb + eo) 4 0) w
    (overwrite ((PLive eb, VLive er) :: byte_ps eb eo (le_bytes 0 4)) h)).

(** The errno cell is inside the represented address space. *)
Context (Heo : 0 <= eo) (Herange : 0 <= eb + eo < 2 ^ 64) (Heend : eb + eo + 4 <= r_end er)
  (He48 : r_end er <= 2 ^ 48).

(** Find a stream-close block without unfolding the module in a proof. *)
Ltac cs_enter s :=
  iApply (wp_enter _ _ _ _ _ _ _ _ (cs_block s));
  [vm_compute; reflexivity | word_premise |]; iNext;
  cbn [b_insts b_jump cs_block hblk].

(** A pure instruction, with the environment kept abstract. *)
Ltac close_let :=
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |];
  iNext; gen_env.

(** After the error decision, close_stream returns zero or EOF, clearing
    errno only when an earlier error accompanies a successful fclose. *)
Lemma close_stream_L22 e n t xs Φ :
  lookup (TAtom "v14") e = Some (WInt n) -> lookup (TAtom "v37") e = Some (WInt t) ->
  0 <= n < 2 ^ 32 -> (t = 0 \/ t = 1) -> length xs = 4%nat ->
  live eb er -∗ bytes eb eo xs -∗
  ▷ (∀ r ys, ⌜(r = 0 \/ r = 4294967295) /\ length ys = 4%nat⌝ -∗
    live eb er -∗ bytes eb eo ys -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame close_stream_fn e [] None
    (Exec (TAtom "L22") [] (b_jump (cs_block "L22")))) : cexpr) {{ Φ }}.
Proof.
  intros Hn Ht Hrange Ht01 Hlen. iIntros "Hl Hx HΦ".
  destruct Ht01 as [-> | ->].
  - iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    cs_enter "L19". iApply wp_ret; [reflexivity|reflexivity|]. iNext.
    iApply ("HΦ" $! 0 xs with "[%] Hl Hx"). auto.
  - iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    cs_enter "L17". destruct (Z.eq_dec n 0) as [->|Hnz].
    + close_let. iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
      cs_enter "L38". iApply wp_close_errno. iNext. gen_env.
      iApply (wp_check with "Hl"); [reflexivity|word_premise|reflexivity|unfold ep; addr_premise|unfold ep; addr_premise|unfold ep; addr_premise|].
      iNext. iIntros "Hl". gen_env.
      iApply (wp_raw_store_w with "Hl Hx");
        [word_premise|word_premise|reflexivity|unfold ep; addr_premise|exact Hlen|apply Kerrno|].
      iNext. iIntros "Hl Hx". iApply wp_goto. iNext. cs_enter "L40".
      iApply wp_ret; [reflexivity|reflexivity|]. iNext.
      iApply ("HΦ" $! 4294967295 (le_bytes 0 4) with "[%] Hl Hx").
      split; [auto|apply length_le_bytes].
    + close_let. iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
      cs_enter "L40". iApply wp_ret; [reflexivity|reflexivity|]. iNext.
      iApply ("HΦ" $! 4294967295 xs with "[%] Hl Hx"). auto.
Qed.

(** Hand the merged error flag to the shared return blocks. *)
Ltac cs_finish n t Hn Hlen :=
  cs_enter "L22"; gen_env;
  iApply (close_stream_L22 _ n t with "Hl Hx HΦ");
  [word_premise | word_premise | exact Hn | auto | exact Hlen].

(** close_stream consumes a usable stream and returns zero or EOF. It
    returns ownership of errno, whose contents may have changed. Sticky
    error, pending data, fclose failure and EBADF take distinct paths. *)
Lemma close_stream_spec p xs Φ :
  length xs = 4%nat ->
  stream p -∗ live eb er -∗ bytes eb eo xs -∗
  ▷ (∀ r ys, ⌜(r = 0 \/ r = 4294967295) /\ length ys = 4%nat⌝ -∗
    live eb er -∗ bytes eb eo ys -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (invocation close_stream_fn [WPtr p]) : cexpr) {{ Φ }}.
Proof.
  intros Hlen. iIntros "Hs Hl Hx HΦ". rewrite close_stream_entry.
  cs_enter "start".
  iApply (Hquery (TAtom "__fpending") L with "Hs Hx");
    [left; auto | word_premise | exact Hlen |].
  iNext. iIntros (pending Hpending) "Hs Hx". cbn [class_eqb] in Hpending. gen_env. close_let.
  iApply (Hquery (TAtom "ferror") W with "Hs Hx");
    [right; auto | word_premise | exact Hlen |].
  iNext. iIntros (err Herr) "Hs Hx". cbn [class_eqb] in Herr. gen_env. close_let.
  iApply (Hfclose with "Hs Hx"); [word_premise | exact Hlen |].
  iNext. iIntros (n ys [Hn Hys]) "Hx". gen_env. close_let.
  destruct (Z.eq_dec err 0) as [Herr0 | Herr0].
  - iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    cs_enter "L21". destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
    + iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
      cs_finish n 0 Hn Hys.
    + iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
      cs_enter "L24". destruct (Z.eq_dec pending 0) as [Hp0 | Hp0].
      * iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
        cs_enter "L27". iApply wp_close_errno. iNext. gen_env.
        iApply (wp_check with "Hl");
          [reflexivity|word_premise|reflexivity|unfold ep; addr_premise|unfold ep; addr_premise|unfold ep; addr_premise|].
        iNext. iIntros "Hl". gen_env.
        iApply (wp_close_load_w with "Hl Hx"); [word_premise|exact Herange|exact Hys|].
        iNext. iIntros "Hl Hx". gen_env.
        pose proof (close_w_range ys) as Hwr.
        destruct (Z.eq_dec (close_w ys) 9) as [Hw9 | Hw9]; close_let;
          iApply wp_goto; iNext.
        -- cs_finish n 0 Hn Hys.
        -- cs_finish n 1 Hn Hys.
      * iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
        cs_finish n 1 Hn Hys.
  - iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    cs_finish n 1 Hn Hys.
Qed.

(** Hello's read-only unnamed-file diagnostic strings. *)
Let fmt := mkPtr 65744 (Ro 65744).
(** The write-error text. *)
Let text := mkPtr 65680 (Ro 65680).

(** The caller hands the diagnostic's represented string pieces to
    error; they return unchanged while errno may change. *)
Context (diag_ps : list (piece * pval)) (error_spec : contract world)
  (Herror_reg : registry (TAtom "error") = Some error_spec)
  (Herror_ret : contract_returns error_spec = RVoid)
  (Herror_abi : forall v fmtv txtv, contract_abi error_spec CVoid
    [Arg W (Const 0); Arg W v; Arg P fmtv; Arg P txtv])
  (Herror_pre : forall n xs m w h, 0 <= n < 2 ^ 32 -> length xs = 4%nat ->
    agrees m h -> wi m w h ->
    (forall l v, (l,v) ∈ diag_ps ++ byte_ps eb eo xs -> h !! l = Some v) ->
    contract_pre error_spec [WInt 0; WInt n; WPtr fmt; WPtr text] m w)
  (Herror_post : forall v fmtv txtv n xs s m w h tr vs s' m' w', length xs = 4%nat ->
    agrees m h -> live_disjoint m -> R.ready s m -> wi m w h ->
    (forall l v, (l,v) ∈ diag_ps ++ byte_ps eb eo xs -> h !! l = Some v) ->
    M.E.invoke error_spec CVoid [Arg W (Const 0); Arg W v; Arg P fmtv; Arg P txtv]
      [WInt 0; WInt n; WPtr fmt; WPtr text] s m w tr (CallReturn vs) s' m' w' ->
    exists ys, vs = [] /\ length ys = 4%nat /\
      (diag_ps ++ byte_ps eb eo ys).*1 = (diag_ps ++ byte_ps eb eo xs).*1 /\
      agrees m' (overwrite (diag_ps ++ byte_ps eb eo ys) h) /\ live_disjoint m' /\ R.ready s' m' /\
      wi m' w' (overwrite (diag_ps ++ byte_ps eb eo ys) h)).

(** error with zero status returns void; it never substitutes an exit
    for the following _exit. Resource terminals need no continuation. *)
Lemma wp_close_error f e ls lab v fmtv txtv rest j n xs Φ :
  arg_x ge e (Arg W v) = Some (WInt n) -> arg_x ge e (Arg P fmtv) = Some (WPtr fmt) ->
  arg_x ge e (Arg P txtv) = Some (WPtr text) -> 0 <= n < 2 ^ 32 -> length xs = 4%nat ->
  pts diag_ps -∗ bytes eb eo xs -∗
  ▷ (∀ ys, ⌜length ys = 4%nat⌝ -∗ pts diag_ps -∗ bytes eb eo ys -∗
    WP (ERun (mkFrame f e ls None (Exec lab rest j)) : cexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab
    (Call CVoid (Global (TAtom "error")) [Arg W (Const 0); Arg W v; Arg P fmtv; Arg P txtv] :: rest) j)) : cexpr) {{ Φ }}.
Proof.
  intros Hv Hfmt Htext Hn Hlen. iIntros "Hd Hx HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ error_spec [WInt 0; WInt n; WPtr fmt; WPtr text]
    (pts (diag_ps ++ byte_ps eb eo xs)) with "[Hd Hx] [HK]").
  - apply linked_outside; [exact Hlinked|reflexivity].
  - apply linked_unbound; [exact Hlinked|reflexivity].
  - reflexivity.
  - exact Herror_reg.
  - cbn [map_option]. rewrite Hv Hfmt Htext. reflexivity.
  - apply Herror_abi.
  - iIntros (σ) "Hσ Hps". iDestruct "Hσ" as (h) "[Hh %Hσ]".
    iDestruct (pts_lookup with "Hh Hps") as %Hl. iPureIntro.
    apply (Herror_pre _ _ _ _ _ Hn Hlen (proj1 Hσ) (proj2 (proj2 (proj2 Hσ))) Hl).
  - rewrite pts_app. iFrame.
  - iNext. iIntros (σ tr vs s' m' w' Hi) "Hσ Hps".
    iDestruct "Hσ" as (h) "[Hh %Hσ]". destruct Hσ as (Ha & Hd & Hr & Hw).
    iDestruct (pts_lookup with "Hh Hps") as %Hl.
    destruct (Herror_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hlen Ha Hd Hr Hw Hl Hi)
      as (ys & -> & Hys & Hkeys & Ha' & Hd' & Hr' & Hw').
    iMod (pts_update with "Hh Hps") as "[Hh Hps]"; [exact Hkeys|].
    iModIntro. iExists e. iSplit.
    + iPureIntro. unfold external_env. rewrite Herror_ret. reflexivity.
    + iSplitL "Hh"; [iExists (overwrite (diag_ps ++ byte_ps eb eo ys) h); iFrame; iPureIntro; auto|].
      rewrite pts_app. iDestruct "Hps" as "[Hd Hx]".
      iApply ("HK" $! ys with "[%] Hd Hx"). exact Hys.
Qed.

(** _exit's raw contract admits a canonical status and has no ordinary
    return endpoint. Its actual process-exit semantics belong to Ending. *)
Context (exit_spec : contract world)
  (Hexit_reg : registry (TAtom "_exit") = Some exit_spec)
  (Hexit_ret : contract_returns exit_spec = RVoid)
  (Hexit_abi : forall v, contract_abi exit_spec CVoid [Arg W v])
  (Hexit_pre : forall n m w h, 0 <= n < 2 ^ 32 -> wi m w h -> contract_pre exit_spec [WInt n] m w)
  (Hexit_post : forall args n s m w tr vs s' m' w',
    M.E.invoke exit_spec CVoid args [WInt n] s m w tr (CallReturn vs) s' m' w' -> False).

(** An admissible _exit call is safe under every postcondition. *)
Lemma wp_close_exit f e ls lab v rest j n Φ :
  arg_x ge e (Arg W v) = Some (WInt n) -> 0 <= n < 2 ^ 32 ->
  ⊢ WP (ERun (mkFrame f e ls None (Exec lab
    (Call CVoid (Global (TAtom "_exit")) [Arg W v] :: rest) j)) : cexpr) {{ Φ }}.
Proof.
  intros Hv Hn.
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ exit_spec [WInt n] True%I with "[] []").
  - apply linked_outside; [exact Hlinked|reflexivity].
  - apply linked_unbound; [exact Hlinked|reflexivity].
  - reflexivity.
  - exact Hexit_reg.
  - cbn [map_option]. rewrite Hv. reflexivity.
  - apply Hexit_abi.
  - iIntros (σ) "Hσ _". iDestruct "Hσ" as (h) "[_ %Hσ]". iPureIntro.
    exact (Hexit_pre _ _ _ _ Hn (proj2 (proj2 (proj2 Hσ)))).
  - done.
  - iNext. iIntros (σ tr vs s' m' w' Hi) "_ _". exfalso. exact (Hexit_post _ _ _ _ _ _ _ _ _ _ Hi).
Qed.

(** Load a stream pointer while borrowing its life from the stream's
    represented pieces, without duplicating that linear life token. *)
Lemma wp_close_stream_pointer f e ls lab d v rest j b reg p Φ :
  (exists pb pr ps, ptr_cap p = Obj pb /\ stream_ps p = (PLive pb, VLive pr) :: ps) ->
  value_x ge e A v = Some (WPtr (mkPtr b (Obj b))) -> 0 <= b < 2 ^ 64 -> b mod 8 = 0 ->
  0 <= ptr_addr p < 2 ^ 64 ->
  live b reg -∗ pcell b 0 p -∗ stream p -∗
  ▷ (live b reg -∗ pcell b 0 p -∗ stream p -∗
    WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec lab rest j)) : cexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab
    (Let d P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [v] :: rest) j)) : cexpr) {{ Φ }}.
Proof.
  intros (pb & pr & ps & Hcap & Hps) Hv Hb Hb8 Hp. iIntros "Hl Hc Hs HK".
  iAssert (live pb pr ∗ pts ps)%I with "[Hs]" as "[Hpl Hrest]".
  { rewrite /stream Hps /live /pts big_sepL_cons big_sepL_singleton. iExact "Hs". }
  iApply (wp_raw_load_pointer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pr with "Hl Hc [Hpl] [HK Hrest]").
  - reflexivity.
  - cbn [map2_option]. rewrite Hv. reflexivity.
  - reflexivity.
  - unfold raw_address. cbn [ptr_addr]. rewrite Z.add_0_r Z.mod_small; [lia|exact Hb].
  - rewrite Z.add_0_r. exact Hb8.
  - exact Hp.
  - rewrite /live_cap Hcap. iExact "Hpl".
  - iNext. iIntros "Hl Hc Hpl". rewrite /live_cap Hcap.
    iApply ("HK" with "Hl Hc [Hpl Hrest]").
    rewrite /stream Hps /live /pts !big_sepL_cons big_sepL_nil. iFrame.
    iDestruct "Hpl" as "[$ _]".
Qed.

(** The null file-name pointer is eight owned zero bytes and a null aux
    slot. This is a module invariant, not a fact about libc's world. *)
Lemma close_file_name :
  bytes 65584 0 (replicate 8 0) ∗ auxes 65584 0 [CNone] ⊣⊢ pcell 65584 0 (mkPtr 0 CNone).
Proof.
  change (pts (Heap.cell 65584 0 0) ∗ pts [(PAux 65584 0, VAux CNone)] ⊣⊢
    pts ([(PAux 65584 0, VAux CNone)] ++ Heap.cell 65584 0 0)).
  rewrite pts_app. apply bi.sep_comm.
Qed.

(** The concrete module cells; libc supplies only stdout and stderr's
    pointer-cell locations. All these pieces are handed back on return. *)
Context (ob sb : Z) (oreg sreg freg ireg xreg : region) (outp errp : ptr)
  (Hout_live : exists b reg ps, ptr_cap outp = Obj b /\ stream_ps outp = (PLive b, VLive reg) :: ps)
  (Herr_live : exists b reg ps, ptr_cap errp = Obj b /\ stream_ps errp = (PLive b, VLive reg) :: ps)
  (Hstdout : lookup (TAtom "stdout") (ge_globals ge) = Some (mkPtr ob (Obj ob)))
  (Hstderr : lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr sb (Obj sb)))
  (Hob : 0 <= ob < 2 ^ 64) (Hob8 : ob mod 8 = 0) (Hoend : ob + 8 <= r_end oreg)
  (Hsb : 0 <= sb < 2 ^ 64) (Hsb8 : sb mod 8 = 0) (Hsend : sb + 8 <= r_end sreg)
  (Hout : 0 <= ptr_addr outp < 2 ^ 64) (Herrp : 0 <= ptr_addr errp < 2 ^ 64)
  (Hfend : 65584 + 8 <= r_end freg) (Hiend : 65616 + 1 <= r_end ireg)
  (Hxend : 65776 + 4 <= r_end xreg).

(** Closeout's owned module memory and the imported pointer cells. *)
Definition close_cells (fs : list Z) : iProp Σ :=
  live ob oreg ∗ pcell ob 0 outp ∗ live sb sreg ∗ pcell sb 0 errp ∗
  live 65584 freg ∗ bytes 65584 0 (replicate 8 0) ∗ auxes 65584 0 [CNone] ∗
  live 65616 ireg ∗ ibyte 65616 0 0 ∗ live 65776 xreg ∗ bytes 65776 0 fs.

(** The module's symbols put closeout's statics and literals there. *)
Lemma close_lookups :
  lookup (TAtom "closeout#file_name") (ge_globals ge) = Some (mkPtr 65584 (Obj 65584)) /\
  lookup (TAtom "closeout#ignore_EPIPE") (ge_globals ge) = Some (mkPtr 65616 (Obj 65616)) /\
  lookup (TAtom "exit_failure") (ge_globals ge) = Some (mkPtr 65776 (Obj 65776)) /\
  lookup (TAtom "closeout#str.55") (ge_globals ge) = Some fmt /\
  lookup (TAtom "closeout#str.53") (ge_globals ge) = Some text /\
  exists p, lookup (TAtom "closeout#str.52") (ge_globals ge) = Some p.
Proof.
  destruct Hlinked as (_ & Hg & _). repeat split; try (apply Hg; vm_compute; reflexivity).
  exists (mkPtr 65648 (Ro 65648)). apply Hg. vm_compute. reflexivity.
Qed.

(** Enter one of close_stdout's blocks. *)
Ltac co_enter s :=
  iApply (wp_enter _ _ _ _ _ _ _ _ (co_block s));
  [vm_compute; reflexivity | word_premise |]; iNext;
  cbn [b_insts b_jump co_block hblk].

(** The linked module dispatches close_stream to its proved body. *)
Lemma close_stream_linked : find_fn ge (TAtom "close_stream") = Some (Defined close_stream_fn).
Proof. unfold find_fn. rewrite (proj1 Hlinked). vm_compute. reflexivity. Qed.

(** A null file name takes the unnamed-file diagnostic, then _exit.
    quotearg_colon is not called and needs no premise triple. *)
Lemma close_stdout_error e xs fs Φ :
  length xs = 4%nat -> length fs = 4%nat ->
  live 65584 freg -∗ bytes 65584 0 (replicate 8 0) -∗ auxes 65584 0 [CNone] -∗
  live 65776 xreg -∗ bytes 65776 0 fs -∗ live eb er -∗ bytes eb eo xs -∗ pts diag_ps -∗
  WP (ERun (mkFrame close_stdout_fn e [] None (Enter (TAtom "L0") (Some (TAtom "L8")))) : cexpr) {{ Φ }}.
Proof.
  intros Hxs Hfs. iIntros "Hfl Hfb Hfa Hxl Hxb Hl Hx Hd".
  destruct close_lookups as (Hfile & Hignore & Hfailure & Hfmt & Htext & p & Hdomain).
  iAssert (pcell 65584 0 (mkPtr 0 CNone)) with "[Hfb Hfa]" as "Hfc".
  { iApply close_file_name. iFrame. }
  co_enter "L0". close_let. close_let. close_let.
  iApply (wp_check with "Hfl").
  - reflexivity.
  - word_premise.
  - reflexivity.
  - change (65584 <= 65584). lia.
  - change (65584 + 8 <= r_end freg). exact Hfend.
  - reflexivity.
  -
  iNext. iIntros "Hfl". gen_env.
  iApply (wp_raw_load_pointer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ freg with "Hfl Hfc []");
    [reflexivity|word_premise|reflexivity|addr_premise|reflexivity|cbn; lia|done|].
  iNext. iIntros "Hfl Hfc _". gen_env. close_let. close_let.
  iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
  co_enter "L61". iApply wp_close_errno. iNext. gen_env.
  iApply (wp_check with "Hl");
    [reflexivity|word_premise|reflexivity|unfold ep; addr_premise|unfold ep; addr_premise|unfold ep; addr_premise|].
  iNext. iIntros "Hl". gen_env.
  iApply (wp_close_load_w with "Hl Hx"); [word_premise|exact Herange|exact Hxs|].
  iNext. iIntros "Hl Hx". gen_env. close_let.
  pose proof (close_w_range xs) as Hwr.
  iApply (wp_close_error with "Hd Hx");
    [word_premise|unfold fmt; word_premise|unfold text; word_premise|apply close_w_range|exact Hxs|].
  iNext. iIntros (ys Hys) "Hd Hx". iApply wp_goto. iNext. co_enter "L26". close_let.
  iApply (wp_check with "Hxl");
    [reflexivity|word_premise|reflexivity|addr_premise|addr_premise|addr_premise|].
  iNext. iIntros "Hxl". gen_env.
  iApply (wp_close_load_w with "Hxl Hxb"); [word_premise|cbn; lia|exact Hfs|].
  iNext. iIntros "Hxl Hxb". gen_env. pose proof (close_w_range fs) as Hfr.
  iApply wp_close_exit; [word_premise|apply close_w_range].
Qed.

(** Close stderr after stdout was settled. Its failure exits directly;
    a successful return preserves all module cells and errno ownership. *)
Lemma close_stdout_L91 e xs fs Φ :
  length xs = 4%nat -> length fs = 4%nat ->
  stream errp -∗ close_cells fs -∗ live eb er -∗ bytes eb eo xs -∗ pts diag_ps -∗
  ▷ (∀ ys, ⌜length ys = 4%nat⌝ -∗ close_cells fs -∗ live eb er -∗ bytes eb eo ys -∗
    pts diag_ps -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame close_stdout_fn e [] None (Enter (TAtom "L91") (Some (TAtom "L8")))) : cexpr) {{ Φ }}.
Proof.
  intros Hxs Hfs. iIntros "Hs Hcells Hl Hx Hd HΦ".
  iDestruct "Hcells" as "(Hol & Hoc & Hsl & Hsc & Hfl & Hfb & Hfa & Hil & Hib & Hxl & Hxb)".
  destruct close_lookups as (_ & _ & Hfailure & _).
  co_enter "L91". close_let.
  assert (Esb : raw_address sb 0 = sb) by (unfold raw_address; rewrite Z.add_0_r; apply Z.mod_small; exact Hsb).
  iApply (wp_check with "Hsl");
    [reflexivity|word_premise|reflexivity|
     change (sb <= raw_address sb 0); rewrite Esb; lia|
     change (raw_address sb 0 + 8 <= r_end sreg); rewrite Esb; exact Hsend|
     change (raw_address sb 0 mod 8 = 0); rewrite Esb; exact Hsb8|].
  iNext. iIntros "Hsl". gen_env.
  iApply (wp_close_stream_pointer with "Hsl Hsc Hs");
    [exact Herr_live|word_premise|exact Hsb|exact Hsb8|exact Herrp|].
  iNext. iIntros "Hsl Hsc Hs". gen_env.
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ close_stream_fn (invocation close_stream_fn [WPtr errp]));
    [word_premise|exact close_stream_linked|reflexivity|].
  iNext. iApply (close_stream_spec with "Hs Hl Hx"); [exact Hxs|].
  iNext. iIntros (r ys [Hr Hys]) "Hl Hx".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. gen_env. close_let.
  destruct Hr as [-> | ->].
  - iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    co_enter "L89". iApply wp_ret_void. iNext.
    iApply ("HΦ" $! ys with "[%] [Hol Hoc Hsl Hsc Hfl Hfb Hfa Hil Hib Hxl Hxb] Hl Hx Hd");
      [exact Hys|rewrite /close_cells; iFrame].
  - iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    co_enter "L87". close_let.
    iApply (wp_check with "Hxl");
      [reflexivity|word_premise|reflexivity|addr_premise|addr_premise|addr_premise|].
    iNext. iIntros "Hxl". gen_env.
    iApply (wp_close_load_w with "Hxl Hxb"); [word_premise|cbn; lia|exact Hfs|].
    iNext. iIntros "Hxl Hxb". gen_env. pose proof (close_w_range fs) as Hfr.
    iApply wp_close_exit; [word_premise|apply close_w_range].
Qed.

(** The exit callback closes stdout then stderr. It returns all module
    statics and pointer cells on normal return; errors either report the
    unnamed write failure and exit or, for stderr, exit directly. *)
Lemma close_stdout_spec xs fs Φ :
  length xs = 4%nat -> length fs = 4%nat ->
  stream outp -∗ stream errp -∗ close_cells fs -∗ live eb er -∗ bytes eb eo xs -∗ pts diag_ps -∗
  ▷ (∀ ys, ⌜length ys = 4%nat⌝ -∗ close_cells fs -∗ live eb er -∗ bytes eb eo ys -∗
    pts diag_ps -∗ Φ RetVoid) -∗
  WP (ERun (invocation close_stdout_fn []) : cexpr) {{ Φ }}.
Proof.
  intros Hxs Hfs. iIntros "Hout Herr Hcells Hl Hx Hd HΦ".
  iDestruct "Hcells" as "(Hol & Hoc & Hsl & Hsc & Hfl & Hfb & Hfa & Hil & Hib & Hxl & Hxb)".
  destruct close_lookups as (_ & Hignore & _).
  change (invocation close_stdout_fn []) with
    (mkFrame close_stdout_fn [] [] None (Enter (TAtom "start") None)).
  co_enter "start". close_let.
  assert (Eob : raw_address ob 0 = ob) by (unfold raw_address; rewrite Z.add_0_r; apply Z.mod_small; exact Hob).
  iApply (wp_check with "Hol");
    [reflexivity|word_premise|reflexivity|
     change (ob <= raw_address ob 0); rewrite Eob; lia|
     change (raw_address ob 0 + 8 <= r_end oreg); rewrite Eob; exact Hoend|
     change (raw_address ob 0 mod 8 = 0); rewrite Eob; exact Hob8|].
  iNext. iIntros "Hol". gen_env.
  iApply (wp_close_stream_pointer with "Hol Hoc Hout");
    [exact Hout_live|word_premise|exact Hob|exact Hob8|exact Hout|].
  iNext. iIntros "Hol Hoc Hout". gen_env.
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ close_stream_fn (invocation close_stream_fn [WPtr outp]));
    [word_premise|exact close_stream_linked|reflexivity|].
  iNext. iApply (close_stream_spec with "Hout Hl Hx"); [exact Hxs|].
  iNext. iIntros (r ys [Hr Hys]) "Hl Hx".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. gen_env. close_let.
  destruct Hr as [-> | ->].
  - iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    co_enter "L8".
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply (close_stdout_L91 with "Herr [Hol Hoc Hsl Hsc Hfl Hfb Hfa Hil Hib Hxl Hxb] Hl Hx Hd HΦ");
      [exact Hys|exact Hfs|rewrite /close_cells; iFrame].
  - iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    co_enter "L7". close_let.
    iApply (wp_check with "Hil");
      [reflexivity|word_premise|reflexivity|addr_premise|addr_premise|addr_premise|].
    iNext. iIntros "Hil". gen_env.
    iApply (wp_raw_load_byte with "Hil Hib");
      [reflexivity|word_premise|reflexivity|reflexivity|left; reflexivity|addr_premise|].
    iNext. iIntros "Hil Hib". gen_env.
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    co_enter "L12". close_let. iApply wp_goto. iNext. co_enter "L8".
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply (close_stdout_error with "Hfl Hfb Hfa Hxl Hxb Hl Hx Hd"); [exact Hys|exact Hfs].
Qed.

End close.
End HelloCloseOn.

(** [HelloCloseOn] over a Logic instance of its own. *)
Module HelloClose (R : Runtime).
Module LG0 := Logic R.
Include HelloCloseOn R LG0.
End HelloClose.
