(** Pizlonation expands each unchecked memory access into a capability
    check and its consumer. This file tracks those instructions through
    decoding and validation. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Maps Syntax Values Memory Ops Semantics Cfg Validate Transport.
From Backend Require Import Text Pizlonate PizlonatePollProof PizlonateEvidenceProof.
From Backend Require NfbTransport.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Unset Lia Cache.

(** ## Names reserved by the input *)

(** The fresh-name generator reads the source terms before the validator
    sees their typed definitions. The decoders connect the two lists at
    parameters, phi nodes, and instruction results. *)

(** Each decoded list element has a source term at the corresponding step of
    the decoder. *)
Local Lemma decoded_member {X Y} (d : X -> option Y) : forall xs ys y,
  map_option d xs = Some ys -> In y ys -> exists x, In x xs /\ d x = Some y.
Proof.
  induction xs as [|x xs IH]; intros ys y H I.
  - injection H as <-. contradiction.
  - cbn [map_option] in H. destruct (d x) as [a|] eqn:D; [|discriminate].
    destruct (map_option d xs) as [rest|] eqn:R; [|discriminate].
    injection H as <-. destruct I as [<-|I]; [exists x; auto using in_eq|].
    destruct (IH _ _ eq_refl I) as (z & Hz & E). exists z; auto using in_cons.
Qed.

(** A successful block decode supplies a decoder equation for each of its
    three fields after the label. *)
Local Lemma block_shape : forall b ub, dublock b = Some ub ->
  exists l ps ins j ph us dj,
    b = TApp "block" [l; TList ps; TList ins; j] /\
    map_option dphi ps = Some ph /\ map_option duinst ins = Some us /\
    djump j = Some dj /\ ub = mkUBlock l ph us dj.
Proof.
  intros b ub H. unfold dublock in H.
  repeat match type of H with
  | (match ?v with _ => _ end) = Some _ =>
    first [is_var v; destruct v; cbn iota in H; try discriminate H |
           destruct v eqn:?; cbn iota in H; try discriminate H]
  end. injection H as <-. do 7 eexists. repeat split; eauto.
Qed.

(** Every name with the generated prefix that the input defines occurs
    in the list that the fresh-name generator consults. *)
Lemma defined_chks_covers : forall n lk r ps bs uf a k,
  dufunc n lk r ps (TList bs) = Some uf ->
  In (TAtom a, k) (utemp_defs uf) -> String.prefix "chk" a = true ->
  In a (Pizlonate.defined_chks ps bs).
Proof.
  intros n lk r ps bs uf a k H I Prefix.
  destruct ps as [| | |params]; unfold dufunc in H;
    destruct (dret r) as [ret|] eqn:R; try discriminate.
  cbn [dlist] in H.
  destruct (map_option dparam params) as [ds|] eqn:D; [|discriminate].
  destruct (map_option dublock bs) as [ubs|] eqn:B; [|discriminate].
  injection H as <-. unfold utemp_defs in I. cbn [ufn_params ufn_blocks] in I.
  unfold Pizlonate.defined_chks. apply in_app_iff in I. apply in_or_app.
  destruct I as [I|I].
  - left. apply in_map_iff in I as ([cl d] & E & I). injection E as -> ->.
    destruct (decoded_member _ _ _ _ D I) as (p & Hp & Ep).
    apply in_flat_map. exists p. split; [exact Hp|].
    rewrite <- (NfbTransport.dparam_enc _ _ Ep). simpl. rewrite Prefix. now left.
  - right. apply in_flat_map in I as (ub & Hu & I).
    destruct (decoded_member _ _ _ _ B Hu) as (b & Hb & Eb).
    destruct (block_shape _ _ Eb) as (l & ps & ins & j & ph & us & dj & -> & Ph & Us & J & ->).
    apply in_flat_map. eexists. split; [exact Hb|]. cbn [String.eqb Ascii.eqb Bool.eqb andb].
    apply in_app_iff in I. apply in_or_app. destruct I as [I|I].
    + left. apply in_map_iff in I as ([d cl pairs] & E & I). injection E as -> ->.
      destruct (decoded_member _ _ _ _ Ph I) as (p & Hp & Ep).
      apply in_flat_map. exists p. split; [exact Hp|].
      rewrite <- (NfbTransport.dphi_enc _ _ Ep). simpl. rewrite Prefix. now left.
    + right. apply in_flat_map in I as (ui & Hui & I).
      destruct (decoded_member _ _ _ _ Us Hui) as (t & Ht & Et).
      apply in_flat_map. exists t. split; [exact Ht|]. eapply duinst_defined_chks; eauto.
Qed.

(** ## Instruction and block expansion *)

(** Each source instruction owns a slice of the output [[block]]. A location
    marker can own an empty slice, while an access owns both its check
    and the instruction that consumes the proof. *)

(** A row pairs a source instruction with the name available for its check.
    Only an access consumes the name. *)
Local Definition row := (name * uinst)%type.
(** The pass can erase a source location marker when the module requests it. *)
Local Definition omit drop ui := drop && uinst_is_loc ui.
(** The instructions in a slice appear together in the output block. *)
Local Definition slice filc drop (p : row) :=
  if omit drop (snd p) then [] else step_uinst filc (fst p) (snd p).
(** An access in Fil-C mode contributes one new temporary and its proof class. *)
Local Definition generated filc (p : row) : list (name * class) :=
  if filc && uinst_is_access (snd p) then [(fst p, uinst_proof_class (snd p))] else [].

(** The next check can skip reserved names. Its counter must still
    exceed every counter that precedes it in instruction order. *)
Local Fixpoint increasing_checks lo hi (gs : list (name * class)) : Prop :=
  match gs with
  | [] => lo <= hi
  | (q,_)::rest => exists c, lo <= c /\ q = TAtom (String.append "chk" (decimal c)) /\
                              increasing_checks (c+1) hi rest
  end.

(** Lowering the starting counter preserves the order of the generated names. *)
Local Lemma increasing_lower : forall gs a b c, a <= b ->
  increasing_checks b c gs -> increasing_checks a c gs.
Proof.
  intros [|[q k] gs] a b c Le H; cbn in *; [lia|].
  destruct H as (i & Bound & E & Tail). exists i; split; [lia|auto].
Qed.

(** Adjacent counter intervals put every name in the first list before those
    in the second. *)
Local Lemma increasing_join : forall xs ys a b c,
  increasing_checks a b xs -> increasing_checks b c ys -> increasing_checks a c (xs ++ ys).
Proof.
  induction xs as [|[q k] xs IH]; intros ys a b c H J; cbn in *.
  - eapply increasing_lower; eauto.
  - destruct H as (i & Bound & E & Tail). exists i; split; auto. split; eauto.
Qed.

(** Each generated name identifies its counter and lies outside the set
    reserved by the function. *)
Local Definition fresh_range names lo hi (gs : list (name * class)) :=
  lo <= hi /\ (NoDup (map fst gs) /\ increasing_checks lo hi gs) /\
  forall q k, In (q,k) gs -> exists c,
    lo <= c < hi /\ q = TAtom (String.append "chk" (decimal c)) /\
    ~ In (String.append "chk" (decimal c)) names.

(** An empty prefix consumes no counters and defines no names. *)
Local Lemma range_nil : forall ns n, fresh_range ns n n [].
Proof. intros. split; [lia|]. split; [split; [constructor|cbn; lia]|contradiction]. Qed.

(** A collision between the two lists would put one counter in two disjoint
    intervals. *)
Local Lemma range_join : forall ns a b c xs ys,
  0 <= a -> fresh_range ns a b xs -> fresh_range ns b c ys ->
  fresh_range ns a c (xs ++ ys).
Proof.
  intros ns a b c xs ys Ha (Hab & [Nx Ox] & X) (Hbc & [Ny Oy] & Y).
  split; [lia|]. split.
  - split; [|eapply increasing_join; eauto]. rewrite map_app. apply NoDup_app; [exact Nx|exact Ny|].
    intros q I J. apply in_map_iff in I as ([x k] & <- & I).
    apply in_map_iff in J as ([y h] & E & J). cbn in E. subst y.
    destruct (X _ _ I) as (i & Bi & -> & _).
    destruct (Y _ _ J) as (j & Bj & E & _). injection E as E.
    apply decimal_injective in E; lia.
  - intros q k H. apply in_app_iff in H as [H|H].
    + destruct (X _ _ H) as (i & Bi & E & F). exists i; repeat split; auto; lia.
    + destruct (Y _ _ H) as (i & Bi & E & F). exists i; repeat split; auto; lia.
Qed.

(** This source-order walk exposes the counter that the next block receives. *)
Local Definition emit_terms (filc drop : bool) names fuel n ts :=
  let kept := if drop then filter (fun t => negb (Pizlonate.is_loc t)) ts else ts in
  if filc then expand_insts names fuel n kept else (n,kept).

(** Decoding concatenated instruction lists concatenates their typed
    instructions. *)
Local Lemma decode_append {X Y} (d : X -> option Y) : forall xs ys us vs,
  map_option d xs = Some us -> map_option d ys = Some vs ->
  map_option d (xs ++ ys) = Some (us ++ vs).
Proof.
  induction xs as [|x xs IH]; intros ys us vs H T; [now injection H as <- | ].
  cbn [map_option] in H. destruct (d x) eqn:D; [|discriminate].
  destruct (map_option d xs) eqn:E; [|discriminate]. injection H as <-.
  cbn [app map_option]. rewrite D, (IH _ _ _ eq_refl T). reflexivity.
Qed.

(** Each source instruction contributes one row, even when the pass drops its
    location marker. *)
Local Lemma emit_rows : forall ts filc drop ns n umd defs us,
  0 <= n -> map_option duinst ts = Some us ->
  Forall (fun u => uvalid_inst filc umd defs u = true) us ->
  let '(stop,out) := emit_terms filc drop ns (length ns) n ts in
  exists rows, map snd rows = us /\
    map_option dinst out = Some (flat_map (slice filc drop) rows) /\
    fresh_range ns n stop (flat_map (generated filc) rows).
Proof.
  induction ts as [|t ts IH]; intros filc drop ns n umd defs us N Dec Val.
  - injection Dec as <-. destruct filc, drop; exists []; split; try reflexivity; split; first [reflexivity|apply range_nil].
  - cbn [map_option] in Dec. destruct (duinst t) as [u|] eqn:D; [|discriminate].
    destruct (map_option duinst ts) as [rest|] eqn:T; [|discriminate].
    injection Dec as <-. inversion Val as [|? ? V Vs]; subst.
    pose proof (is_loc_duinst _ _ D) as L.
    set (kept := if drop then filter (fun x => negb (is_loc x)) ts else ts).
    assert (K : (if drop then filter (fun x => negb (is_loc x)) (t :: ts) else t :: ts) =
                if omit drop u then kept else t :: kept).
    { unfold kept, omit. destruct drop; cbn [filter andb]; [rewrite L; destruct (uinst_is_loc u)|]; reflexivity. }
    unfold emit_terms. rewrite K.
    specialize (fun m Nm => IH filc drop ns m umd defs rest Nm eq_refl Vs) as Next.
    unfold emit_terms in Next. fold kept in Next.
    destruct (omit drop u) eqn:O.
    + assert (G : uinst_is_access u = false).
      { apply andb_true_iff in O as [_ Loc]. destruct u; try discriminate. destruct i; reflexivity || discriminate. }
      specialize (Next n N). destruct (if filc then expand_insts ns (length ns) n kept else (n,kept)) as [end_ out].
      destruct Next as (rs & M & E & R).
      exists ((TInt 0,u)::rs). cbn [map snd flat_map]. rewrite M. split; [reflexivity|].
      unfold slice at 1. unfold generated at 1. cbn [snd]. rewrite O,G,andb_false_r. auto.
    + destruct filc.
      * destruct (uinst_is_access u) eqn:A.
        -- destruct (duinst_checked_access_sim _ _ D A) as (gen & Gen & Decode).
           cbn [expand_insts]. rewrite Gen.
           destruct (fresh (length ns) ns n) as [s mid] eqn:F.
           destruct (fresh_spec _ _ _ _ _ N (Nat.le_refl _) F) as (Free & Lt & Eq & Prefix).
           destruct (expand_insts ns (length ns) mid kept) as [stop out] eqn:Run.
           specialize (Next mid ltac:(lia)). rewrite Run in Next.
           destruct Next as (rs & M & E & R).
           exists ((TAtom s,u)::rs). cbn [map snd flat_map]. rewrite M. split; [reflexivity|].
           unfold slice at 1. unfold generated at 1. cbn [fst snd andb]. rewrite O,A. split.
           ++ eapply decode_append; eauto.
           ++ apply range_join with mid; auto. split; [lia|]. split.
              ** split; [constructor; [intro I; inversion I|constructor]|].
                 exists (mid-1). split; [lia|]. split; [now rewrite Eq|cbn; lia].
              ** intros q k [Pair|[]]. injection Pair as <- <-. exists (mid-1).
                 rewrite <- Eq. repeat split; auto; lia.
        -- destruct (duinst_non_access_sim _ _ (TInt 0) D A) as [Gen Decode].
           cbn [expand_insts]. rewrite Gen.
           destruct (expand_insts ns (length ns) n kept) as [stop out] eqn:Run.
           specialize (Next n N). rewrite Run in Next. destruct Next as (rs & M & E & R).
           exists ((TInt 0,u)::rs). cbn [map snd flat_map]. rewrite M. split; [reflexivity|].
           unfold slice at 1. unfold generated at 1. cbn [fst snd andb]. rewrite O,A. split; [|exact R].
           exact (decode_append _ [_] _ _ _ Decode E).
      * destruct (Next n N) as (rs & M & E & R).
        exists ((TInt 0,u)::rs). cbn [map snd flat_map]. rewrite M. split; [reflexivity|].
        unfold slice at 1. cbn [snd fst]. rewrite O. split; [|exact R].
        exact (decode_append _ [t] _ _ _ (duinst_plain_sim _ _ _ _ _ D V) E).
Qed.

(** The source and destination blocks share one label and phi list. Each has
    its own terminating jump. *)
Record layout := Layout {
  lab : name; phis : list phi; rows : list row; before : jump; after : jump
}.
(** Taking the source instruction from every row reconstructs the unchecked
    block. *)
Local Definition src_block b := mkUBlock (lab b) (phis b) (map snd (rows b)) (before b).
(** Concatenating the slices reconstructs the checked block in execution
    order. *)
Local Definition dst_block filc drop b :=
  mkBlock (lab b) (phis b) (flat_map (slice filc drop) (rows b)) (after b).
(** Adding a poll preserves the successor labels, the operands, and acceptance
    by the jump validator. *)
Local Definition jump_ok b :=
  succ_labels (before b) = succ_labels (after b) /\
  jump_uses (before b) = jump_uses (after b) /\
  forall f classes, valid_jump f classes (before b) = true ->
                    valid_jump f classes (after b) = true.

(** The counter at the end of one block supplies the lower bound for the next
    block. *)
Local Lemma decode_blocks : forall bs filc drop ns idx i n out ubs umd defs,
  0 <= n -> map_option dublock bs = Some ubs ->
  Forall (fun ub => Forall (fun u => uvalid_inst filc umd defs u = true) (ub_insts ub)) ubs ->
  pizlonated_blocks filc drop ns (length ns) idx i n bs = Some out ->
  exists blocks stop, map src_block blocks = ubs /\
    map_option dblock out = Some (map (dst_block filc drop) blocks) /\
    Forall jump_ok blocks /\
    fresh_range ns n stop (flat_map (fun b => flat_map (generated filc) (rows b)) blocks).
Proof.
  induction bs as [|t ts IH]; intros filc drop ns idx i n out ubs umd defs N D V Run.
  - injection Run as <-. injection D as <-. exists [], n. split; [reflexivity|].
    split; [reflexivity|]. split; [constructor|apply range_nil].
  - cbn [map_option] in D. destruct (dublock t) as [ub|] eqn:U; [|discriminate].
    destruct (map_option dublock ts) as [ubs'|] eqn:T; [|discriminate]. injection D as <-.
    destruct (block_shape _ _ U) as (l & ps & ins & j & ph & us & dj & -> & P & I & J & ->).
    inversion V as [|? ? V1 V2]; subst.
    cbn [pizlonated_blocks String.eqb Ascii.eqb Bool.eqb andb] in Run.
    set (kept := if drop then filter (fun x => negb (is_loc x)) ins else ins) in *.
    pose proof (emit_rows ins filc drop ns n umd defs us N I V1) as Head.
    unfold emit_terms in Head. fold kept in Head.
    assert (Eq : (if filc then let '(m,acc) := fold_left (inst_step ns (length ns)) kept (n,[]) in
                                (m, rev' acc) else (n,kept)) =
                 (if filc then expand_insts ns (length ns) n kept else (n,kept))).
    { destruct filc; [|reflexivity]. pose proof (fold_left_inst_step_nil ns (length ns) kept n) as H.
      destruct (fold_left _ kept _) as [k acc]. destruct (expand_insts _ _ _ _) as [m is_].
      destruct H as [-> ->]. reflexivity. }
    rewrite Eq in Run. destruct (if filc then expand_insts ns (length ns) n kept else (n,kept))
      as [mid is_]. destruct Head as (rs & Src & Dst & F).
    destruct (polled_jump idx i j) as [j'|] eqn:Pol; [|discriminate].
    destruct (pizlonated_blocks filc drop ns (length ns) idx (i+1) mid ts) as [bs'|] eqn:E;
      [|discriminate]. injection Run as <-.
    destruct (polled_jump_djump _ _ _ _ _ Pol J) as (dj' & J' & Succ & Uses & _).
    destruct (IH filc drop ns idx (i+1) mid bs' ubs' umd defs
                ltac:(pose proof (proj1 F); lia) eq_refl V2 E)
      as (blocks & stop & S & B & Js & G).
    exists (Layout l ph rs dj dj' :: blocks), stop.
    cbn [map]. split; [unfold src_block at 1; cbn; rewrite Src,S; reflexivity|].
    split; [cbn [map_option dblock]; rewrite P,Dst,J',B; reflexivity|].
    split; [constructor; [|exact Js]|apply range_join with mid; assumption].
    split; [now symmetry|]. split; [now symmetry|]. intros f cs H.
    eapply polled_jump_preserves_valid_jump; eauto.
Qed.

(** Each function carries its block layouts and the facts that depend
    only on rewriting, including freshness and the cycle check. *)
Record func_layout filc drop uf f := {
  blocks : list layout;
  input_blocks : ufn_blocks uf = map src_block blocks;
  output_blocks : fn_blocks f = map (dst_block filc drop) blocks;
  same_name : fn_name f = ufn_name uf;
  same_linkage : fn_linkage f = ufn_linkage uf;
  same_ret : fn_ret f = ufn_ret uf;
  same_params : fn_params f = ufn_params uf;
  good_jumps : Forall jump_ok blocks;
  distinct_checks : NoDup (map fst (flat_map (fun b => flat_map (generated filc) (rows b)) blocks));
  unused_checks : forall q k, In (q,k) (flat_map (fun b => flat_map (generated filc) (rows b)) blocks) ->
    forall cl, ~ In (q,cl) (utemp_defs uf);
  cycles_poll : polls_every_cycle f = true;
  counter_order : exists stop, increasing_checks 0 stop
    (flat_map (fun b => flat_map (generated filc) (rows b)) blocks)
}.

(** A valid unchecked function supplies a typing judgment for every source
    instruction. *)
Local Lemma func_insts_valid : forall filc umd uf, uvalid_func filc umd uf = true ->
  Forall (fun ub => Forall (fun u => uvalid_inst filc umd (utemp_defs uf) u = true) (ub_insts ub))
    (ufn_blocks uf).
Proof.
  intros filc umd uf H. unfold uvalid_func in H.
  destruct (fn_blocks (uskel_func uf)) as [|entry bs]; [discriminate|].
  destruct (block_intervals _) as [doms|]; [|discriminate].
  apply andb_true_iff in H as [_ H]. rewrite forallb_forall in H.
  apply Forall_forall. intros ub I. specialize (H ub I). unfold uvalid_block in H.
  repeat rewrite andb_true_iff in H. apply Forall_forall. rewrite <- forallb_forall. tauto.
Qed.

(** Decoding a rewritten function gives its typed blocks and the freshness
    bound across them. *)
Local Lemma decode_func_layout : forall filc drop n lk r ps bs uf out umd,
  dufunc n lk r ps bs = Some uf -> uvalid_func filc umd uf = true ->
  pizlonated_func filc drop n lk r ps bs = Some out ->
  exists f, ditem out = Some (Some (IFunc f)) /\ inhabited (func_layout filc drop uf f).
Proof.
  intros filc drop n lk r ps bs uf out umd D V Run.
  destruct bs as [| | |ts]; try discriminate Run.
  pose proof (fun a k => defined_chks_covers n lk r ps ts uf a k D) as Cover.
  set (ns := defined_chks ps ts) in *.
  unfold pizlonated_func in Run. fold ns in Run.
  destruct (label_index 0 ts nm_empty) as [idx|] eqn:Idx; [|discriminate].
  destruct (pizlonated_blocks filc drop ns (length ns) idx 0 0 ts) as [bs'|] eqn:R;
    [|discriminate]. injection Run as <-.
  pose proof (func_insts_valid _ _ _ V) as Insts.
  unfold dufunc in D. destruct (dret r) as [ret|] eqn:Ret; [|discriminate].
  destruct ps as [| | |params]; try discriminate D. cbn [dlist] in D.
  destruct (map_option dparam params) as [ds|] eqn:Params; [|discriminate].
  destruct (map_option dublock ts) as [ubs|] eqn:InB; [|discriminate]. injection D as <-.
  destruct (decode_blocks _ _ _ _ _ _ _ _ _ _ _ (Z.le_refl 0) InB Insts R)
    as (ls & stop & E & B & J & Bound & [Dist Ordered] & Free).
  set (f := mkFunc n lk ret ds (map (dst_block filc drop) ls)). exists f. split.
  - cbn [ditem]. unfold dfunc. cbn [dlist]. rewrite Ret,Params,B. reflexivity.
  - constructor. refine (Build_func_layout filc drop _ f ls _ _ _ _ _ _ J Dist _ _ (ex_intro _ stop Ordered));
      try reflexivity; [now symmetry| |].
    + intros q k I cl Old. destruct (Free _ _ I) as (c & C & -> & H).
      apply H. eapply Cover; [exact Old|apply chk_decimal_prefix].
    + eapply pizlonated_blocks_polls_every_cycle; eauto.
Qed.

(** ## Temporary classes *)

(** The validator allows several definitions of one temporary when they
    all give it the same class. We use that agreement to read the class
    from either the lookup list or the validator's table. *)

(** All definitions of a name must specify the same register class. *)
Local Definition agrees (ds : list (name * class)) :=
  forall n k h, In (n,k) ds -> In (n,h) ds -> k = h.

(** The class table keeps the earliest binding of each temporary. *)
Local Definition first_classes (ds : list (name * class)) (m : nmap class) :=
  fold_left (fun m d => if nm_mem (fst d) m then m else nm_add (fst d) (snd d) m) ds m.

(** An existing table entry takes priority. Otherwise the first matching
    definition supplies the class. *)
Local Lemma first_lookup : forall ds m n, nm_find n (first_classes ds m) =
  match nm_find n m with Some k => Some k | None => lookup n ds end.
Proof.
  induction ds as [|[d k] ds IH]; intros m n; [cbn; destruct (nm_find n m); reflexivity|].
  cbn [first_classes fold_left fst snd lookup]. fold (first_classes ds).
  rewrite IH. unfold nm_mem. destruct (nm_find d m) eqn:D.
  - destruct (name_eqb n d) eqn:E; [apply term_eqb_eq in E; subst; rewrite D|]; reflexivity.
  - rewrite nm_find_add. destruct (name_eqb n d) eqn:E; [apply term_eqb_eq in E; subst; rewrite D|];
      reflexivity.
Qed.

(** A successful association-list lookup identifies a binding in the list. *)
Local Lemma lookup_member {A} : forall (ds : list (name * A)) n k,
  lookup n ds = Some k -> In (n,k) ds.
Proof.
  induction ds as [|[x h] ds IH]; intros n k H; [discriminate|].
  cbn in H. destruct (name_eqb n x) eqn:E.
  - apply term_eqb_eq in E. injection H as <-. subst n. now left.
  - right; now apply IH.
Qed.

(** A key that occurs in the list has a first binding. *)
Local Lemma member_lookup {A} : forall (ds : list (name * A)) n k,
  In (n,k) ds -> exists h, lookup n ds = Some h.
Proof.
  induction ds as [|[x h] ds IH]; intros n k H; [contradiction|].
  cbn. destruct (name_eqb n x) eqn:E; [eauto|]. destruct H as [H|H]; [|eauto].
  injection H as -> ->. now rewrite name_eqb_refl in E.
Qed.

(** Agreement makes every binding of a temporary usable as its lookup result. *)
Local Lemma consistent_lookup : forall ds n k,
  agrees ds -> In (n,k) ds -> lookup n ds = Some k.
Proof.
  intros ds n k A I. destruct (member_lookup _ _ _ I) as [h H].
  rewrite <- (A n h k (lookup_member _ _ _ H) I). exact H.
Qed.

(** The executable class check accepts exactly the lists whose bindings agree. *)
Local Lemma classes_agree : forall ds, temp_classes_ok ds = true <-> agrees ds.
Proof.
  intros ds. unfold temp_classes_ok. fold (first_classes ds nm_empty).
  rewrite forallb_forall. split.
  - intros H n k h K J. specialize (H (n,k) K) as E. specialize (H (n,h) J).
    cbn [fst snd] in *. destruct (nm_find n _) as [c|]; [|discriminate].
    destruct c,k,h; reflexivity || discriminate.
  - intros H [n k] I. cbn [fst snd]. rewrite first_lookup,nm_find_empty,(consistent_lookup _ _ _ H I).
    destruct k; reflexivity.
Qed.

(** A list with distinct keys assigns at most one class to each name. *)
Local Lemma distinct_agree : forall ds, NoDup (map fst ds) -> agrees ds.
Proof.
  induction ds as [|[n k] ds IH]; intros N x h j H J; [contradiction|].
  inversion N as [|? ? F Rest]; subst. destruct H as [E|H], J as [D|J].
  - congruence.
  - injection E as -> ->. exfalso; apply F. exact (in_map fst _ _ J).
  - injection D as -> ->. exfalso; apply F. exact (in_map fst _ _ H).
  - exact (IH Rest x h j H J).
Qed.

(** A dropped instruction carries source location information. *)
Local Lemma omitted_loc : forall drop ui, omit drop ui = true -> exists a z, ui = UCore (Loc a z).
Proof.
  intros drop ui H. apply andb_true_iff in H as [_ H].
  destruct ui; try discriminate. destruct i; try discriminate. eauto.
Qed.

(** Each slice preserves the source definitions in order and puts its own
    proof definition first. *)
Local Lemma slice_defs : forall filc drop umd defs p,
  uvalid_inst filc umd defs (snd p) = true ->
  flat_map inst_temp_defs (slice filc drop p) = generated filc p ++ uinst_temp_defs (snd p).
Proof.
  intros filc drop umd defs [q u] V. unfold slice, generated. cbn [fst snd] in *.
  destruct (omit drop u) eqn:E.
  - destruct (omitted_loc _ _ E) as (a & z & ->). destruct filc; reflexivity.
  - eapply step_uinst_temp_defs; eauto.
Qed.

(** Membership in a concatenation can be tested separately for the two
    contributions of each element. *)
Local Lemma flat_members {A B} (f g h : A -> list B) : forall xs,
  (forall x y, In x xs -> (In y (f x) <-> In y (g x) \/ In y (h x))) ->
  forall y, In y (flat_map f xs) <-> In y (flat_map g xs) \/ In y (flat_map h xs).
Proof.
  intros xs H y. repeat rewrite in_flat_map. split.
  - intros (x & I & E). apply (H x y I) in E as [E|E]; eauto.
  - intros [(x & I & E)|(x & I & E)]; exists x; split; auto; apply H; auto.
Qed.

(** Typing a row checks the instruction before expansion. *)
Local Definition row_valid filc umd ds (p : row) := uvalid_inst filc umd ds (snd p) = true.
(** The block layout assigns a source typing judgment to every row. *)
Local Definition rows_valid filc umd ds ls :=
  forall b p, In b ls -> In p (rows b) -> row_valid filc umd ds p.

(** Source function validity supplies the typing judgments required by all its
    slices. *)
Local Lemma layout_valid_rows : forall filc drop umd uf f (L : func_layout filc drop uf f),
  uvalid_func filc umd uf = true -> rows_valid filc umd (utemp_defs uf) (blocks _ _ _ _ L).
Proof.
  intros filc drop umd uf f [ls InB OutB N K R P J D F C] V b p B I.
  pose proof (func_insts_valid _ _ _ V) as H. rewrite InB in H.
  rewrite Forall_forall in H. specialize (H _ (in_map src_block _ _ B)).
  rewrite Forall_forall in H. apply H. exact (in_map snd _ _ I).
Qed.

(** Concatenating nested slices can proceed from the inside out. *)
Local Lemma flatten_twice {A B C} (f : B -> list C) (g : A -> list B) : forall xs,
  flat_map f (flat_map g xs) = flat_map (fun x => flat_map f (g x)) xs.
Proof. induction xs; cbn; [reflexivity|now rewrite flat_map_app,IHxs]. Qed.

(** Projecting each block before collecting its instructions gives the same
    list as a single traversal. *)
Local Lemma flatten_map {A B C} (f : B -> list C) (g : A -> B) : forall xs,
  flat_map f (map g xs) = flat_map (fun x => f (g x)) xs.
Proof. induction xs; cbn; congruence. Qed.

(** A definition in the output belongs either to the source function or to a
    generated check. *)
Local Lemma layout_defs : forall filc drop umd uf f (L : func_layout filc drop uf f),
  uvalid_func filc umd uf = true -> forall dk,
  In dk (temp_defs f) <-> In dk (utemp_defs uf) \/
  In dk (flat_map (fun b => flat_map (generated filc) (rows b)) (blocks _ _ _ _ L)).
Proof.
  intros filc drop umd uf f L V dk. pose proof (layout_valid_rows _ _ _ _ _ L V) as RV.
  destruct L as [ls InB OutB N K R P J D F C]. cbn [blocks] in *.
  unfold temp_defs,utemp_defs. rewrite InB,OutB,P,!flatten_map,!in_app_iff.
  enough (H : In dk (flat_map (fun b => map (fun ph => match ph with Phi d k _ => (d,k) end) (phis b)
      ++ flat_map inst_temp_defs (flat_map (slice filc drop) (rows b))) ls) <->
    In dk (flat_map (fun b => map (fun ph => match ph with Phi d k _ => (d,k) end) (phis b)
      ++ flat_map uinst_temp_defs (map snd (rows b))) ls) \/
    In dk (flat_map (fun b => flat_map (generated filc) (rows b)) ls)) by
    (cbn [b_phis b_insts ub_insts ub_phis dst_block src_block]; tauto).
  apply flat_members. intros b y B. rewrite !in_app_iff,flatten_twice,flatten_map.
  assert (H : In y (flat_map (fun p => flat_map inst_temp_defs (slice filc drop p)) (rows b)) <->
              In y (flat_map (fun p : row => uinst_temp_defs (snd p)) (rows b)) \/
              In y (flat_map (generated filc) (rows b))).
  { apply flat_members. intros p z I. rewrite (slice_defs _ _ _ _ _ (RV b p B I)), in_app_iff. tauto. }
  tauto.
Qed.

(** Freshness keeps the new bindings disjoint from all source classes and from
    one another. *)
Local Lemma layout_classes : forall filc drop umd uf f (L : func_layout filc drop uf f),
  uvalid_func filc umd uf = true -> temp_classes_ok (utemp_defs uf) = true ->
  temp_classes_ok (temp_defs f) = true /\
  (forall n k, lookup n (utemp_defs uf) = Some k -> lookup n (temp_defs f) = Some k) /\
  (forall q k, In (q,k) (flat_map (fun b => flat_map (generated filc) (rows b)) (blocks _ _ _ _ L)) ->
     lookup q (temp_defs f) = Some k).
Proof.
  intros filc drop umd uf f L V A. pose proof (layout_defs _ _ _ _ _ L V) as Both.
  apply classes_agree in A.
  pose proof (distinct_agree _ (distinct_checks _ _ _ _ L)) as Fresh.
  pose proof (unused_checks _ _ _ _ L) as Sep.
  assert (OK : agrees (temp_defs f)).
  { intros n k h X Y. apply Both in X as [X|X]; apply Both in Y as [Y|Y].
    - exact (A _ _ _ X Y).
    - exfalso; exact (Sep _ _ Y _ X).
    - exfalso; exact (Sep _ _ X _ Y).
    - exact (Fresh _ _ _ X Y). }
  split; [now apply classes_agree|]. split; intros n k E; apply consistent_lookup; auto; apply Both.
  - left. now apply lookup_member.
  - now right.
Qed.

(** ## Positions in an expanded block *)

(** The prefix before a source instruction determines its position in
    both programs. The second instruction of an access still precedes
    every slice whose source position comes later. *)

(** The validator counts instruction positions with integers. *)
Local Definition pos {A} (xs : list A) := Z.of_nat (length xs).
(** The position at the end of concatenated lists is the sum of their lengths. *)
Local Lemma pos_app {A} : forall xs ys : list A, pos (xs ++ ys) = pos xs + pos ys.
Proof. intros. unfold pos. rewrite length_app. lia. Qed.
(** Prepending an instruction advances the end position by one. *)
Local Lemma pos_cons {A} : forall x (xs : list A), pos (x::xs) = 1 + pos xs.
Proof. intros. unfold pos. cbn [length]. lia. Qed.
(** Every program prefix has a nonnegative length. *)
Local Lemma pos_nonneg {A} : forall xs : list A, 0 <= pos xs.
Proof. intros. unfold pos. lia. Qed.
(** A projection that retains one element per instruction preserves its
    length. *)
Local Lemma pos_map {A B} (f : A -> B) : forall xs, pos (map f xs) = pos xs.
Proof. intros. unfold pos. now rewrite length_map. Qed.

(** A prefix records the instructions before a use, including a use at the end
    of a block. *)
Local Definition prefixes {A} (xs pre : list A) := exists tail, xs = pre ++ tail.

(** A later source prefix contains the entire earlier slice. This includes its
    final definition. *)
Local Lemma earlier_slice {A B} (g : A -> list B) : forall (xs p1 p2 : list A) x rest,
  xs = p1 ++ x :: rest -> prefixes xs p2 -> pos p1 < pos p2 ->
  pos (flat_map g p1) + pos (g x) <= pos (flat_map g p2).
Proof.
  intros xs p1 p2 x rest -> [tail E] H. unfold pos in H.
  assert (P : firstn (length (p1 ++ [x])) p2 = p1 ++ [x]).
  { assert (Q : firstn (length (p1 ++ [x])) (p2 ++ tail) = firstn (length (p1 ++ [x])) p2).
    { rewrite firstn_app. replace (length (p1 ++ [x]) - length p2)%nat with O by (rewrite length_app; cbn; lia). now rewrite app_nil_r. }
    rewrite <- Q.
    rewrite <- E. change (firstn (length (p1 ++ [x])) (p1 ++ [x] ++ rest) = p1 ++ [x]).
    rewrite app_assoc, firstn_app, firstn_all, Nat.sub_diag, app_nil_r. reflexivity. }
  rewrite <- (firstn_skipn (length (p1 ++ [x])) p2), P, !flat_map_app, !pos_app.
  cbn [flat_map]. rewrite app_nil_r. pose proof (pos_nonneg (flat_map g (skipn (length (p1 ++ [x])) p2))). lia.
Qed.

(** The indexed fold exposes the position that the validator otherwise
    carries beside its accumulator. *)
Local Fixpoint numbered {A} (j : Z) (xs : list A) : list (Z * A) :=
  match xs with [] => [] | x :: rest => (j,x):: numbered (j+1) rest end.

(** The index of an instruction equals the starting index plus the length of
    its prefix. *)
Local Lemma numbered_in {A} : forall (xs : list A) j i x,
  In (i,x) (numbered j xs) <->
  exists pre rest, xs = pre ++ x::rest /\ i = j + pos pre.
Proof.
  induction xs as [|a xs IH]; intros j i x; split.
  - contradiction.
  - intros ([|p pre] & rest & E & H); discriminate.
  - intros [E|I].
    + injection E as <- <-. exists [],xs. split; [reflexivity|unfold pos; cbn; lia].
    + apply IH in I as (pre & rest & -> & ->). exists (a::pre),rest. split; [reflexivity|rewrite pos_cons; lia].
  - intros ([|p pre] & rest & E & H).
    + injection E as -> ->. replace i with j by (rewrite H; unfold pos; cbn; lia). now left.
    + injection E as -> E. right. apply IH. exists pre,rest. rewrite pos_cons in H. split; auto; lia.
Qed.

(** Numbering the instructions first yields the same accumulator as
    incrementing an index during the fold. *)
Local Lemma indexed_fold {A B} (g : B -> Z -> A -> B) : forall xs acc j,
  fst (fold_left (fun (p : B * Z) x => let '(a,i) := p in (g a i x,i+1)) xs (acc,j)) =
  fold_left (fun a p => g a (fst p) (snd p)) (numbered j xs) acc.
Proof. induction xs; intros; cbn; auto. Qed.

(** A fact accumulated by the fold comes from the initial state or from one of
    its inputs. *)
Local Lemma fold_union {A B} (put : A -> B -> A) (has : A -> Prop) (hit : B -> Prop) :
  (forall a b, has (put a b) <-> has a \/ hit b) ->
  forall xs a, has (fold_left put xs a) <-> has a \/ exists x, In x xs /\ hit x.
Proof.
  intros Step xs. induction xs as [|x xs IH]; intro a; cbn.
  - firstorder.
  - rewrite IH,Step. firstorder congruence.
Qed.

(** Recording a site preserves the earlier definitions of the same temporary. *)
Local Definition add_site m n (s : site) :=
  nm_add n (s :: match nm_find n m with Some ss => ss | None => [] end) m.
(** A site belongs to a name when the map contains it among that name's
    definitions. *)
Local Definition has_site n s (m : nmap (list site)) :=
  exists ss, nm_find n m = Some ss /\ In s ss.

(** Recording a definition adds exactly one name and position to the map. *)
Local Lemma add_has : forall n s m x t,
  has_site n s (add_site m x t) <-> has_site n s m \/ (x=n /\ t=s).
Proof.
  intros. unfold has_site,add_site. rewrite nm_find_add. destruct (name_eqb n x) eqn:E.
  - apply term_eqb_eq in E. subst. destruct (nm_find x m) as [ss|].
    + split; [intros (v & H & I); injection H as <-; cbn in I; firstorder|].
      intros [(v & H & I)|[_ ->]]; [injection H as <- | ]; eexists; split; [reflexivity|auto using in_cons,in_eq|reflexivity|now left].
    + split; [intros (v & H & I); injection H as <-; cbn in I; tauto|].
      intros [(v & H & I)|[_ ->]]; [discriminate|]. eexists; split; [reflexivity|now left].
  - assert (x<>n) by (intros ->; rewrite name_eqb_refl in E; discriminate). tauto.
Qed.

(** Both validators record phi definitions before numbering the block's
    instructions. *)
Local Definition site_block {B I} (label : B -> name) (ph : B -> list phi)
    (ins : B -> list I) (ds : I -> list (name * class)) m b :=
  let phi_map := fold_left (fun m p => match p with Phi d _ _ => add_site m d (SAt (label b) (-1)) end) (ph b) m in
  fst (fold_left (fun (acc : nmap (list site) * Z) x => let '(m,j) := acc in
    (fold_left (fun m dk => add_site m (fst dk) (SAt (label b) j)) (ds x) m,j+1))
    (ins b) (phi_map,0)).

(** Parameters seed the site map before the validator visits the blocks. *)
Local Definition sites_for {B I} label ph ins ds params (bs : list B) :=
  fold_left (@site_block B I label ph ins ds) bs
    (fold_left (fun m p => add_site m (snd p) SParam) (params : list (class * name)) nm_empty).

(** A temporary can originate in a parameter, a phi node, or an instruction at
    a known prefix. *)
Local Definition located {B I} (label : B -> name) (ph : B -> list phi)
    (ins : B -> list I) (ds : I -> list (name * class)) (params : list (class * name)) bs n s :=
  (s = SParam /\ exists k, In (k,n) params) \/
  exists b, In b bs /\
    ((s = SAt (label b) (-1) /\ exists k vs, In (Phi n k vs) (ph b)) \/
     exists pre x rest k, ins b = pre ++ x::rest /\ In (n,k) (ds x) /\ s = SAt (label b) (pos pre)).

(** The executable site map contains exactly the definitions at those three
    kinds of position. *)
Local Lemma site_members {B I} : forall label ph ins ds ps bs n s,
  has_site n s (@sites_for B I label ph ins ds ps bs) <-> located label ph ins ds ps bs n s.
Proof.
  intros label ph ins ds ps bs n s. unfold sites_for, located.
  rewrite (fold_union _ (has_site n s) (fun b =>
    (s = SAt (label b) (-1) /\ exists k vs, In (Phi n k vs) (ph b)) \/
    exists pre x rest k, ins b = pre ++ x :: rest /\ In (n,k) (ds x) /\ s = SAt (label b) (pos pre))).
  - rewrite (fold_union _ (has_site n s) (fun p => snd p = n /\ SParam = s)).
    + assert (E : ~ has_site n s nm_empty) by (intros (ss & H & _); rewrite nm_find_empty in H; discriminate).
      split.
      * intros [[H|([k x] & H & X & S)]|H]; try tauto. cbn in X. subst x s. left; split; eauto.
      * intros [[-> [k H]]|H]; [left; right; exists (k,n); auto|now right].
    + intros. apply add_has.
  - intros m b. unfold site_block. rewrite indexed_fold.
    rewrite (fold_union _ (has_site n s) (fun p => (exists k, In (n,k) (ds (snd p))) /\ SAt (label b) (fst p) = s)).
    + rewrite (fold_union _ (has_site n s) (fun p => match p with Phi d _ _ => d=n /\ SAt (label b) (-1)=s end)).
      * split.
        -- intros [[H|([d k vs] & H & -> & <-)]|([j x] & J & [k H] & <-)]; [now left|right; left; split; eauto|]. cbn [fst snd] in *.
           apply numbered_in in J as (pre & rest & E & ->).
           rewrite Z.add_0_l. right; right; eauto 8.
        -- intros [H|[[-> (k & vs & H)]|(pre & x & rest & k & E & D & ->)]].
           ++ left; now left.
           ++ left; right. exists (Phi n k vs). auto.
           ++ right. exists (pos pre,x). cbn. split; [apply numbered_in; exists pre,rest; auto|split; [now exists k|reflexivity]].
      * intros a [d k vs]. apply add_has.
    + intros a [j x]. cbn [fst snd]. rewrite (fold_union _ (has_site n s)
        (fun p => fst p=n /\ SAt (label b) j=s)).
      * split; intros [H|H]; auto. destruct H as ([d k] & D & X & S). cbn in X. subst d s. right; split; eauto.
        destruct H as [[k H] <-]. right. exists (n,k); auto.
      * intros. apply add_has.
Qed.

(** A check defines the temporary consumed by the second instruction of a
    pair. Original results occur at the end of the slice. *)
Inductive slice_shape (u : uinst) : list inst -> Prop :=
| shape_empty : uinst_temp_defs u = [] -> slice_shape u []
| shape_single : forall i, inst_temp_defs i = uinst_temp_defs u ->
    incl (inst_uses i) (uinst_uses u) -> slice_shape u [i]
| shape_pair : forall i j q k, In (q,k) (inst_temp_defs i) ->
    inst_temp_defs j = uinst_temp_defs u -> incl (inst_uses i) (uinst_uses u) ->
    incl (inst_uses j) (q :: uinst_uses u) -> slice_shape u [i;j].

Local Ltac uses_subset :=
  unfold incl; intro; unfold uinst_uses,inst_uses,value_temps;
  cbn [map flight_arg_value flat_map app]; repeat rewrite in_app_iff; cbn [In]; repeat rewrite in_app_iff; cbn [In]; tauto.

(** Expansion introduces only uses of the source operands and, within a pair,
    the check result. *)
Local Lemma row_shape : forall filc drop umd defs p,
  row_valid filc umd defs p -> slice_shape (snd p) (slice filc drop p).
Proof.
  intros filc drop umd defs [q u] V. unfold row_valid in V. unfold slice. cbn [fst snd] in *.
  destruct (omit drop u) eqn:E.
  { destruct (omitted_loc _ _ E) as (a & z & ->). constructor; reflexivity. }
  destruct filc.
  - destruct u as [i| |d k lt a| | | |w v a| | | |d k lt x off| |w v x off];
      cbn [step_uinst negb];
      repeat match goal with |- context [let '(_,_) := ?e in _] => destruct e end;
      try solve [eapply shape_pair; [left; reflexivity|reflexivity|uses_subset|uses_subset]].
    destruct i as [d k o vs| | | |r cal args| | | |]; cbn [step_core_inst];
      try solve [apply shape_single; [reflexivity|apply incl_refl]].
    + destruct k; try solve [apply shape_single; [reflexivity|apply incl_refl]].
      destruct o; try solve [apply shape_single; [reflexivity|apply incl_refl]];
        destruct vs as [|v [|w [|a rest]]]; try solve [apply shape_single; [reflexivity|uses_subset]];
        destruct v; apply shape_single; first [reflexivity|uses_subset].
    + destruct cal; try solve [apply shape_single; [reflexivity|apply incl_refl]].
      eapply shape_pair; [left; reflexivity|reflexivity|uses_subset|uses_subset].
  - destruct u; cbn [uvalid_inst negb] in V; try discriminate. apply shape_single; [reflexivity|apply incl_refl].
Qed.

(** Splitting a projected list at one element identifies the corresponding
    position in the source. *)
Local Lemma map_split {A B} (g : A -> B) : forall xs pre y tail,
  map g xs = pre ++ y :: tail ->
  exists a x b, xs = a ++ x::b /\ pre = map g a /\ y = g x.
Proof.
  induction xs as [|x xs IH]; intros [|p ps] y tail H; try discriminate.
  - injection H as <- <-. exists [],x,xs. auto.
  - injection H as <- H. destruct (IH _ _ _ H) as (a & z & b & -> & -> & ->).
    exists (x::a),z,b. auto.
Qed.

(** Each output instruction has both a source row and a position inside that
    row's slice. *)
Local Lemma flat_split {A B} (g : A -> list B) : forall xs pre y tail,
  flat_map g xs = pre ++ y::tail ->
  exists a x b left right, xs = a ++ x::b /\ g x = left ++ y::right /\
    pre = flat_map g a ++ left.
Proof.
  induction xs as [|x xs IH]; intros pre y tail E; [destruct pre; discriminate|].
  cbn [flat_map] in E. apply app_eq_app in E as (s & [[X Y]|[X Y]]).
  - destruct s as [|h s].
    + cbn in Y. destruct (IH [] y tail (eq_sym Y)) as (a & z & b & l & r & -> & Zs & E).
      exists (x::a),z,b,l,r. cbn [flat_map]. rewrite <- app_assoc, <- E,!app_nil_r in *. auto.
    + injection Y as E _. subst h. exists [],x,xs,pre,s. cbn. auto.
  - destruct (IH _ _ _ Y) as (a & z & b & l & r & -> & Zs & ->).
    exists (x::a),z,b,l,r. cbn [flat_map]. rewrite <- app_assoc. auto.
Qed.

(** Distinct block labels let a same-block dominance comparison identify one
    block layout. *)
Local Lemma labels_unique : forall ls, no_dups (map lab ls) = true ->
  forall b c, In b ls -> In c ls -> lab b = lab c -> b=c.
Proof.
  induction ls as [|a ls IH]; intros N b c B C E; [contradiction|].
  cbn [map no_dups] in N. apply andb_true_iff in N as [F N]. apply negb_true_iff in F.
  assert (None_ : forall z, In z ls -> lab a <> lab z).
  { intros z I Eq. unfold mem in F.
    assert (T : existsb (name_eqb (lab a)) (map lab ls) = true).
    { apply existsb_exists. exists (lab z). split; [now apply in_map|rewrite Eq; apply name_eqb_refl]. }
    congruence. }
  destruct B as [<-|B], C as [<-|C]; [reflexivity|exfalso; exact (None_ _ C E)|exfalso; exact (None_ _ B (eq_sym E))|exact (IH N b c B C E)].
Qed.

(** Expanding the prefix before a row gives the earliest checked position of
    that row. *)
Local Definition prefix_use filc drop pre :=
  pos (flat_map (slice filc drop) pre).

(** A dominating source definition still dominates a use in the corresponding
    slice. Within one block the prefix lengths establish strict precedence. *)
Local Lemma transfer_use : forall filc drop umd uf f (L : func_layout filc drop uf f),
  let ls := blocks _ _ _ _ L in
  rows_valid filc umd (utemp_defs uf) ls -> no_dups (map lab ls) = true ->
  forall doms b pre at_ n, In b ls -> prefixes (rows b) pre ->
  prefix_use filc drop pre <= at_ ->
  dominated_use (utemp_sites uf) doms (lab b) (pos pre) n = true ->
  dominated_use (temp_sites f) doms (lab b) at_ n = true.
Proof.
  intros filc drop umd uf f [ls InB OutB N K R P J D F C] ls' RV Unique doms b pre at_ n B Pr Le H.
  subst ls'. cbn [blocks] in RV,Unique,B. unfold prefix_use in Le.
  unfold dominated_use in *. destruct (nm_find n (utemp_sites uf)) as [ss|] eqn:Find; [|discriminate].
  apply existsb_exists in H as (s & S & Dom).
  assert (Here : has_site n s (utemp_sites uf)) by (exists ss; auto).
  change (has_site n s (sites_for ub_label ub_phis ub_insts uinst_temp_defs (ufn_params uf) (ufn_blocks uf))) in Here.
  apply site_members in Here. unfold located in Here. rewrite InB in Here.
  enough (G : exists s', located b_label b_phis b_insts inst_temp_defs (fn_params f) (fn_blocks f) n s' /\
                         site_dominates doms (lab b) at_ s' = true).
  { destruct G as (s' & Loc & H). apply site_members in Loc.
    change (has_site n s' (temp_sites f)) in Loc. destruct Loc as (ss' & -> & I).
    apply existsb_exists; eauto. }
  unfold located. rewrite P,OutB. destruct Here as [[-> Hp]|(ub & U & X)].
  - exists SParam. split; auto.
  - apply in_map_iff in U as (c & <- & Cs). cbn [src_block ub_insts ub_label ub_phis] in X.
    set (db := dst_block filc drop c). assert (Db : In db (map (dst_block filc drop) ls)) by now apply in_map.
    destruct X as [[-> Hp]|(us & u & tail & k & Split & Def & ->)].
    + exists (SAt (lab c) (-1)). split; [right; exists db; auto|].
      cbn [site_dominates] in *. destruct (name_eqb (lab c) (lab b)); auto.
      apply Z.ltb_lt. pose proof (pos_nonneg (flat_map (slice filc drop) pre)). lia.
    + destruct (map_split snd _ _ _ _ Split) as (a & p & rest & Rows & -> & ->).
      assert (Rp : In p (rows c)) by (rewrite Rows; apply in_or_app; right; now left).
      pose proof (row_shape _ drop _ _ _ (RV c p Cs Rp)) as Sh.
      assert (Place : forall left i right, slice filc drop p = left ++ i :: right ->
        In (n,k) (inst_temp_defs i) ->
        exists s', (exists pre' rest', b_insts db = pre' ++ i::rest' /\ s' = SAt (lab c) (pos pre')) /\
        site_dominates doms (lab b) at_ s' = true).
      { intros left i right Slice Def'. exists (SAt (lab c) (pos (flat_map (slice filc drop) a ++ left))).
        split.
        - exists (flat_map (slice filc drop) a ++ left), (right ++ flat_map (slice filc drop) rest).
          split; [|reflexivity]. unfold db,dst_block; cbn [b_insts]. rewrite Rows,flat_map_app.
          cbn [flat_map]. rewrite Slice,<- !app_assoc. reflexivity.
        - cbn [site_dominates] in *. destruct (name_eqb (lab c) (lab b)) eqn:Eq; auto.
          apply term_eqb_eq in Eq. apply (labels_unique _ Unique c b Cs B) in Eq. subst c.
          apply Z.ltb_lt in Dom. rewrite pos_map in Dom. apply Z.ltb_lt.
          pose proof (earlier_slice (slice filc drop) _ _ _ _ _ Rows Pr Dom) as Mono.
          rewrite Slice,pos_app,pos_cons in Mono. rewrite pos_app. pose proof (pos_nonneg right). lia. }
      assert (Last : exists left i right, slice filc drop p = left ++ i::right /\ In (n,k) (inst_temp_defs i)).
      { destruct Sh as [Z|i Di Ui|i j q h Qi Dj Ui Uj].
        - rewrite Z in Def; contradiction.
        - exists [],i,[]. split; [reflexivity|congruence].
        - exists [i],j,[]. split; [reflexivity|congruence]. }
      destruct Last as (left & i & right & Slice & Di).
      destruct (Place _ _ _ Slice Di) as (s' & (p' & r' & Steps & Site) & Valid).
      exists s'. split; [|exact Valid]. right; exists db. split; auto. right; eauto 8.
Qed.

(** The instruction scan tests the terminating jump at the first index past
    the last instruction. *)
Local Definition scan_uses {A} (uses : A -> list name) (test : Z -> name -> bool)
    (jump : list name) :=
  fix scan (xs : list A) (i : Z) : bool :=
  match xs with
  | [] => forallb (test i) jump
  | x::rest => forallb (test i) (uses x) && scan rest (i+1)
  end.

(** The scan checks every instruction at its prefix length and every jump
    operand at the block end. *)
Local Lemma scan_spec {A} : forall (uses : A -> list name) test jump xs i,
  scan_uses uses test jump xs i = true <->
  (forall pre x rest n, xs = pre ++ x::rest -> In n (uses x) -> test (i+pos pre) n = true) /\
  (forall n, In n jump -> test (i+pos xs) n = true).
Proof.
  intros uses test jump xs. induction xs as [|x xs IH]; intro i; cbn [scan_uses].
  - replace (i+pos (@nil A)) with i by (unfold pos; cbn; lia). rewrite forallb_forall.
    split; [intro H; split; [intros [|a pre]; discriminate|exact H]|tauto].
  - rewrite andb_true_iff,forallb_forall,IH,pos_cons.
    split.
    + intros [Head [Tail End]]. split.
      * intros [|a pre] y rest n E I; injection E as <- E.
        -- replace (i+pos (@nil A)) with i by (unfold pos; cbn; lia). auto.
        -- rewrite pos_cons. replace (i+(1+pos pre)) with (i+1+pos pre) by lia. eauto.
      * replace (i+(1+pos xs)) with (i+1+pos xs) by lia. exact End.
    + intros [All End]. split; [|split].
      * intros n I. specialize (All [] x xs n eq_refl I).
        now rewrite Z.add_0_r in All.
      * intros pre y rest n E I. specialize (All (x::pre) y rest n ltac:(cbn; congruence) I).
        rewrite pos_cons in All. replace (i+1+pos pre) with (i+(1+pos pre)) by lia. exact All.
      * replace (i+1+pos xs) with (i+(1+pos xs)) by lia. exact End.
Qed.

(** A phi operand reads its incoming temporary at the end of the reachable
    predecessor. *)
Local Definition phi_uses_ok (test : name -> Z -> name -> bool) doms (ends : nmap Z) ph :=
  match ph with Phi _ _ pairs => forallb (fun pv => match snd pv with
  | Tmp n => if is_reachable doms (fst pv) then
      match nm_find (fst pv) ends with Some e => test (fst pv) e n | None => true end else true
  | _ => true end) pairs end.

(** The two dominance checks share one scan over instructions, jumps, and phi
    inputs. *)
Local Definition dom_check {B I} (label : B -> name) phis_ (instructions : B -> list I)
    jump uses sites doms (bs : list B) :=
  let ends := nm_of_list (map (fun b => (label b,pos (instructions b))) bs) in
  forallb (fun b => if negb (is_reachable doms (label b)) then true else
    scan_uses uses (dominated_use sites doms (label b)) (jump_uses (jump b)) (instructions b) 0 &&
    forallb (phi_uses_ok (dominated_use sites doms) doms ends) (phis_ b)) bs.

(** Looking up a predecessor in both end-position maps selects lengths from
    the same block. *)
Local Lemma ends_pair {A B C} (label : A -> name) (v : A -> B) (w : A -> C) : forall xs n,
  let fill := fun (m : list A) => nm_of_list (map (fun a => (label a,v a)) m) in
  let fill' := fun (m : list A) => nm_of_list (map (fun a => (label a,w a)) m) in
  match nm_find n (fill xs), nm_find n (fill' xs) with
  | None,None => True
  | Some x,Some y => exists a, In a xs /\ label a=n /\ x=v a /\ y=w a
  | _,_ => False end.
Proof.
  intros xs n. cbn zeta. unfold nm_of_list. rewrite !nm_find_fold_add,!nm_find_empty,<- !map_rev.
  assert (H : forall ys,
    match lookup n (map (fun a => (label a,v a)) ys), lookup n (map (fun a => (label a,w a)) ys) with
    | None,None => True
    | Some x,Some y => exists a, In a ys /\ label a=n /\ x=v a /\ y=w a
    | _,_ => False end).
  { induction ys as [|a ys IH]; [exact I|]. cbn [map lookup]. destruct (name_eqb n (label a)) eqn:E.
    - apply term_eqb_eq in E. exists a; auto using in_eq.
    - destruct (lookup n (map _ ys)), (lookup n (map _ ys)); try contradiction; auto.
      destruct IH as (z & I & H & X & Y). exists z; auto using in_cons. }
  specialize (H (rev xs)).
  destruct (lookup n (map _ (rev xs))), (lookup n (map _ (rev xs))); auto.
  destruct H as (a & I & E & X & Y). apply in_rev in I. exists a; auto.
Qed.

(** Original operands retain their dominating definitions. The first
    instruction of a check pair supplies the new operand at the second. *)
Local Lemma layout_dominate : forall filc drop umd uf f (L : func_layout filc drop uf f) doms,
  rows_valid filc umd (utemp_defs uf) (blocks _ _ _ _ L) ->
  no_dups (map lab (blocks _ _ _ _ L)) = true ->
  udefinitions_dominate uf doms = true -> definitions_dominate f doms = true.
Proof.
  intros filc drop umd uf f L doms V Unique H.
  pose proof (transfer_use _ _ _ _ _ L V Unique doms) as Transfer.
  destruct L as [ls InB OutB N K R P J D F C]. cbn [blocks] in *.
  change (dom_check ub_label ub_phis ub_insts ub_jump uinst_uses (utemp_sites uf) doms (ufn_blocks uf) = true) in H.
  change (dom_check b_label b_phis b_insts b_jump inst_uses (temp_sites f) doms (fn_blocks f) = true).
  unfold dom_check. unfold dom_check in H. rewrite InB in H. rewrite OutB.
  rewrite map_map in H. rewrite map_map. rewrite forallb_forall in H |- *.
  intros db I. apply in_map_iff in I as (b & <- & B).
  specialize (H _ (in_map src_block _ _ B)). cbn [src_block dst_block ub_label b_label ub_phis b_phis
      ub_insts b_insts ub_jump b_jump] in H |- *.
  destruct (negb (is_reachable doms (lab b))); auto.
  apply andb_true_iff in H as [U Ph]. apply andb_true_iff. split.
  - apply scan_spec in U as [Old End]. apply scan_spec. split.
    + intros pre i tail n Eq Use.
      destruct (flat_split _ _ _ _ _ Eq) as (a & p & rest & left & right & Rows & Slice & ->).
      assert (InP : In p (rows b)) by (rewrite Rows; apply in_or_app; right; now left).
      assert (Pr : prefixes (rows b) a) by (exists (p::rest); exact Rows).
      assert (Orig : In n (uinst_uses (snd p)) ->
          dominated_use (temp_sites f) doms (lab b) (0+pos (flat_map (slice filc drop) a ++ left)) n = true).
      { intros Read. eapply Transfer; [exact B|exact Pr|unfold prefix_use; rewrite pos_app; pose proof (pos_nonneg left); lia|].
        specialize (Old (map snd a) (snd p) (map snd rest) n ltac:(rewrite Rows,map_app; reflexivity) Read).
        now rewrite pos_map,Z.add_0_l in Old. }
      pose proof (row_shape _ drop _ _ _ (V b p B InP)) as Sh.
      remember (slice filc drop p) as steps eqn:Steps. destruct Sh as [Z|j Dj Uj|j h q k Q Dh Uj Uh].
      * destruct left; discriminate.
      * destruct left as [|v [|w vs]]; try discriminate. injection Slice as <- _. auto.
      * destruct left as [|v [|w [|l left]]]; try discriminate.
        -- injection Slice as <- _. auto.
        -- injection Slice as <- <- _. destruct (Uh _ Use) as [<-|OrigUse]; [|now apply Orig].
           set (s := SAt (lab b) (pos (flat_map (slice filc drop) a))).
           assert (At : has_site q s (temp_sites f)).
           { change (has_site q s (sites_for b_label b_phis b_insts inst_temp_defs (fn_params f) (fn_blocks f))).
             apply site_members. unfold located. rewrite OutB. right. exists (dst_block filc drop b). split; [now apply in_map|].
             right. exists (flat_map (slice filc drop) a),j,(h::flat_map (slice filc drop) rest),k.
             cbn [dst_block b_insts]. rewrite Rows,flat_map_app. cbn [flat_map]. rewrite <- Steps. auto. }
           destruct At as (ss & Find & S). unfold dominated_use. rewrite Find. apply existsb_exists.
           exists s. split; auto. unfold s. cbn [site_dominates]. rewrite name_eqb_refl,pos_app.
           apply Z.ltb_lt. change (pos [j]) with 1. lia.
    + intros n Read. rewrite Forall_forall in J. destruct (J b B) as [_ [Uses _]].
      rewrite <- Uses in Read. specialize (End n Read). rewrite pos_map,Z.add_0_l in End.
      eapply Transfer; [exact B|exists []; now rewrite app_nil_r|unfold prefix_use; lia|exact End].
  - rewrite forallb_forall in Ph |- *. intros ph Iph. specialize (Ph ph Iph). destruct ph as [d k pairs].
    unfold phi_uses_ok in *. rewrite forallb_forall in Ph |- *. intros [l v] Pair. specialize (Ph _ Pair).
    cbn [fst snd] in *. destruct v; try reflexivity.
    destruct (is_reachable doms l); [|reflexivity].
    pose proof (ends_pair lab (fun b => pos (map snd (rows b)))
      (fun b => pos (flat_map (slice filc drop) (rows b))) ls l) as Ends.
    cbn zeta in Ends.
    destruct (nm_find l (nm_of_list (map (fun b => (lab b,pos (map snd (rows b)))) ls))) as [x|];
    destruct (nm_find l (nm_of_list (map (fun b => (lab b,pos (flat_map (slice filc drop) (rows b)))) ls))) as [y|];
      try contradiction; try reflexivity.
    destruct Ends as (z & Iz & <- & -> & ->). rewrite pos_map in Ph. eapply Transfer;
      [exact Iz|exists []; now rewrite app_nil_r|apply Z.le_refl|exact Ph].
Qed.

(** ## Function observations and local declarations *)

(** A function signature observes the presence of a variadic operation,
    and the local-object check observes a call to setjmp. Both queries
    inspect each slice independently of its position. *)

(** The skeleton keeps exactly the instructions represented by the core
    instruction type. *)
Local Definition core (u : uinst) := match u with UCore i => [i] | _ => [] end.
(** A match in the expanded stream occurs in at least one slice. *)
Local Lemma exists_flat {A B} (test : B -> bool) (g : A -> list B) : forall xs,
  existsb test (flat_map g xs) = existsb (fun x => existsb test (g x)) xs.
Proof. induction xs; cbn; [reflexivity|now rewrite existsb_app,IHxs]. Qed.
(** A search through projected blocks can apply the projection during the
    search. *)
Local Lemma exists_map' {A B} (test : B -> bool) (g : A -> B) : forall xs,
  existsb test (map g xs) = existsb (fun x => test (g x)) xs.
Proof. induction xs; cbn; congruence. Qed.
(** Two tests that agree on every list element give the same search result. *)
Local Lemma same_exists {A} (p q : A -> bool) : forall xs,
  (forall x, In x xs -> p x = q x) -> existsb p xs = existsb q xs.
Proof.
  induction xs as [|x xs IH]; intros H; cbn; auto.
  rewrite (H x (in_eq _ _)),IH; auto using in_cons.
Qed.

(** A function contains a matching instruction when at least one of its blocks
    does. *)
Local Definition observes test f := existsb (fun b => existsb test (b_insts b)) (fn_blocks f).
(** A query preserved by each slice survives the whole pass if it ignores
    location markers. *)
Local Lemma layout_observes : forall filc drop uf f (L : func_layout filc drop uf f) test,
  (forall a z, test (Loc a z) = false) ->
  (forall u q, existsb test (step_uinst filc q u) = existsb test (core u)) ->
  observes test f = observes test (uskel_func uf).
Proof.
  intros filc drop uf f [ls InB OutB N K R P J D F C] test Loc Step.
  unfold observes. cbn [uskel_func fn_blocks]. rewrite InB, OutB,!exists_map'. apply same_exists.
  intros b _. cbn [uskel_block src_block dst_block b_insts ub_insts]. rewrite !exists_flat, exists_map'.
  apply same_exists. intros [q u] _. unfold slice. cbn [fst snd]. destruct (omit drop u) eqn:E.
  - destruct (omitted_loc _ _ E) as (a & z & ->). cbn [existsb]; rewrite Loc; reflexivity.
  - apply Step.
Qed.

Local Ltac observe_with L step :=
  eapply (layout_observes _ _ _ _ L); [reflexivity|intros u q; rewrite step;
    destruct u; cbn [core existsb]; try rewrite orb_false_r; reflexivity].

(** Pizlonation preserves the variadic flag used in direct-call signatures. *)
Local Lemma layout_va : forall filc drop uf f (L : func_layout filc drop uf f),
  variadic_func f = variadic_func (uskel_func uf).
Proof. intros. unfold variadic_func. observe_with L step_uinst_va_args. Qed.
(** The local-object check sees the same presence or absence of setjmp after
    expansion. *)
Local Lemma layout_setjmp : forall filc drop uf f (L : func_layout filc drop uf f),
  setjmp_func f = setjmp_func (uskel_func uf).
Proof. intros. unfold setjmp_func. observe_with L step_uinst_setjmp. Qed.
(** Each alias check observes the same direct calls to its symbol. *)
Local Lemma layout_calls : forall filc drop uf f (L : func_layout filc drop uf f) n,
  calls_global (IFunc f) n = calls_global (IFunc (uskel_func uf)) n.
Proof. intros. cbn [calls_global]. observe_with L step_uinst_calls_global. Qed.

(** A checked local declaration supplies the object's name and size. *)
Local Definition alloc (i : inst) := match i with LocalAlloc x z => [(x,z)] | _ => [] end.
(** The unchecked instruction stream declares objects through the same core
    allocation instruction. *)
Local Definition ualloc (u : uinst) := match u with UCore (LocalAlloc x z) => [(x,z)] | _ => [] end.
(** A checked local access names its object in the check preceding the raw
    access. *)
Local Definition local_target (i : inst) := match i with Let _ _ (CheckLocal x _ _ _ _) _ => Some x | _ => None end.

(** A slice contributes exactly the objects its source instruction declares. *)
Local Lemma row_alloc : forall filc drop p,
  flat_map alloc (slice filc drop p) = ualloc (snd p).
Proof.
  intros filc drop [q u]. unfold slice. cbn [fst snd]. destruct (omit drop u) eqn:E.
  - destruct (omitted_loc _ _ E) as (a & z & ->). reflexivity.
  - apply step_uinst_local_objects.
Qed.

(** Allocation names and sizes retain their order within a block. *)
Local Lemma block_alloc : forall filc drop b,
  flat_map alloc (b_insts (dst_block filc drop b)) = flat_map ualloc (ub_insts (src_block b)).
Proof.
  intros. cbn [dst_block src_block b_insts ub_insts]. rewrite flatten_twice, flatten_map.
  apply flat_map_ext. apply row_alloc.
Qed.

(** The local-object table retains its order across the entire function. *)
Local Lemma layout_objects : forall filc drop uf f (L : func_layout filc drop uf f),
  local_objects f = ulocal_objects uf.
Proof.
  intros filc drop uf f [ls InB OutB N K R P J D F C]. unfold local_objects,ulocal_objects.
  rewrite InB,OutB,!flatten_map. apply flat_map_ext. apply block_alloc.
Qed.

(** Every checked local access names the same object as its source access. *)
Local Lemma row_local_target : forall filc drop umd ds p i x,
  row_valid filc umd ds p -> In i (slice filc drop p) ->
  local_target i = Some x -> uinst_local_target (snd p) = Some x.
Proof.
  intros filc drop umd ds [q u] i x V I T. unfold row_valid in V. unfold slice in I.
  cbn [snd fst] in *. destruct (omit drop u); [contradiction|].
  destruct u as [j| |d k lt a| | | |w v a| | | |d k lt l off| |w v l off].
  1: { assert (N : checked_inst j = false).
    { destruct filc; cbn [uvalid_inst negb] in V; repeat rewrite andb_true_iff in V;
      apply negb_true_iff; tauto. }
    destruct filc; cbn [step_uinst negb] in I.
    + destruct j as [d k o args| | | |r cal args| | | |]; cbn [step_core_inst] in I;
        try solve [destruct I as [<-|[]]; discriminate].
      * destruct k; try (destruct I as [<-|[]]; destruct o; discriminate).
        destruct o; try solve [destruct I as [<-|[]]; discriminate].
        all: destruct args as [|a [|b [|c rest]]]; try destruct a;
          destruct I as [<-|[]]; discriminate.
      * destruct cal; cbn [In] in I; repeat destruct I as [<-|I]; try discriminate; contradiction.
    + destruct I as [<-|[]]. destruct j; try discriminate. destruct o; discriminate. }
  all: destruct filc; cbn [step_uinst negb] in I; try contradiction.
    all: repeat match type of I with context [let '(_,_) := ?e in _] => destruct e end;
      destruct I as [<-|[<-|[]]]; discriminate || exact T.
Qed.

(** The entry block pairs each declared object with its allocation index. *)
Local Definition declares {A} (obj : A -> list (name * Z)) (xs : list A) :=
  flat_map (fun p => map (fun dk => (fst dk,fst p)) (obj (snd p))) (numbered 0 xs).

(** The validator's declaration fold records exactly the indexed allocations. *)
Local Lemma collect_decl {A} (obj : A -> list (name * Z)) : forall xs,
  fst (fold_left (fun (p : list (name * Z) * Z) x => let '(a,j) := p in
        (a ++ map (fun dk => (fst dk,j)) (obj x),j+1)) xs ([],0)) = declares obj xs.
Proof.
  intro xs. rewrite indexed_fold. unfold declares.
  generalize (numbered 0 xs). intros ys.
  assert (H : forall acc, fold_left (fun a (p : Z*A) => a ++ map (fun dk => (fst dk,fst p)) (obj (snd p))) ys acc =
    acc ++ flat_map (fun p => map (fun dk => (fst dk,fst p)) (obj (snd p))) ys).
  { induction ys; intros; cbn; [now rewrite app_nil_r|now rewrite IHys,app_assoc]. }
  apply (H []).
Qed.

(** A declaration lookup identifies an allocation and its prefix in the entry
    block. *)
Local Lemma declared_member {A} (obj : A -> list (name * Z)) : forall xs x j,
  In (x,j) (declares obj xs) <->
  exists pre i rest z, xs = pre ++ i::rest /\ In (x,z) (obj i) /\ j = pos pre.
Proof.
  intros. unfold declares. rewrite in_flat_map. split.
  - intros ([k i] & I & H). apply in_map_iff in H as ([n z] & E & D).
    injection E as -> ->. apply numbered_in in I as (pre & rest & E & ->). exists pre,i,rest,z; auto.
  - intros (pre & i & rest & z & E & D & ->). exists (pos pre,i). split.
    + apply numbered_in. exists pre,rest; auto.
    + apply in_map_iff. exists (x,z); auto.
Qed.

(** Removing the indices from the declaration table recovers the allocation
    names in order. *)
Local Lemma declared_names {A} (obj : A -> list (name * Z)) : forall xs,
  map fst (declares obj xs) = map fst (flat_map obj xs).
Proof.
  intro xs. unfold declares. generalize 0 as j. induction xs as [|x xs IH]; intros j; cbn; auto.
  rewrite !map_app, map_map, IH. reflexivity.
Qed.

(** The validator's distinctness test excludes repeated names. *)
Local Lemma nodup_names : forall ns, no_dups ns = true -> NoDup ns.
Proof.
  induction ns as [|n ns IH]; intro H; constructor; cbn [no_dups] in H;
    apply andb_true_iff in H as [F R]; auto.
  intro I. apply negb_true_iff in F. unfold mem in F.
  assert (E : existsb (name_eqb n) ns = true) by (apply existsb_exists; exists n; auto using name_eqb_refl).
  congruence.
Qed.

(** A declaration with a unique name supplies its recorded index on lookup. *)
Local Lemma lookup_unique {A} : forall (ds : list (name*A)) x j,
  NoDup (map fst ds) -> In (x,j) ds -> lookup x ds = Some j.
Proof.
  induction ds as [|[y h] ds IH]; intros x j N I; [contradiction|].
  inversion N as [|? ? Fresh Tail]; subst. cbn. destruct I as [E|I].
  - injection E as -> ->. now rewrite name_eqb_refl.
  - destruct (name_eqb x y) eqn:E; [|now apply IH]. apply term_eqb_eq in E. subst y.
    exfalso. exact (Fresh (in_map fst _ _ I)).
Qed.

(** A local access requires an entry declaration. Within the entry block that
    declaration must precede the access. *)
Local Definition declared_before same (ds : list (name * Z)) (i : Z) (x : option name) :=
  match x with None => true | Some x =>
    match lookup x ds with None => false | Some j => negb same || (j <? i) end end.

(** The local-access fold tests every instruction at its own prefix length. *)
Local Lemma check_each_index {A} (test : Z -> A -> bool) : forall xs,
  fst (fold_left (fun (p : bool*Z) x => let '(good,j) := p in (good && test j x,j+1)) xs (true,0)) = true
  <-> forall pre x rest, xs = pre ++ x::rest -> test (pos pre) x = true.
Proof.
  intro xs. rewrite indexed_fold.
  assert (H : forall ys ok,
    fold_left (fun a (p : Z*A) => a && test (fst p) (snd p)) ys ok = true <->
    ok = true /\ forall p, In p ys -> test (fst p) (snd p) = true).
  { induction ys as [|p ys IH]; intros ok; cbn; [intuition|]. rewrite IH,andb_true_iff. firstorder congruence. }
  rewrite H. split.
  - intros [_ All] pre x rest E. apply (All (pos pre,x)). apply numbered_in. exists pre,rest; auto.
  - intros All. split; auto. intros [j x] I. apply numbered_in in I as (pre & rest & E & ->). apply (All pre x rest E).
Qed.

(** Folds with identical updates return the same result for any initial
    accumulator. *)
Local Lemma fold_same {A B} (g h : B -> A -> B) : forall xs a,
  (forall acc x, g acc x = h acc x) -> fold_left g xs a = fold_left h xs a.
Proof. induction xs; intros; cbn; [reflexivity|rewrite H; now apply IHxs]. Qed.

(** The checked and unchecked local validators share the object table,
    declaration lookup, and ordering test. *)
Local Definition locals_for {B I} (label : B -> name) (ins : B -> list I) obj target
    (objs : list (name*Z)) sj (bs : list B) :=
  no_dups (map fst objs) && (match objs with [] => true | _ => negb sj end) &&
  match bs with
  | [] => false
  | entry::_ =>
      let ds := declares obj (ins entry) in
      Nat.eqb (length ds) (length objs) &&
      forallb (fun b =>
        fst (fold_left (fun (p : bool * Z) x => let '(good,j) := p in
          (good && declared_before (name_eqb (label b) (label entry)) ds j (target x),j+1))
          (ins b) (true,0))) bs
  end.

(** Pointwise agreement on the elements preserves the result of a universal
    test. *)
Local Lemma forallb_same {A} (g h : A -> bool) : forall xs,
  (forall x, In x xs -> g x = h x) -> forallb g xs = forallb h xs.
Proof. induction xs; intros H; cbn; auto. rewrite (H _ (in_eq _ _)),IHxs; auto using in_cons. Qed.

Local Ltac local_fold_eq :=
  match goal with |- context [fst (fold_left ?g ?xs ([],0))] =>
    match goal with |- context [declares ?obj xs] =>
      let Eq := fresh "Eq" in
      assert (Eq : fst (fold_left g xs ([],0)) = declares obj xs)
        by (rewrite <- collect_decl; f_equal; apply fold_same; intros [ds j] x;
            destruct x; cbn; try match goal with i : inst |- _ => destruct i end; cbn; now rewrite ?app_nil_r);
      rewrite Eq
    end
  end;
  apply f_equal; apply f_equal; apply forallb_same; intros b _;
  apply f_equal; apply fold_same; intros [good j] x; destruct x; try reflexivity;
  try match goal with o : op |- _ => destruct o end; reflexivity.

(** The checked validator reads allocations and local targets through the
    common indexed test. *)
Local Lemma checked_locals_form : forall f, valid_locals f =
  locals_for b_label b_insts alloc local_target (local_objects f) (setjmp_func f) (fn_blocks f).
Proof.
  intros. unfold valid_locals,locals_for. destruct (fn_blocks f) as [|entry rest]; [reflexivity|].
  local_fold_eq.
Qed.

(** The unchecked validator applies that test directly to local loads and
    stores. *)
Local Lemma unchecked_locals_form : forall uf, uvalid_locals uf =
  locals_for ub_label ub_insts ualloc uinst_local_target (ulocal_objects uf) (setjmp_func (uskel_func uf)) (ufn_blocks uf).
Proof.
  intros. unfold uvalid_locals,locals_for. destruct (ufn_blocks uf) as [|entry rest]; [reflexivity|].
  local_fold_eq.
Qed.

(** Every local check finds its allocation at the translated index. Strict
    order matters when both occur in the entry block. *)
Local Lemma layout_locals : forall filc drop umd uf f (L : func_layout filc drop uf f),
  rows_valid filc umd (utemp_defs uf) (blocks _ _ _ _ L) ->
  no_dups (map lab (blocks _ _ _ _ L)) = true ->
  uvalid_locals uf = true -> valid_locals f = true.
Proof.
  intros filc drop umd uf f L RV Unique H. rewrite unchecked_locals_form in H. rewrite checked_locals_form.
  rewrite (layout_objects _ _ _ _ L), (layout_setjmp _ _ _ _ L).
  destruct L as [ls InB OutB N K R P J D F C]. cbn [blocks] in RV. unfold locals_for in *.
  rewrite InB in H. rewrite OutB. destruct ls as [|entry ls]; [exact H|].
  cbn [map] in H |- *. repeat rewrite andb_true_iff in H |- *.
  destruct H as [[ND Sj] [Len All]]. split; [auto|]. split.
  - rewrite <- (length_map fst (declares alloc _)),declared_names,block_alloc,<- declared_names,length_map.
    exact Len.
  - set (uds := declares ualloc (ub_insts (src_block entry))) in *.
    set (ds := declares alloc (b_insts (dst_block filc drop entry))) in *.
    assert (ND' : NoDup (map fst ds)).
    { unfold ds. rewrite declared_names,block_alloc. unfold ulocal_objects in ND.
      rewrite InB in ND. cbn [map flat_map] in ND. rewrite map_app in ND.
      exact (@NoDup_app_remove_r _ _ _ (nodup_names _ ND)). }
    rewrite forallb_forall in All |- *. intros db I.
    change (In db (map (dst_block filc drop) (entry::ls))) in I.
    apply in_map_iff in I as (b & <- & B). specialize (All _ (in_map src_block _ _ B)).
    apply check_each_index. intros pre i tail Eq.
    destruct (local_target i) as [x|] eqn:T; [|reflexivity].
    destruct (flat_split _ _ _ _ _ Eq) as (a & p & rest & left & right & Rows & Slice & ->).
    assert (Ip : In p (rows b)) by (rewrite Rows; apply in_or_app; right; now left).
    assert (Ii : In i (slice filc drop p)) by (rewrite Slice; apply in_or_app; right; now left).
    pose proof (row_local_target _ _ _ _ _ _ _ (RV b p B Ip) Ii T) as Target.
    pose proof (proj1 (check_each_index (fun j u => declared_before (name_eqb (lab b) (lab entry)) uds j (uinst_local_target u)) _) All) as Uses. clear All. rename Uses into All.
    specialize (All (map snd a) (snd p) (map snd rest) ltac:(cbn [src_block ub_insts]; rewrite Rows,map_app; reflexivity)).
    cbv beta in All. rewrite Target in All. unfold declared_before in All |- *. cbn [src_block dst_block ub_label b_label] in *.
    destruct (lookup x uds) as [j|] eqn:Look; [|discriminate].
    pose proof (lookup_member _ _ _ Look) as At. apply declared_member in At as (pre & u & end_ & z & Split & Hit & ->).
    destruct (map_split snd _ _ _ _ Split) as (e & r & etail & Entry & -> & ->).
    destruct r as [q ui]. destruct ui; try contradiction. destruct i0; try contradiction.
    destruct Hit as [Hit|[]]. injection Hit as -> ->.
    assert (S : slice filc drop (q,UCore (LocalAlloc x z)) = [LocalAlloc x z]) by
      (destruct filc,drop; reflexivity).
    assert (Out : In (x,pos (flat_map (slice filc drop) e)) ds).
    { unfold ds. apply declared_member. exists (flat_map (slice filc drop) e),(LocalAlloc x z),
        (flat_map (slice filc drop) etail),z. cbn [dst_block b_insts]. rewrite Entry,flat_map_app.
      cbn [flat_map]. rewrite S. repeat split. now left. }
    rewrite (lookup_unique _ _ _ ND' Out). destruct (name_eqb (lab b) (lab entry)) eqn:Same; [|reflexivity].
    cbn [negb orb] in All |- *. apply Z.ltb_lt in All. rewrite !pos_map in All. apply Z.ltb_lt.
    assert (Bsame : b=entry).
    { apply term_eqb_eq in Same.
      exact (labels_unique _ Unique b entry B (in_eq _ _) Same). }
    subst b. assert (Pr : prefixes (rows entry) a) by (exists (p::rest); exact Rows).
    pose proof (earlier_slice (slice filc drop) _ _ _ _ _ Entry Pr All) as Mono.
    rewrite S in Mono. change (pos [LocalAlloc x z]) with 1 in Mono.
    rewrite pos_app. pose proof (pos_nonneg left). lia.
Qed.

(** ## Function validity *)

(** Control flow determines the [[dominance|dominator intervals]] and the
    predecessors of each [[phi]] node. The remaining block checks read the function
    signature, the temporary classes, and the instructions in each slice. *)

(** Source and output blocks have the same ordered labels and successor lists. *)
Local Lemma layout_cfg : forall filc drop uf f (L : func_layout filc drop uf f),
  let sk := uskel_func uf in
  map b_label (fn_blocks sk) = map lab (blocks _ _ _ _ L) /\
  labels sk = labels f /\
  map (fun b => succ_labels (b_jump b)) (fn_blocks sk) =
  map (fun b => succ_labels (b_jump b)) (fn_blocks f).
Proof.
  intros filc drop uf f [ls InB OutB N K R P J D F C] sk. unfold sk,labels.
  cbn [uskel_func fn_blocks blocks]. rewrite InB,OutB,!map_map. split; [reflexivity|]. split; [reflexivity|].
  apply map_ext_in. rewrite Forall_forall in J. intros b I. exact (proj1 (J b I)).
Qed.

(** A jump remains well typed when its operands retain their classes and its
    return type and targets agree. *)
Local Lemma valid_jump_mono : forall f g ds es j,
  fn_ret f = fn_ret g -> labels f = labels g ->
  (forall n k, lookup n ds = Some k -> lookup n es = Some k) ->
  valid_jump f ds j = true -> valid_jump g es j = true.
Proof.
  intros f g ds es j R L Ext H. destruct j; cbn [valid_jump] in *; rewrite <- ?L, <- ?R;
    try assumption.
  - repeat rewrite andb_true_iff in *. intuition eauto using valid_use_mono.
  - destruct (fn_ret f); try discriminate. eapply valid_use_mono; eauto.
  - destruct (fn_ret f); try discriminate. apply andb_true_iff in H as [Len H].
    apply andb_true_iff. split; auto. rewrite forallb_forall in *. eauto using valid_use_mono.
Qed.

(** A phi node keeps the same predecessor set and the classes of its incoming
    values. *)
Local Lemma valid_phi_mono : forall p ds es ph,
  (forall n k, lookup n ds = Some k -> lookup n es = Some k) ->
  valid_phi ds p ph = true -> valid_phi es p ph = true.
Proof.
  intros p ds es [d k vs] Ext H. cbn [valid_phi] in *. apply andb_true_iff in H as [Sets H].
  apply andb_true_iff. split; auto. rewrite forallb_forall in *. eauto using valid_use_mono.
Qed.

(** Direct and raw calls can share a test on results and arguments while
    applying different acceptance rules. *)
Local Definition call_test (p r : call_result -> list arg -> bool) (i : inst) :=
  match i with Call res _ args => p res args | RawCall res _ args => r res args | _ => true end.

(** An indirect call keeps its results and arguments when the pass inserts a
    function check. *)
Local Lemma row_call_test : forall filc drop p r x,
  (forall res args, p res args = true -> r res args = true) ->
  forallb (call_test p r) (core (snd x)) = true ->
  forallb (call_test p r) (slice filc drop x) = true.
Proof.
  intros filc drop p r [q u] Pr H. unfold slice. cbn [fst snd]. destruct (omit drop u); auto.
  destruct filc; [|destruct u; cbn [step_uinst core negb snd] in *; auto].
  destruct u as [i| |d k lt a| | | |w v a| | | |d k lt x off| |w v x off];
    cbn [step_uinst negb]; repeat match goal with |- context [let '(_,_) := ?v in _] => destruct v end;
    try reflexivity.
  destruct i as [d k o vs| | | |res cal args| | | |]; cbn [step_core_inst]; try exact H.
  - destruct k; try reflexivity. destruct o; try reflexivity;
      destruct vs as [|a [|b [|c rest]]]; try reflexivity; destruct a; reflexivity.
  - destruct cal; try exact H. cbn [core snd forallb call_test andb] in H |- *.
    rewrite andb_true_r in *. auto.
Qed.

(** Preserving a call restriction in each slice preserves it throughout a
    block. *)
Local Lemma block_call_test : forall filc drop p r b,
  (forall res args, p res args = true -> r res args = true) ->
  forallb (call_test p r) (b_insts (uskel_block (src_block b))) = true ->
  forallb (call_test p r) (b_insts (dst_block filc drop b)) = true.
Proof.
  intros filc drop p r b Pr H. rewrite forallb_forall in H |- *. intros i I.
  apply in_flat_map in I as (x & Ix & Ii).
  assert (Good : forallb (call_test p r) (core (snd x)) = true).
  { apply forallb_forall. intros j J. apply H. apply in_flat_map. exists (snd x). split; auto.
    exact (in_map snd _ _ Ix). }
  pose proof (row_call_test filc drop _ _ _ Pr Good) as Out. rewrite forallb_forall in Out. auto.
Qed.

(** A call contributes its scalar or tuple result bindings to the class check. *)
Local Definition result_defs (r : call_result) : list (name*class) :=
  match r with CVoid => [] | CResult d k => [(d,k)] | CTuple rs => rs end.
(** Call arguments and results must all carry ordinary value classes. *)
Local Definition call_classes r args :=
  forallb (fun dk => negb (proof_class (snd dk))) (result_defs r) &&
  forallb (fun a => negb (proof_class (arg_class a))) args.
(** The extended-value check inspects the scalar result and every argument of
    a call. *)
Local Definition call_ext r args :=
  match r with CResult _ k => class_eqb k Extended | _ => false end ||
  existsb (fun a => class_eqb (arg_class a) Extended) args.

(** Generated capability proofs stay outside parameters, phi results, and call
    interfaces. *)
Local Lemma layout_proof_classes : forall filc drop uf f (L : func_layout filc drop uf f),
  proof_class_defs (uskel_func uf) = true -> proof_class_defs f = true.
Proof.
  intros filc drop uf f [ls InB OutB N K R P J D F C] H. unfold proof_class_defs in *.
  rewrite P, OutB. cbn [uskel_func fn_blocks fn_params] in H. rewrite InB in H.
  apply andb_true_iff in H as [Params H]. apply andb_true_iff; split; auto.
  rewrite forallb_forall in H |- *. intros db I. apply in_map_iff in I as (b & <- & B).
  specialize (H _ (in_map uskel_block _ _ (in_map src_block _ _ B))).
  apply andb_true_iff in H as [Ph U]. apply andb_true_iff; split; [exact Ph|].
  match type of U with forallb ?test _ = true =>
    assert (Eq : forall xs, forallb test xs = forallb (call_test call_classes call_classes) xs)
      by (intros; apply forallb_same; intros i _; destruct i; reflexivity)
  end. rewrite Eq in U |- *. eapply block_call_test; eauto.
Qed.

(** A failed search means that every element fails the test. *)
Local Lemma no_exists {A} (p : A -> bool) : forall xs,
  existsb p xs = false <-> forall x, In x xs -> p x = false.
Proof.
  intros xs. split.
  - intros H x I. destruct (p x) eqn:E; auto.
    assert (T : existsb p xs = true) by (apply existsb_exists; eauto). congruence.
  - intros H. destruct (existsb p xs) eqn:E; auto. apply existsb_exists in E as (x & I & E).
    specialize (H _ I). congruence.
Qed.

(** The output keeps extended values out of each interface checked by the
    input validator. *)
Local Lemma layout_extended : forall filc drop uf f (L : func_layout filc drop uf f),
  extended_crosses (uskel_func uf) = false -> extended_crosses f = false.
Proof.
  intros filc drop uf f [ls InB OutB N K R P J D F C] H. unfold extended_crosses in *.
  rewrite R,P,OutB. cbn [uskel_func fn_blocks fn_ret fn_params] in H. rewrite InB in H.
  apply orb_false_iff in H as [Header H]. apply orb_false_iff; split; auto.
  rewrite no_exists in H |- *. intros db I. apply in_map_iff in I as (b & <- & B).
  specialize (H _ (in_map uskel_block _ _ (in_map src_block _ _ B))).
  apply orb_false_iff in H as [Ph H]. apply orb_false_iff; split; [exact Ph|].
  rewrite no_exists in H |- *.
  pose (p := fun r args => negb (call_ext r args)). pose (r := fun (_ : call_result) (_ : list arg) => true).
  assert (Src : forallb (call_test p r) (b_insts (uskel_block (src_block b))) = true).
  { apply forallb_forall. intros i I. specialize (H _ I). destruct i; try reflexivity.
    unfold call_test,p. apply negb_true_iff. exact H. }
  pose proof (block_call_test filc drop p r b ltac:(auto) Src) as Out.
  rewrite forallb_forall in Out. intros i I. specialize (Out _ I). destruct i; try reflexivity.
  apply negb_true_iff. exact Out.
Qed.

(** Erasing location rows recovers the retained source instructions in
    order. Expanding those rows recovers the entire output instruction list. *)
Local Lemma retained_rows : forall filc drop rs,
  let qs := filter (fun p : row => negb (omit drop (snd p))) rs in
  map snd qs = filter (fun u => if drop then negb (uinst_is_loc u) else true) (map snd rs) /\
  flat_map (slice filc drop) rs = flat_map (fun p => step_uinst filc (fst p) (snd p)) qs.
Proof.
  intros filc drop rs. induction rs as [|p rs IH]; [split; reflexivity|].
  cbn zeta in IH |- *. destruct IH as [Names Code]. cbn [map filter flat_map].
  unfold slice at 1. unfold omit in *. destruct drop; destruct (uinst_is_loc (snd p));
    cbn [andb negb map flat_map] in Names,Code |- *; rewrite ?Names, ?Code; split; reflexivity.
Qed.

(** The adjacent check supplies evidence, the expansion introduces no limit
    reads, and the poll pass covers every cycle. *)
Local Lemma layout_stage : forall filc drop umd uf f (L : func_layout filc drop uf f) md doms,
  rows_valid filc umd (utemp_defs uf) (blocks _ _ _ _ L) -> stage_func md f doms = true.
Proof.
  intros filc drop umd uf f [ls InB OutB N K R P J D F C] md doms V.
  assert (H : Forall (fun b => exists qs,
    Forall (fun p => uvalid_inst filc umd (utemp_defs uf) (snd p) = true) qs /\
    b_insts b = flat_map (fun p => step_uinst filc (fst p) (snd p)) qs) (fn_blocks f)).
  { rewrite OutB,Forall_forall. intros db I. apply in_map_iff in I as (b & <- & B).
    exists (filter (fun p => negb (omit drop (snd p))) (rows b)). split.
    - apply Forall_forall. intros p I. apply filter_In in I as [I _]. exact (V _ _ B I).
    - cbn [dst_block b_insts]. exact (proj2 (retained_rows filc drop (rows b))). }
  unfold stage_func. rewrite (piz_func_evidence_pass _ _ _ _ _ H),(piz_func_limit_reads _ _ _ _ H),C. reflexivity.
Qed.

(** Preserving predecessors, temporary classes, and call signatures discharges
    each block check. *)
Local Lemma layout_valid_block : forall filc drop umd uf f (L : func_layout filc drop uf f) md,
  (forall n, func_sig n md = func_sig n (uskel_module umd)) ->
  (forall n, init_entry_named md n = init_entry_named (uskel_module umd) n) ->
  (forall n k, lookup n (utemp_defs uf) = Some k -> lookup n (temp_defs f) = Some k) ->
  (forall q k, In (q,k) (flat_map (fun b => flat_map (generated filc) (rows b)) (blocks _ _ _ _ L)) ->
    lookup q (temp_defs f) = Some k) ->
  forallb (uvalid_block filc umd uf (utemp_defs uf)) (ufn_blocks uf) = true ->
  forallb (valid_block md f (temp_defs f)) (fn_blocks f) = true.
Proof.
  intros filc drop umd uf f L md Sig Init Ext Fresh H.
  destruct (layout_cfg _ _ _ _ L) as [_ [Labels Edges]].
  destruct L as [ls InB OutB N K R P J D F C].
  rewrite OutB,forallb_forall. rewrite InB,forallb_forall in H.
  intros db I. apply in_map_iff in I as (b & <- & B).
  specialize (H _ (in_map src_block _ _ B)). unfold uvalid_block in H. unfold valid_block.
  rewrite <- (same_cfg_preds_of _ _ _ Labels Edges). cbn [src_block dst_block b_label b_phis b_insts b_jump
      ub_label ub_phis ub_insts ub_jump] in H |- *.
  repeat rewrite andb_true_iff in H. repeat rewrite andb_true_iff. destruct H as [[[[Ph Is] Jump] _] Nonempty].
  repeat split; auto.
  - rewrite forallb_forall in *. eauto using valid_phi_mono.
  - rewrite forallb_forall in Is |- *. intros i I. apply in_flat_map in I as (p & Ip & I).
    specialize (Is _ (in_map snd _ _ Ip)). unfold slice in I.
    destruct (omit drop (snd p)); [contradiction|].
    pose proof (step_uinst_valid_inst filc _ _ _ _ (snd p) (fst p) Sig Init Ext) as Step.
    assert (Q : filc = true -> uinst_is_access (snd p) = true ->
      lookup (fst p) (temp_defs f) = Some (uinst_proof_class (snd p))).
    { intros -> Access. apply Fresh. apply in_flat_map. exists b. split; auto.
      apply in_flat_map. exists p. split; auto. unfold generated; rewrite Access; now left. }
    specialize (Step Q Is). rewrite forallb_forall in Step. auto.
  - clear Fresh. rewrite Forall_forall in J. apply (proj2 (proj2 (J b B))).
    eapply valid_jump_mono with (f:=uskel_func uf); [symmetry; exact R|exact Labels|exact Ext|exact Jump].
Qed.

(** The unchanged graph supplies the dominator intervals for both ordinary
    validity and the unconditional stage check. *)
Local Lemma function_validity : forall filc drop umd uf f (L : func_layout filc drop uf f) md,
  (forall n, func_sig n md = func_sig n (uskel_module umd)) ->
  (forall n, init_entry_named md n = init_entry_named (uskel_module umd) n) ->
  uvalid_func filc umd uf = true ->
  valid_func md f = true /\
  exists doms, block_intervals (fn_blocks f) = Some doms /\ stage_func md f doms = true.
Proof.
  intros filc drop umd uf f L md Sig Init V.
  pose proof (layout_valid_rows _ _ _ _ _ L V) as RV.
  destruct (layout_cfg _ _ _ _ L) as (Labs & Labels & Edges).
  destruct (same_cfg_block_intervals _ _ Labels Edges) as [_ Cfg].
  pose proof V as H. unfold uvalid_func in H. cbv zeta in H. unfold valid_func. cbv zeta.
  rewrite <- Cfg. destruct (block_intervals (fn_blocks (uskel_func uf))) as [doms|] eqn:Intervals.
  2: { destruct (fn_blocks (uskel_func uf)); try rewrite Intervals in H; discriminate H. }
  pose proof (layout_stage _ _ _ _ _ L md doms RV) as Stage.
  destruct (fn_blocks (uskel_func uf)) as [|entry rest] eqn:Src; [discriminate|].
  unfold labels in Labels. rewrite Src in Labels. destruct (fn_blocks f) as [|entry' rest'] eqn:Dst;
    [discriminate Labels|]. cbn [map] in Labels. injection Labels as E _.
  rewrite Intervals in H. rewrite <- Cfg. repeat rewrite andb_true_iff in H. destruct H as [[[[[[[[[Link Ret] Ext] LabelsOk] Class] Entry] Proofs] Dom] Loc] Bs].
  assert (Unique : no_dups (map lab (blocks _ _ _ _ L)) = true) by (rewrite <- Labs; exact LabelsOk).
  destruct (layout_classes _ _ _ _ _ L V Class) as (Classes & Look & Fresh).
  pose proof (layout_valid_block _ _ _ _ _ L md Sig Init Look Fresh Bs) as Blocks.
  split; [|exists doms; auto]. repeat rewrite andb_true_iff. repeat split.
  - rewrite (same_linkage _ _ _ _ L). exact Link.
  - rewrite (same_ret _ _ _ _ L). exact Ret.
  - apply negb_true_iff. eapply layout_extended; [exact L|now apply negb_true_iff].
  - rewrite <- Dst. change (no_dups (labels f) = true). rewrite <- (proj1 (proj2 (layout_cfg _ _ _ _ L))). unfold labels. rewrite Src. exact LabelsOk.
  - exact Classes.
  - apply negb_true_iff in Entry. apply negb_true_iff.
    change (existsb (fun b => mem (b_label entry) (succ_labels (b_jump b))) (entry::rest) = false) in Entry.
    rewrite <- (exists_map' (mem (b_label entry)) (fun b => succ_labels (b_jump b))) in Entry.
    rewrite <- (exists_map' (mem (b_label entry')) (fun b => succ_labels (b_jump b))).
    rewrite <- Edges,<- E. exact Entry.
  - eapply layout_proof_classes; eauto.
  - eapply layout_dominate; eauto.
  - eapply layout_locals; eauto.
  - rewrite <- Dst. exact Blocks.
  - rewrite Stage,orb_true_r. reflexivity.
Qed.

(** ## Modules *)

(** Functions retain the declarations that other items use for type
    checking. Data and alias items keep their source order, so each
    symbol lookup still finds the same first declaration. *)

(** Functions carry a layout witness. Data objects and aliases keep every
    field. *)
Inductive item_layout filc drop : uitem -> item -> Prop :=
| layout_function : forall uf f, func_layout filc drop uf f -> item_layout filc drop (UIFunc uf) (IFunc f)
| layout_data : forall n lk a its, item_layout filc drop (UIData n lk a its) (IData n lk a its)
| layout_alias : forall n lk tg, item_layout filc drop (UIAlias n lk tg) (IAlias n lk tg).

(** The source judgment selects the validator for the kind of item being
    transformed. *)
Local Definition source_ok filc umd it :=
  match it with
  | UIFunc uf => uvalid_func filc umd uf = true
  | UIData n lk al its => valid_data (uskel_module umd) n lk al its = true
  | UIAlias n lk tg => valid_alias (uskel_module umd) n lk tg = true
  end.

(** A successful item decode identifies which source form the module pass must
    handle. *)
Local Lemma item_shape : forall t o, duitem t = Some o ->
  match o with
  | None => exists n records, t = TApp "context" [n;records]
  | Some (UIFunc uf) => exists n lk r ps bs, t = TApp "func" [n;lk;r;ps;bs] /\ dufunc n lk r ps bs = Some uf
  | Some (UIData n lk a its) => exists k ts, t = TApp "data" [n;k;TInt a;TList ts] /\
      dlinkage k = Some lk /\ map_option ddata_item ts = Some its
  | Some (UIAlias n lk tg) => t = TApp "alias" [n;lk;tg]
  end.
Proof.
  intros t o H. unfold duitem in H.
  repeat match type of H with
  | (match ?v with _ => _ end) = Some _ =>
    first [is_var v; destruct v; cbn iota in H; try discriminate H |
           destruct v eqn:?; cbn iota in H; try discriminate H]
  end; injection H as <-; cbn; eauto 8.
Qed.

(** A context record contributes no item to the decoded module. *)
Local Definition present {A} (o : option A) := match o with Some x => [x] | None => [] end.

(** The two decoders drop the same context records and pair up every remaining
    item in order. *)
Local Lemma decode_items : forall ts filc drop umd os out,
  map_option duitem ts = Some os -> Forall (source_ok filc umd) (flat_map present os) ->
  map_option (pizlonated_item filc drop) (filter (fun t => negb (is_context t)) ts) = Some out ->
  exists os', map_option ditem out = Some os' /\
    Forall2 (item_layout filc drop) (flat_map present os) (flat_map present os').
Proof.
  induction ts as [|t ts IH]; intros filc drop umd os out D V Run.
  - injection D as <-. injection Run as <-. exists []; split; [reflexivity|constructor].
  - cbn [map_option] in D. destruct (duitem t) as [o|] eqn:O; [|discriminate].
    destruct (map_option duitem ts) as [tail|] eqn:T; [|discriminate]. injection D as <-.
    pose proof (item_shape _ _ O) as Shape. destruct o as [it|].
    + inversion V as [|? ? Good Rest]; subst.
      assert (Keep : is_context t = false).
      { destruct it; cbn in Shape; [destruct Shape as (? & ? & ? & ? & ? & -> & _)|
          destruct Shape as (? & ? & -> & _)|subst t]; reflexivity. }
      cbn [filter] in Run. rewrite Keep in Run. cbn [negb map_option] in Run.
      destruct (pizlonated_item filc drop t) as [t'|] eqn:Item; [|discriminate].
      destruct (map_option _ (filter _ ts)) as [ts'|] eqn:E; [|discriminate]. injection Run as <-.
      destruct (IH _ _ _ _ _ eq_refl Rest E) as (os' & D & R).
      assert (One : exists it', ditem t' = Some (Some it') /\ item_layout filc drop it it').
      { destruct it as [uf|n lk a its|n lk tg].
        - destruct Shape as (n & lk & r & ps & bs & -> & U).
          destruct (decode_func_layout _ _ _ _ _ _ _ _ _ _ U Good Item) as (f & De & [L]).
          exists (IFunc f); split; auto. now constructor.
        - destruct Shape as (k & xs & -> & Lk & Ds). injection Item as <-.
          cbn [ditem]. rewrite Lk,Ds. eexists; split; [reflexivity|constructor].
        - cbn in Shape. subst t. injection Item as <-. eexists; split; [reflexivity|constructor]. }
      destruct One as (it' & Di & Rel). exists (Some it'::os'). cbn [map_option]. rewrite Di,D.
      split; [reflexivity|now constructor].
    + destruct Shape as (n & records & ->). cbn [filter is_context String.eqb Ascii.eqb Bool.eqb andb negb] in Run.
      exact (IH _ _ _ _ _ eq_refl V Run).
Qed.

(** The first matching function, data declaration, or initializer has the same
    public properties in both modules. *)
Local Lemma module_queries : forall filc drop us md,
  Forall2 (item_layout filc drop) us md -> forall n,
  func_sig n md = func_sig n (uskel_module us) /\
  init_entry_named md n = init_entry_named (uskel_module us) n /\
  first_func_linkage n md = first_func_linkage n (uskel_module us) /\
  first_data_linkage n md = first_data_linkage n (uskel_module us).
Proof.
  intros filc drop us md Rel n. induction Rel as [|u it us md One Rel IH]; [repeat split|].
  destruct IH as (Sig & Init & F & D). unfold init_entry_named in Init |- *.
  destruct One as [uf f L|g lk a its|g lk tg]; cbn [uskel_module map uskel_item func_sig existsb
    first_func_linkage first_data_linkage uskel_func fn_name fn_ret fn_linkage fn_params]; fold (uskel_module us).
  - rewrite (same_name _ _ _ _ L),(same_linkage _ _ _ _ L),(same_params _ _ _ _ L),(same_ret _ _ _ _ L),
      (layout_va _ _ _ _ L),Sig,Init,F,D. repeat split.
  - rewrite Sig,Init,F,D. repeat split.
  - rewrite Sig,Init,F,D. repeat split.
Qed.

(** The name checker inserts the same symbols into its set in the same order. *)
Local Lemma module_names : forall filc drop us md, Forall2 (item_layout filc drop) us md ->
  unique_names md = unique_names (uskel_module us).
Proof.
  intros filc drop us md Rel. unfold unique_names.
  match goal with |- context [fold_left ?ins _ _] =>
    enough (Eq : forall acc, fold_left ins md acc = fold_left ins (uskel_module us) acc) by (now rewrite Eq)
  end.
  induction Rel as [|u it us md One Rel IH]; intros acc; [reflexivity|].
  cbn [uskel_module map fold_left]; fold (uskel_module us); rewrite IH; f_equal.
  destruct acc as [seen|]; [|reflexivity]. destruct One as [uf f L| |]; try reflexivity.
  cbn [uskel_item Validate.defined_name uskel_func fn_name]; now rewrite (same_name _ _ _ _ L).
Qed.

(** Selecting the first definition of each function preserves every direct-
    call query used by aliases. *)
Local Lemma module_first_calls : forall filc drop us md, Forall2 (item_layout filc drop) us md ->
  forall seen n, let calls := fun it => match item_name it with
    | Some g => negb (name_eqb g n) && calls_global it n | None => false end in
    existsb calls (first_funcs seen md) = existsb calls (first_funcs seen (uskel_module us)).
Proof.
  intros filc drop us md Rel. induction Rel as [|u it us md One Rel IH]; intros seen n; [reflexivity|].
  cbv zeta in IH |- *. destruct One as [uf f L| |]; cbn [uskel_module map uskel_item first_funcs];
    fold (uskel_module us); try apply IH.
  rewrite (same_name _ _ _ _ L). cbn [uskel_func fn_name].
  destruct (mem (ufn_name uf) seen); [apply IH|]. cbn [existsb item_name].
  rewrite (layout_calls _ _ _ _ L), IH,(same_name _ _ _ _ L). reflexivity.
Qed.

(** A data initializer refers to the same local symbols, functions, and
    initialization entries after the pass. *)
Local Lemma module_data : forall filc drop us md, Forall2 (item_layout filc drop) us md ->
  forall n lk a its, valid_data md n lk a its = valid_data (uskel_module us) n lk a its.
Proof.
  intros filc drop us md Rel n lk a its. pose proof (module_queries _ _ _ _ Rel) as Q.
  unfold valid_data,data_names_ok,func_named,local_global.
  assert (Items : forallb (fun it => match it with Sym s _ => negb (init_entry_named md s) | _ => true end) its =
                  forallb (fun it => match it with Sym s _ => negb (init_entry_named (uskel_module us) s) | _ => true end) its).
  { apply forallb_same. intros it _. destruct it; try reflexivity. now rewrite (proj1 (proj2 (Q _))). }
  rewrite Items. destruct lk; try reflexivity.
  all: try (rewrite (proj1 (proj2 (proj2 (Q n)))), (proj2 (proj2 (proj2 (Q n)))); reflexivity).
  destruct its as [|it [|next rest]]; try reflexivity. destruct it; try reflexivity.
  now rewrite (proj1 (proj2 (proj2 (Q _)))).
Qed.

(** An alias retains its target linkage and the set of callers that can affect
    its validity. *)
Local Lemma module_alias : forall filc drop us md, Forall2 (item_layout filc drop) us md ->
  forall n lk tg, valid_alias md n lk tg = valid_alias (uskel_module us) n lk tg.
Proof.
  intros filc drop us md Rel n lk tg. pose proof (module_queries _ _ _ _ Rel) as Q.
  unfold valid_alias,func_named,data_named. rewrite (module_first_calls _ _ _ _ Rel [] n).
  repeat match goal with |- context [first_func_linkage ?g md] => rewrite (proj1 (proj2 (proj2 (Q g))))
                       | |- context [first_data_linkage ?g md] => rewrite (proj2 (proj2 (proj2 (Q g)))) end.
  reflexivity.
Qed.

(** Every output function passes the checked-stage tests, including
    functions in modules whose vocabulary leaves the stage flag clear. *)
Theorem pizlonate_module_stage_valid : forall m_in m_out,
  valid_unchecked_module m_in ->
  Pizlonate.pizlonate_module m_in = Some m_out ->
  exists md,
    Transport.decode_module m_out = Some md /\
    Validate.valid md = Some true /\
    Forall (fun it =>
              match it with
              | IFunc f =>
                  exists doms,
                    Cfg.block_intervals (fn_blocks f) = Some doms /\
                    Validate.stage_func md f doms = true
              | _ => True
              end) md.
Proof.
  intros m_in m_out (ts & us & -> & D & Names & V) Run.
  cbn [decode_umodule] in D. destruct (map_option duitem ts) as [os|] eqn:Os; [|discriminate].
  injection D as <-. fold (@present uitem) in *. set (us := flat_map present os) in *.
  cbn [pizlonate_module String.eqb Ascii.eqb Bool.eqb andb] in Run.
  set (filc := module_filc ts) in *. set (drop := negb (Pizlonate.module_checked ts)) in *.
  destruct (map_option (pizlonated_item filc drop) (filter _ ts)) as [out|] eqn:Out; [|discriminate].
  injection Run as <-. change (Forall (source_ok filc us) us) in V.
  destruct (decode_items _ _ _ _ _ _ Os V Out) as (os' & D & Rel). fold us in Rel.
  set (md := flat_map present os') in *. exists md. cbn [decode_module]. rewrite D. split; [reflexivity|].
  pose proof (module_names _ _ _ _ Rel) as Unique. rewrite Names in Unique.
  pose proof (module_queries _ _ _ _ Rel) as Q.
  assert (Item : forall u it, item_layout filc drop u it -> source_ok filc us u ->
    match it with
    | IFunc f => valid_func md f = true /\ exists doms, block_intervals (fn_blocks f) = Some doms /\ stage_func md f doms = true
    | IData n lk a its => valid_data md n lk a its = true
    | IAlias n lk tg => valid_alias md n lk tg = true
    | IOutside _ _ => False end).
  { intros u it One Good. destruct One as [uf f L|n lk a its|n lk tg].
    - eapply function_validity; [exact L|intro; apply Q|intro; apply Q|exact Good].
    - rewrite (module_data _ _ _ _ Rel); exact Good.
    - rewrite (module_alias _ _ _ _ Rel); exact Good. }
  assert (All : forall it, In it md ->
    match it with
    | IFunc f => valid_func md f = true /\ exists doms, block_intervals (fn_blocks f) = Some doms /\ stage_func md f doms = true
    | IData n lk a its => valid_data md n lk a its = true
    | IAlias n lk tg => valid_alias md n lk tg = true
    | IOutside _ _ => False end).
  { intros it I. enough (H : exists u, In u us /\ item_layout filc drop u it).
    { destruct H as (u & U & R). apply (Item u it R). rewrite Forall_forall in V. auto. }
    clear -Rel I. induction Rel; [contradiction|]. destruct I as [<-|I]; [eauto using in_eq|].
    destruct (IHRel I) as (u & U & R). eauto using in_cons. }
  unfold Validate.valid, valid_items. rewrite Unique. cbn [andb].
  assert (NoOutside : existsb (fun it => match it with IOutside _ _ => true | _ => false end) md = false).
  { apply no_exists. intros it I. specialize (All _ I). destruct it; auto; contradiction. }
  rewrite NoOutside. split.
  - f_equal. apply forallb_forall. intros it I. specialize (All _ I). destruct it; tauto.
  - apply Forall_forall. intros it I. specialize (All _ I). destruct it; tauto.
Qed.

(** Successful pizlonation produces a module accepted by the typed validator. *)
Theorem pizlonate_module_valid : forall m_in m_out,
  valid_unchecked_module m_in ->
  Pizlonate.pizlonate_module m_in = Some m_out ->
  exists md,
    Transport.decode_module m_out = Some md /\
    Validate.valid md = Some true.
Proof.
  intros m_in m_out H Run. destruct (pizlonate_module_stage_valid _ _ H Run) as (md & D & V & S).
  exists md; auto.
Qed.

(** A caller that observes the checked flag obtains both conjuncts of the checked-module predicate. *)
Corollary pizlonate_module_checked_valid : forall m_in m_out md,
  valid_unchecked_module m_in ->
  Pizlonate.pizlonate_module m_in = Some m_out ->
  Transport.decode_module m_out = Some md ->
  Validate.module_checked md = true ->
  Validate.valid md = Some true /\ Validate.module_checked md = true.
Proof.
  intros m_in m_out md H Run D Flag. destruct (pizlonate_module_valid _ _ H Run) as (m & E & V).
  rewrite D in E. injection E as <-. auto.
Qed.

(** ## Sanity examples *)

(** The loop uses a pointer parameter whose name the generator must
    skip. A separate integer function exercises the pass in plain mode. *)

Local Definition tmp_atom (s : string) := Pizlonate.tmp (TAtom s).
Local Definition example_block (s : string) ins j := TApp "block" [TAtom s; TList []; TList ins; j].

(** The entry allocates a stack slot. Each iteration loads a word at a
    fixed offset from the pointer and branches on the value read back from the slot. *)
Definition example_filc_loop_module :=
  TApp "module" [TList [TApp "func" [TAtom "loop"; TAtom "export"; TAtom "w";
    TList [TApp "param" [TAtom "p"; tmp_atom "chk0"]];
    TList [
      example_block "entry" [TApp "local_alloc" [TAtom "slot"; TInt 4]]
        (TApp "goto" [TAtom "header"]);
      example_block "header" [
        TApp "let" [tmp_atom "address"; TAtom "p"; TAtom "add";
                    TList [tmp_atom "chk0"; TApp "const" [TInt 4]]];
        TApp "let" [tmp_atom "word"; TAtom "w"; TApp "load" [TAtom "sw"]; TList [tmp_atom "address"]];
        TApp "local_store" [TAtom "w"; tmp_atom "word"; TAtom "slot"; TInt 0];
        TApp "local_load" [tmp_atom "again"; TAtom "w"; TAtom "sw"; TAtom "slot"; TInt 0]]
        (TApp "branch" [tmp_atom "again"; TAtom "header"; TAtom "exit"]);
      example_block "exit" [] (TApp "ret" [tmp_atom "again"])]]]].

(** The unchecked validator accepts the loop and its local accesses. *)
Example example_filc_loop_valid_unchecked : valid_unchecked_module example_filc_loop_module.
Proof.
  do 2 eexists. split; [reflexivity|]. split; [vm_compute; reflexivity|].
  split; [reflexivity|]. constructor; [vm_compute; reflexivity|constructor].
Qed.

(** The transformed loop satisfies module validity and sets the checked flag. *)
Example example_filc_loop_pizlonates_valid : exists m_out md,
  Pizlonate.pizlonate_module example_filc_loop_module = Some m_out /\
  Transport.decode_module m_out = Some md /\ Validate.valid md = Some true /\
  Validate.module_checked md = true.
Proof.
  let out := eval vm_compute in (Pizlonate.pizlonate_module example_filc_loop_module) in
  lazymatch out with Some ?m => exists m; assert (Run : Pizlonate.pizlonate_module example_filc_loop_module = Some m)
    by reflexivity end.
  destruct (pizlonate_module_valid _ _ example_filc_loop_valid_unchecked Run) as (md & D & V).
  exists md. split; [exact Run|]. split; [exact D|]. split; [exact V|].
  vm_compute in D. injection D as <-. reflexivity.
Qed.

(** The plain function returns the sum of two words. *)
Definition example_plain_module :=
  TApp "module" [TList [TApp "func" [TAtom "sum"; TAtom "local"; TAtom "w";
    TList [TApp "param" [TAtom "w"; tmp_atom "x"]; TApp "param" [TAtom "w"; tmp_atom "y"]];
    TList [example_block "entry"
      [TApp "let" [tmp_atom "z"; TAtom "w"; TAtom "add"; TList [tmp_atom "x"; tmp_atom "y"]]]
      (TApp "ret" [tmp_atom "z"])]]]].

(** The mode detector selects plain mode for the integer function. *)
Example example_plain_mode :
  match example_plain_module with TApp "module" [TList items] => Pizlonate.module_filc items
                                 | _ => true end = false.
Proof. reflexivity. Qed.

(** The unchecked validator accepts the plain module. *)
Example example_plain_valid_unchecked : valid_unchecked_module example_plain_module.
Proof.
  do 2 eexists. split; [reflexivity|]. split; [vm_compute; reflexivity|].
  split; [reflexivity|]. constructor; [vm_compute; reflexivity|constructor].
Qed.
