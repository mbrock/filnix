(** C strings in the program logic of Logic.v, and the triples of the
    libc string calls derived from [[campaign|Campaign]] 4's contracts.

    [string] p b reg bytes owns a C string: the life of the object b
    that p's capability names, read-write or read-only, and its bytes
    from p's offset through the terminating NUL ([byte_ps]). Owning it
    in an interpreted state gives the contracts' readings of a string,
    [terminated_length] and [c_string] ([string_facts]). One byte of it
    can be lent out to a load ([string_byte]).

    The triples are each contract's precondition read from owned
    pieces, and its postcondition handed back as owned pieces and
    bound results:
    - [wp_strlen] and [wp_strchr], from [strlen_contract] and
      [strchr_contract]: pure calls, which change no memory and no
      world ([pure_return]), so the state interpretation holds again
      with the same ghost heap, over any registry and world;
    - [wp_puts], from [puts_contract]: a call that writes its world's
      roots and may allocate, under the world interpretation
      [stdio_wi]: puts's rep and readiness, and the world's writable
      roots apart from the program's live objects. After a return,
      the frame for external calls (Logic.v's [prefix_agrees]) keeps
      the program's pieces and puts's prefix the world
      ([puts_return_frame]).
    Each triple is stated at any call site, so a program uses it as a
    rule. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Byte pieces *)

(** The pieces of the bytes xs from offset o of the object b. *)
Definition byte_ps (b o : Z) (xs : list Z) : list (piece * pval) :=
  zip_with (fun i x => (PByte b i, VByte x)) (seqZ o (Z.of_nat (length xs))) xs.

(** The first byte's piece, then the rest's. *)
Lemma byte_ps_cons b o x xs : byte_ps b o (x :: xs) = (PByte b o, VByte x) :: byte_ps b (o + 1) xs.
Proof.
  unfold byte_ps. cbn [length]. rewrite Nat2Z.inj_succ seqZ_cons; [|lia].
  rewrite Z.pred_succ. reflexivity.
Qed.

(** The i-th piece is the i-th byte's. *)
Lemma byte_ps_lookup b o xs i x :
  xs !! i = Some x -> byte_ps b o xs !! i = Some (PByte b (o + Z.of_nat i), VByte x).
Proof.
  revert o i. induction xs as [|y xs IH]; intros o i H; [discriminate|].
  rewrite byte_ps_cons. destruct i as [|i]; cbn in H |- *.
  - injection H as ->. rewrite Z.add_0_r. reflexivity.
  - rewrite (IH (o + 1) i H). do 3 f_equal. lia.
Qed.

(** Where the pieces of xs from offset o of the live object b agree,
    each byte is in the object and holds its value. *)
Lemma byte_ps_agree m b reg o xs i x :
  live_at m b reg -> all_agree m (byte_ps b o xs) -> xs !! i = Some x ->
  m_bytes m (b + (o + Z.of_nat i)) = x /\ 0 <= o + Z.of_nat i /\ b + (o + Z.of_nat i) < r_end reg.
Proof.
  intros [E Lv] Ha Hx.
  pose proof (all_agree_elem _ _ _ _ Ha (list_elem_of_lookup_2 _ _ _ (byte_ps_lookup b o xs i x Hx)))
    as [_ Hin].
  destruct (Hin reg E Lv) as (Ho & He & Hv). auto.
Qed.

(** The bytes, nonzero, followed by a NUL, as the memory holds them
    from a, are a [string_at] a. *)
Lemma string_at_of m a bytes :
  Forall (fun x => 0 < x < 256) bytes ->
  (forall i x, (bytes ++ [0]) !! i = Some x -> m_bytes m (a + Z.of_nat i) = x) ->
  string_at m a bytes.
Proof.
  revert a. induction bytes as [|y bytes IH]; intros a Hf Hb.
  - cbn. rewrite <- (Z.add_0_r a). exact (Hb 0%nat 0 eq_refl).
  - apply Forall_cons_1 in Hf as [Hy Hf]. cbn. split; [exact Hy|]. split.
    + rewrite <- (Z.add_0_r a). exact (Hb 0%nat y eq_refl).
    + apply IH; [exact Hf|]. intros i x Hx.
      replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. apply Hb. exact Hx.
Qed.

(** The pieces of xs ++ ys are xs's, then ys's after them. *)
Lemma byte_ps_app b o xs ys :
  byte_ps b o (xs ++ ys) = byte_ps b o xs ++ byte_ps b (o + Z.of_nat (length xs)) ys.
Proof.
  revert o. induction xs as [|x xs IH]; intros o; [cbn; rewrite Z.add_0_r; reflexivity|].
  cbn [app]. rewrite !byte_ps_cons IH. cbn [app length].
  replace (o + Z.of_nat (S (length xs))) with (o + 1 + Z.of_nat (length xs)) by lia. reflexivity.
Qed.

(** The pieces of xs are byte pieces at the offsets from o. *)
Lemma byte_ps_keys b o xs : (byte_ps b o xs).*1 = PByte b <$> seqZ o (Z.of_nat (length xs)).
Proof.
  revert o. induction xs as [|x xs IH]; intros o; [reflexivity|].
  rewrite byte_ps_cons. cbn [fmap list_fmap fst]. rewrite IH.
  cbn [length]. rewrite Nat2Z.inj_succ (seqZ_cons o); [|lia]. rewrite Z.pred_succ. reflexivity.
Qed.

(** ## Strings *)

(** The shape of a C string at p with contents bytes in the object b
    with the region reg: p's capability names b, read-write or
    read-only, at a positive base; the bytes and their NUL lie in the
    region, which ends within the address space; every byte is
    nonzero. *)
Definition string_ok (p : ptr) (b : Z) (reg : region) (bytes : list Z) : Prop :=
  (ptr_cap p = Obj b \/ ptr_cap p = Ro b) /\ 0 < b /\ b <= ptr_addr p /\
  ptr_addr p + Z.of_nat (length bytes) + 1 <= r_end reg /\ r_end reg <= 2 ^ 48 /\
  Forall (fun x => 0 < x < 256) bytes.

(** The pieces of the string: its object's life and its bytes from p's
    offset, NUL included. *)
Definition string_ps (p : ptr) (b : Z) (reg : region) (bytes : list Z) : list (piece * pval) :=
  (PLive b, VLive reg) :: byte_ps b (ptr_addr p - b) (bytes ++ [0]).

(** Where the string's pieces agree, the memory holds its bytes and
    NUL from p. *)
Lemma string_bytes m p b reg bytes :
  string_ok p b reg bytes -> all_agree m (string_ps p b reg bytes) ->
  forall i x, (bytes ++ [0]) !! i = Some x -> m_bytes m (ptr_addr p + Z.of_nat i) = x.
Proof.
  intros _ [Hl Ha] i x Hx. cbn [fst snd agree_piece] in Hl.
  destruct (byte_ps_agree _ _ _ _ _ _ _ Hl Ha Hx) as [Hv _].
  replace (ptr_addr p + Z.of_nat i) with (b + (ptr_addr p - b + Z.of_nat i)) by lia. exact Hv.
Qed.

(** Where the string's pieces agree, p points at a [terminated_length]
    string of its length: Campaign 4's reading of a string. *)
Lemma string_terminated m p b reg bytes :
  string_ok p b reg bytes -> all_agree m (string_ps p b reg bytes) ->
  terminated_length m p (Z.of_nat (length bytes)).
Proof.
  intros Hok Ha. pose proof (string_bytes m p b reg bytes Hok Ha) as Hb.
  destruct Hok as (Hc & H0 & H1 & H2 & H3 & Hf). destruct Ha as [[E Lv] _].
  assert (Hn : Z.of_nat (length bytes) < 2 ^ 64 - 1) by lia.
  split; [|exact Hn]. split; [lia|]. split; [lia|]. split; [exists b, reg; auto|].
  replace (Z.of_nat (length bytes) <? 2 ^ 64 - 1) with true by (symmetry; apply Z.ltb_lt; exact Hn).
  split; [apply (access_read _ b reg); [exact Hc | exact E | lia | lia | apply Z.mod_1_r]|]. split.
  - intros i Hi. destruct (lookup_lt_is_Some_2 bytes (Z.to_nat i) ltac:(lia)) as [x Hx].
    rewrite <- (Z2Nat.id i) by lia. rewrite (Hb (Z.to_nat i) x); [|by apply lookup_app_l_Some].
    exact (Forall_lookup_1 _ _ _ _ Hf Hx).
  - intros _. apply (Hb (length bytes) 0). rewrite lookup_app_r; [|lia].
    rewrite Nat.sub_diag. reflexivity.
Qed.

(** Where the string's pieces agree, p points at a [c_string] with
    contents bytes: puts's reading of a string. *)
Lemma string_c_string m p b reg bytes :
  string_ok p b reg bytes -> all_agree m (string_ps p b reg bytes) -> c_string m p bytes.
Proof.
  intros Hok Ha. pose proof (string_bytes m p b reg bytes Hok Ha) as Hb.
  pose proof Hok as (Hc & _ & H1 & H2 & _ & Hf). destruct Ha as [[E _] _]. split.
  - apply (access_read _ b reg); [exact Hc | exact E | lia | lia | apply Z.mod_1_r].
  - apply string_at_of; [exact Hf | exact Hb].
Qed.

(** No piece of a string is listed twice. *)
Lemma string_ps_nodup p b reg bytes : NoDup (string_ps p b reg bytes).*1.
Proof.
  unfold string_ps. cbn [fmap list_fmap fst]. rewrite byte_ps_keys. apply NoDup_cons_2.
  - rewrite list_elem_of_fmap. intros (o & E & _). discriminate E.
  - apply NoDup_fmap_2; [intros x y E; injection E as ->; reflexivity | apply NoDup_seqZ].
Qed.

(** Every piece of a string is of its object. *)
Lemma string_ps_id p b reg bytes l v : (l, v) ∈ string_ps p b reg bytes -> piece_id l = b.
Proof.
  unfold string_ps. rewrite elem_of_cons. intros [H|H]; [injection H as -> _; reflexivity|].
  apply (list_elem_of_fmap_2 fst) in H. cbn [fst] in H. rewrite byte_ps_keys in H.
  apply list_elem_of_fmap in H as (o & -> & _). reflexivity.
Qed.

(** The suffix of the string p from its i-th byte, at q: the pieces
    of the string are its life, the bytes before q, and the pieces of
    the suffix's bytes, which are the string at q's. *)
Lemma string_ps_suffix p b reg bytes i :
  (i <= length bytes)%nat ->
  let q := mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p) in
  string_ps p b reg bytes =
    (PLive b, VLive reg) :: byte_ps b (ptr_addr p - b) (take i bytes) ++
      byte_ps b (ptr_addr q - b) (drop i bytes ++ [0]) /\
  string_ps q b reg (drop i bytes) = (PLive b, VLive reg) :: byte_ps b (ptr_addr q - b) (drop i bytes ++ [0]).
Proof.
  intros Hi q. split; [|reflexivity]. unfold string_ps. f_equal.
  rewrite <- (take_drop i bytes) at 1. rewrite <- app_assoc, byte_ps_app, length_take.
  cbn [ptr_addr q]. replace (ptr_addr p - b + Z.of_nat (Nat.min i (length bytes)))
    with (ptr_addr p + Z.of_nat i - b) by lia. reflexivity.
Qed.

(** The suffix of a string from a byte before its NUL is a string. *)
Lemma string_ok_suffix p b reg bytes i :
  (i <= length bytes)%nat -> string_ok p b reg bytes ->
  string_ok (mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p)) b reg (drop i bytes).
Proof.
  intros Hi (Hc & H0 & H1 & H2 & H3 & Hf). unfold string_ok. cbn [ptr_addr ptr_cap]. rewrite length_drop.
  split; [exact Hc|]. split; [exact H0|]. split; [lia|]. split; [lia|]. split; [exact H3|].
  apply Forall_drop. exact Hf.
Qed.

(** ## The stdio world *)

(** The world interpretation of a program that calls puts: puts's
    representation rep and [stdio_ready] of the world w in m, and the
    world's writable roots apart from the live objects owning pieces
    of the ghost heap h. *)
Definition stdio_wi (rep : mem -> stdio_world -> Prop) (m : mem) (w : stdio_world)
    (h : gmap piece pval) : Prop :=
  rep m w /\ stdio_ready m w /\ roots_apart (stdio_roots w) h m.

(** C strings and the string calls over any [[runtime]] R. *)
Module StringLogic (R : Runtime).
Module LG := Logic R.
Module L := LG.L.
Import L LG.

(** A safepoint keeps [stdio_wi] where it keeps rep and readiness: the
    roots stay apart since no region changes ([collector_live]). *)
Lemma stdio_wi_safepoint (rep : mem -> stdio_world -> Prop) :
  (forall s m s' m' w, R.safepoint s m s' m' -> rep m w -> stdio_ready m w ->
     rep m' w /\ stdio_ready m' w) ->
  SafepointStable (stdio_wi rep).
Proof.
  intros Hst. split. intros s m s' m' w h Hsp (Hr & Hw & Ha).
  destruct (Hst _ _ _ _ _ Hsp Hr Hw) as [Hr' Hw'].
  split; [exact Hr'|]. split; [exact Hw'|].
  intros sp a Hin Hs (l & v & reg & Hl & [E Hlive] & Hb). apply (Ha sp a Hin Hs).
  rewrite (R.collector_live _ _ _ _ Hsp) in E. exists l, v, reg. split; [exact Hl|]. split; [|exact Hb].
  split; [exact E | exact Hlive].
Qed.

(** A puts call returns one int. *)
Lemma puts_returns_int rep requests r args xs s m w trace values s' m' w' :
  M.E.invoke (puts_contract rep requests) r args xs s m w trace (CallReturn values) s' m' w' ->
  exists n, values = [WInt n].
Proof.
  intros Hi. remember (CallReturn values) as en eqn:Een.
  destruct Hi as [? ? ? ? ? ? _ _ _ Hp | ? ? ? ? ? ? _ _ _ _ _]; [|discriminate Een].
  destruct Hp as (p & bytes & acc & tail & n & _ & _ & _ & _ & _ & Hend & _).
  subst. injection Hend as ->. eauto.
Qed.

(** After a puts call that returns, from a state interpreted with the
    ghost heap h, the state is interpreted with h again: puts's prefix
    keeps the runtime ready, the frame keeps h agreeing and live
    objects apart, and the prefix gives rep and readiness of the new
    world, whose roots it delegated from the old roots and its born
    objects, so they stay apart from h. *)
Lemma puts_return_frame rep requests r args xs s m w trace values s' m' w' h :
  M.E.invoke (puts_contract rep requests) r args xs s m w trace (CallReturn values) s' m' w' ->
  agrees m h -> live_disjoint m -> R.ready s m -> stdio_wi rep m w h ->
  agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ stdio_wi rep m' w' h.
Proof.
  intros Hi Ha Hd Hr (Hrep & Hw & Hapart).
  destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hi) as (born & Hp).
  destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' _].
  destruct (prefix_agrees _ _ _ _ _ _ _ _ _ _ _ h Hp Hr Hd Ha Hapart ltac:(intros ? ? ? []))
    as (Ha' & Hd' & Hb & Hapart').
  destruct Hp as [_ (Hrep' & Hw' & Hdel & _)].
  change (roots_apart (stdio_roots w) h m') in Hapart'.
  split; [exact Ha'|]. split; [exact Hd'|]. split; [exact Hr'|]. split; [exact Hrep'|]. split; [exact Hw'|].
  exact (delegates_apart _ _ _ _ h Hdel Hapart' Hb Hd').
Qed.

Section strings.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** [string] p b reg bytes: owning the C string at p with contents
    bytes, in the object b with the region reg: its life and its bytes
    through the NUL, of the shape [string_ok]. *)
Definition string (p : ptr) (b : Z) (reg : region) (bytes : list Z) : iProp Σ :=
  ⌜string_ok p b reg bytes⌝ ∗ pts (string_ps p b reg bytes).

(** Owning a string in an interpreted state, p points there at a
    [terminated_length] string of its length and at a [c_string]. *)
Lemma string_facts {world : Type} (wi : mem -> world -> gmap piece pval -> Prop) σ p b reg bytes :
  heap_interp wi σ -∗ string p b reg bytes -∗
  ⌜terminated_length (ls_mem σ) p (Z.of_nat (length bytes)) /\ c_string (ls_mem σ) p bytes⌝.
Proof.
  iIntros "Hσ [%Hok Hs]". iDestruct (pts_facts with "Hσ Hs") as %(Ha & _). iPureIntro.
  split; [exact (string_terminated _ _ _ _ _ Hok Ha) | exact (string_c_string _ _ _ _ _ Hok Ha)].
Qed.

(** The string lends its object's life and its i-th byte, x, the NUL
    for i its length, and takes them back. *)
Lemma string_byte p b reg bytes i x :
  (bytes ++ [0]) !! i = Some x ->
  string p b reg bytes -∗
  ⌜string_ok p b reg bytes⌝ ∗ live b reg ∗ ibyte b (ptr_addr p - b + Z.of_nat i) x ∗
  (live b reg -∗ ibyte b (ptr_addr p - b + Z.of_nat i) x -∗ string p b reg bytes).
Proof.
  intros Hx. iIntros "[%Hok [Hl Hs]]". rewrite /live /ibyte /pts /=.
  iDestruct (big_sepL_lookup_acc with "Hs") as "[Hb Hk]"; [exact (byte_ps_lookup _ _ _ _ _ Hx)|].
  iSplit; [done|]. iSplitL "Hl"; [iFrame|]. iSplitL "Hb"; [iFrame|].
  iIntros "[Hl _] [Hb _]". iSplit; [done|]. iFrame "Hl". iApply ("Hk" with "Hb").
Qed.

(** A string lends the suffix from its i-th byte, before its NUL or
    at it, as the string at q, and takes it back. *)
Lemma string_suffix p b reg bytes i :
  (i <= length bytes)%nat ->
  string p b reg bytes -∗
  string (mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p)) b reg (drop i bytes) ∗
  (string (mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p)) b reg (drop i bytes) -∗ string p b reg bytes).
Proof.
  intros Hi. destruct (string_ps_suffix p b reg bytes i Hi) as [Ep Eq].
  iIntros "[%Hok Hs]". rewrite /string Ep Eq /pts big_sepL_cons big_sepL_app.
  iDestruct "Hs" as "(Hl & Hpre & Hsuf)". iSplitL "Hl Hsuf".
  - iSplit; [iPureIntro; exact (string_ok_suffix _ _ _ _ _ Hi Hok)|]. rewrite big_sepL_cons. iFrame.
  - iIntros "[_ Hq]". rewrite big_sepL_cons. iDestruct "Hq" as "[Hl Hsuf]". iSplit; [done|]. iFrame.
Qed.

(** Where the string's pieces agree, p points at a [bounded_length]
    string for any bound n: its length, or n if that is shorter.
    Campaign 4's reading of a string for strncmp. *)
Lemma string_bounded m p b reg bytes n :
  string_ok p b reg bytes -> all_agree m (string_ps p b reg bytes) -> 0 <= n < 2 ^ 64 ->
  bounded_length m p n (Z.min (Z.of_nat (length bytes)) n).
Proof.
  intros Hok Ha Hn. pose proof (string_bytes m p b reg bytes Hok Ha) as Hb.
  destruct Hok as (Hc & H0 & H1 & H2 & H3 & Hf). destruct Ha as [[E Lv] _].
  split; [exact Hn|]. split; [lia|]. split; [exists b, reg; auto|]. split.
  - apply (access_read _ b reg); [exact Hc | exact E | lia | | apply Z.mod_1_r].
    destruct (Z.min _ n <? n); lia.
  - split.
    + intros i Hi. destruct (lookup_lt_is_Some_2 bytes (Z.to_nat i) ltac:(lia)) as [x Hx].
      rewrite <- (Z2Nat.id i) by lia. rewrite (Hb (Z.to_nat i) x); [|by apply lookup_app_l_Some].
      exact (Forall_lookup_1 _ _ _ _ Hf Hx).
    + intros Hk. assert (Z.min (Z.of_nat (length bytes)) n = Z.of_nat (length bytes)) as -> by lia.
      apply (Hb (length bytes) 0). rewrite lookup_app_r; [|lia]. rewrite Nat.sub_diag. reflexivity.
Qed.

(** ## The calls *)

Section calls.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The Iris instance of the registry and wi. *)
Local Instance string_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.

(** The expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A call that changes no memory and no world, from a ready runtime,
    keeps the state interpretation, with the same ghost heap, whatever
    the runtime state after it. *)
Lemma pure_return {spec : contract world} r args xs (σ : lstate world) trace ending s' :
  M.E.invoke spec r args xs (ls_rt σ) (ls_mem σ) (ls_world σ) trace ending s' (ls_mem σ) (ls_world σ) ->
  heap_interp wi σ -∗ heap_interp wi (mkLstate (ls_mem σ) s' (ls_fuel σ) (ls_world σ)).
Proof.
  intros Hi. iIntros "(%h & Hh & %Hf)". destruct Hf as (Ha & Hd & Hr & Hw).
  destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hi) as (born & Hp).
  destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' _].
  iExists h. iFrame "Hh". iPureIntro. cbn. auto.
Qed.

(** strlen's triple, from [strlen_contract]: owning the string at p,
    which v reads as, the call binds d to its length. *)
Lemma wp_strlen f e ls lab d v rest j p b reg bytes Φ :
  registry (TAtom "strlen") = Some (strlen_contract world) ->
  find_fn ge (TAtom "strlen") = None -> lookup (TAtom "strlen") (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr p) ->
  string p b reg bytes -∗
  ▷ (string p b reg bytes -∗
     WP (ERun (mkFrame f (put d (WInt (Z.of_nat (length bytes))) e) ls None (Exec lab rest j)) : sexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d L) (Global (TAtom "strlen")) [Arg P v] :: rest) j)) : sexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hv. iIntros "Hs HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (strlen_contract world) [WPtr p] (string p b reg bytes)
            with "Hs [HK]"); [done | done | done | done | cbn [map_option]; rewrite Hv; done | | |].
  - split; [right; eexists; reflexivity | eexists; reflexivity].
  - iIntros (σ) "Hσ Hs". iDestruct (string_facts with "Hσ Hs") as %[Ht _]. iPureIntro.
    exists p, (Z.of_nat (length bytes)). auto.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "Hσ Hs".
    iDestruct (string_facts with "Hσ Hs") as %[Ht _].
    destruct (M.E.strlen_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & -> & p' & k & Hx & Hk & He). injection Hx as <-. injection He as ->.
    rewrite (terminated_length_unique _ _ _ _ Hk Ht).
    iDestruct (pure_return with "Hσ") as "Hσ"; [exact Hinv|]. destruct σ as [m s fuel w]. iModIntro.
    iExists _. iSplit.
    + iPureIntro. cbn. rewrite Z.mod_small; [reflexivity|]. destruct Ht as [_ ?]. lia.
    + iFrame "Hσ". iApply ("HK" with "Hs").
Qed.

(** What strchr finds in the string p with contents bytes for the int
    c, whose low byte is not the NUL: the first byte equal to it, at
    offset i, with p's capability, or null if there is none. *)
Definition strchr_found (p : ptr) (bytes : list Z) (c : Z) (q : ptr) : Prop :=
  (exists i x, bytes !! i = Some x /\ x = c mod 256 /\
     (forall i' x', (i' < i)%nat -> bytes !! i' = Some x' -> x' <> c mod 256) /\
     q = mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p)) \/
  ((forall i' x', bytes !! i' = Some x' -> x' <> c mod 256) /\ q = mkPtr 0 CNone).

(** strchr's triple, from [strchr_contract]: owning the string at p,
    which v reads as, the call binds d to what it finds of the int c,
    which w reads as. *)
Lemma wp_strchr f e ls lab d v w rest j p b reg bytes c Φ :
  registry (TAtom "strchr") = Some (strchr_contract world) ->
  find_fn ge (TAtom "strchr") = None -> lookup (TAtom "strchr") (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr p) -> arg_x ge e (Arg W w) = Some (WInt c) ->
  0 <= c < 2 ^ 32 -> c mod 256 <> 0 ->
  string p b reg bytes -∗
  ▷ (∀ q, ⌜strchr_found p bytes c q⌝ -∗ string p b reg bytes -∗
     WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec lab rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "strchr")) [Arg P v; Arg W w] :: rest) j))
        : sexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hv Hw Hc Hnz. iIntros "Hs HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (strchr_contract world) [WPtr p; WInt c]
            (string p b reg bytes) with "Hs [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hv Hw; done | | |].
  - split; [right; eexists; reflexivity | do 2 eexists; reflexivity].
  - iIntros (σ) "Hσ Hs". iDestruct (string_facts with "Hσ Hs") as %[Ht _]. iPureIntro.
    exists p, c, (Z.of_nat (length bytes)). auto.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "Hσ Hs".
    iDestruct "Hs" as "[%Hok Hs]".
    iDestruct (pts_facts with "Hσ Hs") as %(Ha & _).
    pose proof (string_terminated _ _ _ _ _ Hok Ha) as Ht.
    pose proof (string_bytes _ _ _ _ _ Hok Ha) as Hb.
    destruct (M.E.strchr_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & -> & p' & c' & q & Hx & _ & (k & Hk & Hq) & He). injection Hx as <- <-.
    injection He as ->. rewrite (terminated_length_unique _ _ _ _ Hk Ht) in Hq.
    iDestruct (pure_return with "Hσ") as "Hσ"; [exact Hinv|]. destruct σ as [m s fuel w0]. iModIntro.
    iExists _. iSplit; [iPureIntro; reflexivity|]. iFrame "Hσ".
    iApply ("HK" with "[%] [Hs]"); [|by iSplit].
    cbn [ls_mem] in Hb. destruct Hq as [(i & Hi & Hv' & Hbefore & ->) | (Hnone & ->)].
    + assert (Hil : (Z.to_nat i < length bytes)%nat).
      { destruct (decide (Z.to_nat i = length bytes)) as [Heq|Hne]; [|lia]. exfalso. apply Hnz.
        rewrite <- Hv'. rewrite <- (Z2Nat.id i) by lia. rewrite Heq. apply (Hb (length bytes) 0).
        rewrite lookup_app_r; [|lia]. rewrite Nat.sub_diag. reflexivity. }
      destruct (lookup_lt_is_Some_2 bytes (Z.to_nat i) Hil) as [x Hx]. left.
      exists (Z.to_nat i), x. split; [exact Hx|]. split.
      * rewrite <- Hv'. rewrite <- (Z2Nat.id i) at 1 by lia. symmetry. apply Hb.
        by apply lookup_app_l_Some.
      * split; [|rewrite Z2Nat.id; [reflexivity | lia]].
        intros i' x' Hlt Hx'. specialize (Hbefore (Z.of_nat i') ltac:(lia)).
        rewrite (Hb i' x') in Hbefore; [exact Hbefore|]. by apply lookup_app_l_Some.
    + right. split; [|reflexivity]. intros i' x' Hx'.
      assert (Hl : (i' < length bytes)%nat) by (apply lookup_lt_Some in Hx'; exact Hx').
      specialize (Hnone (Z.of_nat i') ltac:(lia)).
      rewrite (Hb i' x') in Hnone; [exact Hnone|]. by apply lookup_app_l_Some.
Qed.

(** strcmp's triple, from [strcmp_contract]: owning the strings at p
    and q, which v and w read as, the call binds d to an int. Which
    int does not matter to a caller that only branches on it. *)
Lemma wp_strcmp f e ls lab d v w rest j p b reg xs q b' reg' ys Φ :
  registry (TAtom "strcmp") = Some (strcmp_contract world) ->
  find_fn ge (TAtom "strcmp") = None -> lookup (TAtom "strcmp") (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr p) -> arg_x ge e (Arg P w) = Some (WPtr q) ->
  string p b reg xs -∗ string q b' reg' ys -∗
  ▷ (∀ bits, string p b reg xs -∗ string q b' reg' ys -∗
     WP (ERun (mkFrame f (put d (WInt bits) e) ls None (Exec lab rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d W) (Global (TAtom "strcmp")) [Arg P v; Arg P w] :: rest) j))
        : sexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hv Hw. iIntros "Hs Ht HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (strcmp_contract world) [WPtr p; WPtr q]
            (string p b reg xs ∗ string q b' reg' ys) with "[$Hs $Ht] [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hv Hw; done | | |].
  - split; [right; eexists; reflexivity | do 2 eexists; reflexivity].
  - iIntros (σ) "Hσ [Hs Ht]". iDestruct (string_facts with "Hσ Hs") as %[Hp _].
    iDestruct (string_facts with "Hσ Ht") as %[Hq _]. iPureIntro.
    exists p, q, (Z.of_nat (length xs)), (Z.of_nat (length ys)). auto.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "Hσ [Hs Ht]".
    destruct (M.E.strcmp_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & -> & p' & q' & bits & Hx & _ & He). injection He as ->.
    iDestruct (pure_return with "Hσ") as "Hσ"; [exact Hinv|]. destruct σ as [m s fuel w0]. iModIntro.
    iExists _. iSplit; [iPureIntro; reflexivity|]. iFrame "Hσ". iApply ("HK" with "Hs Ht").
Qed.

(** strncmp's triple, from [strncmp_contract]: owning the strings at p
    and q, which v and w read as, compared up to n bytes, which u reads
    as, the call binds d to an int. *)
Lemma wp_strncmp f e ls lab d v w u rest j p b reg xs q b' reg' ys n Φ :
  registry (TAtom "strncmp") = Some (strncmp_contract world) ->
  find_fn ge (TAtom "strncmp") = None -> lookup (TAtom "strncmp") (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr p) -> arg_x ge e (Arg P w) = Some (WPtr q) ->
  arg_x ge e (Arg L u) = Some (WInt n) -> 0 <= n < 2 ^ 64 ->
  string p b reg xs -∗ string q b' reg' ys -∗
  ▷ (∀ bits, string p b reg xs -∗ string q b' reg' ys -∗
     WP (ERun (mkFrame f (put d (WInt bits) e) ls None (Exec lab rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d W) (Global (TAtom "strncmp")) [Arg P v; Arg P w; Arg L u] :: rest) j))
        : sexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hv Hw Hu Hn. iIntros "Hs Ht HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (strncmp_contract world) [WPtr p; WPtr q; WInt n]
            (string p b reg xs ∗ string q b' reg' ys) with "[$Hs $Ht] [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hv Hw Hu; done | | |].
  - split; [right; eexists; reflexivity | do 3 eexists; reflexivity].
  - iIntros (σ) "Hσ [[%Hok Hs] [%Hok' Ht]]".
    iDestruct (pts_facts with "Hσ Hs") as %(Ha & _). iDestruct (pts_facts with "Hσ Ht") as %(Ha' & _).
    iPureIntro. do 5 eexists. split; [reflexivity|].
    split; [exact (string_bounded _ _ _ _ _ _ Hok Ha Hn) | exact (string_bounded _ _ _ _ _ _ Hok' Ha' Hn)].
  - iNext. iIntros (σ trace values s' m' w' Hinv) "Hσ [Hs Ht]".
    destruct (M.E.strncmp_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & -> & p' & q' & n' & bits & Hx & _ & He). injection He as ->.
    iDestruct (pure_return with "Hσ") as "Hσ"; [exact Hinv|]. destruct σ as [m s fuel w0]. iModIntro.
    iExists _. iSplit; [iPureIntro; reflexivity|]. iFrame "Hσ". iApply ("HK" with "Hs Ht").
Qed.

(** strrchr's triple, from [strrchr_contract]: owning the string at p,
    which v reads as, the call binds d to null or to a pointer into the
    string before its NUL, with p's capability, for an int c, which w
    reads as, whose low byte is not the NUL. *)
Lemma wp_strrchr f e ls lab d v w rest j p b reg bytes c Φ :
  registry (TAtom "strrchr") = Some (strrchr_contract world) ->
  find_fn ge (TAtom "strrchr") = None -> lookup (TAtom "strrchr") (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr p) -> arg_x ge e (Arg W w) = Some (WInt c) ->
  0 <= c < 2 ^ 32 -> c mod 256 <> 0 ->
  string p b reg bytes -∗
  ▷ (∀ q, ⌜q = mkPtr 0 CNone \/
           exists i, (i < length bytes)%nat /\ q = mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p)⌝ -∗
     string p b reg bytes -∗
     WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec lab rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "strrchr")) [Arg P v; Arg W w] :: rest) j))
        : sexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hv Hw Hc Hnz. iIntros "Hs HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (strrchr_contract world) [WPtr p; WInt c]
            (string p b reg bytes) with "Hs [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hv Hw; done | | |].
  - split; [right; eexists; reflexivity | do 2 eexists; reflexivity].
  - iIntros (σ) "Hσ Hs". iDestruct (string_facts with "Hσ Hs") as %[Ht _]. iPureIntro.
    exists p, c, (Z.of_nat (length bytes)). auto.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "Hσ Hs".
    iDestruct "Hs" as "[%Hok Hs]".
    iDestruct (pts_facts with "Hσ Hs") as %(Ha & _).
    pose proof (string_terminated _ _ _ _ _ Hok Ha) as Ht.
    pose proof (string_bytes _ _ _ _ _ Hok Ha) as Hb.
    destruct (M.E.strrchr_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & -> & p' & c' & q & Hx & _ & (k & Hk & Hq) & He). injection Hx as <- <-.
    injection He as ->. rewrite (terminated_length_unique _ _ _ _ Hk Ht) in Hq.
    iDestruct (pure_return with "Hσ") as "Hσ"; [exact Hinv|]. destruct σ as [m s fuel w0]. iModIntro.
    iExists _. iSplit; [iPureIntro; reflexivity|]. iFrame "Hσ".
    iApply ("HK" with "[%] [Hs]"); [|by iSplit].
    cbn [ls_mem] in Hb. destruct Hq as [(i & Hi & Hv' & _ & ->) | (_ & ->)]; [right | left; reflexivity].
    exists (Z.to_nat i). split; [|rewrite Z2Nat.id; [reflexivity | lia]].
    destruct (decide (Z.to_nat i = length bytes)) as [Heq|Hne]; [|lia]. exfalso. apply Hnz.
    rewrite <- Hv'. rewrite <- (Z2Nat.id i) by lia. rewrite Heq. apply (Hb (length bytes) 0).
    rewrite lookup_app_r; [|lia]. rewrite Nat.sub_diag. reflexivity.
Qed.

End calls.

(** ## puts *)

Section puts.
Context (rep : mem -> stdio_world -> Prop) (requests : list word -> mem -> stdio_world -> Z -> Z -> Prop)
  (registry : name -> option (contract stdio_world)) `{!SafepointStable (stdio_wi rep)} (ge : genv).

(** The Iris instance of the registry and [stdio_wi]. *)
Local Instance puts_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (stdio_wi rep) ge.

(** The expressions of the language. *)
Local Notation pexpr := (language.expr (nanofil_lang registry ge)).

(** puts's triple, from [puts_contract]: owning the string at p, which
    v reads as, the call binds d to the int it returns, n modulo 2^32,
    and the string is still owned: puts writes only its world's roots,
    which [stdio_wi] keeps apart from it. *)
Lemma wp_puts f e ls lab d v rest j p b reg bytes Φ :
  registry (TAtom "puts") = Some (puts_contract rep requests) ->
  find_fn ge (TAtom "puts") = None -> lookup (TAtom "puts") (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr p) ->
  string p b reg bytes -∗
  ▷ (∀ n, string p b reg bytes -∗
     WP (ERun (mkFrame f (put d (WInt (n mod 2 ^ 32)) e) ls None (Exec lab rest j)) : pexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d W) (Global (TAtom "puts")) [Arg P v] :: rest) j)) : pexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hv. iIntros "Hs HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (puts_contract rep requests) [WPtr p]
            (string p b reg bytes) with "Hs [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hv; done | | |].
  - split; [right; eexists; reflexivity | eexists; reflexivity].
  - iIntros (σ) "Hσ Hs". iDestruct (string_facts with "Hσ Hs") as %[_ Hc].
    iDestruct "Hσ" as (h) "[_ %Hf]". destruct Hf as (_ & _ & _ & Hrep & Hw & _).
    iPureIntro. split; [exact Hrep|]. split; [exact Hw|]. exists p, bytes. auto.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) Hs".
    destruct Hf as (Ha & Hd & Hr & Hwi).
    destruct (puts_return_frame _ _ _ _ _ _ _ _ _ _ _ _ _ h Hinv Ha Hd Hr Hwi)
      as (Ha' & Hd' & Hr' & Hwi').
    destruct (puts_returns_int _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (n & ->).
    iModIntro. iExists _. iSplit; [iPureIntro; reflexivity|].
    iSplitL "Hh"; [iExists h; iFrame "Hh"; iPureIntro; auto|].
    iApply ("HK" with "Hs").
Qed.

End puts.
End strings.
End StringLogic.
