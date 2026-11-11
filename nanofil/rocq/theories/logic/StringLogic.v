(** A C string occupies consecutive bytes through its terminating NUL,
    and its enclosing object must remain alive while those bytes are read.
    This module describes that ownership and derives calling rules from
    the libc string [[external-call|contracts]] used in the earlier
    [[campaign]]. It uses the program logic of [Logic](Logic.v), rather
    than proving the string functions' C implementations here.

    A string assertion owns its object's lifetime and every byte through
    the terminator, accepting either a writable or a read-only
    [[capability]]. The assertion [string] supplies both the readable
    memory required by libc contracts and the contents needed by the
    caller's proof. A caller can temporarily lend one byte or a suffix,
    provided that it receives the same ownership back afterward.

    Read-only string calls preserve the caller's memory and the external
    world, so their rules return the same string ownership. Output
    requires more care because puts may change stream state and allocate
    storage while leaving its input string alone. The assertion
    [stdio_wi] keeps the stream's writable storage separate from objects
    owned by the program, allowing both sets of state to survive. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Byte pieces

    A string proof must connect a list of expected bytes to the actual
    memory addresses that a C function reads. The following definitions
    assign one [piece] to each byte, so ownership can be split and
    reassembled without losing that connection. *)

(** Each expected byte receives its own object-relative location, which
    [byte_ps] lists consecutively from offset o in object b. *)
Definition byte_ps (b o : Z) (xs : list Z) : list (piece * pval) :=
  zip_with (fun i x => (PByte b i, VByte x)) (seqZ o (Z.of_nat (length xs))) xs.

(** A nonempty byte sequence separates into its first byte and the
    remaining sequence, whose starting offset advances by one. *)
Lemma byte_ps_cons b o x xs : byte_ps b o (x :: xs) = (PByte b o, VByte x) :: byte_ps b (o + 1) xs.
Proof.
  unfold byte_ps. cbn [length]. rewrite Nat2Z.inj_succ seqZ_cons; [|lia].
  rewrite Z.pred_succ. reflexivity.
Qed.

(** Looking up byte i in the sequence identifies its owned piece at
    offset o plus i within the same object. *)
Lemma byte_ps_lookup b o xs i x :
  xs !! i = Some x -> byte_ps b o xs !! i = Some (PByte b (o + Z.of_nat i), VByte x).
Proof.
  revert o i. induction xs as [|y xs IH]; intros o i H; [discriminate|].
  rewrite byte_ps_cons. destruct i as [|i]; cbn in H |- *.
  - injection H as ->. rewrite Z.add_0_r. reflexivity.
  - rewrite (IH (o + 1) i H). do 3 f_equal. lia.
Qed.

(** When the owned bytes agree with a live object's memory, each listed
    byte lies within the object and contains its expected value. *)
Lemma byte_ps_agree m b reg o xs i x :
  live_at m b reg -> all_agree m (byte_ps b o xs) -> xs !! i = Some x ->
  m_bytes m (b + (o + Z.of_nat i)) = x /\ 0 <= o + Z.of_nat i /\ b + (o + Z.of_nat i) < r_end reg.
Proof.
  intros [E Lv] Ha Hx.
  pose proof (all_agree_elem _ _ _ _ Ha (list_elem_of_lookup_2 _ _ _ (byte_ps_lookup b o xs i x Hx)))
    as [_ Hin].
  destruct (Hin reg E Lv) as (Ho & He & Hv). auto.
Qed.

(** Consecutive nonzero bytes followed by a NUL form a C string, as
    [string_at_of] proves from the individual memory readings. *)
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

(** Concatenating two byte lists concatenates their pieces, with the
    second list beginning immediately after the first list's final byte. *)
Lemma byte_ps_app b o xs ys :
  byte_ps b o (xs ++ ys) = byte_ps b o xs ++ byte_ps b (o + Z.of_nat (length xs)) ys.
Proof.
  revert o. induction xs as [|x xs IH]; intros o; [cbn; rewrite Z.add_0_r; reflexivity|].
  cbn [app]. rewrite !byte_ps_cons IH. cbn [app length].
  replace (o + Z.of_nat (S (length xs))) with (o + 1 + Z.of_nat (length xs)) by lia. reflexivity.
Qed.

(** The locations in a byte sequence are consecutive byte offsets,
    independent of the values stored at those locations. *)
Lemma byte_ps_keys b o xs : (byte_ps b o xs).*1 = PByte b <$> seqZ o (Z.of_nat (length xs)).
Proof.
  revert o. induction xs as [|x xs IH]; intros o; [reflexivity|].
  rewrite byte_ps_cons. cbn [fmap list_fmap fst]. rewrite IH.
  cbn [length]. rewrite Nat2Z.inj_succ (seqZ_cons o); [|lia]. rewrite Z.pred_succ. reflexivity.
Qed.

(** ## Strings

    A valid string needs more than matching bytes: its pointer must
    authorize reads through the terminator within a live object. The
    following predicates combine these bounds with the byte sequence
    and connect them to the string contracts' requirements. *)

(** A string pointer must name its enclosing object and leave room for
    every nonzero byte followed by the terminating NUL.
    The predicate [string_ok] records these bounds, a positive object
    base, and an object end within the model's address space. *)
Definition string_ok (p : ptr) (b : Z) (reg : region) (bytes : list Z) : Prop :=
  (ptr_cap p = Obj b \/ ptr_cap p = Ro b) /\ 0 < b /\ b <= ptr_addr p /\
  ptr_addr p + Z.of_nat (length bytes) + 1 <= r_end reg /\ r_end reg <= 2 ^ 48 /\
  Forall (fun x => 0 < x < 256) bytes.

(** Owning a string requires its enclosing object's lifetime and all
    bytes through the terminator, which [string_ps] collects as pieces. *)
Definition string_ps (p : ptr) (b : Z) (reg : region) (bytes : list Z) : list (piece * pval) :=
  (PLive b, VLive reg) :: byte_ps b (ptr_addr p - b) (bytes ++ [0]).

(** Agreement between the string's pieces and memory determines each
    byte read from its pointer, including the final NUL byte. *)
Lemma string_bytes m p b reg bytes :
  string_ok p b reg bytes -> all_agree m (string_ps p b reg bytes) ->
  forall i x, (bytes ++ [0]) !! i = Some x -> m_bytes m (ptr_addr p + Z.of_nat i) = x.
Proof.
  intros _ [Hl Ha] i x Hx. cbn [fst snd agree_piece] in Hl.
  destruct (byte_ps_agree _ _ _ _ _ _ _ Hl Ha Hx) as [Hv _].
  replace (ptr_addr p + Z.of_nat i) with (b + (ptr_addr p - b + Z.of_nat i)) by lia. exact Hv.
Qed.

(** A string with owned, matching bytes satisfies [terminated_length],
    giving length-based contracts a readable range with the expected terminator. *)
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

(** The same owned bytes also satisfy [c_string], giving the puts
    contract both a readable range and the complete string contents. *)
Lemma string_c_string m p b reg bytes :
  string_ok p b reg bytes -> all_agree m (string_ps p b reg bytes) -> c_string m p bytes.
Proof.
  intros Hok Ha. pose proof (string_bytes m p b reg bytes Hok Ha) as Hb.
  pose proof Hok as (Hc & _ & H1 & H2 & _ & Hf). destruct Ha as [[E _] _]. split.
  - apply (access_read _ b reg); [exact Hc | exact E | lia | lia | apply Z.mod_1_r].
  - apply string_at_of; [exact Hf | exact Hb].
Qed.

(** Every owned location occurs only once in a string's piece list,
    so the assertion does not claim the same byte twice. *)
Lemma string_ps_nodup p b reg bytes : NoDup (string_ps p b reg bytes).*1.
Proof.
  unfold string_ps. cbn [fmap list_fmap fst]. rewrite byte_ps_keys. apply NoDup_cons_2.
  - rewrite list_elem_of_fmap. intros (o & E & _). discriminate E.
  - apply NoDup_fmap_2; [intros x y E; injection E as ->; reflexivity | apply NoDup_seqZ].
Qed.

(** The lifetime and byte pieces of a string all refer to the same
    enclosing object, as [string_ps_id] establishes for ownership reasoning. *)
Lemma string_ps_id p b reg bytes l v : (l, v) ∈ string_ps p b reg bytes -> piece_id l = b.
Proof.
  unfold string_ps. rewrite elem_of_cons. intros [H|H]; [injection H as -> _; reflexivity|].
  apply (list_elem_of_fmap_2 fst) in H. cbn [fst] in H. rewrite byte_ps_keys in H.
  apply list_elem_of_fmap in H as (o & -> & _). reflexivity.
Qed.

(** All pieces used to represent a string describe memory, rather than
    runtime bookkeeping, so memory-preservation rules apply to them. *)
Lemma string_ps_mem p b reg bytes l v : (l, v) ∈ string_ps p b reg bytes -> mem_piece l.
Proof.
  unfold string_ps. rewrite elem_of_cons. intros [H|H]; [injection H as -> _; exact I|].
  apply (list_elem_of_fmap_2 fst) in H. cbn [fst] in H. rewrite byte_ps_keys in H.
  apply list_elem_of_fmap in H as (o & -> & _). exact I.
Qed.

(** Splitting a string at byte i separates its preceding bytes from
    the suffix while retaining the same object lifetime.
    The lemma [string_ps_suffix] describes both piece lists without
    duplicating that lifetime when the suffix is lent to a caller. *)
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

(** Advancing within a string, including to its terminator, leaves a
    valid string suffix with the original pointer's object capability. *)
Lemma string_ok_suffix p b reg bytes i :
  (i <= length bytes)%nat -> string_ok p b reg bytes ->
  string_ok (mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p)) b reg (drop i bytes).
Proof.
  intros Hi (Hc & H0 & H1 & H2 & H3 & Hf). unfold string_ok. cbn [ptr_addr ptr_cap]. rewrite length_drop.
  split; [exact Hc|]. split; [exact H0|]. split; [lia|]. split; [lia|]. split; [exact H3|].
  apply Forall_drop. exact Hf.
Qed.

(** ## The stdio world

    A puts call may write stream buffers, but it must not overwrite
    the input string or other storage owned by the caller. The following
    world condition separates those writable buffers from the caller's
    objects and requires the stream state to remain ready. *)

(** Stream state must match its representation in memory, be ready for
    output, and keep its writable storage apart from the program's objects.
    The predicate [stdio_wi] combines these requirements using the
    [[ghost-state|ghost heap]] to identify which objects the program owns. *)
Definition stdio_wi (rep : mem -> stdio_world -> Prop) (m : mem) (w : stdio_world)
    (h : gmap piece pval) : Prop :=
  rep m w /\ stdio_ready m w /\ roots_apart (stdio_roots w) h m.

(** The module [StringLogicOn] builds string assertions and libc calling
    rules over an existing program logic for any [[runtime]] R. *)
Module StringLogicOn (R : Runtime) (LG0 : LogicSig R).
Module LG := LG0.
Module L := LG.L.
Import L LG.

(** Garbage collection preserves the separation between stream storage
    and program objects because a [[poll|safepoint]] never changes object regions.
    Preserving stream representation and readiness therefore suffices to
    preserve the whole condition, as [stdio_wi_safepoint] proves. *)
Lemma stdio_wi_safepoint (rep : mem -> stdio_world -> Prop) :
  (forall s m s' m' w, R.safepoint s m s' m' -> rep m w -> stdio_ready m w ->
     rep m' w /\ stdio_ready m' w) ->
  SafepointStable (stdio_wi rep).
Proof.
  intros Hst. split. intros s m s' m' w h Hsp (Hr & Hw & Ha).
  destruct (Hst _ _ _ _ _ Hsp Hr Hw) as [Hr' Hw'].
  split; [exact Hr'|]. split; [exact Hw'|].
  intros sp a Hin Hs (l & v & reg & Hl & Hm & [E Hlive] & Hb). apply (Ha sp a Hin Hs).
  rewrite (R.collector_live _ _ _ _ Hsp) in E. exists l, v, reg. split; [exact Hl|]. split; [exact Hm|].
  split; [|exact Hb].
  split; [exact E | exact Hlive].
Qed.

(** Whenever puts returns normally, its contract supplies exactly one
    integer result, as [puts_returns_int] establishes for the calling rule. *)
Lemma puts_returns_int rep requests r args xs s m w trace values s' m' w' :
  M.E.invoke (puts_contract rep requests) r args xs s m w trace (CallReturn values) s' m' w' ->
  exists n, values = [WInt n].
Proof.
  intros Hi. remember (CallReturn values) as en eqn:Een.
  destruct Hi as [? ? ? ? ? ? _ _ _ Hp | ? ? ? ? ? ? _ _ _ _ _]; [|discriminate Een].
  destruct Hp as (p & bytes & acc & tail & n & _ & _ & _ & _ & _ & Hend & _).
  subst. injection Hend as ->. eauto.
Qed.

(** After puts returns, the caller still owns the same objects and
    bytes, while the stream representation describes the new output state.
    The lemma [puts_return_frame] proves this by restricting stream writes
    to its previous storage and any objects allocated during the call.
    Those locations remain separate from the caller's objects, and the
    runtime remains ready for subsequent execution. *)
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

(** A caller owns a C string through [string], which combines its
    pointer bounds with ownership of the object lifetime and terminated bytes. *)
Definition string (p : ptr) (b : Z) (reg : region) (bytes : list Z) : iProp Σ :=
  ⌜string_ok p b reg bytes⌝ ∗ pts (string_ps p b reg bytes).

(** String ownership guarantees that actual memory satisfies both
    length-based and content-based string contracts, as [string_facts] derives from the shared memory interpretation. *)
Lemma string_facts {world : Type} (wi : mem -> world -> gmap piece pval -> Prop) σ p b reg bytes :
  heap_interp wi σ -∗ string p b reg bytes -∗
  ⌜terminated_length (ls_mem σ) p (Z.of_nat (length bytes)) /\ c_string (ls_mem σ) p bytes⌝.
Proof.
  iIntros "Hσ [%Hok Hs]". iDestruct (pts_facts with "Hσ Hs") as %(Ha & _). iPureIntro.
  split; [exact (string_terminated _ _ _ _ _ Hok Ha) | exact (string_c_string _ _ _ _ _ Hok Ha)].
Qed.

(** A string can lend its lifetime and one byte for a load, including
    the terminator when i equals the string's length.
    The rule [string_byte] also supplies the means to rebuild full string
    ownership once the borrower returns both resources unchanged. *)
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

(** A caller can borrow the string beginning at any byte through the
    terminator, while retaining the bytes before that position.
    Returning the borrowed suffix restores the original string ownership
    through [string_suffix], without duplicating the shared object's lifetime. *)
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

(** A bounded string read stops at either the terminator or the
    supplied limit, whichever it reaches first.
    The lemma [string_bounded] derives this [bounded_length] guarantee
    from owned bytes, providing the readable range required by strncmp. *)
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

(** ## The calls

    Read-only libc string calls leave the caller's owned bytes and
    the external world unchanged when they return.
    Their rules below turn string ownership into contract preconditions
    and return that ownership alongside the call's result. *)

Section calls.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The instance [string_irisGS] equips these calling rules with the
    chosen contract registry and the interpretation of external state. *)
Local Instance string_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.

(** The notation [sexpr] names expressions in this language, keeping
    the contract registry implicit in the calling rules below. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A read-only call leaves the memory and external world unchanged,
    although the runtime's private bookkeeping may change during execution.
    The lemma [pure_return] reestablishes the memory interpretation with
    the same owned pieces because the contract preserves runtime readiness. *)
Lemma pure_return {spec : contract world} r args xs (σ : lstate world) trace ending s' :
  M.E.invoke spec r args xs (ls_rt σ) (ls_mem σ) (ls_world σ) trace ending s' (ls_mem σ) (ls_world σ) ->
  heap_interp wi σ -∗ heap_interp wi (mkLstate (ls_mem σ) s' (ls_fuel σ) (ls_world σ)).
Proof.
  intros Hi. iIntros "(%h & Hh & %Hf)". destruct Hf as (Ha & Hd & Hr & Hw).
  destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hi) as (born & Hp).
  destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hp Hr) as [Hr' _].
  iExists h. iFrame "Hh". iPureIntro. cbn. auto.
Qed.

(** Calling strlen returns the owned string's length without consuming
    its ownership, as [wp_strlen] derives from the registered [strlen_contract]. *)
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

(** Searching for a nonzero character returns its first matching byte
    with the string's capability, or null if no byte matches.
    The predicate [strchr_found] describes this result after reducing
    the character argument to its low byte. *)
Definition strchr_found (p : ptr) (bytes : list Z) (c : Z) (q : ptr) : Prop :=
  (exists i x, bytes !! i = Some x /\ x = c mod 256 /\
     (forall i' x', (i' < i)%nat -> bytes !! i' = Some x' -> x' <> c mod 256) /\
     q = mkPtr (ptr_addr p + Z.of_nat i) (ptr_cap p)) \/
  ((forall i' x', bytes !! i' = Some x' -> x' <> c mod 256) /\ q = mkPtr 0 CNone).

(** Calling strchr preserves string ownership and returns the first
    matching position or null, as [wp_strchr] proves for a nonzero search byte. *)
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

(** Calling strcmp preserves both owned strings and returns an integer,
    but [wp_strcmp] deliberately gives no information about its sign or value.
    A caller can use this rule when its safety proof handles every
    result without relying on the strings' relative ordering. *)
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

(** Calling strncmp compares no more than n bytes and preserves both
    strings, while [wp_strncmp] leaves the returned integer unspecified.
    The rule therefore supports safety proofs that do not need the
    comparison's sign or a relation between the string contents. *)
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

(** Searching backward for a nonzero character returns null or a
    pointer before the string's terminator, retaining the original capability.
    The rule [wp_strrchr] preserves string ownership but does not expose
    which byte matched or whether it was the last match. *)
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

(** ## puts

    Output changes stream state even though it only reads the caller's
    input string, so its rule uses the separated stdio world.
    The following rule returns string ownership and an integer result
    after accounting for any stream writes and allocations. *)

Section puts.
Context (rep : mem -> stdio_world -> Prop) (requests : list word -> mem -> stdio_world -> Z -> Z -> Prop)
  (registry : name -> option (contract stdio_world)) `{!SafepointStable (stdio_wi rep)} (ge : genv).

(** The instance [puts_irisGS] uses the stdio world condition to keep
    stream writes separate from memory owned by the caller. *)
Local Instance puts_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (stdio_wi rep) ge.

(** The notation [pexpr] names expressions whose external state follows
    the stdio world condition, keeping that choice implicit below. *)
Local Notation pexpr := (language.expr (nanofil_lang registry ge)).

(** Calling puts preserves the input string because all stream writes
    remain separate from its storage under [stdio_wi].
    The rule [wp_puts] returns that ownership and the contract's integer
    result, wrapped to the 32-bit representation of a C int. *)
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
End StringLogicOn.

(** The module [StringLogic] creates its own program-logic instance,
    then supplies the string assertions and calling rules from [StringLogicOn]. *)
Module StringLogic (R : Runtime).
Module LG0 := Logic R.
Include StringLogicOn R LG0.
End StringLogic.
