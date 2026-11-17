(** The startup code of glibc asks the processor what it supports by
    calling `c: init_cpu_features`. The larger proof about startup
    treats that call as one step with a contract, which says what
    memory the call needs and what it gives back. This module proves
    the contract, which [CpuInitSpec](CpuInitSpec.v) states. The
    proof is not tied to one program. It holds for every linked
    program that defines the function and its callees as the
    hi_atexit image does. [CpuHiAtexit](CpuHiAtexit.v) applies it to
    that image.

    [CpuInit](CpuInit.v) already proves that the function never
    panics. It does so with an abstract interpreter, which these
    modules call the checker. The checker follows the function over
    descriptions of memory, and its theorem is stated in its own
    terms. It numbers the objects that the function touches, it takes
    a list that gives the place of each numbered object, and it
    describes the contents of each object byte by byte. The contract
    instead owns each global object through the assertions that the
    other startup proofs use. This module shows that the two
    statements say the same thing.

    The proof has three steps. First it says what the description of
    an object means for the bytes of the object. Then it shows that a
    caller who gives up the memory of the contract has given the
    function everything that the checker requires. Last, it shows
    that what the function hands back is the memory of the contract
    again.

    The contract keeps the one assumption of [CpuInit](CpuInit.v),
    that the list of caches that CPUID leaf 4 reports ends. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Pieces Heap Logic StringLogic MemLogic.
From Nanofil Require Import AbsRun AbsInfer AbsDen AbsMem AbsCall AbsOwn AbsSound.
From Glibc Require Import Fix GlibcProgram GlibcSpec OsWorld OsBlocks OsCpuid OsRegistry HiAtexitModule
  FileInv LibioCloseSteps CpuRules CpuHook CpuSetup CpuSound CpuTunables CpuInit CpuInitSpec.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

(** * Abstract objects as plain facts

    An abstract object describes every byte and every shadow slot of
    a real object. Most bytes of the objects here are unconstrained.
    The lemmas of this section state what an abstract object asks for
    without the abstract bytes, so that a contract can say it in its
    own words. *)

Section pure.
Variable guard : Prop.

(** The function [pinned] lists the bytes of an object that are
    constrained, each with its offset. The offsets count from i. *)
Fixpoint pinned (i : nat) (bs : list abyte) : list (nat * abyte) :=
  match bs with
  | [] => []
  | BR :: bs' => pinned (Datatypes.S i) bs'
  | b :: bs' => (i, b) :: pinned (Datatypes.S i) bs'
  end.

(** Real bytes fit abstract bytes exactly when there are as many of
    them, each is below 256, and each constrained byte meets its
    constraint. The list pre stands for the bytes before the ones
    that the induction has reached. *)
Lemma dbytes_pinned ρ bs : forall pre xs,
  Forall2 (dbyte guard ρ) bs xs <->
  length xs = length bs /\ Forall is_byte xs /\
  Forall (fun p => exists x, nth_error (pre ++ xs) (fst p) = Some x /\ dbyte guard ρ (snd p) x)
    (pinned (length pre) bs).
Proof using Type.
  induction bs as [|b bs IH]; intros pre [|x xs]; cbn [length pinned].
  - split; [intros _; repeat constructor | constructor].
  - split; [intros H; inversion H | intros [[=] _]].
  - split; [intros H; inversion H | intros [[=] _]].
  - specialize (IH (pre ++ [x]) xs). rewrite -app_assoc length_app Nat.add_1_r in IH. cbn [app length] in IH.
    assert (Hp : (exists x', nth_error (pre ++ x :: xs) (length pre) = Some x' /\ dbyte guard ρ b x') <->
                 dbyte guard ρ b x).
    { rewrite nth_error_app2; [|lia]. rewrite Nat.sub_diag. cbn [nth_error].
      split; [intros (x' & [= <-] & H); exact H | intros H; eauto]. }
    assert (Hb : dbyte guard ρ b x -> is_byte x) by (intros H; exact (proj1 H)).
    assert (Hr : is_byte x -> dbyte guard ρ BR x) by (intros H; split; [exact H | exact I]).
    rewrite Forall2_cons_iff Forall_cons_iff IH.
    destruct b; rewrite ?Forall_cons_iff; cbn [fst snd]; rewrite ?Hp; intuition lia.
Qed.

(** A byte that the object fixes to z is the byte z. *)
Lemma pin_known ρ xs i z :
  Forall is_byte xs ->
  (exists x, nth_error xs i = Some x /\ dbyte guard ρ (BK z) x) <-> nth_error xs i = Some z.
Proof using Type.
  intros Hx. split.
  - intros (x & Hi & _ & ->). exact Hi.
  - intros Hi. exists z. split; [exact Hi|]. split; [|reflexivity].
    rewrite Forall_forall in Hx. exact (Hx z (nth_error_In _ _ Hi)).
Qed.

(** An object that fixes all its bytes has exactly those bytes. *)
Lemma dbytes_known ρ zs : Forall is_byte zs -> forall xs, Forall2 (dbyte guard ρ) (map BK zs) xs <-> xs = zs.
Proof using Type.
  induction 1 as [|z zs Hz _ IH]; intros [|x xs]; cbn [List.map].
  - split; [reflexivity | constructor].
  - split; [intros H; inversion H | discriminate].
  - split; [intros H; inversion H | discriminate].
  - rewrite Forall2_cons_iff IH. unfold dbyte. split; [intros [[_ ->] ->]; reflexivity | intros [= -> ->]; auto].
Qed.

(** An object that constrains no byte takes any n bytes below 256. *)
Lemma dbytes_any ρ n : forall xs,
  Forall2 (dbyte guard ρ) (map open_byte (repeat BR n)) xs <-> length xs = n /\ Forall is_byte xs.
Proof using Type.
  induction n as [|n IH]; intros [|x xs]; cbn [repeat List.map length open_byte].
  - split; [intros _; split; [reflexivity | constructor] | constructor].
  - split; [intros H; inversion H | intros [[=] _]].
  - split; [intros H; inversion H | intros [[=] _]].
  - rewrite Forall2_cons_iff Forall_cons_iff IH. unfold dbyte, is_byte. intuition lia.
Qed.

(** Shadow slots that may hold anything are any n capabilities. *)
Lemma daux_any B n : forall cs, Forall2 (daux B) (repeat XAny n) cs <-> length cs = n.
Proof using Type.
  induction n as [|n IH]; intros [|c cs]; cbn [repeat length].
  - split; [reflexivity | constructor].
  - split; [intros H; inversion H | discriminate].
  - split; [intros H; inversion H | discriminate].
  - rewrite Forall2_cons_iff IH. cbn [daux]. intuition lia.
Qed.

(** Shadow slots that hold no capability are n empty slots. *)
Lemma daux_none B n : forall cs, Forall2 (daux B) (repeat XNone n) cs <-> cs = repeat CNone n.
Proof using Type.
  induction n as [|n IH]; intros [|c cs]; cbn [repeat].
  - split; [reflexivity | constructor].
  - split; [intros H; inversion H | discriminate].
  - split; [intros H; inversion H | discriminate].
  - rewrite Forall2_cons_iff IH. cbn [daux]. split; [intros [-> ->]; reflexivity | intros [= -> ->]; auto].
Qed.

End pure.

Section conv.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world) (ge : genv) {Hge : CpuImage ge}.

(** The contract is about one program. A program is a linked image
    together with the world of answers that the processor and the
    kernel give. The image is ge and the world is w0. *)
Local Instance icf_program : GlibcProgram (hlc := hlc) Σ := program_of w0 glibc_os_registry ge.

(** Two short names make the statements below easier to read. The
    proposition guard says that the kernel enabled XSAVE. The function
    may read the extended control register only when that holds. The
    function ρ0 gives the value zero to every unknown number. The
    specifications in this module have no unknown numbers, so the
    choice does not matter. *)
Local Notation guard := (ow_osxsave w0 = true).
Local Notation ρ0 := (fun _ : nat => 0).

(** * One object

    The checker owns an object as one list of pieces at a numbered
    place. The contract owns the lifetime of the object and its
    contents separately. The lemmas of this section convert between
    the two for each kind of object that the precondition names. *)

(** This lemma does the conversion for any object. The predicate Φ
    is the contract's description of the contents, and it must say
    what the abstract object says. *)
Lemma dcobj_own B i b reg ob (Φ : list Z -> list cap -> Prop) :
  nth_error B i = Some (mkPlace b reg (o_ro ob)) ->
  b mod o_align ob = 0 -> b + o_size ob <= r_end reg -> length (o_aux ob) = length (o_bytes ob) ->
  (forall xs cs, Φ xs cs <->
     Forall2 (dbyte guard ρ0) (map open_byte (o_bytes ob)) xs /\ Forall2 (daux B) (o_aux ob) cs) ->
  (∃ pl xs cs, ⌜nth_error B i = Some pl /\ obj_ok guard ρ0 B pl (open_obj ob) xs cs⌝ ∗ AS.own_obj pl xs cs) ⊣⊢
  live b reg ∗ ∃ xs cs, ⌜Φ xs cs⌝ ∗ pts (byte_ps b 0 xs ++ aux_ps b 0 cs).
Proof using Type.
  intros HB Hal Hsz Hlen HΦ. iSplit.
  - iIntros "(%pl & %xs & %cs & [%Hp %Hok] & H)". rewrite HB in Hp. injection Hp as <-.
    destruct Hok as (Hb & Ha & _). rewrite /AS.own_obj /place_ps /block_ps (pts_app [_]).
    iDestruct "H" as "[$ H]". iExists xs, cs. iFrame "H". iPureIntro. apply HΦ. split; assumption.
  - iIntros "[Hl (%xs & %cs & %H & H)]". apply HΦ in H as [Hb Ha].
    iExists (mkPlace b reg (o_ro ob)), xs, cs. rewrite /AS.own_obj /place_ps /block_ps (pts_app [_]). iFrame.
    iPureIntro. split; [exact HB|]. unfold obj_ok, o_size.
    cbn [open_obj o_bytes o_aux o_ro o_align pl_ro pl_base pl_reg]. rewrite length_map. auto 10.
Qed.

(** The feature structure constrains one byte, the one that carries
    the guard. *)
Lemma cpu0_shape :
  pinned 0 (map open_byte (o_bytes cpu0)) = [(31%nat, BGuard 3)] /\ length (o_bytes cpu0) = 528%nat /\
  o_aux cpu0 = repeat XAny 528 /\ o_ro cpu0 = false /\ o_align cpu0 = 8.
Proof using Type*. vm_compute. auto. Qed.

Lemma features_own B i cf reg :
  nth_error B i = Some (mkPlace cf reg false) -> cf mod 8 = 0 -> cf + 528 <= r_end reg ->
  (∃ pl xs cs, ⌜nth_error B i = Some pl /\ obj_ok guard ρ0 B pl (open_obj cpu0) xs cs⌝ ∗ AS.own_obj pl xs cs) ⊣⊢
  live cf reg ∗ icf_features cf.
Proof using Type.
  destruct cpu0_shape as (Hpin & Hlen & Haux & Hro & Hal). intros HB Hmod Hsz.
  apply (dcobj_own B i cf reg cpu0).
  - rewrite Hro. exact HB.
  - rewrite Hal. exact Hmod.
  - unfold o_size. rewrite Hlen. exact Hsz.
  - rewrite Haux Hlen. apply repeat_length.
  - intros xs cs. rewrite (dbytes_pinned guard ρ0 _ [] xs) Haux daux_any length_map Hlen. cbn [app length].
    rewrite Hpin. split.
    + intros (Lx & Lc & Hx & Hg). split; [|exact Lc]. split; [exact Lx|]. split; [exact Hx|].
      constructor; [|constructor]. exists (nth 31 xs 0). cbn [fst snd].
      split; [apply nth_error_nth'; lia|]. split; [|exact Hg]. rewrite Forall_forall in Hx. apply Hx, nth_In. lia.
    + intros [(Lx & Hx & Hp) Lc]. apply Forall_inv in Hp as (x & Hi & _ & Hg). cbn [fst snd] in Hi, Hg.
      rewrite (nth_error_nth _ _ 0 Hi). auto.
Qed.

(** The tunable table constrains the bytes that the contract lists,
    in the same order. *)
Lemma tun0_shape :
  pinned 0 (map open_byte (o_bytes tun0)) = map (fun q => (Z.to_nat (fst q), BK (snd q))) icf_tunable_bytes /\
  length (o_bytes tun0) = 4896%nat /\ o_aux tun0 = repeat XAny 4896 /\ o_ro tun0 = false /\ o_align tun0 = 8.
Proof using Type*. vm_compute. auto. Qed.

Lemma tunables_own B i tl reg :
  nth_error B i = Some (mkPlace tl reg false) -> tl mod 8 = 0 -> tl + 4896 <= r_end reg ->
  (∃ pl xs cs, ⌜nth_error B i = Some pl /\ obj_ok guard ρ0 B pl (open_obj tun0) xs cs⌝ ∗ AS.own_obj pl xs cs) ⊣⊢
  live tl reg ∗ icf_tunables tl.
Proof using Type.
  destruct tun0_shape as (Hpin & Hlen & Haux & Hro & Hal). intros HB Hmod Hsz.
  apply (dcobj_own B i tl reg tun0).
  - rewrite Hro. exact HB.
  - rewrite Hal. exact Hmod.
  - unfold o_size. rewrite Hlen. exact Hsz.
  - rewrite Haux Hlen. apply repeat_length.
  - intros xs cs. rewrite (dbytes_pinned guard ρ0 _ [] xs) Haux daux_any length_map Hlen. cbn [app length].
    rewrite Hpin Forall_map. unfold icf_tunables_ok.
    assert (E : Forall is_byte xs ->
      Forall (fun q => exists x, nth_error xs (fst (Z.to_nat (fst q), BK (snd q))) = Some x /\
                                 dbyte guard ρ0 (snd (Z.to_nat (fst q), BK (snd q))) x) icf_tunable_bytes <->
      Forall (fun '(o, x) => nth_error xs (Z.to_nat o) = Some x) icf_tunable_bytes).
    { intros Hx. rewrite !Forall_forall. split; intros H [o x] Hin; specialize (H _ Hin); cbn [fst snd] in *;
        apply (pin_known guard ρ0 xs _ x Hx); exact H. }
    split; intros [(Lx & Hx & Hp) Lc]; (split; [|exact Lc]); (split; [exact Lx|]); (split; [exact Hx|]);
      apply (E Hx); exact Hp.
Qed.

(** The descriptor table of the image holds the bytes that the
    contract lists, and no pointer. *)
Lemma known_shape :
  map open_byte (o_bytes known) = map BK icf_known_bytes /\ length (o_bytes known) = 544%nat /\
  o_aux known = repeat XNone 544 /\ o_ro known = true /\ o_align known = 4 /\
  forallb (fun x => (0 <=? x) && (x <? 256)) icf_known_bytes = true.
Proof using Type*. vm_compute. auto 10. Qed.

Lemma known_own B i kn reg :
  nth_error B i = Some (mkPlace kn reg true) -> kn mod 4 = 0 -> kn + 544 <= r_end reg ->
  (∃ pl xs cs, ⌜nth_error B i = Some pl /\ obj_ok guard ρ0 B pl (open_obj known) xs cs⌝ ∗ AS.own_obj pl xs cs) ⊣⊢
  live kn reg ∗ icf_known kn.
Proof using Type.
  destruct known_shape as (Hby & Hlen & Haux & Hro & Hal & Hsm). intros HB Hmod Hsz.
  assert (Hk : Forall is_byte icf_known_bytes).
  { apply Forall_forall. intros x Hx. rewrite forallb_forall in Hsm. specialize (Hsm x Hx). unfold is_byte. lia. }
  rewrite (dcobj_own B i kn reg known (fun xs cs => xs = icf_known_bytes /\ cs = repeat CNone 544)).
  - apply bi.sep_proper; [reflexivity|]. rewrite /icf_known /bytes /auxes -pts_app. iSplit.
    + iIntros "(%xs & %cs & [-> ->] & $)".
    + iIntros "H". iExists _, _. iFrame "H". iPureIntro. split; reflexivity.
  - rewrite Hro. exact HB.
  - rewrite Hal. exact Hmod.
  - unfold o_size. rewrite Hlen. exact Hsz.
  - rewrite Haux Hlen. apply repeat_length.
  - intros xs cs. rewrite Hby Haux (dbytes_known guard ρ0 _ Hk) daux_none. reflexivity.
Qed.

(** A small global fits its object when it is aligned to its size and
    lies inside its region. *)
Definition small_fit (g : string * Z) (q : Z * region) : Prop :=
  0 <= snd g /\ fst q mod snd g = 0 /\ fst q + snd g <= r_end (snd q).

Lemma small_own B i g q :
  nth_error B i = Some (mkPlace (fst q) (snd q) false) -> small_fit g q ->
  (∃ pl xs cs, ⌜nth_error B i = Some pl /\
                obj_ok guard ρ0 B pl (open_obj (weak (snd g) (Z.to_nat (snd g)))) xs cs⌝ ∗ AS.own_obj pl xs cs) ⊣⊢
  live (fst q) (snd q) ∗ blk_u8 (fst q) (snd g).
Proof using Type.
  intros HB (Hn & Hmod & Hsz).
  apply (dcobj_own B i (fst q) (snd q) (weak (snd g) (Z.to_nat (snd g)))); unfold o_size;
    cbn [weak o_ro o_align o_bytes o_aux]; rewrite ?repeat_length; [exact HB | exact Hmod | lia | reflexivity |].
  intros xs cs. rewrite dbytes_any daux_any. unfold is_byte. tauto.
Qed.

(** The function also writes fifteen small globals, such as the
    cache sizes that `c: memcpy` later reads. This lemma converts all
    of them at once. Each one is a block of unknown bytes on both
    sides. *)
Lemma smalls_own B : forall gs qs i,
  Forall2 small_fit gs qs ->
  (forall k q, nth_error qs k = Some q -> nth_error B (i + k) = Some (mkPlace (fst q) (snd q) false)) ->
  AS.dcobjs_at guard i B (map (fun g => Some (weak (snd g) (Z.to_nat (snd g)))) gs ++ [None]) ⊣⊢
  [∗ list] g; q ∈ gs; qs, live (fst q) (snd q) ∗ blk_u8 (fst q) (snd g).
Proof using Type.
  intros gs qs i H. revert i. induction H as [|g q gs qs Hgq _ IH]; intros i HB; cbn [List.map app].
  - rewrite AS.dcobjs_at_cons /AS.dcobjs_at /=. iSplit; by iIntros "_".
  - rewrite AS.dcobjs_at_cons big_sepL2_cons. apply bi.sep_proper.
    + apply small_own; [|exact Hgq]. specialize (HB 0%nat q eq_refl). by rewrite Nat.add_0_r in HB.
    + apply IH. intros k q' Hk. specialize (HB (Datatypes.S k) q' Hk). by rewrite Nat.add_succ_r in HB.
Qed.

(** * A weaker postcondition

    The checker's postcondition describes what the function leaves
    behind more exactly than the contract needs. Objects that fit a
    description also fit every description that the checker's order
    puts above it. *)

(** The empty state has no symbols and no guard, so every valuation
    satisfies it. *)
Lemma sat_st0 : sat guard ρ0 (st0 false).
Proof using Type.
  split; [|split; [|split]]; cbn [st0 st_bnd st_flags st_lin st_guard].
  - intros [|s] lo hi H; discriminate.
  - intros s fl [].
  - intros t s c [].
  - discriminate.
Qed.

(** The bytes of a closed object name no symbol. *)
Lemma wf_open n bs : Forall (wf_byte n) (map open_byte bs).
Proof using Type. apply Forall_map, Forall_forall. intros [] _; exact I. Qed.

Lemma dcobjs_at_le B : forall ts os i,
  objs_le (st0 false) (map (option_map open_obj) os) ts = true ->
  AS.dcobjs_at guard i B os ⊢ AS.dcobjs_at guard i B ts.
Proof using Type.
  induction ts as [|[t|] ts IH]; intros [|o os] i H; cbn [List.map objs_le] in H; try discriminate.
  - reflexivity.
  - rewrite /AS.dcobjs_at big_sepL_nil. by iIntros "_".
  - destruct o as [ob|]; [|discriminate]. cbn [option_map] in H. apply andb_prop in H as [Hle H].
    rewrite !AS.dcobjs_at_cons. iIntros "[(%pl & %xs & %cs & [%Hp %Hok] & Ho) H]". iSplitL "Ho".
    + iExists pl, xs, cs. iFrame "Ho". iPureIntro. split; [exact Hp|].
      exact (obj_le_sound guard ρ0 ρ0 B B (st0 false) pl (open_obj ob) t xs cs sat_st0 (wf_open _ _) Hok Hle
               (fun _ _ => eq_refl)).
    + iApply (IH with "H"). exact H.
  - rewrite !AS.dcobjs_at_cons. iIntros "[_ H]". iSplitR; [done|]. iApply (IH with "H"). exact H.
Qed.

(** * The specification that was checked

    [CpuInit](CpuInit.v) proved one specification of
    `c: init_cpu_features`. A specification is a record with a
    precondition, a postcondition, the arguments and the result. This
    one is large, because it describes thousands of bytes. The lemma
    below computes the few facts about it that the proof uses. Before
    the call the function owns the feature structure, the tunable
    table, the descriptor table and then the small globals. After the
    call every object still fits the description it had before. The
    function takes the address of the feature structure and returns no
    value. It can start without the XSAVE assumption. *)
Lemma icf_shape :
  sp_pre icf_spec = Some cpu0 :: Some tun0 :: Some known ::
    map (fun g => Some (weak (snd g) (Z.to_nat (snd g)))) icf_small_globals ++ [None] /\
  objs_le (st0 false) (map (option_map open_obj) (sp_post icf_spec)) (sp_pre icf_spec) = true /\
  sp_args icf_spec = [CP 0 0 0] /\ sp_guard icf_spec = false /\ sp_ret icf_spec = None /\
  gobjs = map TAtom (cpu :: tl :: kn :: map fst icf_small_globals) /\
  forallb (fun g => 0 <=? snd g) icf_small_globals = true.
Proof using Type*. vm_compute. auto 10. Qed.

(** * Places

    The checker numbers the objects of a specification, and a list of
    places says where each one lies. The places of the contract are
    the addresses and regions of its record, in the order of the
    precondition. The last entry stands for the parameter. It names
    the feature structure again, and the precondition owns nothing
    there. *)
Definition icf_places (o : icf_objs) : list place :=
  mkPlace (icf_cf o) (icf_cfreg o) false :: mkPlace (icf_tl o) (icf_tlreg o) false ::
  mkPlace (icf_kn o) (icf_knreg o) true ::
  map (fun q => mkPlace (fst q) (snd q) false) (icf_small o) ++ [mkPlace (icf_cf o) (icf_cfreg o) false].

(** Every live object lies in the address space from 0 to 2^48. The
    checker asks for that bound, and the contract does not, because
    the logic gives it for every object whose lifetime is owned. *)
Definition fits (b : Z) (reg : region) : Prop := 0 <= b /\ r_end reg <= 2 ^ 48.
Definition icf_fits (o : icf_objs) : Prop :=
  fits (icf_cf o) (icf_cfreg o) /\ fits (icf_tl o) (icf_tlreg o) /\ fits (icf_kn o) (icf_knreg o) /\
  Forall (fun q => fits (fst q) (snd q)) (icf_small o).

Lemma icf_small_fit o : icf_ok o -> Forall2 small_fit icf_small_globals (icf_small o).
Proof using Type.
  intros Hok. destruct icf_shape as (_ & _ & _ & _ & _ & _ & Hn). rewrite forallb_forall in Hn.
  do 9 destruct Hok as [_ Hok]. revert Hn Hok. generalize icf_small_globals as gs. intros gs Hn H.
  induction H as [|g q gs qs (_ & Hmod & Hsz) _ IH]; constructor.
  - split; [|split; assumption]. apply Z.leb_le, Hn. left. reflexivity.
  - apply IH. intros g' Hg'. apply Hn. right. exact Hg'.
Qed.

Lemma icf_places_ok o : icf_ok o -> icf_fits o -> Forall place_ok (icf_places o).
Proof using Type.
  intros Hok (Hcf & Htl & Hkn & Hsm). pose proof (icf_small_fit o Hok) as Hfit.
  destruct Hok as (_ & _ & _ & _ & Hcfe & _ & Htle & _ & Hkne & _). unfold fits in *.
  assert (Hc : place_ok (mkPlace (icf_cf o) (icf_cfreg o) false)) by (unfold place_ok; cbn [pl_base pl_reg]; lia).
  unfold icf_places. constructor; [exact Hc|]. constructor; [unfold place_ok; cbn [pl_base pl_reg]; lia|].
  constructor; [unfold place_ok; cbn [pl_base pl_reg]; lia|].
  apply Forall_app. split; [|constructor; [exact Hc|constructor]].
  clear -Hfit Hsm. induction Hfit as [|g q gs qs (Hn & _ & Hsz) _ IH]; cbn [List.map]; [constructor|].
  apply Forall_cons_iff in Hsm as [Hq Hsm]. constructor; [|exact (IH Hsm)].
  unfold place_ok, fits in *. cbn [pl_base pl_reg]. lia.
Qed.

(** The image names each global object of the checker at its place. *)
Lemma icf_globals_ok o : icf_ok o -> globals_ok ge gobjs (icf_places o).
Proof using Type.
  intros (Hcf & Htl & Hkn & _ & _ & _ & _ & _ & _ & Hsm) i g Hi.
  destruct icf_shape as (_ & _ & _ & _ & _ & Hg & _). rewrite Hg in Hi. unfold icf_places.
  destruct i as [|[|[|k]]]; cbn [List.map nth_error] in Hi |- *;
    try (injection Hi as <-; eexists; split; [reflexivity|assumption]).
  revert Hi Hsm. generalize icf_small_globals as gs. intros gs Hi Hsm. revert k Hi.
  induction Hsm as [|g0 q gs qs (Hl & _) _ IH]; intros [|k] Hi; cbn [List.map nth_error app] in Hi |- *;
    try discriminate.
  - injection Hi as <-. eexists. split; [reflexivity|exact Hl].
  - exact (IH k Hi).
Qed.

(** The assertion of the contract owns exactly the objects of the
    checker's precondition. *)
Lemma icf_owns_pre o : icf_ok o -> icf_owns o ⊣⊢ AS.dcobjs guard (icf_places o) (sp_pre icf_spec).
Proof using Type.
  intros Hok. pose proof (icf_small_fit o Hok) as Hfit. destruct icf_shape as (Hpre & _). rewrite Hpre.
  destruct Hok as (_ & _ & _ & Hcfm & Hcfe & Htlm & Htle & Hknm & Hkne & _).
  rewrite -AS.dcobjs_at_0 3!AS.dcobjs_at_cons /icf_owns.
  rewrite (features_own _ _ (icf_cf o) (icf_cfreg o)); [|reflexivity|assumption|assumption].
  rewrite (tunables_own _ _ (icf_tl o) (icf_tlreg o)); [|reflexivity|assumption|assumption].
  rewrite (known_own _ _ (icf_kn o) (icf_knreg o)); [|reflexivity|assumption|assumption].
  rewrite (smalls_own _ _ (icf_small o) 3 Hfit).
  - iSplit; [iIntros "($ & $ & $ & $ & $ & $ & $)" | iIntros "(($ & $) & ($ & $) & ($ & $) & $)"].
  - intros k q Hk. cbn [Nat.add nth_error icf_places]. rewrite nth_error_app1.
    + rewrite nth_error_map Hk. reflexivity.
    + rewrite length_map. apply nth_error_Some. rewrite Hk. discriminate.
Qed.

(** * The contract *)

(** The theorem of [CpuInit](CpuInit.v) gives the triple of the
    contract once every object is known to lie below 2^48. *)
Lemma icf_triple o :
  ow_leaf4_ends w0 = true -> icf_ok o -> icf_fits o ->
  AS.fn_triple glibc_os_registry (os_wi w0) ge (TAtom "glibc_libc_start#init_cpu_features")
    [WPtr (mkPtr (icf_cf o) (Obj (icf_cf o)))] (icf_owns o) (fun r => ⌜r = RetVoid⌝ ∗ icf_owns o)%I.
Proof using Hge.
  intros Hends Hok Hfit. destruct icf_shape as (Hpre & Hle & Hargs & Hg & Hret & _).
  destruct (init_cpu_features_safe w0 ge Hends (icf_places o) [WPtr (mkPtr (icf_cf o) (Obj (icf_cf o)))])
    as (gf & Hgf & Hfr & Ht).
  - rewrite Hpre. cbn [length icf_places]. rewrite !length_app !length_map. cbn [length].
    rewrite (Forall2_length (icf_small_fit o Hok)). reflexivity.
  - exact (icf_places_ok o Hok Hfit).
  - exact (icf_globals_ok o Hok).
  - rewrite Hargs. constructor; [|constructor]. eexists _, 0. split; [reflexivity|]. split; [lia|].
    cbn [pl_base pl_cap pl_ro]. rewrite Z.add_0_r. reflexivity.
  - rewrite Hg. discriminate.
  - exists gf. split; [exact Hgf|]. split; [exact Hfr|]. intros fr Φ Hcall. iIntros "Ho HK".
    iApply (Ht fr Φ Hcall with "[Ho]"); [rewrite (icf_owns_pre o Hok); iExact "Ho"|].
    iIntros (r) "(%Hr & _ & Hpost)". iApply "HK". rewrite Hret in Hr. iSplit; [done|].
    rewrite (icf_owns_pre o Hok) -!AS.dcobjs_at_0. iApply (dcobjs_at_le with "Hpost"). exact Hle.
Qed.

(** The logic shows the bound of a live object before a step of the
    program, so the bounds are collected inside the call. *)
Lemma live_fit b reg fr Φ :
  live b reg -∗
  (⌜fits b reg⌝ -∗ live b reg -∗ WP (ERun fr : language.expr (nanofil_lang glibc_os_registry ge)) {{ Φ }}) -∗
  WP (ERun fr : language.expr (nanofil_lang glibc_os_registry ge)) {{ Φ }}.
Proof using Type. exact (wp_live_fit1 (glibc_program := icf_program) b reg fr Φ). Qed.

Lemma wp_smalls_fit (gs : list (string * Z)) : forall (qs : list (Z * region)) fr Φ,
  ([∗ list] g; q ∈ gs; qs, live (fst q) (snd q) ∗ blk_u8 (fst q) (snd g)) -∗
  (⌜Forall (fun q => fits (fst q) (snd q)) qs⌝ -∗
   ([∗ list] g; q ∈ gs; qs, live (fst q) (snd q) ∗ blk_u8 (fst q) (snd g)) -∗
   WP (ERun fr : language.expr (nanofil_lang glibc_os_registry ge)) {{ Φ }}) -∗
  WP (ERun fr : language.expr (nanofil_lang glibc_os_registry ge)) {{ Φ }}.
Proof using Type.
  induction gs as [|g gs IH]; intros [|q qs] fr Φ; iIntros "H HK".
  - iApply ("HK" with "[%] H"). constructor.
  - iDestruct (big_sepL2_length with "H") as %[=].
  - iDestruct (big_sepL2_length with "H") as %[=].
  - rewrite big_sepL2_cons. iDestruct "H" as "[[Hl Hb] H]".
    iApply (live_fit with "Hl"). iIntros (Hq) "Hl".
    iApply (IH with "H"). iIntros (Hqs) "H".
    iApply ("HK" with "[%]"); [constructor; assumption|]. iFrame.
Qed.

(** This theorem is the result of the module. It assumes that the
    list of caches that the processor reports ends. The function
    `c: init_cpu_features` of the linked program then satisfies the
    contract of [CpuInitSpec](CpuInitSpec.v) in the program logic of
    the other startup proofs. *)
Theorem init_cpu_features_has_spec :
  ow_leaf4_ends w0 = true ->
  HasSpec glibc_os_registry (os_wi w0) ge (TAtom "glibc_libc_start#init_cpu_features")
    (init_cpu_features_spec (glibc_program := program_of w0 glibc_os_registry ge)).
Proof using Hge.
  intros Hends o. exists icf. split; [exact (cpu_find ge _ _ icf_find)|]. split; [vm_compute; eauto|].
  intros fr Φ Hfr. cbn [fs_pre fs_post init_cpu_features_spec].
  iIntros "[%Hok Ho] HK". iDestruct "Ho" as "(Hcf & Hf & Htl & Ht & Hkn & Hk & Hsm)".
  iApply (live_fit with "Hcf"). iIntros (Fcf) "Hcf".
  iApply (live_fit with "Htl"). iIntros (Ftl) "Htl".
  iApply (live_fit with "Hkn"). iIntros (Fkn) "Hkn".
  iApply (wp_smalls_fit with "Hsm"). iIntros (Fsm) "Hsm".
  destruct (icf_triple o Hends Hok (conj Fcf (conj Ftl (conj Fkn Fsm)))) as (gf & Hgf & _ & Ht).
  rewrite (cpu_find ge _ _ icf_find) in Hgf. injection Hgf as <-.
  iApply (Ht fr Φ Hfr with "[$Hcf $Hf $Htl $Ht $Hkn $Hk $Hsm] HK").
Qed.

End conv.
