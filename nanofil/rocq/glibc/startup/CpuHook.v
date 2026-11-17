(** The checker of [AbsRun](../../theories/exec/AbsRun.v) cannot see
    inside `c: zcpuid`, `c: zcpuid_count` and `c: zxgetbv`, because
    the Fil-C runtime implements them. It asks the hook of
    [CpuRules](CpuRules.v) what such a call does to its state. The
    soundness theorem of [AbsSound](../../theories/exec/AbsSound.v)
    trusts the hook, so it asks for a proof that every answer of the
    hook is a valid step of the program logic. This module gives that
    proof from the contracts in [OsCpuid](../zsys/OsCpuid.v).

    A CPUID call writes four 32-bit answers through four pointers. The
    checker owns whole objects, and the rule for the call wants four
    separate four-byte blocks. The proof takes the four blocks out of
    the owned objects with the window lemmas of
    [AbsWindow](../../theories/exec/AbsWindow.v), applies the rule, and
    puts the blocks back with their new bytes. Two facts about the new
    bytes come from the contract. Bit 27 of a leaf 1 ECX answer says
    whether the kernel enabled XSAVE, and a leaf 4 answer for the last
    subleaf describes no cache when the world says that the leaf 4
    list ends. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics
  Pieces Heap Language Logic StringLogic MemLogic ExternalCalls Dominance AbsRun AbsInfer AbsDen AbsMem AbsStep
  AbsCall AbsOwn AbsWindow AbsSound.
From Glibc Require Import Fix GlibcProgram OsWorld OsBlocks OsCpuid OsRegistry CpuRules.
Import ListNotations.
Open Scope Z_scope.

(** The glibc proofs share one runtime and one instance of the logic.
    The module [AS] is the checker's soundness theorem at that
    instance. *)
Module AS := AbsSoundOn R LG0.

(** A store changes bytes and an allocation adds an object. Neither
    ends the lifetime of an object. The world invariant of the glibc
    proofs depends only on lifetimes, so it survives both. *)
#[global] Instance os_wi_store_stable w : StoreStable (os_wi w).
Proof. split; [apply os_wi_store | apply os_wi_alloc]. Qed.

(** * What the checker's step means

    The lemmas of this section do not mention ownership. They relate
    the checker's step for a CPUID call to the places, the contents
    and the argument words of a real state that the checker's state
    describes. *)
Section pure.
Variable guard : Prop.
Variable ge : genv.
Variable gobjs : list name.
Local Notation M := (M guard ge gobjs).

(** A result block is usable when it lies in a writable object that the
    state owns, four bytes fit at its offset, and the object fits its
    region. *)
Definition blk_at (B : list place) (X : cont) (p : nat * Z) (pl : place) (xs : list Z) (cs : list cap) : Prop :=
  nth_error B p.1 = Some pl /\ nth_error X p.1 = Some (Some (xs, cs)) /\ pl_ro pl = false /\
  0 <= p.2 /\ p.2 + 4 <= Z.of_nat (length xs) /\ length cs = length xs /\
  pl_base pl + Z.of_nat (length xs) <= r_end (pl_reg pl) /\ place_ok pl.

(** When the checker rewrites a block, the block is usable. The state
    after the rewrite describes any contents that differ from the old
    ones only by four new bytes that the abstract bytes describe. *)
Lemma cpuid_out_sound ρ B st e X p bytes st' :
  M ρ B st e X -> cpuid_out st p bytes = Some st' -> length bytes = 4%nat ->
  Forall (wf_byte (length (st_bnd st))) bytes ->
  exists pl xs cs,
    blk_at B X p pl xs cs /\ length (st_bnd st') = length (st_bnd st) /\
    forall ys ds, Forall2 (dbyte guard ρ) bytes ys -> length ds = 4%nat ->
      M ρ B st' e (list_set p.1 (Some (splice p.2 ys xs, splice p.2 ds cs)) X).
Proof using Type.
  destruct p as [o k]. cbn [fst snd]. intros HM E Lb Wb. unfold cpuid_out in E. destruct (get_obj st o) as [ob|] eqn:Eg; [|discriminate].
  cbn [option_bind] in E.
  destruct (negb (o_ro ob) && (0 <=? k) && (k + 4 <=? o_size ob)) eqn:Ec; [|discriminate]. injection E as <-.
  apply andb_prop in Ec as [Ec E3]. apply andb_prop in Ec as [E1 E2].
  apply negb_true_iff in E1. apply Z.leb_le in E2, E3. unfold o_size in E3.
  destruct (M_obj guard ge gobjs ρ B st e X o ob HM Eg) as (pl & xs & cs & Hp & Hx & Hok & Hpl).
  destruct Hok as (Hbs & Hax & Lax & Hro & Hmod & Hend). unfold o_size in Hend.
  pose proof (Forall2_length Hbs) as L1. pose proof (Forall2_length Hax) as L2.
  exists pl, xs, cs. split.
  { unfold blk_at. cbn [fst snd]. split; [exact Hp|]. split; [exact Hx|]. split; [congruence|]. split; [exact E2|].
    split; [lia|]. split; [lia|]. split; [lia | exact Hpl]. }
  split; [reflexivity|].
  intros ys ds Hys Lds. pose proof (Forall2_length Hys) as L3.
  refine (M_put_obj guard ge gobjs ρ B st e X _ o pl _ (splice k ys xs) (splice k ds cs) HM Hp _ _ _ _ _).
  - unfold obj_ok. cbn [o_bytes o_aux o_ro o_align]. unfold o_size. cbn [o_bytes].
    split; [apply Forall2_splice2; assumption|]. split.
    { apply Forall2_splice2; [exact Hax|]. clear -Lds.
      destruct ds as [|d1 [|d2 [|d3 [|d4 [|]]]]]; try discriminate. repeat constructor. }
    rewrite !length_splice; cbn [length]; try lia. split; [lia|]. split; [exact Hro|]. split; [exact Hmod | lia].
  - cbn [wf_obj o_bytes]. apply Forall_splice; [exact Wb|]. exact (M_wf_obj guard ge gobjs ρ B st e X o ob HM Eg).
  - apply length_list_set.
  - rewrite nth_error_list_set Nat.eqb_refl Hx. reflexivity.
  - intros i Hi. rewrite nth_error_list_set. destruct (Nat.eqb_spec i o); [contradiction | reflexivity].
Qed.

(** A block that the checker accepts after it rewrote another block
    was already acceptable before that rewrite, because a rewrite
    keeps the size and the write permission of every object. *)
Lemma cpuid_out_back st o k bytes st1 o' k' bytes' st2 :
  cpuid_out st (o, k) bytes = Some st1 -> length bytes = 4%nat ->
  cpuid_out st1 (o', k') bytes' = Some st2 -> exists st2', cpuid_out st (o', k') bytes' = Some st2'.
Proof using Type.
  unfold cpuid_out, get_obj. intros E Lb E2.
  destruct (nth_error (st_objs st) o) as [[ob|]|] eqn:En; try discriminate. cbn [option_bind] in E.
  destruct (negb (o_ro ob) && (0 <=? k) && (k + 4 <=? o_size ob)) eqn:Ec; [|discriminate]. injection E as <-.
  apply andb_prop in Ec as [Ec E3]. apply andb_prop in Ec as [_ E1]. apply Z.leb_le in E1, E3. unfold o_size in E3.
  cbn [put_obj set_objs st_objs] in E2. rewrite nth_error_list_set in E2. destruct (Nat.eqb_spec o' o) as [->|Hne].
  - rewrite En in E2 |- *. cbn [option_bind o_ro] in E2 |- *. unfold o_size in E2 |- *. cbn [o_bytes] in E2.
    rewrite length_splice in E2; [| lia | lia].
    destruct (negb (o_ro ob) && (0 <=? k') && (k' + 4 <=? Z.of_nat (length (o_bytes ob)))); [|discriminate]. by eexists.
  - destruct (nth_error (st_objs st) o') as [[ob'|]|]; try discriminate. cbn [option_bind] in E2 |- *.
    destruct (negb (o_ro ob') && (0 <=? k') && (k' + 4 <=? o_size ob')); [|discriminate]. by eexists.
Qed.

(** The checker knows some pointers exactly. The address of such a
    pointer is the base of its object plus the known offset. *)
Lemma exact_ptr_sound ρ B st e X v w p pl :
  M ρ B st e X -> wf_val (length (st_bnd st)) v -> dval ge ρ B v w -> exact_ptr st v = Some p ->
  nth_error B p.1 = Some pl -> w = WPtr (mkPtr (pl_base pl + p.2) (pl_cap pl)).
Proof using Type.
  intros HM Hw Hv E Hp. destruct v as [| | |o0 a| | |]; try discriminate. cbn [exact_ptr wf_val dval] in *.
  destruct (rng st a) as [lo hi] eqn:Er. destruct (Z.eqb_spec lo hi) as [<-|]; [|discriminate]. injection E as <-.
  cbn [fst snd] in *. destruct Hv as (x & Hx & ->). rewrite Hx in Hp. injection Hp as ->.
  pose proof (rng_sound guard ρ st a lo lo (M_sat guard ge gobjs ρ B st e X HM) Hw Er). do 2 f_equal. lia.
Qed.

(** When the checker knows the leaf, the real leaf argument is that
    number. *)
Lemma is_leaf_sound ρ B st e X l n :
  M ρ B st e X -> wf_int (length (st_bnd st)) l -> is_leaf st l n = true -> dint ρ l = n.
Proof using Type.
  intros HM Hw E. unfold is_leaf in E. destruct (rng st l) as [lo hi] eqn:Er. apply andb_prop in E as [E1 E2].
  apply Z.eqb_eq in E1, E2. subst.
  pose proof (rng_sound guard ρ st l n n (M_sat guard ge gobjs ρ B st e X HM) Hw Er). lia.
Qed.

(** The contract returns each block as four numbers below 256. *)
Definition is_bytes (ys : list Z) : Prop := length ys = 4%nat /\ Forall (fun x => 0 <= x < 256) ys.

Lemma is_bytes_inv ys :
  is_bytes ys -> exists y0 y1 y2 y3, ys = [y0; y1; y2; y3] /\
    0 <= y0 < 256 /\ 0 <= y1 < 256 /\ 0 <= y2 < 256 /\ 0 <= y3 < 256.
Proof using Type.
  intros [L H]. destruct ys as [|y0 [|y1 [|y2 [|y3 [|]]]]]; try discriminate.
  apply Forall_cons_iff in H as [H0 H]. apply Forall_cons_iff in H as [H1 H]. apply Forall_cons_iff in H as [H2 H].
  apply Forall_cons_iff in H as [H3 _]. by exists y0, y1, y2, y3.
Qed.

(** Four unknown abstract bytes describe any four bytes. *)
Lemma br_bytes ρ ys : is_bytes ys -> Forall2 (dbyte guard ρ) (repeat BR 4) ys.
Proof using Type.
  intros (y0 & y1 & y2 & y3 & -> & H0 & H1 & H2 & H3)%is_bytes_inv. repeat constructor; lia.
Qed.

(** The EAX answer for the last leaf 4 subleaf is a multiple of 32,
    because its cache type is zero. The checker records that as five
    clear bits in the first byte. The abstract bytes of the EAX block
    therefore describe the real bytes. *)
Lemma eax_bytes_sound ρ B st e X leaf4 l subleaf ys :
  M ρ B st e X -> wf_int (length (st_bnd st)) l -> is_bytes ys ->
  (leaf4 = true -> dint ρ l = 4 -> forall s, subleaf = Some (S s) -> ρ s = last4 -> of_bytes ys mod 32 = 0) ->
  Forall2 (dbyte guard ρ) (eax_bytes leaf4 st l subleaf) ys.
Proof using Type.
  intros HM Hw Hys Hf. unfold eax_bytes. destruct subleaf as [[z|s]|]; try by apply br_bytes.
  destruct leaf4; [|by apply br_bytes]. cbn [andb]. destruct (is_leaf st l 4) eqn:El; [|by apply br_bytes].
  pose proof (Hf eq_refl (is_leaf_sound ρ B st e X l 4 HM Hw El) s eq_refl) as Hz.
  apply is_bytes_inv in Hys as (y0 & y1 & y2 & y3 & -> & H0 & H1 & H2 & H3). repeat constructor; try lia. intros Hs.
  specialize (Hz Hs). unfold of_bytes in Hz. cbn [fold_right] in Hz. change 31 with (Z.ones 5).
  rewrite Z.land_ones; [|lia]. change (2 ^ 5) with 32.
  rewrite -Hz. replace (y0 + 256 * (y1 + 256 * (y2 + 256 * (y3 + 256 * 0)))) with (y0 + (8 * (y1 + 256 * (y2 + 256 * y3))) * 32) by lia.
  by rewrite Z_mod_plus_full.
Qed.

Lemma eax_bytes_wf n leaf4 st l subleaf :
  (forall s, subleaf = Some (S s) -> (s < n)%nat) -> Forall (wf_byte n) (eax_bytes leaf4 st l subleaf).
Proof using Type.
  intros H. unfold eax_bytes. destruct subleaf as [[z|s]|]; try by repeat constructor.
  destruct (leaf4 && is_leaf st l 4); repeat constructor. cbn. by apply H.
Qed.

Lemma eax_bytes_length leaf4 st l subleaf : length (eax_bytes leaf4 st l subleaf) = 4%nat.
Proof using Type. unfold eax_bytes. destruct subleaf as [[z|s]|]; try reflexivity. by destruct (leaf4 && is_leaf st l 4). Qed.

(** The XSAVE bit is bit 27 of the ECX answer, which is bit 3 of its
    last byte. The checker puts the guard on that byte. The abstract
    bytes of the ECX block describe the real bytes when the bit
    implies the guard. *)
Lemma ecx_bytes_sound ρ B st e X l ys :
  M ρ B st e X -> wf_int (length (st_bnd st)) l -> is_bytes ys ->
  (dint ρ l = 1 -> Z.testbit (of_bytes ys) 27 = true -> guard) ->
  Forall2 (dbyte guard ρ) (ecx_bytes st l) ys.
Proof using Type.
  intros HM Hw Hys Hf. unfold ecx_bytes. destruct (is_leaf st l 1) eqn:El; [|by apply br_bytes].
  pose proof (Hf (is_leaf_sound ρ B st e X l 1 HM Hw El)) as Hz.
  apply is_bytes_inv in Hys as (y0 & y1 & y2 & y3 & -> & H0 & H1 & H2 & H3). repeat constructor; try lia. intros Hb. apply Hz.
  unfold of_bytes. cbn [fold_right]. change 27 with (3 + 24). rewrite -Z.div_pow2_bits; [| lia | lia].
  replace ((y0 + 256 * (y1 + 256 * (y2 + 256 * (y3 + 256 * 0)))) / 2 ^ 24) with y3; [exact Hb|].
  apply (Z.div_unique_pos _ _ y3 (y0 + 256 * y1 + 65536 * y2)); lia.
Qed.

Lemma ecx_bytes_wf n st l : Forall (wf_byte n) (ecx_bytes st l).
Proof using Type. unfold ecx_bytes. destruct (is_leaf st l 1); repeat constructor. Qed.

Lemma ecx_bytes_length st l : length (ecx_bytes st l) = 4%nat.
Proof using Type. unfold ecx_bytes. by destruct (is_leaf st l 1). Qed.

(** Two result blocks are apart when they lie in different objects or
    at offsets that do not overlap. *)
Definition oapart (p q : nat * Z) : Prop := p.1 <> q.1 \/ p.2 + 4 <= q.2 \/ q.2 + 4 <= p.2.

Lemma disjoint4_apart a b c d :
  disjoint4 [a; b; c; d] = true ->
  oapart a b /\ oapart a c /\ oapart a d /\ oapart b c /\ oapart b d /\ oapart c d.
Proof using Type.
  assert (Hq : forall p q : nat * Z,
             negb (Nat.eqb p.1 q.1) || (p.2 + 4 <=? q.2) || (q.2 + 4 <=? p.2) = true -> oapart p q).
  { intros p q H. apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
    - left. apply negb_true_iff in H. by apply Nat.eqb_neq.
    - right. left. by apply Z.leb_le.
    - right. right. by apply Z.leb_le. }
  destruct a as [oa ka], b as [ob kb], c as [oc kc], d as [od kd]. cbn [disjoint4 forallb].
  rewrite !andb_true_r. intros H. repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H as [? ?] end.
  repeat match goal with H : _ = true |- _ => apply (Hq (_, _) (_, _)) in H end. tauto.
Qed.

(** The checker accepts a CPUID call in one way only. It finds four
    exact pointers, it finds that the four blocks lie apart, and it
    rewrites the four blocks in turn. *)
Lemma acpuid_inv leaf4 l subleaf pa pb pc pd st st' :
  acpuid leaf4 (VI l) subleaf [pa; pb; pc; pd] st = Some st' ->
  exists a b c d st1 st2 st3,
    exact_ptr st pa = Some a /\ exact_ptr st pb = Some b /\ exact_ptr st pc = Some c /\
    exact_ptr st pd = Some d /\ disjoint4 [a; b; c; d] = true /\
    cpuid_out st a (eax_bytes leaf4 st l subleaf) = Some st1 /\ cpuid_out st1 b (repeat BR 4) = Some st2 /\
    cpuid_out st2 c (ecx_bytes st l) = Some st3 /\ cpuid_out st3 d (repeat BR 4) = Some st'.
Proof using Type.
  cbn [acpuid]. intros E.
  destruct (exact_ptr st pa) as [a|]; [|discriminate]. destruct (exact_ptr st pb) as [b|]; [|discriminate].
  destruct (exact_ptr st pc) as [c|]; [|discriminate]. destruct (exact_ptr st pd) as [d|]; [|discriminate].
  cbn [option_bind] in E. destruct (disjoint4 [a; b; c; d]) eqn:Ed; [|discriminate].
  destruct (cpuid_out st a _) as [st1|] eqn:E1; [|discriminate]. cbn [option_bind] in E.
  destruct (cpuid_out st1 b _) as [st2|] eqn:E2; [|discriminate]. cbn [option_bind] in E.
  destruct (cpuid_out st2 c _) as [st3|] eqn:E3; [|discriminate]. cbn [option_bind] in E.
  exists a, b, c, d, st1, st2, st3. auto 10.
Qed.

(** Every one of the four blocks is usable in the state before the
    call, although the checker tests the later ones in states that
    earlier blocks have already changed. *)
Lemma acpuid_blocks ρ B st e X leaf4 l subleaf a b c d st1 st2 st3 st' :
  M ρ B st e X ->
  cpuid_out st a (eax_bytes leaf4 st l subleaf) = Some st1 -> cpuid_out st1 b (repeat BR 4) = Some st2 ->
  cpuid_out st2 c (ecx_bytes st l) = Some st3 -> cpuid_out st3 d (repeat BR 4) = Some st' ->
  exists pla xa ca plb xb cb plc xc cc pld xd cd,
    blk_at B X a pla xa ca /\ blk_at B X b plb xb cb /\ blk_at B X c plc xc cc /\ blk_at B X d pld xd cd.
Proof using Type.
  intros HM Ea Eb Ec Ed. destruct a as [oa ka], b as [ob kb], c as [oc kc], d as [od kd].
  assert (Hbr : forall n, Forall (wf_byte n) (repeat BR 4)) by (intros n; repeat constructor).
  assert (Hpre : forall o k bytes st0, cpuid_out st (o, k) bytes = Some st0 ->
            exists pl xs cs, blk_at B X (o, k) pl xs cs).
  { intros o k bytes st0 E. unfold cpuid_out in E. destruct (get_obj st o) as [ob0|] eqn:Eg; [|discriminate].
    cbn [option_bind] in E.
    destruct (negb (o_ro ob0) && (0 <=? k) && (k + 4 <=? o_size ob0)) eqn:Ek; [|discriminate].
    apply andb_prop in Ek as [Ek E3]. apply andb_prop in Ek as [E1 E2].
    apply negb_true_iff in E1. apply Z.leb_le in E2, E3. unfold o_size in E3.
    destruct (M_obj guard ge gobjs ρ B st e X o ob0 HM Eg) as (pl & xs & cs & Hp & Hx & Hok & Hpl).
    destruct Hok as (Hbs & Hax & Lax & Hro & Hmod & Hend). unfold o_size in Hend.
    pose proof (Forall2_length Hbs) as L1. pose proof (Forall2_length Hax) as L2.
    exists pl, xs, cs. unfold blk_at. cbn [fst snd]. split; [exact Hp|]. split; [exact Hx|]. split; [congruence|].
    split; [exact E2|]. split; [lia|]. split; [lia|]. split; [lia | exact Hpl]. }
  pose proof (eax_bytes_length leaf4 st l subleaf) as La. pose proof (ecx_bytes_length st l) as Lc.
  destruct (cpuid_out_back _ _ _ _ _ _ _ _ _ Ea La Eb) as (sb & Eb0).
  destruct (cpuid_out_back _ _ _ _ _ _ _ _ _ Eb eq_refl Ec) as (sc1 & Ec1).
  destruct (cpuid_out_back _ _ _ _ _ _ _ _ _ Ea La Ec1) as (sc & Ec0).
  destruct (cpuid_out_back _ _ _ _ _ _ _ _ _ Ec Lc Ed) as (sd2 & Ed2).
  destruct (cpuid_out_back _ _ _ _ _ _ _ _ _ Eb eq_refl Ed2) as (sd1 & Ed1).
  destruct (cpuid_out_back _ _ _ _ _ _ _ _ _ Ea La Ed1) as (sd & Ed0).
  destruct (Hpre _ _ _ _ Ea) as (pla & xa & ca & Ha). destruct (Hpre _ _ _ _ Eb0) as (plb & xb & cb & Hb).
  destruct (Hpre _ _ _ _ Ec0) as (plc & xc & cc & Hc). destruct (Hpre _ _ _ _ Ed0) as (pld & xd & cd & Hd).
  exists pla, xa, ca, plb, xb, cb, plc, xc, cc, pld, xd, cd. auto.
Qed.

(** Two blocks that the checker holds apart do not share a byte of
    memory. Blocks of different objects have different bases, because
    the owned pieces name every lifetime once. *)
Lemma blk_apart B X p q pl xs cs pl' xs' cs' :
  blk_at B X p pl xs cs -> blk_at B X q pl' xs' cs' -> oapart p q -> base.NoDup (all_ps B X).*1 ->
  pl_base pl <> pl_base pl' \/ p.2 + 4 <= q.2 \/ q.2 + 4 <= p.2.
Proof using Type.
  intros (Hp & Hx & _) (Hp' & Hx' & _) [Hne|H] Hnd; [|by right]. left.
  exact (all_ps_bases B X p.1 pl xs cs q.1 pl' xs' cs' Hp Hx Hp' Hx' Hne Hnd).
Qed.

(** The place of a block depends only on the list of places. *)
Lemma blk_at_place B X X' p pl xs cs pl' xs' cs' :
  blk_at B X p pl xs cs -> blk_at B X' p pl' xs' cs' -> pl' = pl.
Proof using Type. intros (Hp & _) (Hp' & _). congruence. Qed.

(** The checker reads the arguments of a call before it asks the hook,
    so the proof starts with the argument words in hand. A CPUID call
    passes a leaf, then a subleaf when it is `c: zcpuid_count`, and
    then four result pointers. *)
Definition sub_vals (osub : option aint) : list aval := match osub with Some sa => [VI sa] | None => [] end.
Definition sub_words (ρ : nat -> Z) (osub : option aint) : list word :=
  match osub with Some sa => [WInt (dint ρ sa)] | None => [] end.

(** The argument words of a CPUID call have that shape. The first
    word is the leaf, the next is the subleaf when there is one, and
    the last four are the result pointers. *)
Lemma cpuid_words ρ B n osub la pa pb pc pd ws :
  Forall (wf_val n) (VI la :: sub_vals osub ++ [pa; pb; pc; pd]) ->
  Forall2 (dval ge ρ B) (VI la :: sub_vals osub ++ [pa; pb; pc; pd]) ws ->
  exists wa wb wc wd,
    ws = WInt (dint ρ la) :: sub_words ρ osub ++ [wa; wb; wc; wd] /\
    wf_int n la /\ (forall s, osub = Some (S s) -> (s < n)%nat) /\
    (wf_val n pa /\ dval ge ρ B pa wa) /\ (wf_val n pb /\ dval ge ρ B pb wb) /\
    (wf_val n pc /\ dval ge ρ B pc wc) /\ (wf_val n pd /\ dval ge ρ B pd wd).
Proof using Type.
  intros Hwf Hv. apply Forall_cons_iff in Hwf as [Wl Hwf]. apply Forall2_cons_inv_l in Hv as (wl & ws0 & Hl & Hv & ->).
  cbn [dval] in Hl. subst wl. cbn [wf_val] in Wl.
  assert (Hs : forall s, osub = Some (S s) -> (s < n)%nat).
  { intros s ->. cbn [sub_vals app] in Hwf. apply Forall_cons_iff in Hwf as [Ws _]. exact Ws. }
  assert (Hsub : exists ws1, ws0 = sub_words ρ osub ++ ws1 /\ Forall (wf_val n) [pa; pb; pc; pd] /\
                             Forall2 (dval ge ρ B) [pa; pb; pc; pd] ws1).
  { destruct osub as [sa|]; cbn [sub_vals sub_words app] in *; [|by exists ws0].
    apply Forall_cons_iff in Hwf as [_ Hwf]. apply Forall2_cons_inv_l in Hv as (w1 & ws1 & H1 & Hv & ->).
    cbn [dval] in H1. subst w1. by exists ws1. }
  destruct Hsub as (ws1 & -> & Hwf4 & Hv4). clear Hwf Hv.
  apply Forall_cons_iff in Hwf4 as [Wa Hwf4]. apply Forall_cons_iff in Hwf4 as [Wb Hwf4].
  apply Forall_cons_iff in Hwf4 as [Wc Hwf4]. apply Forall_cons_iff in Hwf4 as [Wd _].
  apply Forall2_cons_inv_l in Hv4 as (wa & ws2 & Ha & Hv4 & ->). apply Forall2_cons_inv_l in Hv4 as (wb & ws3 & Hb & Hv4 & ->).
  apply Forall2_cons_inv_l in Hv4 as (wc & ws4 & Hc & Hv4 & ->). apply Forall2_cons_inv_l in Hv4 as (wd & ws5 & Hd & Hv4 & ->).
  apply Forall2_nil_inv_l in Hv4 as ->. exists wa, wb, wc, wd. auto 10.
Qed.

(** A call whose arguments have the classes that the hook asks for
    has the shape that the contract asks for. *)
Lemma cpuid_abi (sub : bool) args :
  arg_classes args = W :: (if sub then [W] else []) ++ [P; P; P; P] -> os_cpuid_abi sub CVoid args.
Proof using Type.
  intros H. split; [reflexivity|]. destruct sub; cbn [app] in H.
  - destruct args as [|[k1 v1] [|[k2 v2] [|[k3 v3] [|[k4 v4] [|[k5 v5] [|[k6 v6] [|]]]]]]]; try discriminate.
    injection H as -> -> -> -> -> ->. by exists v1, v2, v3, v4, v5, v6.
  - destruct args as [|[k1 v1] [|[k2 v2] [|[k3 v3] [|[k4 v4] [|[k5 v5] [|]]]]]]; try discriminate.
    injection H as -> -> -> -> ->. by exists v1, v1, v2, v3, v4, v5.
Qed.

End pure.

Import OsWorld OsWorld.L OsWorld.LG ProgramAbbreviations.

(** * The hook is sound

    The lemmas of this section are about ownership. They take blocks
    out of the pieces that the checker's state owns, run the call, and
    put the blocks back. *)
Section hook.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Variable gobjs : list name.

Local Notation zexpr := (language.expr (nanofil_lang registry ge)).
Local Notation guard := (ow_osxsave w0 = true).

(** Ownership of a list of pieces does not depend on their order. *)
Lemma pts_perm ps qs : ps ≡ₚ qs -> pts ps ⊣⊢ pts qs.
Proof using Type. intros H. unfold pts. by rewrite H. Qed.

(** A usable block can be taken out of the owned pieces. The set K
    names the blocks already taken, and the new block must lie apart
    from them. *)
Lemma blk_take K B X p pl xs cs :
  blk_at B X p pl xs cs -> base.NoDup (all_ps B X).*1 ->
  (forall l, l ∈ win_keys (pl_base pl) p.2 4 -> l ∉ K) ->
  pts (but K (all_ps B X)) -∗
  blk_any (pl_base pl) p.2 4 ∗ pts (but (win_keys (pl_base pl) p.2 4 ++ K) (all_ps B X)).
Proof using Type.
  intros (Hp & Hx & _ & Hk & Hn & Lc & _) Hnd HK.
  rewrite (pts_perm _ _ (win_take K B X p.1 pl xs cs p.2 4 Hp Hx Hk Hn Lc Hnd HK)) pts_app.
  iIntros "[Hw $]". iExists _, _. iFrame "Hw". iPureIntro.
  split; apply (length_window' p.2 4); first [exact Hk | exact Hn | lia].
Qed.

(** A block goes back into the owned pieces with new bytes, and the
    result is the ownership of the contents with those bytes spliced
    in. *)
Lemma blk_give K B X p pl xs cs ys ds :
  blk_at B X p pl xs cs -> length ys = 4%nat -> length ds = 4%nat -> base.NoDup (all_ps B X).*1 ->
  (forall l, l ∈ win_keys (pl_base pl) p.2 4 -> l ∉ K) ->
  base.NoDup (all_ps B (list_set p.1 (Some (splice p.2 ys xs, splice p.2 ds cs)) X)).*1 /\
  (pts (byte_ps (pl_base pl) p.2 ys ++ aux_ps (pl_base pl) p.2 ds) -∗
   pts (but (win_keys (pl_base pl) p.2 4 ++ K) (all_ps B X)) -∗
   pts (but K (all_ps B (list_set p.1 (Some (splice p.2 ys xs, splice p.2 ds cs)) X)))).
Proof using Type.
  intros (Hp & Hx & _ & Hk & Hn & Lc & _) Ly Ld Hnd HK.
  destruct (win_give K B X p.1 pl xs cs p.2 4 ys ds Hp Hx Hk Hn Lc Ly Ld Hnd HK) as [Hnd' Hperm].
  split; [exact Hnd'|]. rewrite (pts_perm _ _ Hperm) pts_app. iIntros "$ $".
Qed.

(** A usable block lies in a live object, because taking blocks out
    leaves the lifetime of every object among the owned pieces. *)
Lemma blk_at_live K B X p pl xs cs σ :
  blk_at B X p pl xs cs -> (forall l, l ∈ K -> exists b k, l ∈ win_keys b k 4) ->
  heap_interp (os_wi w0) σ -∗ pts (but K (all_ps B X)) -∗ ⌜blk_live (ls_mem σ) (pl_base pl, p.2, 4)⌝.
Proof using Type.
  intros (Hp & Hx & _ & Hk & Hn & Lc & Hend & _) HK. iIntros "Hσ HR".
  iDestruct (pts_facts with "Hσ HR") as %(Hag & _). iPureIntro.
  pose proof (all_agree_elem _ _ _ _ Hag (all_ps_live K B X p.1 pl xs cs 4 Hp Hx HK)) as Hl. cbn in Hl.
  exists (pl_reg pl). cbn [fst snd]. split; [exact Hl | lia].
Qed.

(** The checker's step for a CPUID call is a valid step of the logic.
    The option says whether the call passes a subleaf, which decides
    between `c: zcpuid` and `c: zcpuid_count`. *)
Lemma cpuid_holds (osub : option aint) la pa pb pc pd B0 st st' f e l args rest j ws Φ :
  let sub := match osub with Some _ => true | None => false end in
  let g := TAtom (if sub then "zcpuid_count" else "zcpuid")%string in
  registry g = Some (os_cpuid_contract sub) -> find_fn ge g = None -> lookup g (ge_globals ge) = None ->
  arg_classes args = W :: (if sub then [W] else []) ++ [P; P; P; P] ->
  acpuid (ow_leaf4_ends w0) (VI la) osub [pa; pb; pc; pd] st = Some st' ->
  map_option (arg_x ge e) args = Some ws ->
  AS.dstate ge guard gobjs B0 st e (VI la :: sub_vals osub ++ [pa; pb; pc; pd]) ws -∗
  ▷ (∀ e', AS.dstate ge guard gobjs B0 st' e' [] [] -∗
       WP (ERun (mkFrame f e' [] None (Exec l rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e [] None (Exec l (Call CVoid (Global g) args :: rest) j)) : zexpr) {{ Φ }}.
Proof using Type.
  intros sub g Hreg Hfn Hgl Hks Hac Hargs.
  iIntros "(%B & %X & [[%B1 ->] (%ρ & %HM & %Hwf & %Hv)] & Hown) HK".
  destruct (acpuid_inv _ _ _ _ _ _ _ _ _ Hac)
    as (a & b & c & d & st1 & st2 & st3 & Epa & Epb & Epc & Epd & Hdis & Ea & Eb & Ec & Ed).
  destruct (acpuid_blocks guard ge gobjs ρ _ st e X _ _ _ a b c d st1 st2 st3 st' HM Ea Eb Ec Ed)
    as (pla & xa & ca & plb & xb & cb & plc & xc & cc & pld & xd & cd & Ba & Bb & Bc & Bd).
  iDestruct (pts_keys_nodup with "Hown") as %Hnd.
  destruct (disjoint4_apart a b c d Hdis) as (Aab & Aac & Aad & Abc & Abd & Acd).
  pose proof (blk_apart _ _ _ _ _ _ _ _ _ _ Ba Bb Aab Hnd) as Pab.
  pose proof (blk_apart _ _ _ _ _ _ _ _ _ _ Ba Bc Aac Hnd) as Pac.
  pose proof (blk_apart _ _ _ _ _ _ _ _ _ _ Ba Bd Aad Hnd) as Pad.
  pose proof (blk_apart _ _ _ _ _ _ _ _ _ _ Bb Bc Abc Hnd) as Pbc.
  pose proof (blk_apart _ _ _ _ _ _ _ _ _ _ Bb Bd Abd Hnd) as Pbd.
  pose proof (blk_apart _ _ _ _ _ _ _ _ _ _ Bc Bd Acd Hnd) as Pcd.
  destruct (cpuid_words ge ρ _ _ osub la pa pb pc pd ws Hwf Hv)
    as (wa & wb & wc & wd & -> & Wl & Ws & [Wa Da] & [Wb Db] & [Wc Dc] & [Wd Dd]).
  pose proof (exact_ptr_sound guard ge gobjs ρ _ st e X pa wa a pla HM Wa Da Epa (proj1 Ba)) as ->.
  pose proof (exact_ptr_sound guard ge gobjs ρ _ st e X pb wb b plb HM Wb Db Epb (proj1 Bb)) as ->.
  pose proof (exact_ptr_sound guard ge gobjs ρ _ st e X pc wc c plc HM Wc Dc Epc (proj1 Bc)) as ->.
  pose proof (exact_ptr_sound guard ge gobjs ρ _ st e X pd wd d pld HM Wd Dd Epd (proj1 Bd)) as ->.
  assert (Ca : pl_cap pla = Obj (pl_base pla)) by (unfold pl_cap; by rewrite (proj1 (proj2 (proj2 Ba)))).
  assert (Cb : pl_cap plb = Obj (pl_base plb)) by (unfold pl_cap; by rewrite (proj1 (proj2 (proj2 Bb)))).
  assert (Cc : pl_cap plc = Obj (pl_base plc)) by (unfold pl_cap; by rewrite (proj1 (proj2 (proj2 Bc)))).
  assert (Cd : pl_cap pld = Obj (pl_base pld)) by (unfold pl_cap; by rewrite (proj1 (proj2 (proj2 Bd)))).
  rewrite Ca Cb Cc Cd in Hargs |- *.
  set (Ka := win_keys (pl_base pla) a.2 4). set (Kb := win_keys (pl_base plb) b.2 4).
  set (Kc := win_keys (pl_base plc) c.2 4). set (Kd := win_keys (pl_base pld) d.2 4).
  iAssert (pts (but [] (all_ps (B0 ++ B1) X))) with "[Hown]" as "HR"; first by rewrite but_nil.
  iDestruct (blk_take [] _ X d pld xd cd Bd Hnd with "HR") as "[Hd HR]".
  { intros l0 _. apply not_elem_of_nil. }
  rewrite app_nil_r. fold Kd.
  iDestruct (blk_take Kd _ X c plc xc cc Bc Hnd with "HR") as "[Hc HR]".
  { intros l0 Hl. exact (win_keys_apart _ _ _ _ _ _ l0 Pcd Hl). }
  fold Kc.
  iDestruct (blk_take (Kc ++ Kd) _ X b plb xb cb Bb Hnd with "HR") as "[Hb HR]".
  { intros l0 Hl. apply not_elem_of_app.
    split; [exact (win_keys_apart _ _ _ _ _ _ l0 Pbc Hl) | exact (win_keys_apart _ _ _ _ _ _ l0 Pbd Hl)]. }
  fold Kb.
  iDestruct (blk_take (Kb ++ Kc ++ Kd) _ X a pla xa ca Ba Hnd with "HR") as "[Ha HR]".
  { intros l0 Hl. apply not_elem_of_app. split; [exact (win_keys_apart _ _ _ _ _ _ l0 Pab Hl)|].
    apply not_elem_of_app. split; [exact (win_keys_apart _ _ _ _ _ _ l0 Pac Hl) | exact (win_keys_apart _ _ _ _ _ _ l0 Pad Hl)]. }
  fold Ka.
  assert (HKall : forall l0, l0 ∈ Ka ++ Kb ++ Kc ++ Kd -> exists b0 k0, l0 ∈ win_keys b0 k0 4).
  { intros l0 Hl. repeat (apply elem_of_app in Hl as [Hl|Hl]; [by eexists _, _|]). by eexists _, _. }
  iApply (wp_cpuid sub f e [] l args rest j _ (dint ρ la) (pl_base pla) a.2 (pl_base plb) b.2
            (pl_base plc) c.2 (pl_base pld) d.2 (pts (but (Ka ++ Kb ++ Kc ++ Kd) (all_ps (B0 ++ B1) X)))
            with "HR Ha Hb Hc Hd"); [exact Hreg | exact Hfn | exact Hgl | exact Hargs | | | |].
  { apply cpuid_abi. exact Hks. }
  { unfold sub. by destruct osub. }
  { intros σ. iIntros "Hσ HR".
    iDestruct (blk_at_live _ _ _ _ _ _ _ σ Bc HKall with "Hσ HR") as %Lc.
    iDestruct (blk_at_live _ _ _ _ _ _ _ σ Ba HKall with "Hσ HR") as %La.
    iDestruct (blk_at_live _ _ _ _ _ _ _ σ Bb HKall with "Hσ HR") as %Lb.
    iDestruct (blk_at_live _ _ _ _ _ _ _ σ Bd HKall with "Hσ HR") as %Ld.
    iPureIntro. repeat constructor; assumption. }
  iNext. iIntros "HR Ha Hb Hc Hd".
  iDestruct "Ha" as (ya da) "[%Fa Ha]". destruct Fa as (Lya & Lda & Bya & Fa).
  iDestruct "Hb" as (yb db) "[%Fb Hb]". destruct Fb as (Lyb & Ldb & Byb).
  iDestruct "Hc" as (yc dc) "[%Fc Hc]". destruct Fc as (Lyc & Ldc & Byc & Fc).
  iDestruct "Hd" as (yd dd) "[%Fd Hd]". destruct Fd as (Lyd & Ldd & Byd).
  assert (Hbr : forall n, Forall (wf_byte n) (repeat BR 4)) by (intros n; repeat constructor).
  assert (Hea : Forall2 (dbyte guard ρ) (eax_bytes (ow_leaf4_ends w0) st la osub) ya).
  { apply (eax_bytes_sound guard ge gobjs ρ _ st e X _ la osub ya HM Wl (conj Lya Bya)).
    intros H4 Hl s -> Hs. apply Fa; [exact H4 | exact Hl | exact Hs | | |]; unfold blocks_apart; lia. }
  assert (Hec : Forall2 (dbyte guard ρ) (ecx_bytes st la) yc).
  { apply (ecx_bytes_sound guard ge gobjs ρ _ st e X la yc HM Wl (conj Lyc Byc)).
    intros Hl Hb. rewrite -Hb. symmetry. apply Fc; [exact Hl|]. unfold blocks_apart. lia. }
  destruct (cpuid_out_sound guard ge gobjs ρ _ st e X a _ st1 HM Ea (eax_bytes_length _ _ _ _)
              (eax_bytes_wf _ _ _ _ _ Ws)) as (pla1 & xa1 & ca1 & Ba1 & Hn1 & HM1).
  specialize (HM1 ya da Hea Lda).
  destruct (cpuid_out_sound guard ge gobjs ρ _ st1 e _ b _ st2 HM1 Eb eq_refl (Hbr _))
    as (plb1 & xb1 & cb1 & Bb1 & Hn2 & HM2).
  specialize (HM2 yb db (br_bytes guard ρ yb (conj Lyb Byb)) Ldb).
  destruct (cpuid_out_sound guard ge gobjs ρ _ st2 e _ c _ st3 HM2 Ec (ecx_bytes_length _ _) (ecx_bytes_wf _ _ _))
    as (plc1 & xc1 & cc1 & Bc1 & Hn3 & HM3).
  specialize (HM3 yc dc Hec Ldc).
  destruct (cpuid_out_sound guard ge gobjs ρ _ st3 e _ d _ st' HM3 Ed eq_refl (Hbr _))
    as (pld1 & xd1 & cd1 & Bd1 & Hn4 & HM4).
  specialize (HM4 yd dd (br_bytes guard ρ yd (conj Lyd Byd)) Ldd).
  pose proof (blk_at_place _ _ _ _ _ _ _ _ _ _ Ba Ba1) as ->. pose proof (blk_at_place _ _ _ _ _ _ _ _ _ _ Bb Bb1) as ->.
  pose proof (blk_at_place _ _ _ _ _ _ _ _ _ _ Bc Bc1) as ->. pose proof (blk_at_place _ _ _ _ _ _ _ _ _ _ Bd Bd1) as ->.
  destruct (blk_give (Kb ++ Kc ++ Kd) _ X a pla xa1 ca1 ya da Ba1 Lya Lda Hnd) as [Hnd1 Ga].
  { intros l0 Hl. apply not_elem_of_app. split; [exact (win_keys_apart _ _ _ _ _ _ l0 Pab Hl)|].
    apply not_elem_of_app. split; [exact (win_keys_apart _ _ _ _ _ _ l0 Pac Hl) | exact (win_keys_apart _ _ _ _ _ _ l0 Pad Hl)]. }
  destruct (blk_give (Kc ++ Kd) _ _ b plb xb1 cb1 yb db Bb1 Lyb Ldb Hnd1) as [Hnd2 Gb].
  { intros l0 Hl. apply not_elem_of_app.
    split; [exact (win_keys_apart _ _ _ _ _ _ l0 Pbc Hl) | exact (win_keys_apart _ _ _ _ _ _ l0 Pbd Hl)]. }
  destruct (blk_give Kd _ _ c plc xc1 cc1 yc dc Bc1 Lyc Ldc Hnd2) as [Hnd3 Gc].
  { intros l0 Hl. exact (win_keys_apart _ _ _ _ _ _ l0 Pcd Hl). }
  destruct (blk_give [] _ _ d pld xd1 cd1 yd dd Bd1 Lyd Ldd Hnd3) as [_ Gd].
  { intros l0 _. apply not_elem_of_nil. }
  iPoseProof (Ga with "Ha HR") as "HR". iPoseProof (Gb with "Hb HR") as "HR".
  iPoseProof (Gc with "Hc HR") as "HR". rewrite app_nil_r in Gd. iPoseProof (Gd with "Hd HR") as "HR". rewrite but_nil.
  iApply "HK". iExists (B0 ++ B1), _. iFrame "HR". iPureIntro. split; [by exists B1|].
  exists ρ. split; [exact HM4|]. split; constructor.
Qed.

(** A program may call `c: zxgetbv` only when the kernel enabled
    XSAVE. The checker takes the step only when its guard is set, and
    the guard means exactly that. The call returns some 64-bit number,
    which the checker names with a new symbol. *)
Lemma xgetbv_holds B0 st st' f e l d args rest j ws Φ s st2 :
  registry (TAtom "zxgetbv") = Some os_xgetbv_contract ->
  find_fn ge (TAtom "zxgetbv") = None -> lookup (TAtom "zxgetbv") (ge_globals ge) = None ->
  st_guard st = true -> fresh st 0 (2 ^ 64 - 1) = (s, st2) -> st' = bind st2 d (VI (S s)) ->
  map_option (arg_x ge e) args = Some ws ->
  AS.dstate ge guard gobjs B0 st e [] ws -∗
  ▷ (∀ e', AS.dstate ge guard gobjs B0 st' e' [] [] -∗
       WP (ERun (mkFrame f e' [] None (Exec l rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e [] None (Exec l (Call (CResult d L) (Global (TAtom "zxgetbv")) args :: rest) j)) : zexpr)
     {{ Φ }}.
Proof using Type.
  intros Hreg Hfn Hgl Hg Hfr -> Hargs.
  iIntros "(%B & %X & [[%B1 ->] (%ρ & %HM & _ & %Hv)] & Hown) HK".
  apply Forall2_nil_inv_l in Hv as ->.
  assert (args = []) as ->.
  { destruct args as [|x args]; [reflexivity|]. cbn in Hargs. destruct (arg_x ge e x); [|discriminate].
    destruct (map_option (arg_x ge e) args); discriminate. }
  iApply (wp_zxgetbv f e [] l d rest j Φ Hreg Hfn Hgl).
  { destruct (M_sat _ _ _ _ _ _ _ _ HM) as (_ & _ & _ & Hgd). exact (Hgd Hg). }
  iNext. iIntros (v Hvr).
  destruct (fresh_sound guard ge gobjs ρ _ st e X 0 (2 ^ 64 - 1) v s st2 HM ltac:(lia) Hfr) as (ρ' & HM2 & _ & Hs & Hρ).
  iApply "HK". iExists (B0 ++ B1), X. iFrame "Hown". iPureIntro. split; [by exists B1|].
  exists ρ'. split; [|split; constructor].
  apply (M_bind guard ge gobjs ρ' _ st2 e X d (VI (S s)) (WInt v) HM2); [exact Hs|]. cbn [dval dint]. by rewrite Hρ.
Qed.

(** The three calls are external in the program: the registry gives
    each its contract, and the program neither defines a function nor
    holds a symbol of that name. *)
Definition cpu_calls : Prop :=
  (registry (TAtom "zcpuid") = Some (os_cpuid_contract false) /\ find_fn ge (TAtom "zcpuid") = None /\
   lookup (TAtom "zcpuid") (ge_globals ge) = None) /\
  (registry (TAtom "zcpuid_count") = Some (os_cpuid_contract true) /\ find_fn ge (TAtom "zcpuid_count") = None /\
   lookup (TAtom "zcpuid_count") (ge_globals ge) = None) /\
  (registry (TAtom "zxgetbv") = Some os_xgetbv_contract /\ find_fn ge (TAtom "zxgetbv") = None /\
   lookup (TAtom "zxgetbv") (ge_globals ge) = None).

(** The hook of [CpuRules](CpuRules.v) is sound. Its guard means that
    the kernel enabled XSAVE, and it uses the leaf 4 fact exactly when
    the world has it. *)
Theorem cpu_builtin_holds :
  cpu_calls ->
  AS.builtin_holds registry (os_wi w0) ge guard (cpu_builtin (ow_leaf4_ends w0)) gobjs.
Proof using Type.
  intros ((R1 & F1 & G1) & (R2 & F2 & G2) & (R3 & F3 & G3)) B0 g r xs st st' f e l args rest j ws Φ Hb Hargs.
  unfold cpu_builtin in Hb. destruct (is_atom g "zcpuid") eqn:E1.
  { apply name_eqb_true in E1 as ->. destruct r; try discriminate. destruct xs as [|lv ps]; [discriminate|].
    destruct (all2 class_eqb (arg_classes args) [W; P; P; P; P]) eqn:Ek; [|discriminate].
    apply all2_class_eq in Ek. injection Hb as Hb.
    destruct lv as [la| | | | | |]; try discriminate.
    destruct ps as [|pa [|pb [|pc [|pd [|]]]]]; try discriminate.
    exact (cpuid_holds None la pa pb pc pd B0 st st' f e l args rest j ws Φ R1 F1 G1 Ek Hb Hargs). }
  destruct (is_atom g "zcpuid_count") eqn:E2.
  { apply name_eqb_true in E2 as ->. destruct r; try discriminate. destruct xs as [|lv [|[sa| | | | | |] ps]]; try discriminate.
    destruct (all2 class_eqb (arg_classes args) [W; W; P; P; P; P]) eqn:Ek; [|discriminate].
    apply all2_class_eq in Ek. injection Hb as Hb.
    destruct lv as [la| | | | | |]; try discriminate.
    destruct ps as [|pa [|pb [|pc [|pd [|]]]]]; try discriminate.
    exact (cpuid_holds (Some sa) la pa pb pc pd B0 st st' f e l args rest j ws Φ R2 F2 G2 Ek Hb Hargs). }
  destruct (is_atom g "zxgetbv") eqn:E3; [|discriminate].
  apply name_eqb_true in E3 as ->. destruct r as [|d k|]; try discriminate. destruct k; try discriminate.
  destruct xs; [|discriminate]. destruct (st_guard st) eqn:Eg; [|discriminate].
  destruct (fresh st 0 (2 ^ 64 - 1)) as [s st2] eqn:Ef. injection Hb as <-.
  exact (xgetbv_holds B0 st _ f e l d args rest j ws Φ s st2 R3 F3 G3 Eg Ef eq_refl Hargs).
Qed.

End hook.
