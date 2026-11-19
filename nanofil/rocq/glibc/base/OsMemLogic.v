(** C code reads and writes memory while the operating system keeps track of live objects.
    These rules describe the bytes of an integer, preserve the OS world across stores,
    and justify reads through shared pointers. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  Pieces Heap Language Logic StringLogic MemLogic StepRules ExternalCalls ExternalMachine.
From Nanofil Require WordBits.
From Glibc Require Import Fix OsBlocks OsWorld GlibcProgram.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L.
Open Scope Z_scope.

Section cells.
Context `{!gen_heapGS piece pval Σ}.

(** The four little-endian bytes of the `c: int` with bits x. *)
Definition int_bytes (x : Z) : list Z := le_bytes x 4.

(** [int_cell] b o x: owning the `c: int` at offset o of b, with bits x
    below 2^32. *)
Definition int_cell (b o x : Z) : iProp Σ := ⌜0 <= x < 2 ^ 32⌝ ∗ bytes b o (int_bytes x).

(** [int_cellq] dq b o x: [int_cell] at the share dq. *)
Definition int_cellq (dq : dfrac) (b o x : Z) : iProp Σ := ⌜0 <= x < 2 ^ 32⌝ ∗ bytesq dq b o (int_bytes x).

(** A shared reader can borrow a contiguous source range and return it to recover the whole source. *)
Lemma bytesq_sub dq b o ys (j c : nat) : (j + c <= length ys)%nat ->
  bytesq dq b o ys ⊢ bytesq dq b (o + Z.of_nat j) (take c (drop j ys)) ∗
    (bytesq dq b (o + Z.of_nat j) (take c (drop j ys)) -∗ bytesq dq b o ys).
Proof using Type.
  intros H. set (zs := take c (drop j ys)).
  assert (E : ys = (take j ys ++ zs ++ drop c (drop j ys))%list) by (unfold zs; rewrite !take_drop; reflexivity).
  assert (Lj : length (take j ys) = j) by (rewrite length_take_le; lia).
  rewrite {1 2}E /bytesq !byte_ps_app !ptsq_app Lj.
  iIntros "(H1 & H2 & H3)". iFrame "H2". iIntros "H2". iFrame.
Qed.

(** A share of an object's life splits into two halves. *)
Lemma liveq_half q b reg : liveq (DfracOwn q) b reg ⊣⊢ liveq (DfracOwn (q / 2)) b reg ∗ liveq (DfracOwn (q / 2)) b reg.
Proof using Type. rewrite /liveq -ptsq_split Qp.div_2. done. Qed.

(** A share of a stored pointer splits into two halves. *)
Lemma pcellq_half q b o p : pcellq (DfracOwn q) b o p ⊣⊢ pcellq (DfracOwn (q / 2)) b o p ∗ pcellq (DfracOwn (q / 2)) b o p.
Proof using Type. rewrite /pcellq -ptsq_split Qp.div_2. done. Qed.

(** A whole life splits into two halves. *)
Lemma live_halves b reg : live b reg ⊣⊢ liveq (DfracOwn (1 / 2)) b reg ∗ liveq (DfracOwn (1 / 2)) b reg.
Proof using Type. rewrite /live /liveq pts_ptsq -ptsq_split Qp.half_half. done. Qed.

(** A whole stored pointer splits into two halves. *)
Lemma pcell_halves b o p : pcell b o p ⊢ pcellq (DfracOwn (1 / 2)) b o p ∗ pcellq (DfracOwn (1 / 2)) b o p.
Proof using Type. iIntros "H". iApply pcellq_half. rewrite /pcellq -pts_ptsq. iExact "H". Qed.

(** Eight zero bytes with no capabilities are a stored null pointer. *)
Lemma zero_bytes_pcell b : bytes b 0 (repeat 0 8%nat) -∗ auxes b 0 (repeat CNone 8%nat) -∗ pcell b 0 null.
Proof using Type.
  assert (E1 : byte_ps b 0 (repeat 0 8%nat) = cell b 0 (ptr_addr null)) by reflexivity.
  assert (E2 : aux_ps b 0 (repeat CNone 8%nat) = (PAux b 0, VAux (ptr_cap null)) :: aux_ps b 1 (repeat CNone 7%nat))
    by reflexivity.
  rewrite /bytes /auxes /pcell E1 E2 (pts_app [_] (aux_ps _ _ _)). iIntros "H [A _]".
  rewrite (pts_app [_] (cell _ _ _)). iFrame.
Qed.

End cells.

(** No piece of ps is a life token. *)
Definition no_life (ps : list (piece * pval)) : Prop :=
  forall l v, (l, v) ∈ ps -> match l with PLive _ => False | _ => True end.

(** A long's cell has none. *)
Lemma no_life_cell b o x : no_life (cell b o x).
Proof.
  intros l v Hin. unfold cell in Hin. cbn in Hin.
  repeat (apply elem_of_cons in Hin as [Hin|Hin]; [injection Hin as -> _; exact I|]).
  by apply not_elem_of_nil in Hin.
Qed.

(** Bytes have none. *)
Lemma no_life_byte_ps b o xs : no_life (byte_ps b o xs).
Proof. intros l v Hin. apply byte_ps_elem in Hin as (i & x & _ & -> & _). exact I. Qed.

(** A pointer's cell, its aux slot and its bytes, has none. *)
Lemma no_life_pcell b o c a : no_life ((PAux b o, VAux c) :: cell b o a).
Proof.
  intros l v Hin. apply elem_of_cons in Hin as [[= -> _] | Hin]; [exact I|]. exact (no_life_cell _ _ _ _ _ Hin).
Qed.

(** One byte has none. *)
Lemma no_life_byte b o x : no_life [(PByte b o, VByte x)].
Proof. intros l v Hin. apply list_elem_of_singleton in Hin. injection Hin as -> _. exact I. Qed.

(** A store into the object b that keeps every region, whose new
    pieces are b's life token, as owned, and pieces with no life
    token, keeps [os_wi]. *)
Lemma os_wi_store_life w0 b reg ps ps' m m' wd h :
  m_regions m' = m_regions m -> no_life ps' ->
  (forall l v, (l, v) ∈ (PLive b, VLive reg) :: ps -> h !! l = Some v) -> os_wi w0 m wd h ->
  os_wi w0 m' wd (overwrite ((PLive b, VLive reg) :: ps') h).
Proof.
  intros Er Hn Hh Hw. apply (os_wi_store w0 m m' wd h); [exact Er | | exact Hw].
  intros l v Hin. apply elem_of_cons in Hin as [[= -> ->] | Hin].
  - apply Hh. left.
  - pose proof (Hn l v Hin) as H. destruct l; [contradiction | exact I | exact I | exact I].
Qed.

(** The four bytes of an int below 2^32 read back as it. *)
Lemma of_bytes_int x : 0 <= x < 2 ^ 32 -> of_bytes (le_bytes x 4) = x.
Proof.
  intros Hx. transitivity (x mod 2 ^ (8 * (3 + 1))); [| apply Z.mod_small; exact Hx].
  rewrite WordBits.low_step; [|lia]. change (8 * 3) with (8 * (2 + 1)).
  rewrite WordBits.low_step; [|lia]. change (8 * 2) with (8 * (1 + 1)).
  rewrite WordBits.low_step; [|lia]. change (8 * 1) with (8 * (0 + 1)).
  rewrite WordBits.low_step; [|lia]. rewrite Z.mul_0_r Z.pow_0_r Z.mod_1_r. cbn -[byte_of].
  change (Z.of_nat 0) with 0. change (Z.of_nat 1) with 1. change (Z.of_nat 2) with 2. change (Z.of_nat 3) with 3. lia.
Qed.

(** A signed 32-bit load of an int's bytes, at class [W], is its bits. *)
Lemma load_sw_int x : 0 <= x < 2 ^ 32 -> extended Sw W (of_bytes (le_bytes x 4)) = Some (WInt x).
Proof.
  intros Hx. rewrite of_bytes_int; [|exact Hx]. cbn. f_equal. f_equal. unfold sign_extension.
  rewrite (Z.mod_small x); [|exact Hx]. destruct (2 ^ 31 <=? x) eqn:E.
  - apply Z.leb_le in E. rewrite Zminus_mod Z_mod_same_full Z.sub_0_r !Z.mod_mod; [|lia].
    apply Z.mod_small. exact Hx.
  - apply Z.mod_small. exact Hx.
Qed.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

Local Instance step_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** [wp_check_read] at a share: a [[check]] for reading of the pointer
    p, through a read-write or read-only capability for the object b of
    which a share of the life is owned. *)
Lemma wp_check_read_dq f e ls l d lo hi al args rest j classes p b reg dq Φ :
  op_arg_classes (Check lo hi Read al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b -> b <= raw_address (ptr_addr p) lo ->
  raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg -> raw_address (ptr_addr p) lo mod al = 0 ->
  liveq dq b reg -∗
  ▷ (liveq dq b reg -∗ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (Check lo hi Read al) args :: rest) j)) : sexpr) {{ Φ }}.
Proof using SafepointStable0.
  intros Hc Hx Hp H1 H2 H3. apply (wp_read_dq registry wi ge dq _ _ _ []).
  intros m fuel (Hf & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E _] _].
  apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
  apply op_check. exact (access_read _ _ _ _ _ _ _ Hp E H1 H2 H3).
Qed.

End rules.

Import ProgramAbbreviations.
Section pointer_load.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** [wp_raw_load_pointer] of a null pointer, whose capability needs
    no life. *)
Lemma wp_raw_load_null f e ls l d off args rest j classes p b reg o Φ :
  op_arg_classes (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) P = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o -> (b + o) mod 8 = 0 ->
  live b reg -∗ pcell b o null -∗
  ▷ (live b reg -∗ pcell b o null -∗
     WP (ERun (mkFrame f (put d (WPtr null) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec l (Let d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) args :: rest) j))
       : sexpr) {{ Φ }}.
Proof using Type.
  iIntros (Hc Hx Hp Ha Hal) "Hl Hc HK".
  iApply (wp_raw_load_pointer with "Hl Hc [//]");
    [exact Hc | exact Hx | exact Hp | exact Ha | exact Hal | cbn; lia |].
  iNext. iIntros "Hl Hc _". iApply ("HK" with "Hl Hc").
  Unshelve. exact reg.
Qed.

(** Every live object lies in the address space from 0 to 2^48
    (Runtime.v's [objects_fit]): owning its life at any share shows
    it, before a step. *)
Lemma wp_live_fit dq b reg fr Φ :
  liveq dq b reg -∗
  (⌜0 <= b /\ r_end reg <= 2 ^ 48⌝ -∗ liveq dq b reg -∗ WP (ERun fr : sexpr) {{ Φ }}) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  iIntros "Hl HK". rewrite !wp_unfold /wp_pre /=. iIntros (σ ns κs nt) "Hσ".
  iDestruct (ptsq_facts with "Hσ Hl") as %(Hag & _ & Hfit).
  cbn [all_agree agree_piece fst snd] in Hag. destruct Hag as [[Hreg _] _].
  destruct (Hfit b reg Hreg) as [H0 H48].
  iSpecialize ("HK" with "[%] Hl"); [lia|]. iApply ("HK" $! σ ns κs nt with "Hσ").
Qed.

(** [wp_live_fit] for a whole life token. *)
Lemma wp_live_fit1 b reg fr Φ :
  live b reg -∗
  (⌜0 <= b /\ r_end reg <= 2 ^ 48⌝ -∗ live b reg -∗ WP (ERun fr : sexpr) {{ Φ }}) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  iIntros "Hl HK". rewrite /live pts_ptsq. iApply (wp_live_fit with "Hl").
  iIntros (H) "Hl". rewrite -pts_ptsq. iApply ("HK" with "[//] Hl").
Qed.

(** The body reads the first slot of the argument array three times.
    The second and third reads renew the check of the first one. The
    call holds only a share of the array, and a share of the lifetime
    of an object is enough to renew a check for reading. *)
Lemma wp_renew_read_dq f e ls l d lo hi al args rest j classes p1 p b reg dq Φ :
  op_arg_classes (Renew lo hi Read al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p1; WPtr p] ->
  ptr_cap p1 = ptr_cap p -> ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  b <= raw_address (ptr_addr p) lo -> raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg ->
  raw_address (ptr_addr p) lo mod al = 0 ->
  liveq dq b reg -∗
  ▷ (liveq dq b reg -∗ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (Renew lo hi Read al) args :: rest) j)) : sexpr) {{ Φ }}.
Proof using Type.
  intros Hc Hx Hp1 Hp H1 H2 H3. apply (wp_read_dq registry (os_wi w0) ge dq _ _ _ []).
  intros m fuel (Hf & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E _] _].
  apply rule_let with (classes := classes) (xs := [WPtr p1; WPtr p]); [reflexivity | exact Hc | exact Hx |].
  apply op_renew; [exact Hp1|]. eapply access_read; eauto.
Qed.

End pointer_load.
