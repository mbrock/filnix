(** The parts of GNU Hello's `set_program_name` (HelloName.v's
    [set_program_name_fn]) linked with glibc after the "/.libs/" test,
    for HelloGlibcProgName.v's triple over the [os_world] of
    [OsWorld](../zsys/OsWorld.v).

    - [base_idx], [in_libs], [lt_prefix], [short_idx] and [name_idx]
      say which of argv[0]'s bytes gnulib's progname.c picks: the base
      name past the last `/`, past "lt-" when the seven bytes before it
      are "/.libs/".
    - [word_string_bytes] lends the bytes of a [word_string] as
      `memcmp` owns them, and [word_string_lend] a share of its tail.
    - [memeq_call] is HelloGlibcLeaf.v's `memeq` triple over its
      [memcmp_spec], for pointers into strings.
    - The three cells, Hello's `program_name` and libc's
      `program_invocation_name` and `program_invocation_short_name`, are
      ordinary objects of the memory ([name_cells]): a pointer store
      into one keeps [os_wi] by [os_wi_store] ([os_keeps]), so
      [spn_L18] needs no premise about the world.
    - [spn_L16] is the "lt-" test, by glibc's own strncmp
      ([wp_call_glibc_strncmp]), and the stores after it. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic StringLogic MemLogic HelloLeaf HelloName.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop OsWorld StrrchrLogic StrncmpCode StrcmpBits
  StrncmpBits StrncmpLogic MemFwdLogic.
From Glibc Require OsWorld StrncmpLogic.
From Glibc Require Import Fix.
Open Scope Z_scope.
Open Scope list_scope.

(** Integer arithmetic on an unknown stays folded when a premise is
    computed (Symbolic.v). *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** ## The bytes gnulib picks *)

(** The last byte c of bs counted from i, after acc, is acc's or one of
    bs's. *)
Lemma last_from_in c i bs acc t :
  last_from c i bs acc = Some t -> acc = Some t \/ ((i <= t)%nat /\ bs !! (t - i)%nat = Some c).
Proof.
  revert i acc. induction bs as [|x bs IH]; intros i acc H; cbn in H; [left; exact H|].
  destruct (IH _ _ H) as [E | [Hle Ht]].
  - destruct (Z.eqb_spec x c) as [<-|]; [|left; exact E]. injection E as <-. right.
    rewrite Nat.sub_diag. split; [lia | reflexivity].
  - right. split; [lia|]. replace (t - i)%nat with (S (t - S i)) by lia. exact Ht.
Qed.

(** The last `/` of a string and its NUL is one of the string's bytes. *)
Lemma last_slash s t : last_byte 47 (s ++ [0]) = Some t -> (t < length s)%nat.
Proof.
  unfold last_byte. intros H. destruct (last_from_in _ _ _ _ _ H) as [E | [_ Ht]]; [discriminate|].
  rewrite Nat.sub_0_r in Ht. destruct (Nat.lt_ge_cases t (length s)) as [Hlt|Hge]; [exact Hlt|].
  rewrite lookup_app_r in Ht; [|exact Hge]. destruct (t - length s)%nat; cbn in Ht; discriminate.
Qed.

(** The index of argv[0]'s base name: past its last `/`, or 0. *)
Definition base_idx (s : list Z) : nat :=
  match last_byte 47 (s ++ [0]) with Some t => S t | None => O end.

(** The seven bytes before the base name are "/.libs/". *)
Definition in_libs (s : list Z) : bool :=
  (7 <=? base_idx s)%nat && bool_decide (take 7 (drop (base_idx s - 7) s) = libs_bytes).

(** The base name starts with "lt-". *)
Definition lt_prefix (s : list Z) : bool := bool_decide (take 3 (drop (base_idx s) s) = lt_bytes).

(** The index of `program_invocation_short_name`: the base name, past
    "lt-" in a libtool build directory. *)
Definition short_idx (s : list Z) : nat :=
  if in_libs s && lt_prefix s then (base_idx s + 3)%nat else base_idx s.

(** The index of `program_name` and `program_invocation_name`: argv[0]
    itself, or the short name in a libtool build directory. *)
Definition name_idx (s : list Z) : nat := if in_libs s then short_idx s else O.

(** The base name lies within the string. *)
Lemma base_idx_le s : (base_idx s <= length s)%nat.
Proof.
  unfold base_idx. destruct (last_byte 47 (s ++ [0])) as [t|] eqn:E; [|lia].
  pose proof (last_slash s t E). lia.
Qed.

(** So does the short name. *)
Lemma short_idx_le s : (short_idx s <= length s)%nat.
Proof.
  unfold short_idx. destruct (in_libs s && lt_prefix s) eqn:E; [|apply base_idx_le].
  apply andb_true_iff in E as [_ E]. unfold lt_prefix in E. apply bool_decide_eq_true_1 in E.
  pose proof (f_equal length E) as L. rewrite length_take length_drop in L. unfold lt_bytes in L. cbn [length] in L. lia.
Qed.

(** The name is at or before the short name. *)
Lemma name_idx_le s : (name_idx s <= short_idx s)%nat.
Proof. unfold name_idx. destruct (in_libs s); lia. Qed.

(** strcmp's answer is a 32-bit `int`'s bits. *)
Lemma strcmp_res_range s t : 0 <= strcmp_res s t < 2 ^ 32.
Proof.
  revert t. induction s as [|c s IH]; intros [|d t]; cbn [strcmp_res]; try (apply Z.mod_pos_bound; lia); [lia|].
  destruct (c =? d); [apply IH | apply Z.mod_pos_bound; lia].
Qed.

(** strncmp of a string's tail and "lt-" over 3 bytes: an int that is 0
    just when the tail starts with "lt-". *)
Lemma lt_res s j : Forall (fun c => 0 < c < 256) s ->
  0 <= strncmp_res 3 (drop j s) lt_bytes < 2 ^ 32 /\
  (strncmp_res 3 (drop j s) lt_bytes = 0 <-> take 3 (drop j s) = lt_bytes).
Proof.
  intros Hc. unfold strncmp_res. change (Z.to_nat 3) with 3%nat. change (take 3 lt_bytes) with lt_bytes.
  split; [apply strcmp_res_range|]. apply strcmp_res_zero; [apply Forall_take, Forall_drop, Hc|].
  apply Forall_forall. intros x Hx. apply list_elem_of_In in Hx. cbn in Hx. lia.
Qed.

(** A string's bytes lie in the first 2^48 addresses, after 0. *)
Lemma str_shape_addr p b reg ws s : str_shape p b reg ws s -> 0 < ptr_addr p /\ ptr_addr p + Z.of_nat (length s) < 2 ^ 48.
Proof.
  intros [Hc Hb0 Hb8 Hst Hf Hsp Hlen Hwr Hby Hch]. unfold wstart in Hf.
  pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)).
  pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)). lia.
Qed.

(** A pointer 0 bytes past p is p. *)
Lemma ptr_add_0 p : ptr_add p 0 = p.
Proof. destruct p. unfold ptr_add. cbn. rewrite Z.add_0_r. reflexivity. Qed.

(** The pieces of the bytes xs: the first a, the n after them, and the
    rest. *)
Lemma byte_ps_three b o xs a n : (a + n <= length xs)%nat ->
  byte_ps b o xs = byte_ps b o (take a xs) ++ byte_ps b (o + Z.of_nat a) (take n (drop a xs)) ++
                   byte_ps b (o + Z.of_nat (a + n)) (drop (a + n) xs).
Proof.
  intros H. rewrite -{1}(take_drop a xs) -{1}(take_drop n (drop a xs)) drop_drop !byte_ps_app.
  rewrite length_take_le; [|lia]. rewrite length_take_le; [|rewrite length_drop; lia].
  rewrite Nat2Z.inj_add Z.add_assoc. reflexivity.
Qed.


(** Byte pieces' shares. *)
Module ML := MemLogicOn R LG0.
(** glibc's strncmp. *)
(** The world's rules. *)
(** The Logic instance. *)
Module LG := LG0.
(** Its language. *)
Module L := LG.L.
Import L LG ML.

Section progname.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** Hello's `strncmp` is glibc's. *)
Context (Hstrncmp : find_fn ge (TAtom "strncmp") = Some (Defined glibc_strncmp)).
(** The three cells, each its own 8-aligned object, and the literal
    "lt-". *)
Context (pb nb sb : Z) (preg nreg sreg : region) (tp : ptr)
  (Hpb : lookup (TAtom "program_name") (ge_globals ge) = Some (mkPtr pb (Obj pb)))
  (Hnb : lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (mkPtr nb (Obj nb)))
  (Hsb : lookup (TAtom "program_invocation_short_name") (ge_globals ge) = Some (mkPtr sb (Obj sb)))
  (Htp : lookup (TAtom "progname#str.4") (ge_globals ge) = Some tp)
  (Hpb_cell : 0 <= pb /\ pb mod 8 = 0 /\ pb + 8 <= r_end preg /\ r_end preg <= 2 ^ 48)
  (Hnb_cell : 0 <= nb /\ nb mod 8 = 0 /\ nb + 8 <= r_end nreg /\ r_end nreg <= 2 ^ 48)
  (Hsb_cell : 0 <= sb /\ sb mod 8 = 0 /\ sb + 8 <= r_end sreg /\ r_end sreg <= 2 ^ 48).

(** [os_wi] w0 survives safepoints. *)
Local Instance pn_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The Iris instance of the registry and [os_wi] w0. *)
Local Instance pn_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry (os_wi w0) ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** HelloGlibcLeaf.v's [memcmp_spec], over this file's byte pieces: a
    call triple for the function at `memcmp` that, on fewer than 16
    bytes, returns an int that is 0 just when they are equal.
    Only fewer than 16 bytes: from 16 bytes on glibc's own memcmp
    reads words through pointers it rebuilds from integers, which have
    no capability, so it traps (MemcmpLogic.v's header). *)
Definition memcmp_spec : Prop :=
  exists F, find_fn ge (TAtom "memcmp") = Some (Defined F) /\
  (forall p q n, is_Some (call_frame F [WPtr p; WPtr q; WInt n])) /\
  forall fr dq1 dq2 b reg o c xs b' reg' o' c' ys Φ,
    call_frame F [WPtr (mkPtr (b + o) c); WPtr (mkPtr (b' + o') c'); WInt (Z.of_nat (length xs))] = Some fr ->
    (length xs < 16)%nat -> (c = Obj b \/ c = Ro b) -> (c' = Obj b' \/ c' = Ro b') -> length ys = length xs ->
    0 <= o -> 0 <= o' -> b + o + Z.of_nat (length xs) <= r_end reg ->
    b' + o' + Z.of_nat (length xs) <= r_end reg' -> r_end reg <= 2 ^ 48 -> r_end reg' <= 2 ^ 48 ->
    Forall (fun x => 0 <= x < 256) xs -> Forall (fun x => 0 <= x < 256) ys ->
    ⊢ liveq dq1 b reg -∗ bytesq dq1 b o xs -∗ liveq dq2 b' reg' -∗ bytesq dq2 b' o' ys -∗
      (∀ k, ⌜k mod 2 ^ 32 = 0 <-> xs = ys⌝ -∗ liveq dq1 b reg -∗ bytesq dq1 b o xs -∗
            liveq dq2 b' reg' -∗ bytesq dq2 b' o' ys -∗ Φ (Ret (WInt k))) -∗
      WP (ERun fr : gexpr) {{ Φ }}.

(** The three cells, holding x, y and z. *)
Definition name_cells (x y z : ptr) : iProp Σ :=
  live pb preg ∗ pcell pb 0 x ∗ live nb nreg ∗ pcell nb 0 y ∗ live sb sreg ∗ pcell sb 0 z.

(** ## Strings' bytes and tails *)

(** The n bytes of a string from its i-th, as memcmp owns them, and a
    wand that gives the string back. *)
Lemma word_string_bytes dq p s i n : (i + n <= length s)%nat ->
  word_string dq p s ⊢ ∃ b reg, ⌜(ptr_cap p = Obj b \/ ptr_cap p = Ro b) /\ 0 < b /\ b <= ptr_addr p /\
      ptr_addr p + Z.of_nat (i + n) < r_end reg /\ r_end reg <= 2 ^ 48⌝ ∗
    liveq dq b reg ∗ bytesq dq b (ptr_addr p - b + Z.of_nat i) (take n (drop i s)) ∗
    (liveq dq b reg -∗ bytesq dq b (ptr_addr p - b + Z.of_nat i) (take n (drop i s)) -∗ word_string dq p s).
Proof.
  intros Hin. iIntros "(%b & %reg & %ws & %Hs & Hl & Hw)".
  pose proof Hs as [Hc Hb0 Hb8 Hst Hf Hsp Hlen Hwr Hby Hch].
  remember (Z.to_nat (ptr_addr p mod 8)) as k eqn:Ek.
  assert (Hk : Z.of_nat k = ptr_addr p mod 8) by (rewrite Ek; apply Z2Nat.id, Z.mod_pos_bound; lia).
  assert (Hlb : (k + S (length s) <= length (wbytes ws))%nat).
  { pose proof (f_equal length Hby) as L. rewrite length_take length_drop length_app in L. cbn [length] in L. lia. }
  assert (Hmid : take n (drop (k + i) (wbytes ws)) = take n (drop i s)).
  { rewrite -drop_drop (take_drop_commute (drop k (wbytes ws)) n i) (take_drop_commute s n i).
    replace (take (i + n) (drop k (wbytes ws))) with (take (i + n) (take (S (length s)) (drop k (wbytes ws))))
      by (rewrite take_take; f_equal; lia).
    rewrite Hby take_app_le; [reflexivity | lia]. }
  rewrite /wstart in Hf. pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)).
  assert (Hend : ptr_addr p + Z.of_nat (i + n) < r_end reg).
  { pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)). lia. }
  assert (Hoff : wstart p - b + Z.of_nat (k + i) = ptr_addr p - b + Z.of_nat i) by (unfold wstart; lia).
  assert (Hsplit : words_ps b (wstart p - b) ws =
    byte_ps b (wstart p - b) (take (k + i) (wbytes ws)) ++ byte_ps b (ptr_addr p - b + Z.of_nat i) (take n (drop i s)) ++
    byte_ps b (wstart p - b + Z.of_nat (k + i + n)) (drop (k + i + n) (wbytes ws))).
  { rewrite words_ps_bytes (byte_ps_three b (wstart p - b) (wbytes ws) (k + i) n ltac:(lia)) Hoff Hmid. reflexivity. }
  iEval (rewrite Hsplit !ptsq_app) in "Hw". iDestruct "Hw" as "(H1 & H2 & H3)".
  iExists b, reg. iSplit; [iPureIntro; split; [exact Hc | lia]|]. iFrame "Hl H2".
  iIntros "Hl H2". iExists b, reg, ws. iSplit; [done|]. iFrame "Hl".
  rewrite /wwin Hsplit !ptsq_app. iFrame.
Qed.

(** A share of a string's tail from its j-th byte, at a share of the
    string's own, and a wand that gives the string back: half of a
    fraction ([word_string_borrow]), or a copy of a read-only string. *)
Lemma word_string_lend dq p s j : (dq = DfracDiscarded \/ exists q, dq = DfracOwn q) -> (j <= length s)%nat ->
  word_string dq p s ⊢ ∃ dq', word_string dq' (ptr_add p (Z.of_nat j)) (drop j s) ∗
    (word_string dq' (ptr_add p (Z.of_nat j)) (drop j s) -∗ word_string dq p s).
Proof.
  intros Hdq Hj. assert (E : s = take j s ++ drop j s) by (symmetry; apply take_drop).
  assert (Lt : length (take j s) = j) by (apply length_take_le; lia).
  destruct Hdq as [-> | [q ->]].
  - iIntros "#Hs". iExists DfracDiscarded. iSplitL; [|iIntros "_"; iExact "Hs"].
    iPoseProof (word_string_suffix _ p (take j s) (drop j s) with "[]") as "H"; [rewrite -E; done|].
    rewrite Lt. iExact "H".
  - iIntros "Hs". iDestruct (word_string_borrow (q / 2) (q / 2) p (take j s) (drop j s) with "[Hs]") as "[H W]".
    { rewrite Qp.div_2 -E. iExact "Hs". }
    rewrite Lt. iExists (DfracOwn (q / 2)). iFrame "H". iIntros "H". iSpecialize ("W" with "H").
    rewrite Qp.div_2 -E. iExact "W".
Qed.

(** ## The calls and the stores *)

(** HelloGlibcLeaf.v's [memeq_glibc] over this file's [memcmp_spec],
    for pointers q and q' that name fewer than 16 bytes: `memeq` returns
    1 just when the n bytes are equal, and 0 otherwise. *)
Lemma memeq_call (Hcmp : memcmp_spec) dq1 dq2 q q' n b reg o xs b' reg' o' ys Φ : 0 < b -> (length xs < 16)%nat ->
  ptr_addr q = b + o -> ptr_addr q' = b' + o' -> n = Z.of_nat (length xs) ->
  (ptr_cap q = Obj b \/ ptr_cap q = Ro b) -> (ptr_cap q' = Obj b' \/ ptr_cap q' = Ro b') -> length ys = length xs ->
  0 <= o -> 0 <= o' -> b + o + Z.of_nat (length xs) <= r_end reg ->
  b' + o' + Z.of_nat (length xs) <= r_end reg' -> r_end reg <= 2 ^ 48 -> r_end reg' <= 2 ^ 48 ->
  Forall (fun x => 0 <= x < 256) xs -> Forall (fun x => 0 <= x < 256) ys ->
  liveq dq1 b reg -∗ bytesq dq1 b o xs -∗ liveq dq2 b' reg' -∗ bytesq dq2 b' o' ys -∗
  ▷ (liveq dq1 b reg -∗ bytesq dq1 b o xs -∗ liveq dq2 b' reg' -∗ bytesq dq2 b' o' ys -∗
     Φ (Ret (WInt (if decide (xs = ys) then 1 else 0)))) -∗
  WP (ERun (invocation memeq_fn [WPtr q; WPtr q'; WInt n]) : gexpr) {{ Φ }}.
Proof.
  destruct Hcmp as (F & HF & Hfr & Hspec). destruct q as [a c], q' as [a' c']. cbn [ptr_addr ptr_cap].
  intros Hb0 H16 -> -> -> Hc Hc' Hly Ho Ho' Hend Hend' Hr Hr' Hx Hy. iIntros "Hl Hx Hl' Hy HΦ". rewrite memeq_entry.
  assert (Hn : Z.of_nat (length xs) < 2 ^ 64) by lia.
  destruct (Hfr (mkPtr (b + o) c) (mkPtr (b' + o') c') (Z.of_nat (length xs))) as [fr Hfr'].
  iApply wp_enter; [exact find_e_start | reflexivity |]. iNext. cbn [b_insts b_jump e_start].
  iApply (wp_call_bind with "[-]"); [cbn; rewrite (Z.mod_small (Z.of_nat (length xs))); [reflexivity | lia]
    | exact HF | exact Hfr' |]. iNext.
  iApply (Hspec with "Hl Hx Hl' Hy"); [exact Hfr' | exact H16 | exact Hc | exact Hc' | exact Hly | exact Ho | exact Ho'
    | exact Hend | exact Hend' | exact Hr | exact Hr' | exact Hx | exact Hy |].
  iIntros (k Hk) "Hl Hx Hl' Hy". iExists _. iSplit; [done|]. iNext.
  iApply wp_let; [reflexivity | reflexivity | reflexivity | intros ?; reflexivity | iNext].
  iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  match goal with |- environments.envs_entails _ (Φ (Ret (WInt ?X))) =>
    replace X with (if decide (xs = ys) then 1 else 0) end; [iApply ("HΦ" with "Hl Hx Hl' Hy")|].
  rewrite Zmod_0_l Zmod_mod. destruct (decide (xs = ys)) as [E|E].
  - rewrite (proj2 Hk E). reflexivity.
  - destruct (Z.eqb_spec (k mod 2 ^ 32) 0) as [E'|E']; [exfalso; exact (E (proj1 Hk E'))|reflexivity].
Qed.

(** A pointer store into the cell at offset o of the object b keeps
    [os_wi]: it keeps every region, and the life it writes back is the
    one the ghost heap holds ([os_wi_store]). *)
Lemma os_keeps b o reg x xp : forall m wd h,
  (forall l v, (l, v) ∈ [(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x) ->
     h !! l = Some v) ->
  os_wi w0 m wd h ->
  os_wi w0 (store_bytes (store_aux m (b + o) (ptr_cap xp)) (b + o) 8 (ptr_addr xp)) wd
    (overwrite ([(PLive b, VLive reg)] ++ (PAux b o, VAux (ptr_cap xp)) :: cell b o (ptr_addr xp)) h).
Proof.
  intros m wd h Hh Hw. apply (os_wi_store w0 m); [reflexivity | | exact Hw].
  intros l v Hin. destruct l; try exact I. apply Hh.
  apply elem_of_app in Hin as [Hin | Hin]; [apply elem_of_app; left; exact Hin|].
  apply elem_of_cons in Hin as [[=] | Hin]. unfold cell in Hin.
  apply list_elem_of_In, in_map_iff in Hin as (? & [=] & _).
Qed.

(** The stores, from L18 after its phis, where `pr.1` reads as x and
    `pr.3` as z: each cell's check passes and its store keeps [os_wi]. *)
Lemma spn_L18 e x z x0 y0 z0 Φ :
  lookup (TAtom "pr.1") e = Some (WPtr x) -> lookup (TAtom "pr.3") e = Some (WPtr z) ->
  name_cells x0 y0 z0 -∗ ▷ (name_cells x x z -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame set_program_name_fn e [] None (Exec (TAtom "L18") (b_insts s_L18) (b_jump s_L18)))
        : gexpr) {{ Φ }}.
Proof.
  intros Hx Hz. destruct Hpb_cell as (Hp0 & Hp8 & Hpend & Hp48).
  destruct Hnb_cell as (Hn0 & Hn8 & Hnend & Hn48). destruct Hsb_cell as (Hs0 & Hs8 & Hsend & Hs48).
  iIntros "(Hlp & Hcp & Hln & Hcn & Hls & Hcs) HΦ". cbn [b_insts b_jump s_L18].
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
  iApply (wp_check with "Hlp"); [reflexivity | word_premise | reflexivity | addr_premise | addr_premise |
                                  addr_premise |].
  iNext. iIntros "Hlp". gen_env.
  iApply (wp_raw_store_pointer with "Hlp Hcp");
    [word_premise | word_premise | reflexivity | addr_premise | addr_premise | intros m wd h; apply os_keeps |].
  iNext. iIntros "Hlp Hcp".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
  iApply (wp_check with "Hln"); [reflexivity | word_premise | reflexivity | addr_premise | addr_premise |
                                  addr_premise |].
  iNext. iIntros "Hln". gen_env.
  iApply (wp_raw_store_pointer with "Hln Hcn");
    [word_premise | word_premise | reflexivity | addr_premise | addr_premise | intros m wd h; apply os_keeps |].
  iNext. iIntros "Hln Hcn".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext.
  iApply (wp_check with "Hls"); [reflexivity | word_premise | reflexivity | addr_premise | addr_premise |
                                  addr_premise |].
  iNext. iIntros "Hls". gen_env.
  iApply (wp_raw_store_pointer with "Hls Hcs");
    [word_premise | word_premise | reflexivity | addr_premise | addr_premise | intros m wd h; apply os_keeps |].
  iNext. iIntros "Hls Hcs".
  iApply wp_ret_void. iNext. iApply "HΦ". iFrame.
Qed.


(** ## The blocks *)

(** The "lt-" test, from L16, in a libtool build directory, with `v15`
    reading as the base name, argv[0]'s tail from its byte [base_idx]:
    glibc's strncmp of it and "lt-", and the stores of the short name,
    past "lt-" or not. *)
Lemma spn_L16 dq p s e x0 y0 z0 Φ :
  (dq = DfracDiscarded \/ exists q, dq = DfracOwn q) -> in_libs s = true ->
  lookup (TAtom "v15") e = Some (WPtr (ptr_add p (Z.of_nat (base_idx s)))) ->
  word_string dq p s -∗ word_string DfracDiscarded tp lt_bytes -∗ name_cells x0 y0 z0 -∗
  ▷ (word_string dq p s -∗ name_cells (ptr_add p (Z.of_nat (short_idx s))) (ptr_add p (Z.of_nat (short_idx s)))
       (ptr_add p (Z.of_nat (short_idx s))) -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame set_program_name_fn e [] None (Exec (TAtom "L16") (b_insts s_L16) (b_jump s_L16)))
        : gexpr) {{ Φ }}.
Proof.
  intros Hdq Hlib Hv15. iIntros "Hs #Hlt Hc HΦ". cbn [b_insts b_jump s_L16].
  iDestruct "Hs" as "(%b & %reg & %ws & %Hs & Hw)". iDestruct (word_string_intro with "Hw") as "Hs"; [exact Hs|].
  pose proof (ss_chars _ _ _ _ _ Hs) as Hch. pose proof (base_idx_le s) as Hj.
  destruct (str_shape_addr _ _ _ _ _ Hs) as [Ha0 Ha48]. destruct (lt_res s (base_idx s) Hch) as [Hr Hres].
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  iDestruct (word_string_lend dq p s (base_idx s) Hdq Hj with "Hs") as (dq') "[Hsuf Hback]".
  iApply (StrncmpLogic.wp_call_glibc_strncmp registry (os_wi w0) ge _ _ _ _ _ _ _ _ _ dq' DfracDiscarded
            (ptr_add p (Z.of_nat (base_idx s))) tp (drop (base_idx s) s) lt_bytes 3 with "Hsuf Hlt");
    [lia | word_premise | exact Hstrncmp | reflexivity |].
  iNext. iIntros "Hsuf _". iDestruct ("Hback" with "Hsuf") as "Hs".
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. gen_env.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]. iNext. gen_env.
  iApply wp_branch; [word_premise|]. iNext.
  rewrite ?Zmod_mod ?(Z.mod_small _ _ Hr). change (0 mod 2 ^ 32) with 0.
  unfold short_idx, lt_prefix. rewrite Hlib. cbn [andb].
  destruct (Z.eqb_spec (strncmp_res 3 (drop (base_idx s) s) lt_bytes) 0) as [E|E]; close_if.
  - rewrite (bool_decide_eq_true_2 _ (proj1 Hres E)).
    assert (Hj3 : (base_idx s + 3 <= length s)%nat).
    { pose proof (f_equal length (proj1 Hres E)) as L. rewrite length_take length_drop in L.
      unfold lt_bytes in L. cbn [length] in L. lia. }
    iApply wp_enter; [exact find_s_L35 | reflexivity |]. iNext. cbn [b_insts b_jump s_L35]. gen_env.
    iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ptr_addr p + Z.of_nat (base_idx s + 3)));
      [word_premise | cbn; do 2 f_equal; rewrite !Z.mod_small; lia | word_premise |].
    iNext. iApply wp_goto. iNext.
    iApply wp_enter; [exact find_s_L18 | reflexivity |]. iNext.
    iApply (spn_L18 with "Hc"); [reflexivity | reflexivity |]. iNext. iIntros "Hc". iApply ("HΦ" with "Hs Hc").
  - rewrite (bool_decide_eq_false_2 _ (fun E' => E (proj2 Hres E'))).
    iApply wp_enter; [exact find_s_L18 | word_premise |]. iNext.
    iApply (spn_L18 with "Hc"); [reflexivity | reflexivity |]. iNext. iIntros "Hc". iApply ("HΦ" with "Hs Hc").
Qed.

End progname.
