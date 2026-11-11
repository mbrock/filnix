(** C strings as glibc's word-at-a-time string functions read them
    (docs/glibc-ir.md): [word_string] dq p s owns, at the share dq, the
    whole aligned 8-byte words from the word that holds p's first byte
    through the word that holds the string's NUL, every byte of each,
    including bytes before p and past the NUL. glibc's strlen, strchr
    and strcmp read exactly those words (StrlenBits.v), so a triple for
    them takes a [word_string], not a byte span.

    - [wwin] dq b reg wo ws is the window: a share of the life of the
      object b and of the words ws from its offset wo ([words_ps]).
    - [str_shape] p b reg ws s says ws is the tight window of the string
      s at p: p names b, read-write or read-only, b is 8-aligned, the
      window lies in b's region, has as many words as the string and its
      NUL span, its words are 64-bit, its bytes from p are s and a NUL,
      and s has no NUL.

    A share splits and joins ([word_string_split]), and can be given up
    for a persistent read-only one ([word_string_persist]), as string
    literals and aliased arguments (`c: strcmp(p, p)`) need. A pointer
    into a string owns the string's tail ([word_string_suffix]), and a
    share of it can be lent out and taken back ([word_string_borrow]).
    In any memory that agrees with the ghost heap the string's bytes are
    readable through p and are s ([str_shape_bytes]), what a contract
    such as zsys_write asks of a buffer. A literal of a module's initial
    memory is a [word_string] from its pieces ([word_string_literal]).

    Why a lent share and not the same share: a [word_string] dq p' s2
    with dq whole may write the bytes of its first word before p', which
    belong to the parent's prefix, so a wand giving back the parent
    from any such string does not hold. A lent fraction is joined back
    by agreement with the part kept ([wwin_agree]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.bi.lib Require Import fractional.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic OsWorld.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The shape of a string *)

(** The address of the 8-aligned word that holds p's byte. *)
Definition wstart (p : ptr) : Z := ptr_addr p - ptr_addr p mod 8.

(** The words ws of the object b with the region reg are the tight
    window of the string s at p (see the header). *)
Record str_shape (p : ptr) (b : Z) (reg : region) (ws s : list Z) : Prop := {
  ss_cap : ptr_cap p = Obj b \/ ptr_cap p = Ro b;
  ss_base : 0 < b;
  ss_align : b mod 8 = 0;
  ss_start : b <= ptr_addr p;
  ss_fit : wstart p + 8 * Z.of_nat (length ws) <= r_end reg;
  ss_space : r_end reg <= 2 ^ 48;
  ss_len : Z.of_nat (length ws) = (ptr_addr p mod 8 + Z.of_nat (length s) + 8) / 8;
  ss_words : Forall (fun w => 0 <= w < 2 ^ 64) ws;
  ss_bytes : take (S (length s)) (drop (Z.to_nat (ptr_addr p mod 8)) (wbytes ws)) = s ++ [0];
  ss_chars : Forall (fun c => 0 < c < 256) s
}.

(** The pointer n bytes past p, with p's capability. *)
Definition ptr_add (p : ptr) (n : Z) : ptr := mkPtr (ptr_addr p + n) (ptr_cap p).

(** [str_shape] as a computation, for a fixed image. *)
Definition str_shape_b (p : ptr) (b : Z) (reg : region) (ws s : list Z) : bool :=
  match ptr_cap p with Obj b' | Ro b' => b' =? b | _ => false end && (0 <? b) && (b mod 8 =? 0) &&
  (b <=? ptr_addr p) && (wstart p + 8 * Z.of_nat (length ws) <=? r_end reg) && (r_end reg <=? 2 ^ 48) &&
  (Z.of_nat (length ws) =? (ptr_addr p mod 8 + Z.of_nat (length s) + 8) / 8) &&
  forallb (fun w => (0 <=? w) && (w <? 2 ^ 64)) ws &&
  bool_decide (take (S (length s)) (drop (Z.to_nat (ptr_addr p mod 8)) (wbytes ws)) = s ++ [0]) &&
  forallb (fun c => (0 <? c) && (c <? 256)) s.

(** [str_shape_b] decides [str_shape]: a literal's shape by [vm_compute]. *)
Lemma str_shape_b_sound p b reg ws s : str_shape_b p b reg ws s = true -> str_shape p b reg ws s.
Proof.
  unfold str_shape_b. intros H. repeat rewrite andb_true_iff in H.
  destruct H as (((((((((Hc & H0) & H8) & Hs) & Hf) & Hsp) & Hl) & Hw) & Hb) & Hch).
  split; try lia.
  - destruct (ptr_cap p); try discriminate; apply Z.eqb_eq in Hc; subst; auto.
  - apply Forall_forall. intros w Hin. apply list_elem_of_In in Hin.
    rewrite forallb_forall in Hw. specialize (Hw w Hin). lia.
  - exact (bool_decide_eq_true_1 _ Hb).
  - apply Forall_forall. intros c Hin. apply list_elem_of_In in Hin.
    rewrite forallb_forall in Hch. specialize (Hch c Hin). lia.
Qed.

(** ## Words and their pieces *)

(** The bytes of two runs of words are each's in turn. *)
Lemma wbytes_app ws1 ws2 : wbytes (ws1 ++ ws2) = wbytes ws1 ++ wbytes ws2.
Proof. apply flat_map_app. Qed.

(** The words ws have 8 bytes each. *)
Lemma wbytes_length ws : length (wbytes ws) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; [reflexivity|]. rewrite wbytes_cons length_app IH. cbn. lia. Qed.

(** The bytes of the words after the first j are the bytes after 8j. *)
Lemma wbytes_drop j ws : wbytes (drop j ws) = drop (8 * j) (wbytes ws).
Proof.
  revert ws. induction j as [|j IH]; intros [|w ws]; try reflexivity.
  - cbn [drop]. rewrite IH wbytes_cons drop_app_ge; [|cbn; lia]. cbn [length map idx8]. f_equal. lia.
Qed.

(** The pieces of two runs of words are each's in turn. *)
Lemma words_ps_app b o ws1 ws2 :
  words_ps b o (ws1 ++ ws2) = words_ps b o ws1 ++ words_ps b (o + 8 * Z.of_nat (length ws1)) ws2.
Proof.
  revert o. induction ws1 as [|w ws1 IH]; intros o; cbn [words_ps app length].
  - by rewrite Z.add_0_r.
  - rewrite IH -app_assoc. do 3 f_equal. lia.
Qed.

(** The keys of the pieces of words are byte keys, one per offset. *)
Lemma words_ps_keys b o ws : (words_ps b o ws).*1 = PByte b <$> seqZ o (8 * Z.of_nat (length ws)).
Proof.
  revert o. induction ws as [|w ws IH]; intros o; [reflexivity|].
  cbn [words_ps length]. rewrite fmap_app IH Nat2Z.inj_succ.
  replace (8 * Z.succ (Z.of_nat (length ws))) with (8 + 8 * Z.of_nat (length ws)) by lia.
  rewrite seqZ_app; [|lia|lia]. rewrite fmap_app. f_equal. unfold seqZ. change (Z.to_nat 8) with 8%nat. cbn.
  repeat (apply (f_equal2 cons); [f_equal; lia|]). reflexivity.
Qed.

(** Two runs of words of one length have the same keys. *)
Lemma words_ps_keys_eq b o ws1 ws2 : length ws1 = length ws2 ->
  (words_ps b o ws1).*1 = (words_ps b o ws2).*1.
Proof. intros H. by rewrite !words_ps_keys H. Qed.

(** Runs of 64-bit words with the same pieces are the same. *)
Lemma words_ps_inj b o ws1 ws2 :
  Forall (fun w => 0 <= w < 2 ^ 64) ws1 -> Forall (fun w => 0 <= w < 2 ^ 64) ws2 ->
  words_ps b o ws1 = words_ps b o ws2 -> ws1 = ws2.
Proof.
  revert o ws2. induction ws1 as [|w1 ws1 IH]; intros o [|w2 ws2] H1 H2 E; try done.
  apply Forall_cons_1 in H1 as [R1 H1], H2 as [R2 H2]. cbn [words_ps] in E.
  apply app_inj_1 in E as [Ec E]; [|reflexivity].
  unfold cell in Ec. cbn in Ec. injection Ec as E0 E1 E2 E3 E4 E5 E6 E7.
  f_equal; [|exact (IH _ _ H1 H2 E)].
  rewrite -(of_bytes_byte_of w1 R1) -(of_bytes_byte_of w2 R2). cbn. congruence.
Qed.

(** Byte i of the words ws is the piece at offset o + i of their
    pieces from o. *)
Lemma words_ps_elem b o ws (i : nat) x :
  wbytes ws !! i = Some x -> (PByte b (o + Z.of_nat i), VByte x) ∈ words_ps b o ws.
Proof.
  revert o i. induction ws as [|w ws IH]; intros o i H; [done|]. cbn [words_ps].
  destruct (Nat.lt_ge_cases i 8) as [Hi|Hi].
  - rewrite wbytes_head in H; [|exact Hi]. injection H as <-. apply elem_of_app. left.
    apply list_elem_of_In, in_map_iff. exists (Z.of_nat i). split; [reflexivity|]. apply idx8_cases. lia.
  - apply elem_of_app. right. replace i with (8 + (i - 8))%nat in H by lia. rewrite wbytes_tail in H.
    replace (o + Z.of_nat i) with (o + 8 + Z.of_nat (i - 8)) by lia. exact (IH _ _ H).
Qed.

(** The first zero of the string's bytes from p is at its length. *)
Lemma str_shape_first_zero p b reg ws s : str_shape p b reg ws s ->
  first_zero (drop (Z.to_nat (ptr_addr p mod 8)) (wbytes ws)) (length s).
Proof.
  intros Hs. pose proof (ss_bytes _ _ _ _ _ Hs) as E. pose proof (ss_chars _ _ _ _ _ Hs) as Hc.
  set (l := drop _ _) in *. split.
  - rewrite -(lookup_take_lt l (S (length s))); [|lia]. rewrite E lookup_app_r; [|lia].
    by rewrite Nat.sub_diag.
  - intros u Hu Hz. rewrite -(lookup_take_lt l (S (length s))) in Hz; [|lia].
    rewrite E lookup_app_l in Hz; [|exact Hu]. apply list_elem_of_lookup_2 in Hz.
    rewrite Forall_forall in Hc. specialize (Hc 0 Hz). lia.
Qed.

(** The string's bytes, at the pointer i bytes in, i at most its length:
    the window's byte, which is s's byte or the NUL. *)
Lemma str_shape_byte p b reg ws s (i : nat) : str_shape p b reg ws s -> (i <= length s)%nat ->
  wbytes ws !! (Z.to_nat (ptr_addr p mod 8) + i)%nat = (s ++ [0]) !! i.
Proof.
  intros Hs Hi. rewrite -(ss_bytes _ _ _ _ _ Hs) lookup_take_lt; [|lia]. by rewrite lookup_drop.
Qed.

(** ## Readable bytes *)

(** In a memory m where the object b is live with the region reg and
    the window's pieces agree, the string's bytes and its NUL are
    readable through p, and its bytes are s. What a contract that reads
    a buffer, such as zsys_write's [readable_bytes], asks. *)
Lemma str_shape_bytes m p b reg ws s : str_shape p b reg ws s -> live_at m b reg ->
  all_agree m (words_ps b (wstart p - b) ws) ->
  (forall n, 0 <= n <= Z.of_nat (length s) + 1 -> readable_bytes m p n) /\
  os_bytes m p (Z.of_nat (length s)) = s.
Proof.
  intros Hs Hlv Ha. pose proof Hs as [Hc Hb0 Hb8 Hst Hf Hsp Hl Hw Hby Hch].
  pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)) as Hk. unfold wstart in Hf.
  assert (Hm : forall i : nat, (i <= length s)%nat -> Some (m_bytes m (ptr_addr p + Z.of_nat i)) = (s ++ [0]) !! i).
  { intros i Hi. rewrite -(str_shape_byte p b reg ws s i Hs Hi).
    destruct (wbytes ws !! (Z.to_nat (ptr_addr p mod 8) + i)%nat) as [x|] eqn:E.
    - apply (words_ps_elem b (wstart p - b)) in E. apply (all_agree_elem _ _ _ _ Ha) in E as [_ E].
      destruct Hlv as [Er Lv]. destruct (E reg Er Lv) as (_ & _ & E'). unfold wstart in E'. f_equal.
      rewrite -E'. f_equal. lia.
    - apply lookup_ge_None in E. rewrite wbytes_length in E. exfalso.
      pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)). lia. }
  assert (Hr : forall i : nat, (i <= length s)%nat -> 0 <= m_bytes m (ptr_addr p + Z.of_nat i) < 256).
  { intros i Hi. specialize (Hm i Hi). destruct (decide (i = length s)) as [->|Hne].
    - rewrite lookup_app_r in Hm; [|lia]. rewrite Nat.sub_diag in Hm. injection Hm as ->. lia.
    - rewrite lookup_app_l in Hm; [|lia]. symmetry in Hm. apply list_elem_of_lookup_2 in Hm.
      rewrite Forall_forall in Hch. specialize (Hch _ Hm). lia. }
  assert (Hend : ptr_addr p + Z.of_nat (length s) + 1 <= r_end reg).
  { pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)). lia. }
  split.
  - intros n Hn. destruct Hlv as [Er Lv]. split; [lia|]. split; [eauto|]. split.
    + apply (access_read _ b reg); [exact Hc | exact Er | lia | lia | apply Z.mod_1_r].
    + intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia. apply Hr. lia.
  - unfold os_bytes. rewrite Nat2Z.id. apply list_eq. intros i.
    destruct (Nat.lt_ge_cases i (length s)) as [Hi|Hi].
    + rewrite list_lookup_fmap lookup_seq_lt; [|exact Hi]. cbn. rewrite (Hm i ltac:(lia)).
      rewrite lookup_app_l; [reflexivity | exact Hi].
    + rewrite list_lookup_fmap lookup_seq_ge; [|exact Hi]. symmetry. by apply lookup_ge_None.
Qed.

(** ## Windows and strings *)

Section word_string.
Context `{!gen_heapGS piece pval Σ}.

(** [wwin] dq b reg wo ws: a share dq of the life of the object b, live
    with the region reg (Logic.v's [liveq]), and of the 64-bit words ws
    from its offset wo. *)
Definition wwin (dq : dfrac) (b : Z) (reg : region) (wo : Z) (ws : list Z) : iProp Σ :=
  ptsq dq [(PLive b, VLive reg)] ∗ ptsq dq (words_ps b wo ws).

(** [word_string] dq p s: a share dq of the tight window of the string s
    at p ([str_shape]). *)
Definition word_string (dq : dfrac) (p : ptr) (s : list Z) : iProp Σ :=
  ∃ b reg ws, ⌜str_shape p b reg ws s⌝ ∗ wwin dq b reg (wstart p - b) ws.

(** Shares of pieces with the same keys hold the same values. *)
Lemma ptsq_agree dq1 dq2 ps1 ps2 : ps1.*1 = ps2.*1 -> ptsq dq1 ps1 -∗ ptsq dq2 ps2 -∗ ⌜ps1 = ps2⌝.
Proof.
  revert ps2. induction ps1 as [|[l1 v1] ps1 IH]; intros [|[l2 v2] ps2] Hk; try discriminate Hk.
  - by iIntros.
  - cbn in Hk. injection Hk as <- Hk. rewrite /ptsq /=. iIntros "[H1 Hs1] [H2 Hs2]".
    iDestruct (pointsto_agree with "H1 H2") as %<-. by iDestruct (IH _ Hk with "Hs1 Hs2") as %<-.
Qed.

(** A window splits into shares and joins back. *)
Lemma wwin_split q1 q2 b reg wo ws :
  wwin (DfracOwn (q1 + q2)) b reg wo ws ⊣⊢ wwin (DfracOwn q1) b reg wo ws ∗ wwin (DfracOwn q2) b reg wo ws.
Proof. rewrite /wwin !ptsq_split. iSplit; [iIntros "[[$ $] [$ $]]" | iIntros "[[$ $] [$ $]]"]. Qed.

(** Any share of a window can be given up for a read-only one. *)
Lemma wwin_persist dq b reg wo ws : wwin dq b reg wo ws ==∗ □ wwin DfracDiscarded b reg wo ws.
Proof.
  iIntros "[Hl Hw]". iMod (ptsq_persist with "Hl") as "#Hl". iMod (ptsq_persist with "Hw") as "#Hw".
  iModIntro. iModIntro. iFrame "#".
Qed.

(** A read-only window is persistent. *)
Global Instance wwin_persistent b reg wo ws : Persistent (wwin DfracDiscarded b reg wo ws).
Proof. rewrite /wwin. apply _. Qed.

(** Two windows of one object, offset and length agree: one region,
    one run of words. *)
Lemma wwin_agree dq1 dq2 b reg1 reg2 wo ws1 ws2 : length ws1 = length ws2 ->
  Forall (fun w => 0 <= w < 2 ^ 64) ws1 -> Forall (fun w => 0 <= w < 2 ^ 64) ws2 ->
  wwin dq1 b reg1 wo ws1 -∗ wwin dq2 b reg2 wo ws2 -∗ ⌜reg1 = reg2 /\ ws1 = ws2⌝.
Proof.
  iIntros (Hl H1 H2) "[Hl1 Hw1] [Hl2 Hw2]".
  iDestruct (ptsq_agree with "Hl1 Hl2") as %E; [reflexivity|].
  iDestruct (ptsq_agree with "Hw1 Hw2") as %Ew; [exact (words_ps_keys_eq _ _ _ _ Hl)|].
  iPureIntro. split; [congruence | exact (words_ps_inj _ _ _ _ H1 H2 Ew)].
Qed.

(** Two shapes of one string at one pointer name one object and have
    windows of one length. *)
Lemma str_shape_same p b1 b2 reg1 reg2 ws1 ws2 s :
  str_shape p b1 reg1 ws1 s -> str_shape p b2 reg2 ws2 s -> b1 = b2 /\ length ws1 = length ws2.
Proof.
  intros [Hc1 _ _ _ _ _ Hl1 _ _ _] [Hc2 _ _ _ _ _ Hl2 _ _ _]. split; [|lia].
  destruct Hc1 as [E1|E1], Hc2 as [E2|E2]; rewrite E1 in E2; congruence.
Qed.

(** A string splits into shares and joins back. *)
Lemma word_string_split q1 q2 p s :
  word_string (DfracOwn (q1 + q2)) p s ⊣⊢ word_string (DfracOwn q1) p s ∗ word_string (DfracOwn q2) p s.
Proof.
  iSplit.
  - iIntros "(%b & %reg & %ws & %Hs & Hw)". rewrite wwin_split. iDestruct "Hw" as "[H1 H2]".
    iSplitL "H1"; iExists b, reg, ws; by iFrame.
  - iIntros "[(%b & %reg & %ws & %Hs & Hw) (%b' & %reg' & %ws' & %Hs' & Hw')]".
    destruct (str_shape_same _ _ _ _ _ _ _ _ Hs Hs') as [<- Hl].
    iDestruct (wwin_agree with "Hw Hw'") as %[<- <-];
      [exact Hl | exact (ss_words _ _ _ _ _ Hs) | exact (ss_words _ _ _ _ _ Hs')|].
    iExists b, reg, ws. iSplit; [done|]. rewrite wwin_split. iFrame.
Qed.

(** Any share of a string can be given up for a read-only one. *)
Lemma word_string_persist dq p s : word_string dq p s ==∗ □ word_string DfracDiscarded p s.
Proof.
  iIntros "(%b & %reg & %ws & %Hs & Hw)". iMod (wwin_persist with "Hw") as "#Hw".
  iModIntro. iModIntro. iExists b, reg, ws. by iFrame "#".
Qed.

(** A read-only string is persistent. *)
Global Instance word_string_persistent p s : Persistent (word_string DfracDiscarded p s).
Proof. rewrite /word_string. apply _. Qed.

(** A string's window: [word_string] from its witnesses. *)
Lemma word_string_intro dq p b reg ws s :
  str_shape p b reg ws s -> wwin dq b reg (wstart p - b) ws -∗ word_string dq p s.
Proof. iIntros (Hs) "Hw". iExists b, reg, ws. by iFrame. Qed.

(** ## Pointers into strings *)

(** The tail s2 of the string s1 ++ s2 at p, at p advanced past s1, has
    the window of the words from the one holding its first byte. *)
Lemma str_shape_suffix p b reg ws s1 s2 :
  str_shape p b reg ws (s1 ++ s2) ->
  let j := Z.to_nat ((ptr_addr p mod 8 + Z.of_nat (length s1)) / 8) in
  str_shape (ptr_add p (Z.of_nat (length s1))) b reg (drop j ws) s2 /\
  wstart (ptr_add p (Z.of_nat (length s1))) - b = wstart p - b + 8 * Z.of_nat j.
Proof.
  intros [Hc Hb0 Hb8 Hst Hf Hsp Hl Hw Hby Hch] j. unfold wstart, ptr_add in *. cbn [ptr_addr ptr_cap] in *.
  rewrite length_app Nat2Z.inj_add in Hl. rewrite length_app in Hby.
  set (a := ptr_addr p) in *. set (n1 := Z.of_nat (length s1)) in *. set (n2 := Z.of_nat (length s2)) in *.
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Hk.
  assert (Hj : Z.of_nat j = (a mod 8 + n1) / 8) by (apply Z2Nat.id; apply Z.div_pos; lia).
  assert (Hmod : (a + n1) mod 8 = (a mod 8 + n1) mod 8) by (rewrite Zplus_mod_idemp_l; reflexivity).
  assert (Hdiv : a + n1 - (a + n1) mod 8 = a - a mod 8 + 8 * Z.of_nat j).
  { rewrite Hmod Hj. pose proof (Z.div_mod (a mod 8 + n1) 8 ltac:(lia)). lia. }
  assert (Hle : (j <= length ws)%nat).
  { apply Nat2Z.inj_le. rewrite Hl Hj. apply Z.div_le_mono; lia. }
  split; [|lia]. split; unfold wstart; cbn [ptr_addr ptr_cap]; try lia.
  - exact Hc.
  - rewrite Hdiv length_drop Nat2Z.inj_sub; [|exact Hle]. lia.
  - rewrite length_drop Nat2Z.inj_sub; [|exact Hle]. rewrite Hl Hj Hmod.
    pose proof (Z.div_mod (a mod 8 + n1) 8 ltac:(lia)).
    replace (a mod 8 + (n1 + n2) + 8) with ((a mod 8 + n1) / 8 * 8 + ((a mod 8 + n1) mod 8 + n2 + 8)) by lia.
    rewrite Z.div_add_l; [|lia]. unfold n2. lia.
  - by apply Forall_drop.
  - rewrite wbytes_drop drop_drop.
    replace (8 * j + Z.to_nat ((a + n1) mod 8))%nat with (Z.to_nat (a mod 8) + length s1)%nat.
    + rewrite -drop_drop take_drop_commute.
      replace (length s1 + S (length s2))%nat with (S (length s1 + length s2))%nat by lia.
      rewrite Hby -app_assoc drop_app_length. reflexivity.
    + rewrite Hmod. apply Nat2Z.inj. pose proof (Z.div_mod (a mod 8 + n1) 8 ltac:(lia)).
      pose proof (Z.mod_pos_bound (a mod 8 + n1) 8 ltac:(lia)). unfold n1 in *. lia.
  - apply Forall_app in Hch. tauto.
Qed.

(** A pointer advanced into a string owns the string's tail, at the
    string's share. The prefix's words are given up: for a read-only
    string, nothing is lost. *)
Lemma word_string_suffix dq p s1 s2 :
  word_string dq p (s1 ++ s2) ⊢ word_string dq (ptr_add p (Z.of_nat (length s1))) s2.
Proof.
  iIntros "(%b & %reg & %ws & %Hs & Hl & Hw)". destruct (str_shape_suffix _ _ _ _ _ _ Hs) as [Hs' Ho].
  iExists b, reg, _. iSplit; [iPureIntro; exact Hs'|]. iFrame "Hl". rewrite Ho.
  rewrite -{1}(take_drop (Z.to_nat ((ptr_addr p mod 8 + Z.of_nat (length s1)) / 8)) ws) words_ps_app ptsq_app.
  iDestruct "Hw" as "[_ Hw]". rewrite length_take_le; [iExact "Hw"|].
  apply Nat2Z.inj_le. rewrite Z2Nat.id; [|apply Z.div_pos; pose proof (Z.mod_pos_bound (ptr_addr p) 8); lia].
  rewrite (ss_len _ _ _ _ _ Hs) length_app Nat2Z.inj_add. apply Z.div_le_mono; lia.
Qed.

(** A share q1 of the tail of a string, lent to a pointer advanced
    into it: the wand takes any share q1 of that tail back and gives the
    whole string. Agreement with the share q2 kept shows the tail came
    back with the same words ([wwin_agree]). *)
Lemma word_string_borrow q1 q2 p s1 s2 :
  word_string (DfracOwn (q1 + q2)) p (s1 ++ s2) ⊢
  word_string (DfracOwn q1) (ptr_add p (Z.of_nat (length s1))) s2 ∗
  (word_string (DfracOwn q1) (ptr_add p (Z.of_nat (length s1))) s2 -∗ word_string (DfracOwn (q1 + q2)) p (s1 ++ s2)).
Proof.
  iIntros "Hs". iDestruct (word_string_split with "Hs") as "[H1 H2]".
  iDestruct "H2" as "(%b & %reg & %ws & %Hs & Hl2 & Hw2)".
  destruct (str_shape_suffix _ _ _ _ _ _ Hs) as [Hs' Ho].
  set (j := Z.to_nat _) in Hs', Ho.
  iDestruct "H1" as "(%b1 & %reg1 & %ws1 & %Hs1 & Hl1 & Hw1)".
  destruct (str_shape_same _ _ _ _ _ _ _ _ Hs Hs1) as [<- Hl].
  iDestruct (wwin_agree with "[$Hl2 $Hw2] [$Hl1 $Hw1]") as %[<- <-];
    [exact Hl | exact (ss_words _ _ _ _ _ Hs) | exact (ss_words _ _ _ _ _ Hs1)|].
  assert (Hj : length (take j ws) = j).
  { apply length_take_le. apply Nat2Z.inj_le. unfold j. rewrite Z2Nat.id;
      [|apply Z.div_pos; pose proof (Z.mod_pos_bound (ptr_addr p) 8); lia].
    rewrite (ss_len _ _ _ _ _ Hs) length_app Nat2Z.inj_add. apply Z.div_le_mono; lia. }
  assert (Hsp : words_ps b (wstart p - b) ws = words_ps b (wstart p - b) (take j ws) ++
                  words_ps b (wstart (ptr_add p (Z.of_nat (length s1))) - b) (drop j ws)).
  { rewrite -{1}(take_drop j ws) words_ps_app Hj Ho. reflexivity. }
  iEval (rewrite Hsp ptsq_app) in "Hw1". iDestruct "Hw1" as "[Ht Hd]".
  iEval (rewrite Hsp ptsq_app) in "Hw2". iDestruct "Hw2" as "[Ht2 Hd2]".
  iSplitL "Hl1 Hd".
  { iExists b, reg, (drop j ws). by iFrame. }
  iIntros "(%b' & %reg' & %ws' & %Hs'' & Hl' & Hd')".
  destruct (str_shape_same _ _ _ _ _ _ _ _ Hs' Hs'') as [<- Hl'].
  iDestruct (wwin_agree with "[$Hl2 $Hd2] [$Hl' $Hd']") as %[<- <-];
    [exact Hl' | exact (ss_words _ _ _ _ _ Hs') | exact (ss_words _ _ _ _ _ Hs'')|].
  rewrite (word_string_split q1 q2). iSplitL "Hl' Ht Hd'"; iExists b, reg, ws; iSplit; try done;
    rewrite /wwin Hsp ptsq_app; iFrame.
Qed.

(** ## Literals *)

(** The pieces of a literal at the base b of its object: its life and
    its words from offset 0. *)
Definition lit_ps (b : Z) (reg : region) (ws : list Z) : list (piece * pval) :=
  (PLive b, VLive reg) :: words_ps b 0 ws.

(** A literal's pieces have distinct keys, as [pieces_never_panics]
    asks. *)
Lemma lit_ps_nodup b reg ws : NoDup (lit_ps b reg ws).*1.
Proof.
  cbn [lit_ps fmap list_fmap fst]. rewrite (words_ps_keys b 0 ws). apply NoDup_cons. split.
  - intros Hin. apply list_elem_of_fmap in Hin as (? & ? & _). discriminate.
  - apply NoDup_fmap_2; [intros x y E; congruence | apply NoDup_seqZ].
Qed.

(** A literal of a module's initial memory, owned as its pieces
    [lit_ps] with a read-only pointer to its base: a whole share of a
    string. Its shape is [str_shape_b] by [vm_compute], its pieces agree
    with the image by Heap.v's [checked_pieces_all_agree]; Run.v lays
    each data item out 16-aligned and rounded up to 8 bytes, so a
    literal's words are whole. The share can then be made persistent
    ([word_string_persist]). *)
Lemma word_string_literal b reg ws s :
  str_shape (mkPtr b (Ro b)) b reg ws s -> pts (lit_ps b reg ws) ⊢ word_string (DfracOwn 1) (mkPtr b (Ro b)) s.
Proof.
  iIntros (Hs) "Hps". iExists b, reg, ws. iSplit; [done|].
  replace (wstart (mkPtr b (Ro b)) - b) with 0 by (unfold wstart; cbn; rewrite (ss_align _ _ _ _ _ Hs); lia).
  rewrite /lit_ps pts_ptsq (ptsq_app _ [_]). iExact "Hps".
Qed.

End word_string.

(** ## Over a Logic instance *)

(** Reading strings over the [[runtime]] R and the Logic instance LG. *)
Module WordStringOn (R : Runtime) (LG0 : LogicSig R).
Module LG := LG0.
Module L := LG.L.
Import L LG.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** The Iris instance of the registry and wi. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** In the memory of σ, a string's bytes and its NUL are readable
    through p and its bytes are s ([str_shape_bytes]). *)
Lemma word_string_readable σ dq p s : heap_interp wi σ -∗ word_string dq p s -∗
  ⌜(forall n, 0 <= n <= Z.of_nat (length s) + 1 -> readable_bytes (ls_mem σ) p n) /\
   os_bytes (ls_mem σ) p (Z.of_nat (length s)) = s⌝.
Proof.
  iIntros "Hσ (%b & %reg & %ws & %Hs & Hl & Hw)".
  iDestruct (ptsq_facts with "Hσ Hl") as %([Hlv _] & _).
  iDestruct (ptsq_facts with "Hσ Hw") as %(Ha & _). iPureIntro. exact (str_shape_bytes _ _ _ _ _ _ Hs Hlv Ha).
Qed.

(** [wp_check_read] at a share: a [[check]] for reading of the pointer
    p, through a read-write or read-only capability for the object b of
    which a share of the life is owned. *)
Lemma wp_check_read_dq f e ls l d lo hi al args rest j classes p b reg dq Φ :
  op_arg_classes (Check lo hi Read al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b \/ ptr_cap p = Ro b -> b <= raw_address (ptr_addr p) lo ->
  raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg -> raw_address (ptr_addr p) lo mod al = 0 ->
  liveq dq b reg -∗
  ▷ (liveq dq b reg -∗ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (Check lo hi Read al) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp H1 H2 H3. apply (wp_read_dq registry wi ge dq _ _ _ []). 
  intros m fuel (Hf & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E _] _].
  apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
  apply op_check. exact (access_read _ _ _ _ _ _ _ Hp E H1 H2 H3).
Qed.

End rules.
End WordStringOn.
