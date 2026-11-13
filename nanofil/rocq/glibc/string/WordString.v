(** Glibc's string routines such as `c: strlen`, `c: strchr`, and
    `c: strcmp` scan memory in aligned 8-byte words rather than one byte
    at a time. Because each load reads an entire word, those functions
    also touch padding bytes before the string's first byte and after
    its NUL terminator. To verify them, this module defines [word_string],
    which owns the aligned word window from the word holding p's first
    byte through the word holding the NUL byte.

    A string window combines the object's liveness token with its word
    pieces in [wwin], while [str_shape] checks that the window fits
    inside an 8-byte aligned [[region]], holds valid 64-bit words, and
    encodes the bytes of s followed by a NUL. Because callers often
    pass the same string twice or read string literals concurrently,
    windows can split into fractional shares and convert to a
    [[persistent-proposition|persistent]] read-only form.

    Advancing a pointer into a string produces ownership of the string's
    tail, and a caller can lend a fraction of that tail and take it back
    with a [[magic-wand|magic wand]]. Lending only a fraction rather than
    the whole share is essential, because an exclusive owner of the tail
    could overwrite bytes before the tail pointer in the shared first
    word. Keeping a fraction behind lets [wwin_agree] verify that the
    returned words still match the original string. *)

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

(** ## The shape of a string

    Before claiming ownership of a string's words in separation logic,
    we must state the pure geometric invariants that relate a C pointer
    p, its underlying object b, and the list of 64-bit words ws. Here we
    define that shape invariant and provide a boolean decision procedure
    so concrete string literals can be checked by computation. *)

(** [wstart] computes the 8-byte aligned base address of the word that
    contains pointer p. *)
Definition wstart (p : ptr) : Z := ptr_addr p - ptr_addr p mod 8.

(** Record [str_shape] states that the 64-bit words ws form the tight
    aligned window of string s at pointer p inside object b and region
    reg. *)
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

(** [ptr_add] advances pointer p by n bytes while preserving its
    [[capability]]. *)
Definition ptr_add (p : ptr) (n : Z) : ptr := mkPtr (ptr_addr p + n) (ptr_cap p).

(** [str_shape_b] evaluates all fields of [str_shape] as a computable
    boolean test for concrete literals and memory images. *)
Definition str_shape_b (p : ptr) (b : Z) (reg : region) (ws s : list Z) : bool :=
  match ptr_cap p with Obj b' | Ro b' => b' =? b | _ => false end && (0 <? b) && (b mod 8 =? 0) &&
  (b <=? ptr_addr p) && (wstart p + 8 * Z.of_nat (length ws) <=? r_end reg) && (r_end reg <=? 2 ^ 48) &&
  (Z.of_nat (length ws) =? (ptr_addr p mod 8 + Z.of_nat (length s) + 8) / 8) &&
  forallb (fun w => (0 <=? w) && (w <? 2 ^ 64)) ws &&
  bool_decide (take (S (length s)) (drop (Z.to_nat (ptr_addr p mod 8)) (wbytes ws)) = s ++ [0]) &&
  forallb (fun c => (0 <? c) && (c <? 256)) s.

(** Concrete string literals in a compiled module have fixed bytes and
    bounds, so we can check their shape by computation rather than
    writing manual inequalities. Lemma [str_shape_b_sound] turns a
    passing boolean check into a [str_shape] proof. *)
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

(** ## Words and their pieces

    Splitting a string at a suffix or agreeing between two fractional
    shares requires reasoning about how word lists map to flat byte
    lists and separation-logic piece keys. These structural lemmas
    connect [wbytes], [words_ps], and [first_zero] across appends and
    drops. *)

(** Appending two word lists concatenates their little-endian byte
    sequences, as [wbytes_app] proves. *)
Lemma wbytes_app ws1 ws2 : wbytes (ws1 ++ ws2) = wbytes ws1 ++ wbytes ws2.
Proof. apply flat_map_app. Qed.

(** [wbytes_length] confirms that ws expands to 8 bytes per 64-bit word. *)
Lemma wbytes_length ws : length (wbytes ws) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; [reflexivity|]. rewrite wbytes_cons length_app IH. cbn. lia. Qed.

(** Dropping the first j words from ws drops the first 8 * j bytes from
    its byte list, as [wbytes_drop] proves. *)
Lemma wbytes_drop j ws : wbytes (drop j ws) = drop (8 * j) (wbytes ws).
Proof.
  revert ws. induction j as [|j IH]; intros [|w ws]; try reflexivity.
  - cbn [drop]. rewrite IH wbytes_cons drop_app_ge; [|cbn; lia]. cbn [length map idx8]. f_equal. lia.
Qed.

(** Appending two word lists splits their piece list at offset
    8 * length ws1, as [words_ps_app] proves. *)
Lemma words_ps_app b o ws1 ws2 :
  words_ps b o (ws1 ++ ws2) = words_ps b o ws1 ++ words_ps b (o + 8 * Z.of_nat (length ws1)) ws2.
Proof.
  revert o. induction ws1 as [|w ws1 IH]; intros o; cbn [words_ps app length].
  - by rewrite Z.add_0_r.
  - rewrite IH -app_assoc. do 3 f_equal. lia.
Qed.

(** [words_ps_keys] shows that the piece keys of ws from offset o form
    contiguous byte keys for object b. *)
Lemma words_ps_keys b o ws : (words_ps b o ws).*1 = PByte b <$> seqZ o (8 * Z.of_nat (length ws)).
Proof.
  revert o. induction ws as [|w ws IH]; intros o; [reflexivity|].
  cbn [words_ps length]. rewrite fmap_app IH Nat2Z.inj_succ.
  replace (8 * Z.succ (Z.of_nat (length ws))) with (8 + 8 * Z.of_nat (length ws)) by lia.
  rewrite seqZ_app; [|lia|lia]. rewrite fmap_app. f_equal. unfold seqZ. change (Z.to_nat 8) with 8%nat. cbn.
  repeat (apply (f_equal2 cons); [f_equal; lia|]). reflexivity.
Qed.

(** Two word lists of the same length generate the exact same piece
    keys at offset o, as [words_ps_keys_eq] records. *)
Lemma words_ps_keys_eq b o ws1 ws2 : length ws1 = length ws2 ->
  (words_ps b o ws1).*1 = (words_ps b o ws2).*1.
Proof. intros H. by rewrite !words_ps_keys H. Qed.

(** Because each 64-bit word is uniquely determined by its eight bytes,
    [words_ps_inj] proves that equal piece lists come from equal word
    lists. *)
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

(** [words_ps_elem] connects byte i of `wbytes ws` to the corresponding
    byte piece at offset o + i in [words_ps]. *)
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

(** [str_shape_first_zero] proves that the first zero byte reachable from
    pointer p in a well-shaped window sits at index `length s`. *)
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

(** For any offset i up to the string length, [str_shape_byte] extracts
    the string byte or its terminating NUL from the window's byte list. *)
Lemma str_shape_byte p b reg ws s (i : nat) : str_shape p b reg ws s -> (i <= length s)%nat ->
  wbytes ws !! (Z.to_nat (ptr_addr p mod 8) + i)%nat = (s ++ [0]) !! i.
Proof.
  intros Hs Hi. rewrite -(ss_bytes _ _ _ _ _ Hs) lookup_take_lt; [|lia]. by rewrite lookup_drop.
Qed.

(** ## Readable bytes

    External system-call contracts such as `zsys_write` check physical
    memory readability rather than word-window ownership. When a
    window's pieces agree with physical memory m, the next lemma bridges
    [str_shape] to [readable_bytes] and [os_bytes]. *)

(** Whenever object b is live in memory m and the window's pieces agree
    with m, [str_shape_bytes] proves that all bytes of s and its NUL
    terminator are readable through p and match s. *)
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

(** ## Windows and strings

    Wrapping [wwin] and [str_shape] in an existential separation-logic
    predicate gives callers an abstract string resource that hides the
    underlying base address and padding words. The lemmas in this
    section show how to split a string into fractional shares, re-join
    two shares by agreement, and freeze a string into a persistent
    read-only resource. *)

Section word_string.
Context `{!gen_heapGS piece pval Σ}.

(** Word-at-a-time string routines need shared read access to both the
    object's liveness token and its aligned 64-bit words. Predicate
    [wwin] bundles fractional ownership dq of both resources starting at
    offset wo. *)
Definition wwin (dq : dfrac) (b : Z) (reg : region) (wo : Z) (ws : list Z) : iProp Σ :=
  ptsq dq [(PLive b, VLive reg)] ∗ ptsq dq (words_ps b wo ws).

(** Callers of string routines should not have to track the underlying
    object base address or padding words directly. Predicate
    [word_string] existentially hides those witnesses behind pointer p
    and string s. *)
Definition word_string (dq : dfrac) (p : ptr) (s : list Z) : iProp Σ :=
  ∃ b reg ws, ⌜str_shape p b reg ws s⌝ ∗ wwin dq b reg (wstart p - b) ws.

(** Two fractional piece maps with identical keys must hold identical
    values, as [ptsq_agree] proves. *)
Lemma ptsq_agree dq1 dq2 ps1 ps2 : ps1.*1 = ps2.*1 -> ptsq dq1 ps1 -∗ ptsq dq2 ps2 -∗ ⌜ps1 = ps2⌝.
Proof.
  revert ps2. induction ps1 as [|[l1 v1] ps1 IH]; intros [|[l2 v2] ps2] Hk; try discriminate Hk.
  - by iIntros.
  - cbn in Hk. injection Hk as <- Hk. rewrite /ptsq /=. iIntros "[H1 Hs1] [H2 Hs2]".
    iDestruct (pointsto_agree with "H1 H2") as %<-. by iDestruct (IH _ Hk with "Hs1 Hs2") as %<-.
Qed.

(** [wwin_split] splits a fractional window into two smaller shares and
    joins them back together. *)
Lemma wwin_split q1 q2 b reg wo ws :
  wwin (DfracOwn (q1 + q2)) b reg wo ws ⊣⊢ wwin (DfracOwn q1) b reg wo ws ∗ wwin (DfracOwn q2) b reg wo ws.
Proof. rewrite /wwin !ptsq_split. iSplit; [iIntros "[[$ $] [$ $]]" | iIntros "[[$ $] [$ $]]"]. Qed.

(** Any share of a window can be frozen into a persistent read-only
    window by [wwin_persist]. *)
Lemma wwin_persist dq b reg wo ws : wwin dq b reg wo ws ==∗ □ wwin DfracDiscarded b reg wo ws.
Proof.
  iIntros "[Hl Hw]". iMod (ptsq_persist with "Hl") as "#Hl". iMod (ptsq_persist with "Hw") as "#Hw".
  iModIntro. iModIntro. iFrame "#".
Qed.

(** Once a window becomes read-only, multiple calls can share it freely
    without splitting fractions again. Instance [wwin_persistent] marks
    a read-only window as [[persistent-proposition|persistent]]. *)
Global Instance wwin_persistent b reg wo ws : Persistent (wwin DfracDiscarded b reg wo ws).
Proof. rewrite /wwin. apply _. Qed.

(** Two fractional windows of the same object, offset, and word count
    must share the same region and word values, as [wwin_agree] proves. *)
Lemma wwin_agree dq1 dq2 b reg1 reg2 wo ws1 ws2 : length ws1 = length ws2 ->
  Forall (fun w => 0 <= w < 2 ^ 64) ws1 -> Forall (fun w => 0 <= w < 2 ^ 64) ws2 ->
  wwin dq1 b reg1 wo ws1 -∗ wwin dq2 b reg2 wo ws2 -∗ ⌜reg1 = reg2 /\ ws1 = ws2⌝.
Proof.
  iIntros (Hl H1 H2) "[Hl1 Hw1] [Hl2 Hw2]".
  iDestruct (ptsq_agree with "Hl1 Hl2") as %E; [reflexivity|].
  iDestruct (ptsq_agree with "Hw1 Hw2") as %Ew; [exact (words_ps_keys_eq _ _ _ _ Hl)|].
  iPureIntro. split; [congruence | exact (words_ps_inj _ _ _ _ H1 H2 Ew)].
Qed.

(** Two shapes for the same string s at the same pointer p must name the
    same object and span the same number of words, as [str_shape_same]
    verifies. *)
Lemma str_shape_same p b1 b2 reg1 reg2 ws1 ws2 s :
  str_shape p b1 reg1 ws1 s -> str_shape p b2 reg2 ws2 s -> b1 = b2 /\ length ws1 = length ws2.
Proof.
  intros [Hc1 _ _ _ _ _ Hl1 _ _ _] [Hc2 _ _ _ _ _ Hl2 _ _ _]. split; [|lia].
  destruct Hc1 as [E1|E1], Hc2 as [E2|E2]; rewrite E1 in E2; congruence.
Qed.

(** [word_string_split] splits a [word_string] into two fractional
    shares and recombines them using [wwin_agree]. *)
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

(** Any share of a string can be frozen into a persistent read-only
    string by [word_string_persist]. *)
Lemma word_string_persist dq p s : word_string dq p s ==∗ □ word_string DfracDiscarded p s.
Proof.
  iIntros "(%b & %reg & %ws & %Hs & Hw)". iMod (wwin_persist with "Hw") as "#Hw".
  iModIntro. iModIntro. iExists b, reg, ws. by iFrame "#".
Qed.

(** Once a string becomes read-only, callers can duplicate it across
    aliased arguments such as `c: strcmp(p, p)`. Instance
    [word_string_persistent] marks a read-only string as persistent. *)
Global Instance word_string_persistent p s : Persistent (word_string DfracDiscarded p s).
Proof. rewrite /word_string. apply _. Qed.

(** When a proof constructs a window and a shape witness separately, it
    needs to pack them into the abstract string predicate. Lemma
    [word_string_intro] combines both into [word_string]. *)
Lemma word_string_intro dq p b reg ws s :
  str_shape p b reg ws s -> wwin dq b reg (wstart p - b) ws -∗ word_string dq p s.
Proof. iIntros (Hs) "Hw". iExists b, reg, ws. by iFrame. Qed.

(** ## Pointers into strings

    C callers often advance a pointer into the middle of a string, for
    example to inspect a suffix after skipping a prefix. When we advance
    p past prefix s1, we drop the leading words before the tail s2 and
    either forget them permanently or lend a fraction of the tail so we
    can restore the whole string afterward. *)

(** Advancing pointer p past prefix s1 shifts the window start to the
    word holding the first byte of tail s2, as [str_shape_suffix]
    proves. *)
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

(** [word_string_suffix] weakens ownership of `s1 ++ s2` at pointer p to
    ownership of the tail s2 at the advanced pointer, discarding any
    leading words. *)
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

(** A caller that passes a suffix pointer into a helper function still
    needs to recover the full string once that helper returns. Lemma
    [word_string_borrow] lends a fractional share q1 of the tail s2 and
    returns a [[magic-wand|magic wand]] that restores the full string. *)
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

(** ## Literals

    String literals in a module's initial memory are laid out 16-byte
    aligned and rounded up to whole 8-byte words. Here we package a
    literal's liveness token and words into [lit_ps], prove its keys
    are distinct, and turn it into an exclusive [word_string] that can
    then be frozen with [word_string_persist]. *)

(** [lit_ps] collects the liveness token and aligned word pieces for a
    string literal at base address b. *)
Definition lit_ps (b : Z) (reg : region) (ws : list Z) : list (piece * pval) :=
  (PLive b, VLive reg) :: words_ps b 0 ws.

(** [lit_ps_nodup] proves that all piece keys in [lit_ps] are distinct,
    as required when initializing the program logic heap. *)
Lemma lit_ps_nodup b reg ws : NoDup (lit_ps b reg ws).*1.
Proof.
  cbn [lit_ps fmap list_fmap fst]. rewrite (words_ps_keys b 0 ws). apply NoDup_cons. split.
  - intros Hin. apply list_elem_of_fmap in Hin as (? & ? & _). discriminate.
  - apply NoDup_fmap_2; [intros x y E; congruence | apply NoDup_seqZ].
Qed.

(** At program startup, string literals begin as raw byte and liveness
    pieces in initial memory. Lemma [word_string_literal] converts those
    initial pieces [lit_ps] into a full [word_string] whenever the
    literal satisfies [str_shape]. *)
Lemma word_string_literal b reg ws s :
  str_shape (mkPtr b (Ro b)) b reg ws s -> pts (lit_ps b reg ws) ⊢ word_string (DfracOwn 1) (mkPtr b (Ro b)) s.
Proof.
  iIntros (Hs) "Hps". iExists b, reg, ws. iSplit; [done|].
  replace (wstart (mkPtr b (Ro b)) - b) with 0 by (unfold wstart; cbn; rewrite (ss_align _ _ _ _ _ Hs); lia).
  rewrite /lit_ps pts_ptsq (ptsq_app _ [_]). iExact "Hps".
Qed.

End word_string.

(** ## Over a Logic instance

    The final two lemmas connect [word_string] back to the program logic
    over an arbitrary [[runtime]] R and logic instance LG0. They allow
    callers to extract physical memory readability for external calls
    and to discharge read checks using a fractional liveness token. *)

(** The module [WordStringOn] lifts string readability and fractional
    read checks into an arbitrary [[runtime]] R and logic instance LG0. *)
Module WordStringOn (R : Runtime) (LG0 : LogicSig R).
Module LG := LG0.
Module L := LG.L.
Import L LG.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** Every Iris proof needs a state interpretation linking memory and
    world state to the operational semantics. [rules_irisGS] builds that
    instance from [registry], [wi], and [ge]. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** [gexpr] abbreviates the expression type of the parameterized
    language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** [word_string_readable] extracts from [heap_interp] and [word_string]
    that every byte of s and its NUL terminator is readable in state σ
    and matches s. *)
Lemma word_string_readable σ dq p s : heap_interp wi σ -∗ word_string dq p s -∗
  ⌜(forall n, 0 <= n <= Z.of_nat (length s) + 1 -> readable_bytes (ls_mem σ) p n) /\
   os_bytes (ls_mem σ) p (Z.of_nat (length s)) = s⌝.
Proof.
  iIntros "Hσ (%b & %reg & %ws & %Hs & Hl & Hw)".
  iDestruct (ptsq_facts with "Hσ Hl") as %([Hlv _] & _).
  iDestruct (ptsq_facts with "Hσ Hw") as %(Ha & _). iPureIntro. exact (str_shape_bytes _ _ _ _ _ _ Hs Hlv Ha).
Qed.

(** Reading through a pointer only requires shared ownership of the
    target object's liveness token. Lemma [wp_check_read_dq] verifies a
    read [[check]] using a fractional share dq of [liveq] and binds the
    checked pointer to d. *)
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
