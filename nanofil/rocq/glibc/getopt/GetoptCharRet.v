From Glibc Require Import GlibcProgram.
(** One step of glibc's scanner reads a character from the current word
    of a cluster such as "-ab", looks it up in the short option string,
    and returns. The getopt wrapper then copies the private index, the
    bad-option field and the argument into the public variables, and the
    next call resumes from the private object. This file joins the
    character step with the known-option and unknown-option returns. It
    states every way the step can return in one relation, and it proves
    that the private object again makes up a session at the new index. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrchrCode StrchrnulLogic GetoptModule
  GetoptState GetoptBytes GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor GetoptDiag
  GetoptReqTail GetoptShort GetoptOptArg GetoptShortRet GetoptShortCap GetoptKnownCap GetoptKnownRet
  GetoptLongSession.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptEntry GetoptExchange GetoptInitialize
  GetoptKnownCap GetoptKnownRet GetoptLongSession GetoptShort GetoptShortCap GetoptState OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** ## The returned byte

    A known option returns its character as the return block reads it
    back, which converts the byte that the step loaded a second time.
    The conversion only looks at the low byte, so the second pass gives
    the same word as the first. *)

(** Converting a converted byte gives the first conversion again. *)
Lemma chr_w_twice y : 0 <= y < 256 -> chr_w (chr_w y) = chr_w y.
Proof.
  intros Hy. unfold chr_w at 1.
  assert (E : sign_extension 256 128 (chr_w y) = sign_extension 256 128 y).
  { unfold sign_extension. rewrite chr_w_byte; [|exact Hy]. rewrite (Z.mod_small y 256); [reflexivity | lia]. }
  rewrite E. reflexivity.
Qed.

(** The byte 200 converts to 2^32 - 56 both times, not to the byte 200. *)
Lemma chr_w_twice_ctl : chr_w (chr_w 200) = 4294967240 /\ chr_w 200 <> 200.
Proof. split; [reflexivity | discriminate]. Qed.

(** ## The ways a step returns

    A step returns in six ways. An unknown character returns '?'. A
    known character returns itself when it takes no argument, takes an
    optional argument, or takes a required argument from the rest of the
    word or from the next word. A required argument that is missing at
    the last word returns ':' or '?'. The relation below names, for each
    way, the returned value x, the new index i', the new bad-option field
    oo', the new argument a' and the new cursor c'. The index i, the
    bad-option field oo, the cursor cur and the argument a are their
    values before the step, and t is the rest of the word at the cursor.
    The form W; keeps its own exit and is not part of the relation. *)
Definition char_ret_case (ps : list ptr) (n i oo : Z) (cur a : ptr) (t so : list Z)
    (x i' oo' : Z) (a' c' : ptr) : Prop :=
  (x = 63 /\ i' = (if sbyte t 1 =? 0 then i + 1 else i) /\ oo' = chr_w (sbyte t 0) /\ a' = a /\
     c' = ptr_add cur 1) \/
  exists k : nat, (k < List.length so)%nat /\ sbyte so k = sbyte t 0 /\ sbyte t 0 <> 58 /\ sbyte t 0 <> 59 /\
  ((sbyte so (S k) <> 58 /\ x = chr_w (sbyte t 0) /\ i' = (if sbyte t 1 =? 0 then i + 1 else i) /\
      oo' = oo /\ a' = a /\ c' = ptr_add cur 1) \/
   (sbyte so (S k) = 58 /\ sbyte so (S (S k)) = 58 /\ x = chr_w (sbyte t 0) /\ i' = i + 1 /\ oo' = oo /\
      a' = (if sbyte t 1 =? 0 then null else ptr_add cur 1) /\ c' = null) \/
   (sbyte so (S k) = 58 /\ sbyte so (S (S k)) <> 58 /\ sbyte t 1 <> 0 /\ x = chr_w (sbyte t 0) /\
      i' = i + 1 /\ oo' = oo /\ a' = ptr_add cur 1 /\ c' = null) \/
   (sbyte so (S k) = 58 /\ sbyte so (S (S k)) <> 58 /\ sbyte t 1 = 0 /\ i + 1 < n /\ x = chr_w (sbyte t 0) /\
      i' = i + 2 /\ oo' = oo /\ a' = nth (Z.to_nat (i + 1)) ps null /\ c' = null) \/
   (sbyte so (S k) = 58 /\ sbyte so (S (S k)) <> 58 /\ sbyte t 1 = 0 /\ i + 1 = n /\
      x = (if sbyte so 0 =? 58 then 58 else 63) /\ i' = n /\ oo' = chr_w (sbyte t 0) /\ a' = a /\ c' = null)).

(** The next call can resume only from a sound place. After a step,
    either the cursor is one byte further on, and the index moved only
    if that byte ends the word, or the cursor is cleared. When it is
    cleared, the index moved by at most two, and by two only when a word
    was left for the argument. *)
Lemma char_ret_move ps n i oo cur a t so x i' oo' a' c' :
  char_ret_case ps n i oo cur a t so x i' oo' a' c' ->
  (c' = ptr_add cur 1 /\ i' = (if sbyte t 1 =? 0 then i + 1 else i)) \/
  (c' = null /\ (i <= i' <= i + 1 \/ (i' = i + 2 /\ i + 1 < n))).
Proof.
  intros [H | (k & _ & _ & _ & _ & H)]; [left; tauto|].
  destruct H as [H | H]; [left; tauto | right].
  destruct H as [H | [H | [H | H]]]; destruct_and? H; split; (assumption || lia).
Qed.

(** These controls tell the cases apart. The cluster "-ab" with the
    option string "ab" returns 'a' at the same index, with the cursor one
    byte on at "b". *)
Lemma char_ret_ctl_short :
  char_ret_case [] 1 0 0 null null [97; 98] [97; 98] 97 0 0 null (ptr_add null 1).
Proof.
  right. exists 0%nat. cbn. repeat split; try lia. left. cbn. repeat split; lia.
Qed.

(** The cluster "-a" with the option string "a:" and a second word p1
    takes p1 as the argument and moves the index by two. *)
Lemma char_ret_ctl_next p1 :
  char_ret_case [null; p1] 2 0 0 null null [97] [97; 58] 97 2 0 p1 null.
Proof.
  right. exists 0%nat. cbn. repeat split; try lia. right. right. right. left. cbn. repeat split; lia.
Qed.

(** An unknown character never moves the index by two. *)
Lemma char_ret_ctl_unknown t i x i' oo' (a a' cur c' : ptr) :
  x = 63 /\ i' = (if sbyte t 1 =? 0 then i + 1 else i) /\ oo' = chr_w (sbyte t 0) /\ a' = a /\
    c' = ptr_add cur 1 -> i' <> i + 2.
Proof. intros (_ & -> & _). destruct (_ =? _); lia. Qed.

Import GetoptShortCap GetoptKnownCap GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML
  FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

(** The step must keep these names of the entry environment, because
    the option blocks after it read them. *)
Definition char_ret_keys : list name := Eval vm_compute in
  List.map TAtom ["v0"; "v2"; "v6"; "v12"; "v80"; "pr.1"; "pr.3"; "chk0"; "chk1"; "chk2"; "chk19";
    "chk20"]%string.

Import ProgramAbbreviations.
Section char_ret.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance charret_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** ## The session after a return

    The step rewrites the index, the bad-option field, the argument and
    the cursor, and leaves the other five fields alone. When the cursor
    stays inside the word, the session keeps its index. When the cursor
    reaches the terminator or the step clears it, the index moves and the
    session follows it. *)

(** After a step, the next call must find a sound private object. This
    lemma shows that it does: the object makes up a session at the new
    index. It uses what held before the step, namely the bounds, the
    cursor, the rest t of the word and its first byte. *)
Lemma char_ret_session b r av ar ps s oo t so x i' oo' a a' c' :
  getopt_bounds (Z.of_nat (List.length ps)) (gs_ind s) s -> gs_ind s < Z.of_nat (List.length ps) ->
  gs_initialized s = 1 -> 0 <= gs_order s <= 2 -> sbyte t 0 <> 0 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (Z.of_nat (List.length ps) + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  char_ret_case ps (Z.of_nat (List.length ps)) (gs_ind s) oo (gs_next s) a t so x i' oo' a' c' ->
  getopt_cursor ps (gs_ind s) s -∗ word_string DfracDiscarded (gs_next s) t -∗
  live b r -∗ int_cell b 0 i' -∗ int_cell b 4 (gs_err s) -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗
  int_cell b 24 (gs_initialized s) -∗ pcell b 32 c' -∗ int_cell b 40 (gs_order s) -∗
  int_cell b 44 (gs_first s) -∗ int_cell b 48 (gs_last s) -∗
  getopt_session b r av ar ps i'.
Proof.
  intros Hbd Hlt Hin Hord Ht0 Hb Hal Hend Hr Hav Hala Hda Hra Hcase.
  iIntros "Hcu #Hws Hl Hib Her Hoo Hab Hini Hcur Hord Hfi Hla".
  iDestruct (ws_shape with "Hws") as %(Htc & _ & _).
  pose proof (sbyte_in_len t 0 Ht0) as Hlen0.
  destruct (char_ret_move _ _ _ _ _ _ _ _ _ _ _ _ _ Hcase) as [[-> ->] | [-> Hi']].
  - destruct (Z.eqb_spec (sbyte t 1) 0) as [Ht1 | Ht1].
    + apply (sbyte_zero t 1 Htc) in Ht1; [|lia].
      iApply (long_session b r av ar ps s (gs_ind s + 1) oo' a' (ptr_add (gs_next s) 1) t
                with "Hcu Hws Hl Hib Her Hoo Hab Hini Hcur Hord Hfi Hla"); try assumption; [lia|].
      right. right. rewrite -Ht1. reflexivity.
    + iApply (short_session b r av ar ps s oo' a' t with "Hcu Hws Hl Hib Her Hoo Hab Hini Hcur Hord Hfi Hla");
        try assumption. pose proof (sbyte_in_len t 1 Ht1). lia.
  - iApply (long_session b r av ar ps s i' oo' a' null t with "Hcu Hws Hl Hib Her Hoo Hab Hini Hcur Hord Hfi Hla");
      try assumption. by left.
Qed.

(** ## From the character to the return

    A caller of the scanner needs to know what one step returns and what
    it hands back. The rule below runs the step from the block that loads
    the character up to the return. It starts in the environment that the
    entry blocks leave, where po is the option string. The step keeps the
    names in ks, and the option blocks after it keep the names in ks2. *)

(** A step reads the first byte of the rest t of the current word and
    returns in one of the ways that [char_ret_case] lists. The caller gets
    back the four fields that the relation names: the index, the bad
    option, the argument and the cursor. It also gets the evidence that
    the new argument is usable, the argument vector and the resource G
    for reports. The form W; stops at its own block instead. *)
Lemma wp_getopt_char_ret ks ks2 e fr i n pe cur t po so oo a lo li lonly b r av ar ps (G : iProp Σ) T fp dom
    se sereg mid mid' Φ :
  avoids ks char_names = true -> incl char_ret_keys ks ->
  avoids ks2 opt_names = true -> avoids ks2 req_names = true -> avoids ks2 diag_names = true ->
  avoids ks2 ret_names = true -> incl known_req_keys ks2 ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid' ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  entry_env e n (mkPtr av (Obj av)) po lo li lonly b pe ->
  0 <= i < n -> n < 2 ^ 31 -> Z.of_nat (List.length ps) = n -> sbyte t 0 <> 0 -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  word_string DfracDiscarded cur t -∗ word_string DfracDiscarded po so -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo -∗ pcell b 16 a -∗ pcell b 32 cur -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ arg_cap a -∗
  ((∀ e' e'' k, ⌜keeps ks e e' /\ keeps ks2 e' e'' /\ lookup (TAtom "v455") e' = Some (WInt (chr_w (sbyte t 0))) /\
        (k < List.length so)%nat /\ sbyte so k = sbyte t 0 /\
        lookup (TAtom "v459") e' = Some (WPtr (ptr_add po (Z.of_nat k))) /\
        lookup (TAtom "chk137") e' = Some (WPtr (mkPtr (b + 32) (Obj b))) /\
        sbyte so k = 87 /\ sbyte so (S k) = 59 /\ ptr_addr lo mod 2 ^ 64 <> 0⌝ -∗
      live b r -∗ int_cell b 0 (if sbyte t 1 =? 0 then i + 1 else i) -∗ int_cell b 8 oo -∗ pcell b 16 a -∗
      pcell b 32 (ptr_add cur 1) -∗ live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap a -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e'' [] None (Enter (TAtom "L508") (Some (TAtom "L524")))) : gexpr)
        {{ Φ }}) ∧
   (∀ x i' oo' a' c', ⌜char_ret_case ps n i oo cur a t so x i' oo' a' c'⌝ -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap a' -∗ Φ (Ret (WInt x)))) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L75") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hkin Hop Hrq Hdg Hrt Hinc Hg Hgn Hdiag Hse Hmid' Hmid
    (H0 & H2 & H6 & H8 & H10 & H12 & Hpr1 & Hpr3 & Hc0 & Hc1 & Hc2 & Hc19 & Hc20 & H80)
    Hi Hn Hlen Ht0 Hpe Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser.
  iIntros "#Hws #Hpo Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl #Hs HG Hca HK".
  iDestruct (ws_shape with "Hws") as %(Htc & _ & _).
  pose proof (sbyte_range t 0 Htc) as Hrg.
  iApply (wp_getopt_char ks e fr i cur t po so b r Φ with "Hws Hpo Hl Hib Hcur [-]"); try (assumption || lia).
  iSplit.
  - iIntros (e' (Hk' & H455)) "Hl Hib Hcur".
    assert (Hkp : forall k0 v, In k0 char_ret_keys -> lookup k0 e = v -> lookup k0 e' = v).
    { intros k0 v Hm. apply keeps_in with ks; [exact Hk' | exact (Hkin k0 Hm)]. }
    iApply (wp_getopt_unknown_ret ks2 e' (TAtom "L485") (chr_w (sbyte t 0)) pe
              (if sbyte t 1 =? 0 then i + 1 else i) a (ptr_add cur 1) oo b r av ar ps G T fp dom se sereg mid' Φ
              with "Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl Hs HG Hca [HK]");
      try (assumption || lia || apply chr_w_range);
      try (apply Hkp; [cbn; repeat (first [left; reflexivity | right]) | eassumption]).
    { destruct ps; cbn in Hlen; [lia | discriminate]. }
    iIntros "Hl Hib Hoob Hab Hcur Ha Hcl HG Hca". iDestruct "HK" as "[_ HK]".
    iApply ("HK" $! 63 (if sbyte t 1 =? 0 then i + 1 else i) (chr_w (sbyte t 0)) a (ptr_add cur 1)
              with "[%] Hl Hib Hoob Hab Hcur Ha Hcl HG Hca").
    left. split_and!; auto.
  - iIntros (e' k (Hk' & H455 & Hk & Hso & H58 & H59 & H459 & H137)) "Hl Hib Hcur".
    assert (Hkp : forall k0 v, In k0 char_ret_keys -> lookup k0 e = v -> lookup k0 e' = v).
    { intros k0 v Hm. apply keeps_in with ks; [exact Hk' | exact (Hkin k0 Hm)]. }
    iApply (wp_getopt_known_ret ks2 e' i n (chr_w (sbyte t 0)) pe cur t po so k a lo oo b r av ar ps G T fp dom
              se sereg mid Φ with "Hws Hpo Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl Hs HG Hca [HK]");
      try (assumption || lia || apply chr_w_range);
      try (apply Hkp; [cbn; repeat (first [left; reflexivity | right]) | eassumption]).
    rewrite (chr_w_twice (sbyte t 0) Hrg).
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]].
    + iDestruct "HK" as "[HK _]". iIntros (e'' Hp) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hca".
      iApply ("HK" $! e' e'' k with "[%] Hl Hib Hoob Hab Hcur Ha Hcl HG Hca"). destruct_and?. split_and!; auto.
    + iDestruct "HK" as "[_ HK]". iIntros (Hp) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hca".
      iApply ("HK" $! (chr_w (sbyte t 0)) (if sbyte t 1 =? 0 then i + 1 else i) oo a (ptr_add cur 1)
                with "[%] Hl Hib Hoob Hab Hcur Ha Hcl HG Hca").
      right. exists k. split_and!; try assumption. left. split_and!; auto.
    + iDestruct "HK" as "[_ HK]". iIntros (Hp) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hca".
      iApply ("HK" $! (chr_w (sbyte t 0)) (i + 1) oo (if sbyte t 1 =? 0 then null else ptr_add cur 1) null
                with "[%] Hl Hib Hoob Hab Hcur Ha Hcl HG Hca").
      right. exists k. split_and!; try assumption. right. left. destruct_and?. split_and!; auto.
    + iDestruct "HK" as "[_ HK]". iIntros (Hp) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hca".
      iApply ("HK" $! (chr_w (sbyte t 0)) (i + 1) oo (ptr_add cur 1) null with "[%] Hl Hib Hoob Hab Hcur Ha Hcl HG Hca").
      right. exists k. split_and!; try assumption. right. right. left. destruct_and?. split_and!; auto.
    + iDestruct "HK" as "[_ HK]". iIntros (Hp) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hca".
      iApply ("HK" $! (chr_w (sbyte t 0)) (i + 2) oo (nth (Z.to_nat (i + 1)) ps null) null
                with "[%] Hl Hib Hoob Hab Hcur Ha Hcl HG Hca").
      right. exists k. split_and!; try assumption. right. right. right. left. destruct_and?. split_and!; auto.
    + iDestruct "HK" as "[_ HK]". iIntros (Hp) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hca".
      replace (chr_w (if sbyte so 0 =? 58 then 58 else 63)) with (if sbyte so 0 =? 58 then 58 else 63)
        by (destruct (_ =? _); reflexivity).
      iApply ("HK" $! (if sbyte so 0 =? 58 then 58 else 63) n (chr_w (sbyte t 0)) a null
                with "[%] Hl Hib Hoob Hab Hcur Ha Hcl HG Hca").
      right. exists k. split_and!; try assumption. right. right. right. right. destruct_and?. split_and!; auto.
Qed.

(** ## The session after a step

    The next call of the scanner needs a session, so a caller wants the
    step to end with one. The rule below starts from the private object
    as the entry blocks leave it. It runs the rule above and then makes
    the object a session again, at the new index. The caller also gets
    the evidence for the new argument. The form W; gets the object back
    as the step left it, with the cursor that held before the step. *)

(** A step from a session state s, whose cursor points at the rest t of
    the current word, returns with a session at the new index i'. The
    relation [char_ret_case] names i' and the new argument a', for which
    the caller also gets the evidence that the wrapper needs. *)
Lemma wp_getopt_char_session ks ks2 e fr s pe t po so lo li lonly b r av ar ps (G : iProp Σ) T fp dom
    se sereg mid mid' Φ :
  avoids ks char_names = true -> incl char_ret_keys ks ->
  avoids ks2 opt_names = true -> avoids ks2 req_names = true -> avoids ks2 diag_names = true ->
  avoids ks2 ret_names = true -> incl known_req_keys ks2 ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid' ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  entry_env e (Z.of_nat (List.length ps)) (mkPtr av (Obj av)) po lo li lonly b pe ->
  getopt_bounds (Z.of_nat (List.length ps)) (gs_ind s) s -> gs_ind s < Z.of_nat (List.length ps) ->
  Z.of_nat (List.length ps) < 2 ^ 31 -> gs_initialized s = 1 -> 0 <= gs_order s <= 2 ->
  sbyte t 0 <> 0 -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (Z.of_nat (List.length ps) + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  getopt_cursor ps (gs_ind s) s -∗ word_string DfracDiscarded (gs_next s) t -∗
  word_string DfracDiscarded po so -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 (gs_ind s) -∗ int_cell b 4 (gs_err s) -∗ int_cell b 8 (gs_opt s) -∗
  pcell b 16 (gs_arg s) -∗ int_cell b 24 (gs_initialized s) -∗ pcell b 32 (gs_next s) -∗
  int_cell b 40 (gs_order s) -∗ int_cell b 44 (gs_first s) -∗ int_cell b 48 (gs_last s) -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ arg_cap (gs_arg s) -∗
  ((∀ e' e'' k, ⌜keeps ks e e' /\ keeps ks2 e' e'' /\ lookup (TAtom "v455") e' = Some (WInt (chr_w (sbyte t 0))) /\
        (k < List.length so)%nat /\ sbyte so k = sbyte t 0 /\
        lookup (TAtom "v459") e' = Some (WPtr (ptr_add po (Z.of_nat k))) /\
        lookup (TAtom "chk137") e' = Some (WPtr (mkPtr (b + 32) (Obj b))) /\
        sbyte so k = 87 /\ sbyte so (S k) = 59 /\ ptr_addr lo mod 2 ^ 64 <> 0⌝ -∗
      getopt_cursor ps (gs_ind s) s -∗
      live b r -∗ int_cell b 0 (if sbyte t 1 =? 0 then gs_ind s + 1 else gs_ind s) -∗ int_cell b 4 (gs_err s) -∗
      int_cell b 8 (gs_opt s) -∗ pcell b 16 (gs_arg s) -∗ int_cell b 24 (gs_initialized s) -∗
      pcell b 32 (ptr_add (gs_next s) 1) -∗ int_cell b 40 (gs_order s) -∗ int_cell b 44 (gs_first s) -∗
      int_cell b 48 (gs_last s) -∗ live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap (gs_arg s) -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e'' [] None (Enter (TAtom "L508") (Some (TAtom "L524")))) : gexpr)
        {{ Φ }}) ∧
   (∀ x i' oo' a' c',
      ⌜char_ret_case ps (Z.of_nat (List.length ps)) (gs_ind s) (gs_opt s) (gs_next s) (gs_arg s) t so x i' oo' a' c'⌝ -∗
      getopt_session b r av ar ps i' -∗ live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap a' -∗ Φ (Ret (WInt x)))) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L75") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hkin Hop Hrq Hdg Hrt Hinc Hg Hgn Hdiag Hse Hmid' Hmid Henv Hbd Hlt Hn Hin Hord Ht0 Hpe
    Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser.
  iIntros "Hcu #Hws #Hpo Hsl Hsc Hl Hib Her Hoob Hab Hini Hcur Hord Hfi Hla Ha Hcl #Hs HG Hca HK".
  pose proof Hbd as (_ & Hi0 & _).
  iApply (wp_getopt_char_ret ks ks2 e fr (gs_ind s) (Z.of_nat (List.length ps)) pe (gs_next s) t po so (gs_opt s)
            (gs_arg s) lo li lonly b r av ar ps G T fp dom se sereg mid mid' Φ
            with "Hws Hpo Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl Hs HG Hca [-]"); try (assumption || lia).
  iSplit.
  - iDestruct "HK" as "[HK _]". iIntros (e' e'' k Hp) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hca".
    iApply ("HK" $! e' e'' k with "[%] Hcu Hl Hib Her Hoob Hab Hini Hcur Hord Hfi Hla Ha Hcl HG Hca"). exact Hp.
  - iDestruct "HK" as "[_ HK]". iIntros (x i' oo' a' c' Hc) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hca".
    iApply ("HK" $! x i' oo' a' c' with "[%] [Hcu Hl Hib Her Hoob Hab Hini Hcur Hord Hfi Hla] Ha Hcl HG Hca");
      [exact Hc|].
    iApply (char_ret_session b r av ar ps s (gs_opt s) t so x i' oo' (gs_arg s) a' c'
              with "Hcu Hws Hl Hib Her Hoob Hab Hini Hcur Hord Hfi Hla"); assumption.
Qed.

End char_ret.
