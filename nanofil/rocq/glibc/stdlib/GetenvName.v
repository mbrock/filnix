(** A non-null environment does not by itself make a getenv call readable.
    After reading its globals, glibc checks the name's first character and calls strlen for nonempty names.
    These rules use the shared string's bytes for both operations and leave
    the environment scan as a separate continuation. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  Machine Pieces Heap Language Logic ExternalCalls StepRules Symbolic.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics WordString
  GetoptBytes GetenvCode GetenvEntry StrlenWord StrlenLogic.
Import ListNotations LG0 LG0.L ProgramAbbreviations GetoptBytes.ML.
Open Scope Z_scope.

(** The nonempty-name branch retains the byte read and both guard results. *)
Definition getenv_name_env e p s :=
  put (TAtom "v25") (WInt 0)
    (put (TAtom "v23") (WInt 0)
      (put (TAtom "v22") (WInt (chr_w (sbyte s 0)))
        (put (TAtom "chk2") (WPtr p) e))).

(** The first slot read records the length, array cursor, and loaded pointer. *)
Definition getenv_slot_env e ep q n :=
  put (TAtom "v45") (WInt (if ptr_addr q =? 0 then 1 else 0))
    (put (TAtom "v43") (WInt (ptr_addr q))
      (put (TAtom "v38") (WPtr q)
        (put (TAtom "chk3") (WPtr ep)
          (put (TAtom "pr.1") (WPtr ep) (put (TAtom "v29") (WInt n) e))))).

(** A changed counter leaves its new sample in the environment before retrying. *)
Definition getenv_retry_env e bc counter :=
  put (TAtom "v88") (WInt 0)
    (put (TAtom "v86") (WInt (counter mod 2 ^ 64))
      (put (TAtom "chk7") (WPtr (mkPtr bc (Obj bc)))
        (put (TAtom "v85") (WPtr (mkPtr bc (Obj bc))) e))).

(** Before testing the name, getenv has saved the counter value and
    environment pointer in these temporary variables. *)
Definition getenv_nonnull_env p bc be counter ep :=
  [(TAtom "v17", WInt 0); (TAtom "v16", WInt 0);
   (TAtom "v15", WInt (ptr_addr ep)); (TAtom "v10", WPtr ep);
   (TAtom "chk1", WPtr (mkPtr be (Obj be))); (TAtom "v9", WPtr (mkPtr be (Obj be)));
   (TAtom "v7", WInt (counter mod 2 ^ 64));
   (TAtom "chk0", WPtr (mkPtr bc (Obj bc))); (TAtom "v6", WPtr (mkPtr bc (Obj bc)));
   (TAtom "v0", WPtr p)].

Section name.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance getenv_name_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** An empty name returns null without calling strlen. A nonempty name reaches
    the actual strlen block with the caller's memory unchanged. The shared
    byte-access lemmas supply the bounds needed by the checked signed load. *)
Lemma getenv_name_guard e p s (G : iProp Σ) Φ :
  lookup (TAtom "v0") e = Some (WPtr p) ->
  word_string DfracDiscarded p s -∗ G -∗
  (match s with
   | [] => G -∗ Φ (Ret (WPtr null))
   | _ :: _ => G -∗ WP (ERun (mkFrame glibc_getenv (getenv_name_env e p s) [] None
       (Enter (TAtom "L13") (Some (TAtom "L19")))) : gexpr) {{ Φ }}
   end) -∗
  WP (ERun (mkFrame glibc_getenv e [] None
       (Enter (TAtom "L18") (Some (TAtom "L3")))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hp. iIntros "#Hname HG HK".
  iDestruct (ws_shape with "Hname") as %(Hchars & Hpos & Hfit).
  iDestruct (ws_byte p s 0 with "Hname") as (b reg) "(%Hb & #Hl & #Hb)"; [lia |].
  destruct Hb as (Hcap & Hbpos & Hbase & Hend & Hspace).
  step.
  check_read_dq "Hl" by (unfold raw_address; cbn; rewrite Z.add_0_r;
    rewrite (Z.mod_small (ptr_addr p) (2 ^ 64)); lia).
  iNext. iIntros "_".
  load_bytes_dq "Hl Hb" decode (apply extended_chr) by
    (unfold raw_address; rewrite Z.add_0_r; rewrite Z.mod_small; lia).
  iNext. iIntros "_ _". step. step. step.
  destruct s as [|a s].
  - branch. step. iApply wp_ret; [reflexivity | reflexivity |].
    iNext. iApply ("HK" with "HG").
  - apply Forall_cons_1 in Hchars as [Ha Hs].
    assert (Hcmp : (chr_w a mod 2 ^ 32 =? 0) = false).
    { rewrite (Z.mod_small (chr_w a)); [|apply chr_w_range].
      rewrite chr_w_eqb; [apply Z.eqb_neq; lia | lia | lia]. }
    cbn [sbyte nth app] in *.
    rewrite Hcmp. branch.
    iApply ("HK" with "HG").
Qed.

(** Glibc measures the name, then reads the first pointer in the environment
    array. If that pointer is null, it checks whether the counter changed.
    Otherwise it starts comparing the pointed-to string. The rule returns
    all borrowed memory permissions before either branch continues. *)
Lemma getenv_strlen_slot e p s ep q b reg o qreg dq dqtarget (G : iProp Σ) Φ
    `{!Defines ge "__GI_strlen" glibc_strlen} :
  lookup (TAtom "v0") e = Some (WPtr p) ->
  lookup (TAtom "v10") e = Some (WPtr ep) ->
  lookup (TAtom "v16") e = Some (WInt 0) ->
  (ptr_cap ep = Obj b \/ ptr_cap ep = Ro b) -> ptr_addr ep = b + o ->
  0 < b -> 0 <= o -> b + o + 8 <= r_end reg -> r_end reg <= 2 ^ 48 ->
  (b + o) mod 8 = 0 -> 0 <= ptr_addr q < 2 ^ 64 ->
  word_string DfracDiscarded p s -∗ liveq dq b reg -∗ pcellq dq b o q -∗
  live_capq dqtarget (ptr_cap q) qreg -∗ G -∗
  (liveq dq b reg -∗ pcellq dq b o q -∗ live_capq dqtarget (ptr_cap q) qreg -∗ G -∗
   WP (ERun (mkFrame glibc_getenv (getenv_slot_env e ep q (Z.of_nat (length s))) [] None
       (Enter (TAtom (if ptr_addr q =? 0 then "L35" else "L41")) (Some (TAtom "L32"))))
       : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getenv e [] None
       (Enter (TAtom "L13") (Some (TAtom "L19")))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hp Hep Hzero Hcap Haddr Hb Ho Hend Hspace Hal Hq.
  iIntros "#Hname Hl Hslot Htarget HG HK".
  iDestruct (ws_shape with "Hname") as %(_ & Hpos & Hlen). step.
  iApply (StrlenWord.wp_call_glibc_strlen registry (os_wi w0) ge with "Hname");
    [vx | apply defines | reflexivity |].
  iNext. iIntros "_". cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. step. step.
  check_read_dq "Hl" by (unfold raw_address; rewrite Haddr Z.add_0_r;
    rewrite (Z.mod_small (b + o) (2 ^ 64)); [first [lia | exact Hal] | lia]).
  iNext. iIntros "Hl".
  iApply (getenv_atomic_load with "Hl Hslot Htarget");
    [reflexivity | vx | exact Hcap |
     unfold raw_address; rewrite Haddr Z.add_0_r Z.mod_small; lia |
     exact Hal | exact Hq |].
  iNext. iIntros "Hl Hslot Htarget". step. step.
  rewrite (Z.mod_small (ptr_addr q) (2 ^ 64)); [|exact Hq].
  rewrite Zmod_0_l (Z.mod_small (Z.of_nat (length s)) (2 ^ 64)); [|lia].
  unfold getenv_slot_env.
  destruct (ptr_addr q =? 0) eqn:Hnull; branch;
    iApply ("HK" with "Hl Hslot Htarget HG").
Qed.

(** After finding the end of the array, getenv rereads the counter. Equal
    samples let it return null; unequal samples make it restart at L3.
    This rule leaves the restart for the caller to prove. *)
Lemma getenv_counter_check e old dq bc rc counter (G : iProp Σ) Φ :
  lookup (TAtom "v7") e = Some (WInt old) ->
  lookup (TAtom "__environ_counter") (ge_globals ge) = Some (mkPtr bc (Obj bc)) ->
  0 < bc -> bc + 8 <= r_end rc -> r_end rc <= 2 ^ 48 ->
  liveq dq bc rc -∗ icellq dq bc 0 counter -∗ G -∗
  (liveq dq bc rc -∗ icellq dq bc 0 counter -∗ G -∗
   if counter mod 2 ^ 64 =? old mod 2 ^ 64 then Φ (Ret (WPtr null)) else
   WP (ERun (mkFrame glibc_getenv (getenv_retry_env e bc counter) [] None
       (Enter (TAtom "L3") (Some (TAtom "L35")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getenv e [] None
       (Enter (TAtom "L35") (Some (TAtom "L32")))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hold Hcounter Hb Hend Hspace. iIntros "Hl Hcell HG HK".
  step. step_global Hcounter.
  check_read_dq "Hl" by (unfold raw_address; cbn; rewrite Z.add_0_r Z.mod_small; lia).
  iNext. iIntros "Hl".
  iApply (wp_raw_load_read_dq with "Hl Hcell");
    [reflexivity | vx | left; reflexivity |
     unfold raw_address; cbn; rewrite Z.add_0_r Z.mod_small; lia |].
  iNext. iIntros "Hl Hcell". step.
  rewrite Z.mod_mod; [|lia].
  destruct (counter mod 2 ^ 64 =? old mod 2 ^ 64) eqn:Hsame; branch.
  - step. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    iApply ("HK" with "Hl Hcell HG").
  - iApply ("HK" with "Hl Hcell HG").
Qed.

(** A non-null environment reaches the name guard after both global reads.
    The stored environment pointer retains its target lifetime, so reading
    its capability does not silently replace a freed pointer. *)
Lemma getenv_nonnull_entry p s dq bc rc be re counter ep dqtarget reg (G : iProp Σ) Φ :
  lookup (TAtom "__environ_counter") (ge_globals ge) = Some (mkPtr bc (Obj bc)) ->
  lookup (TAtom "__environ") (ge_globals ge) = Some (mkPtr be (Obj be)) ->
  0 < bc -> bc + 8 <= r_end rc -> r_end rc <= 2 ^ 48 ->
  0 < be -> be + 8 <= r_end re -> r_end re <= 2 ^ 48 -> be mod 8 = 0 ->
  0 < ptr_addr ep < 2 ^ 64 ->
  word_string DfracDiscarded p s -∗ getenv_globals dq bc rc be re counter ep -∗
  live_capq dqtarget (ptr_cap ep) reg -∗ G -∗
  (getenv_globals dq bc rc be re counter ep -∗ live_capq dqtarget (ptr_cap ep) reg -∗ G -∗
   WP (ERun (mkFrame glibc_getenv (getenv_nonnull_env p bc be counter ep) [] None
       (Enter (TAtom "L18") (Some (TAtom "L3")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (getenv_frame p) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hcounter Henv Hbc Hrc Hrcmax Hbe Hre Hremax Hal Hep.
  iIntros "#Hname (Hcl & Hcc & Hel & Hec) Htarget HG HK".
  unfold getenv_frame. step. step. step. step_global Hcounter.
  check_read_dq "Hcl" by (unfold raw_address; cbn; rewrite Z.add_0_r Z.mod_small; lia).
  iNext. iIntros "Hcl".
  iApply (wp_raw_load_read_dq with "Hcl Hcc");
    [reflexivity | reflexivity | left; reflexivity |
     unfold raw_address; cbn; rewrite Z.add_0_r Z.mod_small; lia |].
  iNext. iIntros "Hcl Hcc". step_global Henv.
  check_read_dq "Hel" by (unfold raw_address; cbn; rewrite Z.add_0_r;
    rewrite (Z.mod_small be (2 ^ 64)); [first [lia | exact Hal] | lia]).
  iNext. iIntros "Hel".
  iApply (getenv_atomic_load with "Hel Hec Htarget");
    [reflexivity | reflexivity | left; reflexivity |
     unfold raw_address; cbn; rewrite Z.add_0_r Z.mod_small; lia |
     rewrite Z.add_0_r; exact Hal | lia |].
  iNext. iIntros "Hel Hec Htarget". step. step. step.
  rewrite (Z.mod_small (ptr_addr ep) (2 ^ 64)); [|lia].
  rewrite ?Zmod_0_l (proj2 (Z.eqb_neq (ptr_addr ep) 0) ltac:(lia)). branch.
  iApply ("HK" with "[Hcl Hcc Hel Hec] Htarget HG"). iFrame.
Qed.

(** A call with an empty name returns null without scanning the environment.
    A nonempty name also returns null when the array starts with a null
    pointer and the counter has not changed. Otherwise this proof stops
    before comparing the first string, leaving that block's proof to the caller. *)
Lemma getenv_first_slot p s dq bc rc be re counter ep b reg o q qreg dqa dqt
    (E : iProp Σ) Φ `{!Defines ge "__GI_strlen" glibc_strlen} :
  lookup (TAtom "__environ_counter") (ge_globals ge) = Some (mkPtr bc (Obj bc)) ->
  lookup (TAtom "__environ") (ge_globals ge) = Some (mkPtr be (Obj be)) ->
  0 < bc -> bc + 8 <= r_end rc -> r_end rc <= 2 ^ 48 ->
  0 < be -> be + 8 <= r_end re -> r_end re <= 2 ^ 48 -> be mod 8 = 0 ->
  ptr_cap ep = Obj b -> ptr_addr ep = b + o ->
  0 < b -> 0 <= o -> b + o + 8 <= r_end reg -> r_end reg <= 2 ^ 48 ->
  (b + o) mod 8 = 0 -> 0 <= ptr_addr q < 2 ^ 64 ->
  let owned := (getenv_globals dq bc rc be re counter ep ∗ liveq dqa b reg ∗
                pcellq dqa b o q ∗ live_capq dqt (ptr_cap q) qreg ∗ E)%I in
  word_string DfracDiscarded p s -∗ owned -∗
  (owned -∗ match s with
    | [] => Φ (Ret (WPtr null))
    | _ :: _ => if ptr_addr q =? 0 then Φ (Ret (WPtr null)) else
      WP (ERun (mkFrame glibc_getenv
          (getenv_slot_env (getenv_name_env (getenv_nonnull_env p bc be counter ep) p s)
            ep q (Z.of_nat (length s))) [] None
          (Enter (TAtom "L41") (Some (TAtom "L32")))) : gexpr) {{ Φ }}
    end) -∗
  WP (ERun (getenv_frame p) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hcounter Henv Hbc Hrc Hrcmax Hbe Hre Hremax Hal Hcap Haddr
    Hb Ho Hend Hspace Halarray Hq owned.
  iIntros "#Hname (Hglobals & Hl & Hslot & Htarget & HE) HK".
  iAssert (live_capq dqa (ptr_cap ep) reg) with "[Hl]" as "Hcap".
  { rewrite /live_capq Hcap. iExact "Hl". }
  iCombine "Hslot Htarget HE" as "HG".
  iApply (getenv_nonnull_entry with "Hname Hglobals Hcap HG");
    try eassumption; try (rewrite Haddr; lia).
  iIntros "Hglobals Hcap (Hslot & Htarget & HE)".
  rewrite /live_capq Hcap. iRename "Hcap" into "Hl".
  iApply (getenv_name_guard _ p s owned with "Hname [Hglobals Hl Hslot Htarget HE]").
  { reflexivity. }
  { unfold owned. iFrame. }
  destruct s as [|a s].
  - iIntros "Howned". iApply ("HK" with "Howned").
  - iIntros "(Hglobals & Hl & Hslot & Htarget & HE)".
    iCombine "Hglobals HE" as "HG".
    iApply (getenv_strlen_slot with "Hname Hl Hslot Htarget HG");
      try (unfold getenv_name_env, getenv_nonnull_env; reflexivity);
      try eassumption; try (left; exact Hcap).
    iIntros "Hl Hslot Htarget [Hglobals HE]".
    destruct (ptr_addr q =? 0) eqn:Hnull.
    + iDestruct "Hglobals" as "(Hcl & Hcc & Hel & Hec)".
      iCombine "Hel Hec Hl Hslot Htarget HE" as "HG".
      iApply (getenv_counter_check with "Hcl Hcc HG");
        try eassumption.
      { unfold getenv_slot_env, getenv_name_env, getenv_nonnull_env. reflexivity. }
      iIntros "Hcl Hcc (Hel & Hec & Hl & Hslot & Htarget & HE)".
      rewrite Z.mod_mod; [|lia]. rewrite Z.eqb_refl.
      iApply ("HK" with "[Hcl Hcc Hel Hec Hl Hslot Htarget HE]").
      unfold owned, getenv_globals. iFrame.
    + iApply ("HK" with "[Hglobals Hl Hslot Htarget HE]").
      unfold owned. iFrame.
Qed.
End name.
