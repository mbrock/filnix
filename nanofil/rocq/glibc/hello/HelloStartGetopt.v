(** When getopt reports a bad option, gettext translates the message
    and glibc's formatter prints it to stderr. Both read objects of
    Hello's image that neither startup nor the rest of main uses. Hello
    therefore starts with them in its private state, and this module
    says which objects those are and what they give.

    The objects come in two groups. Gettext's constants, the formats of
    getopt's messages and the formatter's tables never change, so they
    freeze into read-only strings and bytes that any call may read.
    Gettext's three locks, its cache root and its list of bound domains
    are writable, so the private state owns them outright. Each of them
    starts as zero bytes, so every lock is free, the cache is empty and
    no domain is bound. *)

From Glibc Require Import GlibcTactics GlibcProgram.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From stdpp Require Import list.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Run Semantics Pieces Heap Logic MemLogic StringLogic.
From Glibc Require Import FileInv WordString RdlockLogic RwlockIdle TfindEmpty PrintfSpec StartImageCpu
  HelloGetoptDiagMsgs HelloGettextLocaleConst HelloGettextSuffix HelloGettextDomain
  HelloImageModule HelloImageLoad HelloImageKept HelloImageDiagObjs.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** ## What the pieces give *)

Section own.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** These are the places of the objects, as the image gives them. *)
Local Abbreviation nb := (img_a "_nl_category_names").
Local Abbreviation ib := (img_a "_nl_category_name_idxs").
Local Abbreviation cb := (img_a "_nl_C_name").
Local Abbreviation s276 := (img_a "glibc_dcigettext#str.276").
Local Abbreviation s277 := (img_a "glibc_dcigettext#str.277").
Local Abbreviation dmb := (img_a "__GI__libc_intl_domainname").

(** Every call may read these constants: the nine formats, the two
    pieces of a catalog's file name, the name of the message category
    and its index, the locale name "C", the C library's domain and the
    formatter's tables. *)
Definition hello_getopt_ro : iProp Σ :=
  dgx_msgs hello_msg_bases ∗
  word_string DfracDiscarded (mkPtr s276 (Ro s276)) [47] ∗
  word_string DfracDiscarded (mkPtr s277 (Ro s277)) [46; 109; 111] ∗
  word_string DfracDiscarded (mkPtr (nb + lc_messages_off) (Ro nb)) lc_messages ∗
  liveq DfracDiscarded ib (img_gd "_nl_category_name_idxs") ∗ bytesq DfracDiscarded ib 5 [lc_messages_off] ∗
  word_string DfracDiscarded (mkPtr cb (Ro cb)) lc_c ∗
  word_string DfracDiscarded (mkPtr dmb (Ro dmb)) libc_domain_text ∗
  printf_ro.

#[global] Instance hello_getopt_ro_persistent : Persistent hello_getopt_ro.
Proof using Type. rewrite /hello_getopt_ro. apply _. Qed.

(** The private state owns gettext's three locks, which are free, its
    cache, which is empty, and its list of domains, which is empty. It
    also owns the name of the messages' locale, which is "C". *)
Definition hello_getopt_rw : iProp Σ :=
  rw_state (img_a "_nl_state_lock") (img_gd "_nl_state_lock") 0 0 0 0 ∗
  rw_state (img_a "__libc_setlocale_lock") (img_gd "__libc_setlocale_lock") 0 0 0 0 ∗
  rw_state (img_a "glibc_dcigettext#tree_lock") (img_gd "glibc_dcigettext#tree_lock") 0 0 0 0 ∗
  tfind_root (DfracOwn 1) (img_a "glibc_dcigettext#root") 0 (img_gd "glibc_dcigettext#root") ∗
  liveq (DfracOwn 1) (img_a "_nl_domain_bindings") (img_gd "_nl_domain_bindings") ∗
  pcellq (DfracOwn 1) (img_a "_nl_domain_bindings") 0 null ∗
  pcell (img_a "_nl_global_locale") 168 (mkPtr cb (Ro cb)).

(** Eight zero bytes with no capabilities are a stored null pointer. *)
Lemma zero_null_cell b reg : pts (obj_ps (b, reg) (repeat 0 8%nat)) ⊢ live b reg ∗ pcell b 0 null.
Proof using Type.
  rewrite obj_ps_own. cbn [fst snd].
  assert (E1 : byte_ps b 0 (repeat 0 8%nat) = cell b 0 (ptr_addr null)) by reflexivity.
  assert (E2 : aux_ps b 0 (repeat CNone 8%nat) = (PAux b 0, VAux (ptr_cap null)) :: aux_ps b 1 (repeat CNone 7%nat))
    by reflexivity.
  rewrite /bytes /auxes /pcell E1 E2 (pts_app [_] (aux_ps _ _ _)) (pts_app [_] (cell _ _ _)).
  iIntros "($ & H & [A _])". iFrame.
Qed.

(** A lock of 56 zero bytes is free: no reader, no writer and no flag. *)
Lemma zero_rw_lock b reg : pts (obj_ps (b, reg) (repeat 0 56%nat)) ⊢ rw_state b reg 0 0 0 0.
Proof using Type.
  rewrite obj_ps_own. cbn [fst snd].
  assert (E : repeat 0 56%nat = int_bytes 0 ++ repeat 0 4%nat ++ int_bytes 0 ++ int_bytes 0 ++ repeat 0 8%nat ++
    int_bytes 0 ++ int_bytes 0 ++ repeat 0 16%nat ++ int_bytes 0 ++ repeat 0 4%nat) by reflexivity.
  rewrite E !bytes_app. cbn [length repeat Z.of_nat int_bytes].
  iIntros "(Hl & (B0 & _ & B8 & B12 & _ & B24 & B28 & _ & B48 & _) & _)". iApply rw_state_zero.
  rewrite /rw_cells /int_cell. iFrame "Hl".
  iSplitL "B0"; [iSplit; [iPureIntro; lia | iExact "B0"]|].
  iSplitL "B8"; [iSplit; [iPureIntro; lia | iExact "B8"]|].
  iSplitL "B12"; [iSplit; [iPureIntro; lia | iExact "B12"]|].
  iSplitL "B24"; [iSplit; [iPureIntro; lia | iExact "B24"]|].
  iSplitL "B28"; [iSplit; [iPureIntro; lia | iExact "B28"]|]. iSplit; [iPureIntro; lia | iExact "B48"].
Qed.

(** A table whose bytes are the formatter's bytes is a read-only
    table. *)
Lemma ro_table_own n b reg xs :
  lookup (TAtom n) (ge_globals ge) = Some (mkPtr b (Ro b)) -> 0 < b ->
  b + Z.of_nat (length (table_bytes n)) <= r_end reg -> r_end reg <= 2 ^ 63 -> xs = table_bytes n ->
  pts (obj_ps (b, reg) xs) ==∗ ro_table n.
Proof using Type.
  intros Hl Hb He Ht ->. rewrite obj_ps_own /live /bytes. cbn [fst snd]. iIntros "(Hl & Hb & _)".
  rewrite !pts_ptsq. iMod (ptsq_persist with "Hl") as "#Hl". iMod (ptsq_persist with "Hb") as "#Hb".
  iModIntro. iExists b, reg. iSplit; [done|]. iFrame "Hl Hb".
Qed.

(** A null global is a null global that nobody writes. *)
Lemma null_global_own n b reg :
  lookup (TAtom n) (ge_globals ge) = Some (mkPtr b (Obj b)) -> 0 < b -> b mod 8 = 0 ->
  b + 8 <= r_end reg -> r_end reg <= 2 ^ 63 ->
  pts (obj_ps (b, reg) (repeat 0 8%nat)) ==∗ null_global n.
Proof using Type.
  intros Hl Hb H8 He Ht. rewrite zero_null_cell /live /pcell. iIntros "[Hl Hc]".
  rewrite !pts_ptsq. iMod (ptsq_persist with "Hl") as "#Hl". iMod (ptsq_persist with "Hc") as "#Hc".
  iModIntro. iExists b, reg. iSplit; [done|]. iFrame "Hl Hc".
Qed.

(** At startup, Hello's private memory holds the bytes of these
    objects. This lemma turns those bytes into the strings, tables and
    cells above. *)
Lemma hello_getopt_own : ge_globals ge = img_globals ->
  pts hello_getopt_priv_ps ==∗ hello_getopt_ro ∗ hello_getopt_rw.
Proof using Type.
  intros Hg. rewrite /hello_getopt_priv_ps /hello_kept_ps /hello_diag_objs_ps /hello_gettext_rw_ps /hello_printf_ro_ps.
  iIntros "H". iDestruct (pts_app with "H") as "[HK [HR HP]]". iDestruct (pts_app with "HP") as "[HP Sl]".
  iDestruct (pts_app with "HK") as "[Hlc HK]". iDestruct (pts_app with "HK") as "[Hmsg HK]".
  iDestruct (pts_app with "HK") as "[Hsuf Hdom]".
  iDestruct (pts_app with "HR") as "[L1 HR]". iDestruct (pts_app with "HR") as "[L2 HR]".
  iDestruct (pts_app with "HR") as "[L3 HR]". iDestruct (pts_app with "HR") as "[Rt Db]".
  iDestruct (pts_app with "HP") as "[J HP]". iDestruct (pts_app with "HP") as "[S HP]".
  iDestruct (pts_app with "HP") as "[N1 HP]". iDestruct (pts_app with "HP") as "[N2 N3]".
  iMod (lc_own with "Hlc") as "#(Hcat & Hil & Hib & Hc)"; [vm_compute; intuition congruence|].
  iMod (dgx_msgs_own with "Hmsg") as "#Hm".
  { repeat apply Forall2_cons; try apply Forall2_nil; unfold lit_fit; vm_compute; split_and!; first [reflexivity | discriminate]. }
  iMod (dci_suffix_own with "Hsuf") as "#[H276 H277]"; [vm_compute; intuition congruence..|].
  iMod (libc_domain_own with "Hdom") as "#Hd"; [rewrite Hg; vm_compute; reflexivity | vm_compute; intuition congruence|].
  iMod (ro_table_own jump_table with "J") as "#J";
    [rewrite Hg; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
     vm_compute; reflexivity|].
  iMod (ro_table_own step0_jumps with "S") as "#S";
    [rewrite Hg; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
     vm_compute; reflexivity|].
  iMod (null_global_own "__printf_function_table" with "N1") as "#N1";
    [rewrite Hg; vm_compute; reflexivity | vm_compute; first [reflexivity | congruence].. |].
  iMod (null_global_own "__printf_modifier_table" with "N2") as "#N2";
    [rewrite Hg; vm_compute; reflexivity | vm_compute; first [reflexivity | congruence].. |].
  iMod (null_global_own "__printf_va_arg_table" with "N3") as "#N3";
    [rewrite Hg; vm_compute; reflexivity | vm_compute; first [reflexivity | congruence].. |].
  iModIntro. iSplitR.
  { rewrite /hello_getopt_ro /printf_ro.
    iSplit; [iExact "Hm"|]. iSplit; [iExact "H276"|]. iSplit; [iExact "H277"|]. iSplit; [iExact "Hcat"|].
    iSplit; [iExact "Hil"|]. iSplit; [iExact "Hib"|]. iSplit; [iExact "Hc"|]. iSplit; [iExact "Hd"|].
    iSplit; [iExact "J"|]. iSplit; [iExact "S"|]. iSplit; [iExact "N1"|]. iSplit; [iExact "N2" | iExact "N3"]. }
  rewrite /hello_getopt_rw (zero_rw_lock _ _) (zero_rw_lock _ _) (zero_rw_lock _ _).
  iDestruct (zero_null_cell with "Rt") as "[Rl Rc]". iDestruct (zero_null_cell with "Db") as "[Dl Dc]".
  iFrame "L1 L2 L3". rewrite /hello_locale_slot_ps. rewrite /tfind_root /liveq /pcellq /live /pcell -!pts_ptsq. iFrame.
Qed.

End own.
