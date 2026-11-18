(** Hello's main first calls `c: setlocale (LC_ALL, "")`. The empty
    name asks setlocale to read each category's locale from the
    environment, and Hello runs in an environment that selects the C
    locale. This module proves that call over glibc's own code, which
    the image links in.

    In the C locale the call changes nothing that a reader can see.
    Setlocale takes its write lock, asks getenv for a locale path and
    finds none, and looks up every category, which finds the C data. All
    the names are "C", so the composite name is `c: _nl_C_name` itself.
    Switching each category stores the pointer that the global locale
    already holds, and the character type's update rewrites its table
    pointers with their current values. Setlocale then adds one to the
    catalog counter, releases the lock and returns the name "C". The
    proof follows the code in that order, one category at a time, and
    its last lemma joins the parts into the whole call. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine StepRules Symbolic
  ExternalCalls ExternalMachine Pieces Heap Language Logic MemLogic StringLogic VariadicLogic.
From Glibc Require Import HelloImageModule HelloImageLoad HelloImageEarly OsWorld OsRegistry FileInv LibioLogic WordString
  GetoptBytes GetenvEntry RdlockLogic RwlockIdle StrcmpLogic StrchrnulLogic StrlenWord GetenvCode GetenvScan GetenvStatic GetenvCall
  StartGetenv LocaleEnv FindlocaleEnv FindlocaleCode FindlocaleC SetlocaleCode PostloadCtypeCode
  StartCtypeInitSpec StartEarlyInitSpec StartImageEarly HelloImageLocaleObjs HelloImageCLocaleObjs GetoptShortOpt WrlockCode RwunlockCode
  HelloSetlocalePostload HelloLocaleState HelloStartHdBuild WrlockCode RwunlockCode StrchrCode StrlenLogic StrncmpCode AllocLogic LibioCloseSteps StartPtmallocInit SysWrappers LibioCleanupExit Fix.
Module FL := VariadicLogicOn R LG0.
Import ListNotations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic FL.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** Each category other than LC_ALL has its C data object, the offset of
    its name in the table of names, and that name. *)
Definition sl_table : list (Z * string * Z * string) :=
  [(0, "_nl_C_LC_CTYPE", 11, "LC_CTYPE"); (1, "_nl_C_LC_NUMERIC", 32, "LC_NUMERIC"); (2, "_nl_C_LC_TIME", 43, "LC_TIME");
   (3, "_nl_C_LC_COLLATE", 0, "LC_COLLATE"); (4, "_nl_C_LC_MONETARY", 20, "LC_MONETARY");
   (5, "_nl_C_LC_MESSAGES", 51, "LC_MESSAGES"); (7, "_nl_C_LC_PAPER", 63, "LC_PAPER"); (8, "_nl_C_LC_NAME", 72, "LC_NAME");
   (9, "_nl_C_LC_ADDRESS", 80, "LC_ADDRESS"); (10, "_nl_C_LC_TELEPHONE", 91, "LC_TELEPHONE");
   (11, "_nl_C_LC_MEASUREMENT", 104, "LC_MEASUREMENT"); (12, "_nl_C_LC_IDENTIFICATION", 119, "LC_IDENTIFICATION")]%string.

(** This list holds the same rows with the image's addresses and regions filled in. *)
Definition sl_rows : list (Z * Z * region * Z * list Z) := Eval vm_compute in
  map (fun '(c, n, i, k) => (c, img_addr n, snd (img_obj n), i, lit k)) sl_table.

Section all.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w : os_world) (fr : word -> mem -> option (res unit * mem)).
Local Abbreviation hge := (mkGenv hello_image_module img_globals fr).
#[local] Instance all_program : GlibcProgram Σ := program_of w glibc_os_registry hge.
Local Abbreviation sexpr := (language.expr (nanofil_lang glibc_os_registry hge)).
Local Instance all_stable : SafepointStable (os_wi w) := os_wi_stable w.
Local Abbreviation gl := (img_a "_nl_global_locale").
Local Abbreviation glreg := (img_gd "_nl_global_locale").
Local Abbreviation cb := (img_a "_nl_C_name").
Local Abbreviation cv := (mkPtr cb (Ro cb)).
Local Abbreviation objp b := (mkPtr b (Obj b)).
Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation p80 := (rop (img_a "hello#str.80")).
Local Abbreviation lk := (img_a "__libc_setlocale_lock").
Local Abbreviation lkreg := (img_gd "__libc_setlocale_lock").

Local Instance d_wrlock : Defines hge "__GI___pthread_rwlock_wrlock" WrlockCode.glibc_pthread_rwlock_wrlock.
Proof. vm_compute. reflexivity. Qed.

Local Instance d_unlock : Defines hge "__GI___pthread_rwlock_unlock" RwunlockCode.glibc_pthread_rwlock_unlock.
Proof. vm_compute. reflexivity. Qed.
Local Instance d_getenv : Defines hge "__GI_getenv" glibc_getenv.
Proof. vm_compute. reflexivity. Qed.
Local Instance d_strlen : Defines hge "__GI_strlen" glibc_strlen.
Proof. vm_compute. reflexivity. Qed.
Local Instance d_strncmp : Defines hge "__GI_strncmp" glibc_strncmp.
Proof. vm_compute. reflexivity. Qed.
Local Instance d_strchr : Defines hge "__GI_strchr" glibc_strchr.
Proof. vm_compute. reflexivity. Qed.
Local Instance d_strchrnul : Defines hge "__GI___strchrnul" glibc_strchrnul.
Proof. vm_compute. reflexivity. Qed.
Local Instance d_find : Defines hge "_nl_find_locale" glibc_nl_find_locale.
Proof. vm_compute. reflexivity. Qed.
Local Instance d_free : Defines hge "free" free_fn.
Proof. vm_compute. reflexivity. Qed.

Local Ltac sums := repeat match goal with |- context [(?A + ?Y) mod 2 ^ 64] =>
  tryif has_var Y then fail else let v := eval vm_compute in Y in tryif constr_eq Y v then fail else change Y with v end.
Local Ltac fill N := step; closed_ints; branch; step; step; closed_ints; branch; step; step; step; step; sums;
  check "L103"; store "L103" N; step; step; step; step; step.

Local Ltac normp name v := match goal with |- context [put (TAtom name) (WPtr (mkPtr ?X _)) _] => replace X with v by a2 end.

Local Lemma all_ext : sys_external hge.
Proof. repeat constructor; vm_compute; reflexivity. Qed.

Context (dq dqa dqe : dfrac) (bc : Z) (rc : region) (be : Z) (re : region) (counter : Z) (ep : ptr)
  (es : list getenv_entry) (Himage : getenv_image_ok hge bc rc be re) (Henv : c_locale_env (map entry_text es)) (Hfh : frees_heap fr).
Local Notation globals := (getenv_globals dq bc rc be re counter ep).
Local Notation storage := (getenv_storage dqa dqe ep es).

Local Abbreviation lb := (img_a "_nl_C_locobj").
Local Abbreviation pbt := (img_a "glibc_setlocale#_nl_category_postload").
Local Abbreviation plp := (mkPtr (img_a "_nl_postload_ctype") (Fn (TAtom "_nl_postload_ctype"))).
Local Abbreviation ib := (img_a "_nl_category_name_idxs").
Local Abbreviation nb := (img_a "_nl_category_names").

(** The search for one category reads the category's slot in the C
    locale object, the life and use count of its data, the offset of
    its name and the name itself. *)
Definition sl_cat_ro (x : Z * Z * region * Z * list Z) : iProp Σ :=
  let '(c, b, reg, i, key) := x in
  pcellq DfracDiscarded lb (8 * c) (rop b) ∗ liveq DfracDiscarded b reg ∗
  bytesq DfracDiscarded b 40 [255; 255; 255; 255] ∗ bytesq DfracDiscarded ib c [i] ∗
  word_string DfracDiscarded (mkPtr (nb + i) (Ro nb)) key ∗
  pcellq DfracDiscarded pbt (8 * c) (if c =? 0 then plp else null).

Local Instance sl_cat_ro_persistent x : Persistent (sl_cat_ro x).
Proof. destruct x as [[[[? ?] ?] ?] ?]. rewrite /sl_cat_ro /pcellq /liveq /bytesq. apply _. Qed.

(** These are the constants that setlocale reads in every category. *)
Definition sl_ro : iProp Σ :=
  word_string DfracDiscarded p80 [] ∗ word_string DfracDiscarded cv [67] ∗
  word_string DfracDiscarded (rop (img_a "_nl_POSIX_name")) (lit "POSIX") ∗
  word_string DfracDiscarded (rop (img_a "glibc_findlocale#str.243")) (lit "LC_ALL") ∗
  word_string DfracDiscarded (rop (img_a "glibc_findlocale#str.244")) (lit "LANG") ∗
  word_string DfracDiscarded (rop (img_a "glibc_setlocale#str.234")) (lit "LOCPATH") ∗
  liveq DfracDiscarded lb (img_gd "_nl_C_locobj") ∗ liveq DfracDiscarded ib (img_gd "_nl_category_name_idxs") ∗
  liveq DfracDiscarded (img_a "_nl_category_name_sizes") (img_gd "_nl_category_name_sizes") ∗
  bytesq DfracDiscarded (img_a "_nl_category_name_sizes") 0 hello_name_sizes ∗
  liveq DfracDiscarded pbt (img_gd "glibc_setlocale#_nl_category_postload") ∗
  [∗ list] x ∈ sl_rows, sl_cat_ro x.

Local Instance sl_ro_persistent : Persistent sl_ro.
Proof. rewrite /sl_ro /liveq /bytesq. apply _. Qed.

Local Ltac al := iApply wp_alloc; [reflexivity | vm_compute; congruence | vm_compute; congruence |
  intros ? ? ? ? Hf Hw; exact (os_wi_alloc w _ _ _ _ _ Hf Hw) |]; iNext.

(** One byte of a shared byte string is a shared byte of its own. *)
Lemma bytesq_nth b o xs k x : xs !! k = Some x -> bytesq DfracDiscarded b o xs ⊢ bytesq DfracDiscarded b (o + Z.of_nat k) [x].
Proof.
  intros Hk. rewrite /bytesq /ptsq. iIntros "H".
  iDestruct (big_sepL_lookup with "H") as "H'"; [exact (byte_ps_lookup _ _ _ _ _ Hk)|].
  rewrite byte_ps_cons /byte_ps /=. iFrame.
Qed.

(** A fresh object of n words holds a null pointer in each word. *)
Lemma zero_cells b o (n : nat) :
  pts (byte_ps b o (replicate (8 * n) 0)) -∗ pts (aux_ps b o (replicate (8 * n) CNone)) -∗
  [∗ list] i ∈ seq 0 n, pcell b (o + 8 * Z.of_nat i) null.
Proof.
  revert o. induction n as [|n IH]; intros o; [iIntros "_ _"; done|].
  replace (8 * S n)%nat with (8 + 8 * n)%nat by lia. iIntros "B A".
  iDestruct (zero_cell_prefix with "B A") as "(C & B & A)". rewrite -cons_seq -seq_shift big_sepL_cons big_sepL_fmap.
  rewrite Z.add_0_r. iFrame "C". iDestruct (IH with "B A") as "H". iApply (big_sepL_impl with "H").
  iIntros "!>" (k i _) "H". replace (o + 8 * Z.of_nat (S i)) with (o + 8 + 8 * Z.of_nat i) by lia. iExact "H".
Qed.

(** A fresh object of n words is a live object with a null pointer in each word. *)
Lemma obj_cells b sz (n : nat) : req_extent (heap_req 8 sz) = 8 * Z.of_nat n ->
  obj b (heap_req 8 sz) ⊢ live b (mkRegion b (b + 8 * Z.of_nat n) Heap Live) ∗
    [∗ list] i ∈ seq 0 n, pcell b (8 * Z.of_nat i) null.
Proof.
  intros E. rewrite obj_zero_block; [|lia]. rewrite E. cbn [req_kind].
  replace (Z.to_nat (8 * Z.of_nat n)) with (8 * n)%nat by lia.
  iIntros "(L & B & A)". iFrame "L". iDestruct (zero_cells b 0 n with "B A") as "H". done.
Qed.

(** ## The search in each category *)

Definition sl_L262 : block := Eval vm_compute in
  match find_block (TAtom "L262") (fn_blocks glibc_setlocale) with
  | Some b => b | None => mkBlock (TAtom "L262") [] [] JRetVoid end.

(** These temporaries hold setlocale's arguments and its locals for the
    rest of the call. *)
Definition sl_regs (e : env) (b4 b5 b103 b104 : Z) : Prop :=
  lookup (TAtom "v0") e = Some (WInt 6) /\ lookup (TAtom "v2") e = Some (WPtr p80) /\
  lookup (TAtom "v4") e = Some (WPtr (objp b4)) /\ lookup (TAtom "chk4") e = Some (WPtr (objp b4)) /\
  lookup (TAtom "v5") e = Some (WPtr (objp b5)) /\ lookup (TAtom "chk5") e = Some (WPtr (objp b5)) /\
  lookup (TAtom "v103") e = Some (WPtr (objp b103)) /\ lookup (TAtom "v104") e = Some (WPtr (objp b104)) /\
  lookup (TAtom "v30") e = Some (WInt 0) /\ lookup (TAtom "pr.5") e = Some (WPtr null).

Definition sl_names : list name :=
  map TAtom ["v0"; "v2"; "v4"; "chk4"; "v5"; "chk5"; "v103"; "v104"; "v30"; "pr.5"].

Lemma sl_regs_keeps e e' b4 b5 b103 b104 :
  keeps sl_names e e' -> sl_regs e b4 b5 b103 b104 -> sl_regs e' b4 b5 b103 b104.
Proof. unfold keeps. rewrite Forall_forall. intros Hk H. unfold sl_regs in *. rewrite !Hk; [exact H | cbn; tauto ..]. Qed.

(** The four locals are fresh heap objects of two, two, fourteen and
    fourteen words. *)
Definition sl_fresh (b4 b5 b103 b104 : Z) : Prop :=
  (0 < b4 /\ b4 mod 16 = 0 /\ b4+16 <= 2^48) /\ (0 < b5 /\ b5 mod 16 = 0 /\ b5+16 <= 2^48) /\
  (0 < b103 /\ b103 mod 16 = 0 /\ b103+112 <= 2^48) /\ (0 < b104 /\ b104 mod 16 = 0 /\ b104+112 <= 2^48).

Local Abbreviation hreg b n := (mkRegion b (b + 8 * Z.of_nat n) Heap Live).

Definition sl_tmp (b4 b5 b103 b104 : Z) : iProp Σ :=
  live b4 (hreg b4 2) ∗ pcell b4 0 null ∗ live b5 (hreg b5 2) ∗ icell b5 0 0 ∗
  live b103 (hreg b103 14) ∗ live b104 (hreg b104 14).

Local Abbreviation at262 e := (ERun (mkFrame glibc_setlocale e [] None
  (Exec (TAtom "L262") (b_insts sl_L262) (b_jump sl_L262))) : sexpr).

Local Ltac vmr := vm_compute; reflexivity.
Local Ltac cl := first [cbn; lia | cbn; Z.div_mod_to_equations; lia].
Local Ltac vl := first [vmr | cbn; lia].
Local Ltac sl_cases H := repeat destruct H as [<-|H]; try contradiction.

Local Lemma sl_index_words c : 0 <= c < 13 ->
  sign_extension (2^32) (2^31) (c mod 2^32) mod 2^64 = c /\
  (c mod 2^64 * 8) mod 2^64 = 8*c.
Proof.
  intros Hc. unfold sign_extension.
  assert (E32 : c mod 2^32 = c) by (apply Z.mod_small; lia).
  assert (Elt : (2^31 <=? c) = false) by (apply Z.leb_gt; lia).
  rewrite !E32 Elt. split; unwrap2; lia.
Qed.

Local Ltac sl_index_offset c :=
  let E := fresh in let S := fresh in
  destruct (sl_index_words c ltac:(lia)) as [E S]; step; rewrite E; step; rewrite S; step.

Local Ltac sl_next_index := cbn -[Z.modulo Z.pow Z.add]; f_equal; f_equal; unwrap2; lia.

(** This tactic runs the lookup call for one category. *)
Local Ltac find_call c i key :=
  iApply (wp_findlocale_c (glibc_program := all_program) dq dqa dqe bc rc be re counter ep es Himage Henv _ _ cb ib nb
    i c (img_gd "_nl_category_name_idxs") DfracDiscarded DfracDiscarded key
    with "H80 HC HP Hall Hk Hlang L103 N [$HG $HS $Hib $Hi] Hlb Hs Hd");
  [ vmr | vmr | vmr | vmr | vmr | assumption | cl | cl | cl | assumption | assumption
  | rewrite (Z.mod_small c (2^32)); [reflexivity|lia] | vmr | vmr | vmr
  | cl | cl | cl | cl | cl | vl | vl | cl | vl | cl | ].

(** This lemma runs one round of the search for a category other than LC_ALL. It looks
    up the category's C data, keeps it in the second array and puts the
    name "C" in the first. *)
Lemma sl_find_one x e b4 b5 b103 b104 Φ :
  In x sl_rows -> sl_fresh b4 b5 b103 b104 -> sl_regs e b4 b5 b103 b104 ->
  lookup (TAtom "pr.2") e = Some (WInt (x.1.1.1.1 + 1)) ->
  sl_ro -∗ globals -∗ storage -∗ sl_tmp b4 b5 b103 b104 -∗
  pcell b103 (8 * x.1.1.1.1) p80 -∗ pcell b104 (8 * x.1.1.1.1) null -∗
  (∀ e', ⌜sl_regs e' b4 b5 b103 b104 /\ lookup (TAtom "pr.2") e' = Some (WInt x.1.1.1.1)⌝ -∗
     globals -∗ storage -∗ sl_tmp b4 b5 b103 b104 -∗
     pcell b103 (8 * x.1.1.1.1) cv -∗ pcell b104 (8 * x.1.1.1.1) (rop x.1.1.1.2) -∗ WP at262 e' {{ Φ }}) -∗
  WP at262 e {{ Φ }}.
Proof.
  intros Hin Hfr Hr Hpr. iIntros "#Hro HG HS (L4 & P4 & L5 & P5 & L103 & L104) N D HK".
  pose proof Himage as (Hcnt & Henvg & Hbc & Hbce & Hrc & Hbe & Hbee & Hre & Hbe8).
  destruct Hfr as (H4 & H5 & H103 & H104). pose proof Hr as (R0 & R2 & R4 & R4c & R5 & R5c & R103 & R104 & R30 & R5p).
  iDestruct "Hro" as "(#H80 & #HC & #HP & #Hall & #Hlang & #Hlp & #Hlb & #Hib & #Hsl & #Hsz & #Hpb & #T)".
  iDestruct (ws_byte cv [67] 0 with "HC") as (cbb creg ([Hcc|Hcc] & _)) "[#Hcl _]"; [cbn; lia|discriminate Hcc|].
  injection Hcc as <-.
  iDestruct (big_sepL_elem_of with "T") as "Tc"; [apply list_elem_of_In; exact Hin|].
  assert (Hrow : 0 <= x.1.1.1.1 < 13 /\ x.1.1.1.1 <> 6 /\ 0 < x.1.1.1.2 /\
    x.1.1.1.2 + 44 <= r_end x.1.1.2 /\ r_end x.1.1.2 <= 2^48 /\ 0 <= x.1.2 < 256 /\ In x.2 locale_vars)
    by (sl_cases Hin; cbn [fst snd r_end]; repeat split; first [lia | vm_compute; tauto]).
  destruct Hrow as (Hbounds & Hne & Hb & Hbe44 & Hbend & Hidx & Hkey).
  destruct x as [[[[c b] reg] i] key]; cbn [fst snd] in *. iDestruct "Tc" as "(Hs & Hd & Hu & Hi & Hk & _)".
  cbn [sl_L262 b_insts b_jump]; step.
  match goal with |- context [put (TAtom "v266") (WInt ?t) _] => replace t with c by (unwrap2; lia) end.
  step; branch_as false; step; step; branch_as false; step. sl_index_offset c. check "L4".
  iApply (wp_raw_load_null (glibc_program := all_program) with "L4 P4"); [reflexivity | vx | reflexivity | a2 | a2 |].
  iNext; iIntros "L4 P4"; check "L5".
  iApply (wp_raw_load with "L5 P5"); [reflexivity | vx | reflexivity | a2 |].
  iNext; iIntros "L5 P5"; step; sums; closed_ints. normp "v283" (b103 + 8*c).
  iApply wp_call_bind; [vx | apply defines | reflexivity |]; iNext; find_call c i key.
  iNext; iIntros "L103 N (HG & HS & _ & _) _ _ _"; iExists _; iSplit; [iPureIntro; reflexivity|].
  iNext; cbn [fr_fn fr_env fr_locals fr_at]; check "L104"; store "L104" "D"; check "L104".
  load_pointer_dq "L104 D Hd" by a2; iNext; iIntros "L104 D _"; step; step; branch_as true; step.
  (* The use count already marks the data as never freed. *)
  load_pointer_dq "L104 D Hd" by a2; iNext; iIntros "L104 D _"; step; sums.
  check_read_dq "Hd" by a2; iNext; iIntros "_".
  load_bytes_dq "Hd Hu" decode (vm_compute; reflexivity) by a2; iNext; iIntros "_ _"; step; closed_ints; branch; step.
  (* The search left the name "C" in the slot, which needs no copy. *)
  check "L103"; load_pointer_dq "L103 N Hcl" by a2; iNext; iIntros "L103 N _".
  step; step; step; step; closed_ints; branch; step; cbn [edge_label].
  iApply ("HK" with "[%] HG HS [$L4 $P4 $L5 $P5 $L103 $L104] N D").
  split; [eapply sl_regs_keeps; [keeps_tac | exact Hr] | sl_next_index].
Qed.

(** The search skips LC_ALL, which has no data of its own. *)
Lemma sl_find_skip e Φ :
  lookup (TAtom "pr.2") e = Some (WInt 7) ->
  (∀ e', ⌜keeps sl_names e e' /\ lookup (TAtom "pr.2") e' = Some (WInt 6)⌝ -∗ WP at262 e' {{ Φ }}) -∗
  WP at262 e {{ Φ }}.
Proof.
  intros Hpr. iIntros "HK".
  cbn [sl_L262 b_insts b_jump]; step; closed_ints; step; closed_ints; branch; step; step; closed_ints; branch.
  step; cbn [edge_label]. iApply "HK". iPureIntro. split; [keeps_tac | apply Symbolic.lookup_after_put_same].
Qed.

(** ## The composite name *)

Definition sl_C10 : block := Eval vm_compute in
  match find_block (TAtom "iw_2.L10") (fn_blocks glibc_setlocale) with
  | Some b => b | None => mkBlock (TAtom "iw_2.L10") [] [] JRetVoid end.

Local Abbreviation atC10 e := (ERun (mkFrame glibc_setlocale e [] None
  (Exec (TAtom "iw_2.L10") (b_insts sl_C10) (b_jump sl_C10))) : sexpr).

Local Abbreviation szb := (img_a "_nl_category_name_sizes").

(** Setlocale builds one name for all the categories. These temporaries
    carry that name's state from one category to the next, and a flag
    stays set while every name equals the first. *)
Definition sl_comp_regs (e : env) (c : Z) : Prop :=
  lookup (TAtom "iw_2.pr.5") e = Some (WInt c) /\ lookup (TAtom "iw_2.pr.9") e = Some (WInt 1) /\
  (exists t, lookup (TAtom "iw_2.pr.3") e = Some (WInt t)) /\ (exists t, lookup (TAtom "iw_2.pr.1") e = Some (WInt t)).

(** This lemma runs one round of the composite name for a category after
    the first. Its name is the same "C" as the first category's, so the
    flag stays set. *)
Lemma sl_comp_one x e b4 b5 b103 b104 Φ :
  In x (tail sl_rows) -> sl_fresh b4 b5 b103 b104 -> sl_regs e b4 b5 b103 b104 -> sl_comp_regs e x.1.1.1.1 ->
  sl_ro -∗ live b103 (hreg b103 14) -∗ pcell b103 0 cv -∗ pcell b103 (8 * x.1.1.1.1) cv -∗
  (∀ e', ⌜keeps sl_names e e' /\ sl_comp_regs e' (x.1.1.1.1 + 1)⌝ -∗
     live b103 (hreg b103 14) -∗ pcell b103 0 cv -∗ pcell b103 (8 * x.1.1.1.1) cv -∗ WP atC10 e' {{ Φ }}) -∗
  WP atC10 e {{ Φ }}.
Proof.
  intros Hin Hfr Hr (Hp5 & Hp9 & [t3 Hp3] & [t1 Hp1]). iIntros "#Hro L103 N0 N HK".
  destruct Hfr as (H4 & H5 & H103 & H104). pose proof Hr as (R0 & R2 & R4 & R4c & R5 & R5c & R103 & R104 & R30 & R5p).
  iDestruct "Hro" as "(_ & #HC & _ & _ & _ & _ & _ & _ & #Hsl & #Hsz & _)".
  iDestruct (ws_byte cv [67] 0 with "HC") as (cbb creg ([Hcc|Hcc] & _)) "[#Hcl _]"; [cbn; lia|discriminate Hcc|].
  injection Hcc as <-.
  set (c := x.1.1.1.1) in *.
  assert (Hc : 1 <= c < 13 /\ c <> 6) by (subst c; sl_cases Hin; cbn [fst snd]; lia).
  destruct Hc as [Hbounds Hne].
  cbn [sl_C10 b_insts b_jump]; step; branch_as false; step; step; branch_as false; step.
  sl_index_offset c.
  check "L103"; load_pointer_dq "L103 N Hcl" by a2; iNext; iIntros "L103 N _".
  iApply (wp_call_glibc_strlen with "HC"); [vx | vmr | reflexivity |].
  iNext; iIntros "_"; cbn [fr_fn fr_env fr_locals fr_at]; step; step; sums; check_read_dq "Hsl" by a2; iNext; iIntros "_".
  assert (Hsize : is_Some (hello_name_sizes !! Z.to_nat c)) by (apply lookup_lt_is_Some_2; cbn; lia).
  destruct Hsize as [sz Hsize]. iDestruct (bytesq_nth _ _ _ _ _ Hsize with "Hsz") as "Hs1".
  iEval (rewrite Z2Nat.id; [|lia]) in "Hs1". load_bytes_dq "Hsl Hs1" decode reflexivity by a2.
  iNext; iIntros "_ _"; step; step; step; step; step; branch.
  (* The name is the first category's name itself. *)
  step; check "L103"; load_pointer_dq "L103 N0 Hcl" by a2.
  iNext; iIntros "L103 N0 _"; step; step; step; closed_ints; step; step; branch; step; branch.
  step; step; step; step; step; step; cbn [edge_label].
  iApply ("HK" with "[%] L103 N0 N"); split; [keeps_tac|].
  split; [|split; [|split]]; [ | | eexists | eexists ]; try reflexivity.
  sl_next_index.
Qed.

(** The first round of the composite name compares the first name with
    itself. *)
Lemma sl_comp_first e b4 b5 b103 b104 Φ :
  sl_fresh b4 b5 b103 b104 -> sl_regs e b4 b5 b103 b104 -> sl_comp_regs e 0 ->
  sl_ro -∗ live b103 (hreg b103 14) -∗ pcell b103 0 cv -∗
  (∀ e', ⌜keeps sl_names e e' /\ sl_comp_regs e' 1⌝ -∗ live b103 (hreg b103 14) -∗ pcell b103 0 cv -∗ WP atC10 e' {{ Φ }}) -∗
  WP atC10 e {{ Φ }}.
Proof.
  intros Hfr Hr (Hp5 & Hp9 & [t3 Hp3] & [t1 Hp1]). iIntros "#Hro L103 N0 HK".
  destruct Hfr as (H4 & H5 & H103 & H104). pose proof Hr as (R0 & R2 & R4 & R4c & R5 & R5c & R103 & R104 & R30 & R5p).
  iDestruct "Hro" as "(#H80 & #HC & #HP & #Hall & #Hlang & #Hlp & #Hlb & #Hib & #Hsl & #Hsz & #Hpb & #T)".
  iDestruct (ws_byte cv [67] 0 with "HC") as (cbb creg ([Hcc|Hcc] & _)) "[#Hcl _]"; [cbn; lia|discriminate Hcc|].
  injection Hcc as <-.
  all: cbn [sl_C10 b_insts b_jump]; step; closed_ints; branch; step; step; closed_ints; branch; step.
  all: step; step; step; sums; check "L103"; load_pointer_dq "L103 N0 Hcl" by a2; iNext; iIntros "L103 N0 _".
  all: iApply (wp_call_glibc_strlen with "HC"); [vx | vm_compute; reflexivity | reflexivity |].
  all: iNext; iIntros "_"; cbn [fr_fn fr_env fr_locals fr_at]; step; step; sums; check_read_dq "Hsl" by a2; iNext; iIntros "_".
  all: match type of Hp5 with _ = Some (WInt ?c) =>
    iDestruct (bytesq_nth _ _ _ (Z.to_nat c) with "Hsz") as "Hs1"; [reflexivity|] end.
  all: load_bytes_dq "Hsl Hs1" decode (vm_compute; reflexivity) by a2.
  all: iNext; iIntros "_ _"; step; step; step; step; step; branch.
  (* The name is the first category's name itself. *)
  all: step; check "L103"; load_pointer_dq "L103 N0 Hcl" by a2.
  all: iNext; iIntros "L103 N0 _"; step; step; step; closed_ints; step; step; branch; step; branch.
  all: step; step; step; step; step; step; cbn [edge_label].
  all: iApply ("HK" with "[%] L103 N0"); split; [keeps_tac|].
  all: split; [|split; [|split]]; [ | | eexists | eexists ]; cbn; reflexivity.
Qed.

(** The composite name skips LC_ALL. *)
Lemma sl_comp_skip e Φ :
  sl_comp_regs e 6 ->
  (∀ e', ⌜keeps sl_names e e' /\ sl_comp_regs e' 7⌝ -∗ WP atC10 e' {{ Φ }}) -∗ WP atC10 e {{ Φ }}.
Proof.
  intros (Hp5 & Hp9 & [t3 Hp3] & [t1 Hp1]). iIntros "HK".
  cbn [sl_C10 b_insts b_jump]; step; closed_ints; branch; step; step; closed_ints; branch.
  step; step; step; step; cbn [edge_label]. iApply "HK". iPureIntro. split; [keeps_tac|].
  split; [|split; [|split]]; [ | | eexists | eexists ]; cbn; first [reflexivity | eassumption].
Qed.


(** ## Switching the categories *)

Definition sl_L394 : block := Eval vm_compute in
  match find_block (TAtom "L394") (fn_blocks glibc_setlocale) with
  | Some b => b | None => mkBlock (TAtom "L394") [] [] JRetVoid end.

Local Abbreviation at394 e := (ERun (mkFrame glibc_setlocale e [] None
  (Exec (TAtom "L394") (b_insts sl_L394) (b_jump sl_L394))) : sexpr).

(** The composite name is "C". *)
Definition sl_set_regs (e : env) (c : Z) : Prop :=
  lookup (TAtom "pr.3") e = Some (WInt c) /\ lookup (TAtom "v386") e = Some (WPtr cv) /\
  lookup (TAtom "v391") e = Some (WInt cb).

(** A category other than the character type has nothing to update
    after its switch. Storing its data pointer stores the value that is
    already there, and its name is already "C". *)
Lemma sl_set_one x e b4 b5 b103 b104 dn Φ :
  In x (tail sl_rows) -> sl_fresh b4 b5 b103 b104 -> sl_regs e b4 b5 b103 b104 -> sl_set_regs e x.1.1.1.1 ->
  sl_ro -∗ live gl glreg -∗ live b103 (hreg b103 14) -∗ live b104 (hreg b104 14) -∗
  pcell b103 (8 * x.1.1.1.1) cv -∗ pcell b104 (8 * x.1.1.1.1) (rop x.1.1.1.2) -∗
  pcell gl (8 * x.1.1.1.1) (rop x.1.1.1.2) -∗ pcellq dn gl (128 + 8 * x.1.1.1.1) cv -∗
  (∀ e', ⌜keeps sl_names e e' /\ sl_set_regs e' (x.1.1.1.1 + 1)⌝ -∗
     live gl glreg -∗ live b103 (hreg b103 14) -∗ live b104 (hreg b104 14) -∗
     pcell b103 (8 * x.1.1.1.1) cv -∗ pcell b104 (8 * x.1.1.1.1) (rop x.1.1.1.2) -∗
     pcell gl (8 * x.1.1.1.1) (rop x.1.1.1.2) -∗ pcellq dn gl (128 + 8 * x.1.1.1.1) cv -∗ WP at394 e' {{ Φ }}) -∗
  WP at394 e {{ Φ }}.
Proof.
  intros Hin Hfr Hr (Hp3 & Hv386 & Hv391). iIntros "#Hro Hgl L103 L104 N D G Gn HK".
  destruct Hfr as (H4 & H5 & H103 & H104). pose proof Hr as (R0 & R2 & R4 & R4c & R5 & R5c & R103 & R104 & R30 & R5p).
  iDestruct "Hro" as "(_ & #HC & _ & _ & _ & _ & _ & _ & _ & _ & #Hpb & #T)".
  iDestruct (ws_byte cv [67] 0 with "HC") as (cbb creg ([Hcc|Hcc] & _)) "[#Hcl _]"; [cbn; lia|discriminate Hcc|].
  injection Hcc as <-.
  iDestruct (big_sepL_elem_of with "T") as "Tc"; [apply list_elem_of_In; right; exact Hin|].
  assert (Hrow : (1 <= x.1.1.1.1 < 13 /\ x.1.1.1.1 <> 6) /\ 0 <= x.1.1.1.2 < 2^64)
    by (sl_cases Hin; cbn [fst snd]; lia).
  destruct Hrow as [[Hbounds Hne] Hb]. destruct x as [[[[c b] reg] i] key]; cbn [fst snd] in *.
  iDestruct "Tc" as "(_ & Hd & _ & _ & _ & Hq)".
  cbn [sl_L394 b_insts b_jump]; step; branch_as false; step; step; branch_as false; step.
  sl_index_offset c. check "L104"; load_pointer_dq "L104 D Hd" by a2.
  iNext; iIntros "L104 D _"; step; step; sums; check "Hgl"; store "Hgl" "G".
  (* Only the character type has an update to run. *)
  assert (Hnz : (c =? 0) = false) by (apply Z.eqb_neq; lia). iEval (rewrite Hnz) in "Hq".
  step; step; sums; check_read_dq "Hpb" by a2; iNext; iIntros "_".
  iAssert (live_capq DfracDiscarded (ptr_cap null) glreg) as "Hn"; [done|]; iApply (wp_raw_load_pointer_dq with "Hpb Hq Hn"); [reflexivity | vx | right; reflexivity | a2 | a2 | cbn; lia |].
  iNext; iIntros "_ _ _"; step; step; closed_ints; branch; step.
  (* The name is already "C", so setname stores nothing. *)
  step; sums; check "L103"; load_pointer_dq "L103 N Hcl" by a2.
  iNext; iIntros "L103 N _"; step; step; step; sums; check "Hgl"; load_pointer_dq "Hgl Gn Hcl" by a2.
  iNext; iIntros "Hgl Gn _"; step; step; step; closed_ints; branch; step; step; step; cbn [edge_label]; step.
  iApply ("HK" with "[%] Hgl L103 L104 N D G Gn"); split; [keeps_tac|].
  split; [sl_next_index|split; lk_prove].
Qed.

Local Abbreviation lt := (img_a "__libc_tsd_LOCALE").
Local Abbreviation ltreg := (img_gd "__libc_tsd_LOCALE").
Local Abbreviation ccp := (rop (img_a "_nl_C_LC_CTYPE")).

(** Switching the character type runs its update, which rewrites the
    table pointers with the values they already hold. *)
Lemma sl_set_zero e b4 b5 b103 b104 dqt dn Φ :
  sl_fresh b4 b5 b103 b104 -> sl_regs e b4 b5 b103 b104 -> sl_set_regs e 0 ->
  sl_ro -∗ pl_ro -∗ live gl glreg -∗ live b103 (hreg b103 14) -∗ live b104 (hreg b104 14) -∗
  pcell b103 0 cv -∗ pcell b104 0 ccp -∗ pcell gl 0 ccp -∗ pcellq dn gl 128 cv -∗
  liveq dqt lt ltreg -∗ pcellq dqt lt 0 (objp gl) -∗ pl_cells -∗
  (∀ e', ⌜keeps sl_names e e' /\ sl_set_regs e' 1⌝ -∗
     live gl glreg -∗ live b103 (hreg b103 14) -∗ live b104 (hreg b104 14) -∗
     pcell b103 0 cv -∗ pcell b104 0 ccp -∗ pcell gl 0 ccp -∗ pcellq dn gl 128 cv -∗
     liveq dqt lt ltreg -∗ pcellq dqt lt 0 (objp gl) -∗ pl_cells -∗ WP at394 e' {{ Φ }}) -∗
  WP at394 e {{ Φ }}.
Proof.
  intros Hfr Hr (Hp3 & Hv386 & Hv391). iIntros "#Hro #Hpl Hgl L103 L104 N D G Gn Hlt Hlc Hpc HK".
  destruct Hfr as (H4 & H5 & H103 & H104). pose proof Hr as (R0 & R2 & R4 & R4c & R5 & R5c & R103 & R104 & R30 & R5p).
  iDestruct "Hro" as "(#H80 & #HC & #HP & #Hall & #Hlang & #Hlp & #Hlb & #Hib & #Hsl & #Hsz & #Hpb & #T)".
  iDestruct (ws_byte cv [67] 0 with "HC") as (cbb creg ([Hcc|Hcc] & _)) "[#Hcl _]"; [cbn; lia|discriminate Hcc|].
  injection Hcc as <-.
  iDestruct (big_sepL_lookup _ _ 0 with "T") as "Tc"; [reflexivity|]. iDestruct "Tc" as "(Hs & Hd & Hu & Hi & Hk & Hq)".
  cbn [sl_L394 b_insts b_jump]; step; closed_ints; branch; step; step; closed_ints; branch; step.
  step; step; step; sums; check "L104"; load_pointer_dq "L104 D Hd" by a2.
  iNext; iIntros "L104 D _"; step; step; sums; check "Hgl"; store "Hgl" "G".
  step; step; sums; check_read_dq "Hpb" by a2; iNext; iIntros "_".
  iAssert (live_capq DfracDiscarded (ptr_cap plp) glreg) as "Hn"; [done|].
  iApply (wp_raw_load_pointer_dq with "Hpb Hq Hn"); [reflexivity | vx | right; reflexivity | a2 | a2 | vm_compute; split; congruence |].
  iNext; iIntros "_ _ _"; step; step; closed_ints; branch; step.
  step; step; sums; check_read_dq "Hpb" by a2; iNext; iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hpb Hq Hn"); [reflexivity | vx | right; reflexivity | a2 | a2 | vm_compute; split; congruence |].
  iNext; iIntros "_ _ _". iApply wp_check_function; [vx | vm_compute; reflexivity |]. iNext.
  iApply wp_raw_call_bind; [vx | reflexivity | vm_compute; reflexivity | vx | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity |]. iNext.
  iApply (wp_postload_ctype_c w fr with "Hlt Hlc Hgl G Hpl Hpc"); [reflexivity|].
  iNext. iIntros "Hlt Hlc Hgl G Hpc". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  cbn [fr_fn fr_env fr_locals fr_at fr_doomed]. step. step.
  (* The name is already "C", so setname stores nothing. *)
  step; sums; check "L103"; load_pointer_dq "L103 N Hcl" by a2.
  iNext; iIntros "L103 N _"; step; step; step; sums; check "Hgl"; load_pointer_dq "Hgl Gn Hcl" by a2.
  iNext; iIntros "Hgl Gn _"; step; step; step; closed_ints; branch; step; step; step; cbn [edge_label]; step.
  iApply ("HK" with "[%] Hgl L103 L104 N D G Gn Hlt Hlc Hpc"); split; [keeps_tac|].
  split; [vm_compute; reflexivity|]; split; lk_prove.
Qed.

(** The switch skips LC_ALL. *)
Lemma sl_set_skip e Φ :
  sl_set_regs e 6 ->
  (∀ e', ⌜keeps sl_names e e' /\ sl_set_regs e' 7⌝ -∗ WP at394 e' {{ Φ }}) -∗ WP at394 e {{ Φ }}.
Proof.
  intros (Hp3 & Hv386 & Hv391). iIntros "HK".
  cbn [sl_L394 b_insts b_jump]; step; closed_ints; branch; step; step; closed_ints; branch.
  step; step; step; cbn [edge_label]; step. iApply "HK". iPureIntro. split; [keeps_tac|].
  split; [vm_compute; reflexivity|]; split; lk_prove.
Qed.

(** After the last category, setlocale stores nothing more: the name of
    LC_ALL is already "C". It adds one to the catalog counter, releases
    the lock, frees two null pointers and returns the name. *)
Lemma sl_tail e b4 b5 b103 b104 n tb treg dqt dqi tid sh Φ :
  sl_fresh b4 b5 b103 b104 -> sl_regs e b4 b5 b103 b104 -> sl_set_regs e 13 ->
  rw_place (objp lk) lk lkreg tb treg ->
  sl_ro -∗ live gl glreg -∗ pcell gl 176 cv -∗ sl_tmp b4 b5 b103 b104 -∗
  pts (StartImageCpu.obj_ps (img_ob "_nl_msg_cat_cntr") (le_bytes n 4)) -∗
  rw_writing lk lkreg tid sh 0 -∗ rw_self dqt tb treg dqi tid -∗
  (live gl glreg -∗ pcell gl 176 cv -∗ hello_cat_cntr -∗ rw_state lk lkreg 0 0 sh 0 -∗ rw_self dqt tb treg dqi tid -∗
     Φ (Ret (WPtr cv))) -∗
  WP at394 e {{ Φ }}.
Proof.
  intros Hfr Hr (Hp3 & Hv386 & Hv391) Hp. iIntros "#Hro Hgl H176 (L4 & P4 & L5 & P5 & L103 & L104) Hn Hlk Hself HK".
  destruct Hfr as (H4 & H5 & H103 & H104). pose proof Hr as (R0 & R2 & R4 & R4c & R5 & R5c & R103 & R104 & R30 & R5p).
  iDestruct "Hro" as "(#H80 & #HC & #HP & #Hall & #Hlang & #Hlp & #Hlb & #Hib & #Hsl & #Hsz & #Hpb & #T)".
  iDestruct (ws_byte cv [67] 0 with "HC") as (cbb creg ([Hcc|Hcc] & _)) "[#Hcl _]"; [cbn; lia|discriminate Hcc|].
  injection Hcc as <-.
  cbn [sl_L394 b_insts b_jump]; step; closed_ints; branch.
  step; step; step; step; sums; check "Hgl"; load_pointer_dq "Hgl H176 Hcl" by a2.
  iNext; iIntros "Hgl H176 _"; step; step; closed_ints; branch; step; step.
  (* The counter goes up by one. *)
  rewrite le_bytes_mod32 /StartImageCpu.obj_ps. iEval (rewrite (pts_app [_]) pts_app) in "Hn".
  iDestruct "Hn" as "(Cl & Cb & Ca)". assert (Hn32 : 0 <= n mod 2^32 < 2^32) by (apply Z.mod_pos_bound; lia).
  iAssert (live (img_a "_nl_msg_cat_cntr") (img_gd "_nl_msg_cat_cntr")) with "Cl" as "Cl".
  iAssert (bytes (img_a "_nl_msg_cat_cntr") 0 (le_bytes (n mod 2^32) 4)) with "Cb" as "Cb".
  check "Cl". load_s32 "Cl" "Cb". step. check "Cl". store_int "Cl" "Cb". step. step. cbn [edge_label]. step.
  (* Release the lock, free the two null pointers and return the name. *)
  assert (Hreg : holds_os glibc_os_registry) by (intros ? ? H; exact H).
  iApply (wp_call_rwunlock_writing (glibc_program := all_program) with "[$Hlk $Hself]");
    [exact Hreg | exact all_ext | vx | exact Hp |]. iNext. iIntros "[Hlk Hself]".
  check "L4". iApply (wp_raw_load_null (glibc_program := all_program) with "L4 P4"); [reflexivity | vx | reflexivity | a2 | a2 |].
  iNext. iIntros "L4 P4".
  do 2 (iApply wp_call_bind; [vx | apply defines | reflexivity |]; iNext;
    iApply (AllocLogic.wp_glibc_free_null glibc_os_registry (os_wi w) hge); [exact Hfh | vm_compute; reflexivity | vm_compute; reflexivity |];
    iExists _; iSplit; [iPureIntro; reflexivity|]; iNext; cbn [fr_fn fr_env fr_locals fr_at fr_doomed]).
  iApply wp_ret; [reflexivity | vx |]. iNext. iApply ("HK" with "Hgl H176 [Cl Cb Ca] Hlk Hself").
  iExists _. rewrite /StartImageCpu.obj_ps. iEval (rewrite (pts_app [_]) pts_app). iFrame "Cl Cb".
  rewrite !length_fmap length_seq. iExact "Ca".
Qed.

(** ## The whole call *)

(** Setlocale stores into the category slots and name slots of the
    global locale, and this assertion holds each slot at its C value.
    It holds the name slot of the messages as a frozen share, because
    getopt's warnings read that slot too. *)
Definition sl_gl_cells : iProp Σ :=
  [∗ list] x ∈ sl_rows, pcell gl (8 * x.1.1.1.1) (rop x.1.1.1.2) ∗
    pcellq (if x.1.1.1.1 =? 5 then DfracDiscarded else DfracOwn 1) gl (128 + 8 * x.1.1.1.1) cv.


Local Ltac pr2 := first [match goal with |- lookup _ ?E = _ => match goal with H : lookup (TAtom "pr.2") E = _ |- _ =>
  rewrite H; vm_compute; reflexivity end end | vm_compute; reflexivity].
Local Ltac kregs := match goal with H : keeps sl_names ?a ?b, H2 : sl_regs ?a _ _ _ _ |- _ =>
  pose proof (sl_regs_keeps _ _ _ _ _ _ H H2); clear H end.
Local Ltac fo k P N D := iApply (sl_find_one (nth k sl_rows (0,0,hreg 0 0,0,[])) with P);
  [vm_compute; tauto | eassumption | eassumption | pr2 | ]; iIntros (?) "[% %] HG HS Ht"; iIntros N; iIntros D.
Local Ltac co k P N := iApply (sl_comp_one (nth k (tail sl_rows) (0,0,hreg 0 0,0,[])) with P);
  [vm_compute; tauto | match goal with H : sl_fresh _ _ _ _ |- _ => exact H end | eassumption | eassumption | ];
  iIntros (?) "[% %] L103 N0"; iIntros N; kregs.
Local Ltac so k P Q := iApply (sl_set_one (nth k (tail sl_rows) (0,0,hreg 0 0,0,[])) with P);
  [vm_compute; tauto | match goal with H : sl_fresh _ _ _ _ |- _ => exact H end | eassumption | eassumption | ];
  iIntros (?) "[% %]"; iIntros Q; kregs.

Lemma sl_explore fr0 tb treg dqt dqi tid cw sh treg' dql Φ :
  call_frame glibc_setlocale [WInt 6; WPtr p80] = Some fr0 ->
  rw_place (objp lk) lk lkreg tb treg -> cw <> tid ->
  rw_state lk lkreg 0 cw sh 0 -∗ rw_self dqt tb treg dqi tid -∗
  live gl glreg -∗ pcell gl 176 cv -∗ live_capq DfracDiscarded (Ro cb) treg' -∗
  sl_ro -∗ pl_ro -∗ globals -∗ storage -∗ sl_gl_cells -∗
  liveq dql lt ltreg -∗ pcellq dql lt 0 (objp gl) -∗ pl_cells -∗ hello_cat_cntr -∗
  (globals -∗ storage -∗ live gl glreg -∗ pcell gl 176 cv -∗ sl_gl_cells -∗
     liveq dql lt ltreg -∗ pcellq dql lt 0 (objp gl) -∗ pl_cells -∗ hello_cat_cntr -∗
     rw_state lk lkreg 0 0 sh 0 -∗ rw_self dqt tb treg dqi tid -∗ Φ (Ret (WPtr cv))) -∗
  WP (ERun fr0 : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hp Hcw. injection Hfr as <-.
  iIntros "Hlk Hself Hgl H176 Hcl #Hro #Hpl HG HS Hgc Hlt Hlc Hpc [%n Hn] HK".
  iPoseProof "Hro" as "(#H80 & #HC & #HP & #Hall & #Hlang & #Hlp & #Hlb & #Hib & #Hsl & #Hsz & #Hpb & #T)".
  assert (Hreg : holds_os glibc_os_registry) by (intros ? ? H; exact H).
  step. al. iIntros (b4 H4) "O4". al. iIntros (b5 H5) "O5". al. iIntros (b103 H103) "O103".
  al. iIntros (b104 H104) "O104". al. iIntros (? _) "_".
  change (0 < b4 /\ b4 mod 16 = 0 /\ b4+16 <= 2^48) in H4. change (0 < b5 /\ b5 mod 16 = 0 /\ b5+16 <= 2^48) in H5.
  change (0 < b103 /\ b103 mod 16 = 0 /\ b103+112 <= 2^48) in H103.
  change (0 < b104 /\ b104 mod 16 = 0 /\ b104+112 <= 2^48) in H104.
  assert (Hfr : sl_fresh b4 b5 b103 b104) by exact (conj H4 (conj H5 (conj H103 H104))).
  iDestruct (obj_cells b4 _ 2 with "O4") as "(L4 & P4 & _)"; [reflexivity|].
  iDestruct (obj_cells b5 _ 2 with "O5") as "(L5 & P5 & _)"; [reflexivity|].
  iDestruct (obj_cells b103 _ 14 with "O103") as "(L103 & N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & _)"; [reflexivity|].
  iDestruct (obj_cells b104 _ 14 with "O104") as "(L104 & D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _)"; [reflexivity|].
  iEval (rewrite /pcell (pts_app [_])) in "P5". iDestruct "P5" as "[_ P5]". iEval (rewrite -/(icell b5 0 0)) in "P5".
  (* The category is LC_ALL and the name is not null. *)
  step. closed_ints. step. branch. step. step. step. step. branch.
  step. step. step. closed_ints. step. closed_ints. branch.
  (* Take the write lock. *)
  step. step.
  iApply (wp_call_wrlock_state (glibc_program := all_program) Hreg all_ext _ with "[$Hlk $Hself]");
    [vx | exact Hp | exact Hcw |]. iNext. iIntros "[Hlk Hself]".
  (* The name differs from the current name of LC_ALL. *)
  step. step. step. step. closed_ints. check "Hgl". load_pointer_dq "Hgl H176 Hcl" by a2. iNext. iIntros "Hgl H176 Hcl".
  iApply (wp_call_glibc_strcmp with "H80 HC"); [vx | vm_compute; reflexivity | reflexivity |]. iNext. iIntros "_ _".
  cbn [fr_fn fr_env fr_locals fr_at]. step. branch.
  (* No locale path: getenv("LOCPATH") gives null or the empty string. *)
  step. check "L4". store "L4" "P4". check "L5". store_long "L5" "P5". step.
  pose proof Himage as (Hcnt & Henvg & Hbc & Hbce & Hrc & Hbe & Hbee & Hre & Hbe8).
  iApply (wp_call_getenv_static (glibc_program := all_program) with "Hlp HG HS []"); try eassumption; [vx | iEmpIntro |].
  iNext. iIntros "HG HS _ _".
  iDestruct (findlocale_getenv_value _ _ _ _ _ _ (fun v => v = []) with "Hlp HS") as "[HS Hv]";
    [intros v Hv; exact (proj2 Henv v Hv)|].
  iDestruct "Hv" as "[%Hq | (%v & %Hq & #Hv)]"; rewrite Hq.
  1: step; step; closed_ints; branch; step; branch.
  (* An empty path counts as no path: its first byte ends it. *)
  2: set (q := getenv_result (lit "LOCPATH") es) in *; clearbody q;
    iDestruct (ws_byte _ [] 0 with "Hv") as (qb qreg (Hqc & Hq0 & Hqb & Hqe & Hqr)) "[#Hql Hqy]"; [cbn; lia|];
    step; step; branch_as false; step; destruct q as [qa qc]; cbn in Hqc, Hqb, Hqe;
    check_read_dq "Hql" by a2; iNext; iIntros "_"; load_bytes_dq "Hql Hqy" decode (vm_compute; reflexivity) by a2;
    iNext; iIntros "_ _"; step; step; cbn [edge_label]; step; closed_ints; branch_as true.
  (* The category is LC_ALL: every other slot gets the requested name. *)
  all: step; step; closed_ints; branch.
  all: step; step; closed_ints; branch; step; step; closed_ints; branch; step; step; step; step.
  all: check "L103"; store "L103" "N0"; step; step; step; step; step.
  all: fill "N1"; fill "N2"; fill "N3"; fill "N4"; fill "N5".
  all: step; closed_ints; branch; step; step; closed_ints; branch; step; step; step; step.
  all: fill "N7"; fill "N8"; fill "N9"; fill "N10"; fill "N11"; fill "N12".
  all: step; closed_ints; branch; step.
  (* The name has no semicolon, so it is the same for every category. *)
  all: iApply (wp_call_glibc_strchr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 59 with "H80");
    [vx | lia | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity |].
  all: iNext; iIntros "_"; cbn [fr_fn fr_env fr_locals fr_at]; step; step; closed_ints; branch.
  (* The search runs from LC_IDENTIFICATION down to LC_CTYPE. *)
  all: step; step; step; cbn [edge_label].
  all: match goal with |- context [ERun {| fr_env := ?E |}] =>
    assert (Hr0 : sl_regs E b4 b5 b103 b104) by (unfold sl_regs; vm_compute; tauto) end.
  all: fo 11%nat "Hro HG HS [$L4 $P4 $L5 $P5 $L103 $L104] N12 D12" "N12" "D12".
  all: fo 10%nat "Hro HG HS Ht N11 D11" "N11" "D11"; fo 9%nat "Hro HG HS Ht N10 D10" "N10" "D10".
  all: fo 8%nat "Hro HG HS Ht N9 D9" "N9" "D9"; fo 7%nat "Hro HG HS Ht N8 D8" "N8" "D8".
  all: fo 6%nat "Hro HG HS Ht N7 D7" "N7" "D7".
  all: iApply sl_find_skip; [pr2|]; iIntros (?) "[% %]"; kregs.
  all: fo 5%nat "Hro HG HS Ht N5 D5" "N5" "D5"; fo 4%nat "Hro HG HS Ht N4 D4" "N4" "D4".
  all: fo 3%nat "Hro HG HS Ht N3 D3" "N3" "D3"; fo 2%nat "Hro HG HS Ht N2 D2" "N2" "D2".
  all: fo 1%nat "Hro HG HS Ht N1 D1" "N1" "D1"; fo 0%nat "Hro HG HS Ht N0 D0" "N0" "D0".
  (* Every category found its C data. The composite name is "C". *)
  all: cbn [sl_L262 b_insts b_jump]; step; closed_ints; step; closed_ints; branch; step; step; closed_ints; branch; step.
  all: iDestruct "Ht" as "(L4 & P4 & L5 & P5 & L103 & L104)".
  all: match goal with H : sl_regs ?a _ _ _ _ |- context [ERun {| fr_env := ?E |}] =>
    assert (Hr10 : sl_regs E b4 b5 b103 b104) by (eapply sl_regs_keeps; [keeps_tac | exact H]) end.
  all: iApply (sl_comp_first with "Hro L103 N0"); [exact Hfr | exact Hr10
    | split; [lk_prove|split; [lk_prove|split; eexists; lk_prove]] |].
  all: iIntros (?) "[% %] L103 N0"; kregs.
  all: co 0%nat "Hro L103 N0 N1" "N1".
  all: co 1%nat "Hro L103 N0 N2" "N2".
  all: co 2%nat "Hro L103 N0 N3" "N3".
  all: co 3%nat "Hro L103 N0 N4" "N4".
  all: co 4%nat "Hro L103 N0 N5" "N5".
  all: iApply sl_comp_skip; [eassumption|]; iIntros (?) "[% %]"; kregs.
  all: co 5%nat "Hro L103 N0 N7" "N7".
  all: co 6%nat "Hro L103 N0 N8" "N8".
  all: co 7%nat "Hro L103 N0 N9" "N9".
  all: co 8%nat "Hro L103 N0 N10" "N10".
  all: co 9%nat "Hro L103 N0 N11" "N11".
  all: co 10%nat "Hro L103 N0 N12" "N12".
  (* Every name equals the first, which is _nl_C_name itself. *)
  all: match goal with H : sl_comp_regs _ _ |- _ => destruct H as (Hq5 & Hq9 & [? Hq3] & [? Hq1]) end; vm_compute in Hq5.
  all: cbn [sl_C10 b_insts b_jump]; step; closed_ints; branch; step; branch; step.
  all: match goal with H : sl_regs ?a _ _ _ _ |- context [ERun {| fr_env := ?E |}] =>
    assert (Hr92 : sl_regs E b4 b5 b103 b104) by (eapply sl_regs_keeps; [keeps_tac | exact H]) end.
  all: pose proof Hr92 as (R0 & R2 & R4 & R4c & R5 & R5c & R103 & R104 & R30 & R5p).
  all: check "L103"; load_pointer_dq "L103 N0 Hcl" by a2; iNext; iIntros "L103 N0 _"; step.
  all: iApply (wp_call_glibc_strcmp with "HC HC"); [vx | vm_compute; reflexivity | reflexivity |]; iNext; iIntros "_ _".
  all: cbn [fr_fn fr_env fr_locals fr_at]; step; closed_ints; branch; step.
  all: do 8 first [branch | step | closed_ints].
  (* Switch every category to the data it already has. *)
  all: iDestruct "Hgc" as "([G0 Gn0] & [G1 Gn1] & [G2 Gn2] & [G3 Gn3] & [G4 Gn4] & [G5 Gn5] & [G7 Gn7] & [G8 Gn8]
    & [G9 Gn9] & [G10 Gn10] & [G11 Gn11] & [G12 Gn12] & _)".
  all: step; match goal with H : sl_regs ?a _ _ _ _ |- context [ERun {| fr_env := ?E |}] =>
    assert (Hr394 : sl_regs E b4 b5 b103 b104) by (eapply sl_regs_keeps; [keeps_tac | exact H]) end.
  all: iApply (sl_set_zero with "Hro Hpl Hgl L103 L104 N0 D0 G0 Gn0 Hlt Hlc Hpc"); [exact Hfr | exact Hr394
    | split; [lk_prove | split; lk_prove] |].
  all: iIntros (?) "[% %] Hgl L103 L104 N0 D0 G0 Gn0 Hlt Hlc Hpc"; kregs.
  all: so 0%nat "Hro Hgl L103 L104 N1 D1 G1 Gn1" "Hgl L103 L104 N1 D1 G1 Gn1".
  all: so 1%nat "Hro Hgl L103 L104 N2 D2 G2 Gn2" "Hgl L103 L104 N2 D2 G2 Gn2".
  all: so 2%nat "Hro Hgl L103 L104 N3 D3 G3 Gn3" "Hgl L103 L104 N3 D3 G3 Gn3".
  all: so 3%nat "Hro Hgl L103 L104 N4 D4 G4 Gn4" "Hgl L103 L104 N4 D4 G4 Gn4".
  all: so 4%nat "Hro Hgl L103 L104 N5 D5 G5 Gn5" "Hgl L103 L104 N5 D5 G5 Gn5".
  all: iApply sl_set_skip; [eassumption|]; iIntros (?) "[% %]"; kregs.
  all: so 5%nat "Hro Hgl L103 L104 N7 D7 G7 Gn7" "Hgl L103 L104 N7 D7 G7 Gn7".
  all: so 6%nat "Hro Hgl L103 L104 N8 D8 G8 Gn8" "Hgl L103 L104 N8 D8 G8 Gn8".
  all: so 7%nat "Hro Hgl L103 L104 N9 D9 G9 Gn9" "Hgl L103 L104 N9 D9 G9 Gn9".
  all: so 8%nat "Hro Hgl L103 L104 N10 D10 G10 Gn10" "Hgl L103 L104 N10 D10 G10 Gn10".
  all: so 9%nat "Hro Hgl L103 L104 N11 D11 G11 Gn11" "Hgl L103 L104 N11 D11 G11 Gn11".
  all: so 10%nat "Hro Hgl L103 L104 N12 D12 G12 Gn12" "Hgl L103 L104 N12 D12 G12 Gn12".
  (* The last category is done: count up, unlock and return the name. *)
  all: iApply (sl_tail with "Hro Hgl H176 [$L4 $P4 $L5 $P5 $L103 $L104] Hn Hlk Hself");
    [exact Hfr | eassumption | match goal with H : sl_set_regs ?e _ |- sl_set_regs ?e _ => exact H end | exact Hp |].
  all: iIntros "Hgl H176 Hc Hlk Hself".
  all: iApply ("HK" with "HG HS Hgl H176 [G0 Gn0 G1 Gn1 G2 Gn2 G3 Gn3 G4 Gn4 G5 Gn5 G7 Gn7 G8 Gn8 G9 Gn9 G10 Gn10 G11 Gn11 G12 Gn12] Hlt Hlc Hpc Hc Hlk Hself").
  all: iFrame "G0 Gn0 G1 Gn1 G2 Gn2 G3 Gn3 G4 Gn4 G5 Gn5 G7 Gn7 G8 Gn8 G9 Gn9 G10 Gn10 G11 Gn11 G12 Gn12"; done.
Qed.

End all.
