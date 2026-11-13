(** In long-only mode glibc's long-option parser accepts long options
    after a single dash, so a word such as "-x" that names no long option
    may still be a short option. When the word's second byte is not a
    dash and the first character of the name is in the short option
    string, the parser returns -1 and leaves the word to the short
    options. Otherwise it goes on to report the word. This file proves
    that test safe: it reads the vector, the word and the option string
    only inside them and writes nothing. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrchrCode StrchrnulLogic StrlenBits StrlenLogic StrlenLoop StrlenWord
  StrncmpCode StrcmpBits StrcmpLoop StrncmpBits StrncmpLoop StrncmpWords StrncmpLogic
  GetoptModule GetoptState GetoptBytes GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor
  GetoptDiag GetoptReqTail GetoptLongScan GetoptLongExact GetoptLongDiag GetoptLongStore GetoptLongTail GetoptLongReq GetoptLongEq GetoptLongPre GetoptLongArg GetoptLongUnrec.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The long-only test assigns these names. *)
Definition lonly_names : list name := Eval vm_compute in
  List.map TAtom ["chk35"; "v341"; "v342"; "v343"; "v344"; "chk36"; "v345"; "v346"; "chk37"; "v347"; "v348"; "v350";
    "v355"; "chk38"; "v356"; "chk39"; "v357"; "v358"; "v359"; "v361"; "v363"]%string.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptLongMissOnlyOn (R : Runtime) (LG0 : LogicSig R).
(** The report module supplies the report, the option table and the tactics. *)
Module LU := GetoptLongUnrecOn R LG0.
Import LU LU.LA LU.LA.LP LU.LA.LP.LQE LU.LA.LP.LQE.LQ LU.LA.LP.LQE.LQ.LL LU.LA.LP.LQE.LQ.LL.LT LU.LA.LP.LQE.LQ.LL.LT.LD
  LU.LA.LP.LQE.LQ.LL.LT.LD.LE LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT
  LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I
  LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI
  LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.ML LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.LG
  LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.L LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.ST
  LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.GB LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.A.
(** The strchr module proves glibc's own strchr. *)
Module SC := StrchrnulLogicOn R LG0.

Section only.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance only_stable : SafepointStable (os_wi w0) := LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance only_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The parser is in long-only mode and found no entry for the name at
    the cursor cur, in the word q at index i. It reads the word's second
    byte. When that byte is not a dash, it looks up the name's first
    character in the option string po. It returns -1 when it finds the
    character there, and it goes on to report the word otherwise. *)
Lemma wp_long_miss_only ks e cur s q sq po so i n b r av ar ps Φ :
  avoids ks lonly_names = true ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) -> lookup (TAtom "v4") e = Some (WPtr po) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "v90") e = Some (WInt 0) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  ps !! Z.to_nat i = Some q -> sbyte sq 0 <> 0 ->
  0 <= i < n -> n < 2 ^ 31 - 1 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  word_string DfracDiscarded q sq -∗ word_string DfracDiscarded po so -∗ word_string DfracDiscarded cur s -∗
  live b r -∗ int_cell b 0 i -∗ pcell b 32 cur -∗ live av ar -∗ argv_cells av ps -∗
  ((∀ e' fr, ⌜keeps ks e e'⌝ -∗
      live b r -∗ int_cell b 0 i -∗ pcell b 32 cur -∗ live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L332") (Some fr))) : gexpr) {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e'⌝ -∗
      live b r -∗ int_cell b 0 i -∗ pcell b 32 cur -∗ live av ar -∗ argv_cells av ps -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec (TAtom "L334") [] (JRet (Const 4294967295))))
        : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L337") (Some (TAtom "L325")))) : gexpr)
    {{ Φ }}.
Proof.
  intros Hks Hg Hgn H2 H4 H12 H90 Hc0 Hq Hq0 Hi Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra.
  iIntros "#Hwq #Hpo #Hws Hl [%Hi0 Hib] Hcur Ha Hcl HK".
  iDestruct (argv_str_cap with "Hws") as (rc) "[#Hcapc %Hc0']".
  iDestruct (argv_str_cap with "Hwq") as (rq) "[#Hcapq %Hq0']".
  iDestruct (ws_shape with "Hwq") as %(Hchq & Hqp & Hqe). iDestruct (ws_shape with "Hws") as %(Hch & Hcp & Hce).
  pose proof (sbyte_in_len sq 0 Hq0) as Hql. pose proof (sbyte_range sq 1 Hchq) as Hq1r.
  pose proof (sbyte_range s 0 Hch) as Hs0r.
  en. chk "Hl". load_int "Hl Hib". st. st. st. idx i. chk "Ha".
  iDestruct (big_sepL_lookup_acc with "Hcl") as "[Hcj Hcl]"; [exact Hq|].
  iApply (wp_raw_load_pointer_dq with "Ha Hcj Hcapq"); [reflexivity | vx | left; reflexivity | arith | arith | lia |].
  iNext. iIntros "Ha Hcj _". iSpecialize ("Hcl" with "Hcj"). st. norm.
  iDestruct (ws_byte q sq 1 with "Hwq") as (bb breg) "(%Hbb & #Hbl & #Hbt)"; [lia|].
  destruct Hbb as (Hcap & ? & ? & ? & ?).
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hbl");
    [reflexivity | vx | exact Hcap | arith | cbn [ptr_addr]; unfold raw_address; rewrite Z.mod_small; lia | arith |].
  iNext; iIntros "_".
  iApply (wp_raw_load_sub_bytes_dq with "Hbl Hbt");
    [reflexivity | vx | reflexivity | apply extended_chr | exact Hcap | arith |].
  iNext; iIntros "_ _". iClear "Hbl Hbt". st. rewrite chr_cmp; [|lia|lia].
  st. en. iApply wp_branch; [vx | iNext].
  destruct (Z.eqb_spec (sbyte sq 1) 45) as [E45 | E45]; cbn [edge_label].
  { en. iApply wp_branch; [vx | iNext]. close_br. iDestruct "HK" as "[HK _]".
    iApply ("HK" with "[%] Hl [Hib] Hcur Ha Hcl"); [xkeep | by iSplit]. }
  en. st. chk "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hcur Hcapc"); [reflexivity | vx | left; reflexivity | arith | arith | lia |].
  iNext. iIntros "Hl Hcur _".
  iDestruct (ws_byte cur s 0 with "Hws") as (cb creg) "(%Hcb & #Hcbl & #Hcbt)"; [lia|].
  destruct Hcb as (Hccap & ? & ? & ? & ?).
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hcbl");
    [reflexivity | vx | exact Hccap | arith | cbn [ptr_addr]; unfold raw_address; rewrite Z.mod_small; lia | arith |].
  iNext; iIntros "_".
  iApply (wp_raw_load_sub_bytes_dq with "Hcbl Hcbt");
    [reflexivity | vx | reflexivity | apply extended_chr | exact Hccap | arith |].
  iNext; iIntros "_ _". iClear "Hcbl Hcbt".
  iApply (SC.wp_call_glibc_strchr registry (os_wi w0) ge with "Hpo");
    [vx | apply Z.mod_pos_bound; lia | exact Hg | exact Hgn | reflexivity |].
  iNext. iIntros "_". cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. st. st. st. en.
  iApply wp_branch; [vx | iNext].
  match goal with |- context [edge_label (if ?c then _ else _)] => destruct c end; cbn [edge_label].
  - iDestruct "HK" as "[_ HK]". en. iApply ("HK" with "[%] Hl [Hib] Hcur Ha Hcl"); [xkeep | by iSplit].
  - iDestruct "HK" as "[HK _]". iApply ("HK" with "[%] Hl [Hib] Hcur Ha Hcl"); [xkeep | by iSplit].
Qed.

End only.
End GetoptLongMissOnlyOn.
