From Glibc Require Import GlibcProgram.
(** The option string "W;" tells getopt to read "-W foo" as "--foo".
    [GetoptWExit](GetoptWExit.v) carries the W of a single-dash word
    from the long-option parser to a return. This file uses that bridge
    for the two other places where getopt meets the W, a resumed group
    and the start of a new group, and for the long-only fallback. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
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
  GetoptDiag GetoptReqTail GetoptLongScan GetoptLongExact GetoptLongDiag GetoptLongStore GetoptLongTail GetoptLongReq GetoptLongEq GetoptLongPre GetoptLongArg GetoptLongUnrec GetoptLongMissOnly
  GetoptLongMiss GetoptLongPfxCmp GetoptLongPfxMark GetoptLongPfxAlloc GetoptLongPfxSet GetoptLongPfxStep GetoptLongPfxIter GetoptLongPfxLoop GetoptLongPfxEnd GetoptLongAmbTail GetoptLongAmbPrint GetoptLongAmbItem GetoptLongAmbList
  GetoptLongAmbHead GetoptLongAmbPoss GetoptLongAmbRep GetoptLongPfxPath GetoptLongFind GetoptLongBody GetoptLongJoinMiss GetoptLongJoinFound GetoptLongJoin GetoptLongCall GetoptLongOnly GetoptDispatch GetoptLongSession GetoptLongDash GetoptLongSite GetoptLongCap GetoptDashRet GetoptLongOnlyRet GetoptLongOnlyShort GetoptWTail GetoptWOpt GetoptLongW GetoptWOptSession GetoptWRet GetoptWExit GetoptKnownCap GetoptDiag GetoptReqTail GetoptShort GetoptOptArg GetoptShortRet
  GetoptShortCap GetoptColon GetoptEntry GetoptEntryScan GetoptScanChoice GetoptCharRet GetoptEntryChar GetoptScanChar.
From Glibc Require GetoptWExit GetoptLongOnlyShort GetoptWRet GetoptWOptSession GetoptLongOnlyRet GetoptCharRet GetoptLongSite GetoptDashRet GetoptLongDash GetoptLongCap GetoptShortCap GetoptEntryScan GetoptScanChar FileInv GetoptArgv GetoptBytes GetoptExchange GetoptInitialize GetoptLongAmbTail GetoptLongBody GetoptLongCall GetoptLongDiag GetoptLongExact GetoptLongJoinMiss GetoptLongPfxAlloc GetoptLongSession GetoptLongStore GetoptState LibioLogic OsWorld StrlenLoop.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Import GetoptWExit GetoptLongCall GetoptLongSite GetoptLongSession GetoptLongJoinMiss GetoptLongCap GetoptShortCap GetoptKnownCap
  GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic
  GetoptBytes GetoptArgv.

Import ProgramAbbreviations.
Section w_exit_ret.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance wexit_ret_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** A shared view of the stream's liveness can be copied. *)
Local Instance wexit_ret_liveq_persistent b0 reg : Persistent (liveq DfracDiscarded b0 reg).
Proof using Type. unfold liveq. apply _. Qed.
(** A shared view of a pointer cell can be copied. *)
Local Instance wexit_ret_pcellq_persistent b0 o x : Persistent (pcellq DfracDiscarded b0 o x).
Proof using Type. unfold pcellq. apply _. Qed.

(** getopt is safe when it reads W in a resumed group. The caller lends
    the parser's resources and handles the three cases. It needs no proof
    for the argument, because the argument is null. The returns of the
    parser keep the relation that names the entry behind the argument,
    and the caller gets the string of the word. *)
Lemma entry_w_ret_arg_with ks ks2 n av ar p os lo li lonly b r ps j (G : iProp Σ) T fp dom (M : iProp Σ) se sereg mid f138 f139 f140 f141 lmid mid3 mid4 los F pfx pxs Φ :
  incl char_ret_keys ks -> In (TAtom "v8") ks -> incl known_req_keys ks2 -> In (TAtom "v6") ks2 ->
  In (TAtom "v8") ks2 ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx ->
  getopt_cutoff_rule_with w0 registry ge G -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) los -> (List.length los < 2 ^ 31)%Z -> n < 2 ^ 31 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  Z.of_nat (List.length ps) = n ->
  opt_table lo los -∗ word_string DfracDiscarded pfx pxs -∗ word_string DfracDiscarded p os -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗ argv_strs ps -∗
  flags_own F -∗ M -∗ longind_own li -∗
  (∀ s q sq k0, ⌜entry_resume_facts n av ar b r ps j s q sq k0⌝ -∗ word_string DfracDiscarded q sq -∗
     w_ret_exits_arg b r av ar ps los li F G M j n 87 null (drop (opt_skip os) os) q sq k0 Φ) -∗
  entry_w_exit n av ar p os lo li lonly b r ps j G ks ks2 Φ.
Proof using Type.
  intros Hinc Hc8 Hinr Hr6 Hr8 Hrule Hse Hmid Hgp Hstr Hcut Hmal Hset Hlrule Hfree Hgn Hgl Hg Hgc H138 H139 H140 H141 Hlmid Hmid3 Hmid4 Hfl Hos Hn Hse0 Hsea Hsee Hser Hlen.
  iIntros "#Ht #Hpfx #Hos #Hsl #Hsc #Hs HF HM Hli HK".
  iIntros (e' e2 e3 s q sq k0 k (Hfacts & Henv & Hk2 & Hk3 & H455 & Hk & Hkw & H459 & H137 & H87 & H59 & Hlo))
    "#Hwq #Hwc Hl Hib Her Hoo Hab Hini Hcur Hor Hfi Hla Ha Hcl HG".
  pose proof Hfacts as (_ & Hind & Hini1 & Hord & Hbd & Hj & Hq & Hk0 & Hsk & Hnx & Hla' & Hb & Hal & Hend & Hr &
    Hav & Hala & Hda & Hra).
  rewrite Hkw in H87. unfold getopt_bounds in Hbd.
  iDestruct "Her" as "[%Her0 Her]". iEval (rewrite Hnx) in "Hcur". iPoseProof arg_cap_null as "Hca".
  iApply (w_exit_bridge_arg_with ks ks2 e' e2 e3 n av ar p os lo li lonly (print_errors os (gs_err s)) b r ps j q sq k0
    (gs_opt s) null (gs_err s) (gs_order s) (gs_first s) (gs_last s) G T fp dom M se sereg mid f138 f139 f140 f141 lmid mid3 mid4 los F pfx pxs Φ
    with "Ht Hwq Hos Hpfx Hsl Hsc Hl Hib [Her] Hoo Hab Hini Hcur Hor Hfi Hla Ha Hcl Hs HG HF HM Hli Hca [HK]");
    try (assumption || lia || exact (print_errors_range os (gs_err s) Her0)).
  - by iSplit.
  - iApply ("HK" $! s q sq k0 with "[%] Hwq"). exact Hfacts.
Qed.

(** Callers that need no resource for the cutoff keep this form. *)
Lemma entry_w_ret_arg ks ks2 n av ar p os lo li lonly b r ps j (G : iProp Σ) T fp dom (M : iProp Σ) se sereg mid f138 f139 f140 f141 lmid mid3 mid4 los F pfx pxs Φ :
  incl char_ret_keys ks -> In (TAtom "v8") ks -> incl known_req_keys ks2 -> In (TAtom "v6") ks2 ->
  In (TAtom "v8") ks2 ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) los -> (List.length los < 2 ^ 31)%Z -> n < 2 ^ 31 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  Z.of_nat (List.length ps) = n ->
  opt_table lo los -∗ word_string DfracDiscarded pfx pxs -∗ word_string DfracDiscarded p os -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗ argv_strs ps -∗
  flags_own F -∗ M -∗ longind_own li -∗
  (∀ s q sq k0, ⌜entry_resume_facts n av ar b r ps j s q sq k0⌝ -∗ word_string DfracDiscarded q sq -∗
     w_ret_exits_arg b r av ar ps los li F G M j n 87 null (drop (opt_skip os) os) q sq k0 Φ) -∗
  entry_w_exit n av ar p os lo li lonly b r ps j G ks ks2 Φ.
Proof using Type.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 Hcut.
  exact (entry_w_ret_arg_with ks ks2 n av ar p os lo li lonly b r ps j G T fp dom M se sereg mid f138 f139 f140 f141 lmid mid3 mid4 los F pfx pxs Φ H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 (getopt_cutoff_rule_with_any w0 registry ge G Hcut)).
Qed.

(** The same exit serves a caller that handles the cases without the relation. *)
Lemma entry_w_ret ks ks2 n av ar p os lo li lonly b r ps j (G : iProp Σ) T fp dom (M : iProp Σ) se sereg mid f138 f139 f140 f141 lmid mid3 mid4 los F pfx pxs Φ :
  incl char_ret_keys ks -> In (TAtom "v8") ks -> incl known_req_keys ks2 -> In (TAtom "v6") ks2 ->
  In (TAtom "v8") ks2 ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) los -> (List.length los < 2 ^ 31)%Z -> n < 2 ^ 31 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  Z.of_nat (List.length ps) = n ->
  opt_table lo los -∗ word_string DfracDiscarded pfx pxs -∗ word_string DfracDiscarded p os -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗ argv_strs ps -∗
  flags_own F -∗ M -∗ longind_own li -∗
  (∀ s q sq k0, ⌜entry_resume_facts n av ar b r ps j s q sq k0⌝ -∗
     w_ret_exits b r av ar ps los li F G M j n 87 null (drop (opt_skip os) os) q sq k0 Φ) -∗
  entry_w_exit n av ar p os lo li lonly b r ps j G ks ks2 Φ.
Proof using Type.
  intros. iIntros "Ht Hpfx Hos Hsl Hsc Hs HF HM Hli HK".
  iApply (entry_w_ret_arg ks ks2 n av ar p os lo li lonly b r ps j G T fp dom M se sereg mid f138 f139 f140 f141 lmid mid3 mid4 los F pfx pxs Φ with "Ht Hpfx Hos Hsl Hsc Hs HF HM Hli");
    try eassumption.
  iIntros (s q sq k0 Hf) "_". iApply w_ret_exits_weaken. iApply ("HK" $! s q sq k0 with "[%]"). exact Hf.
Qed.

(** A new cluster that starts with W is safe. The word is the one that
    the scan found, and the W is its second byte. The argument is null
    there as well, and each return of the parser says which entry chose
    the argument. *)
Lemma scan_w_ret_arg_with ks ks2 n av ar p os lo li lonly b r ps j (G : iProp Σ) T fp dom (M : iProp Σ) se sereg mid f138 f139 f140 f141 lmid mid3 mid4 los F pfx pxs Φ :
  incl char_ret_keys ks -> In (TAtom "v8") ks -> incl known_req_keys ks2 -> In (TAtom "v6") ks2 ->
  In (TAtom "v8") ks2 ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx ->
  getopt_cutoff_rule_with w0 registry ge G -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) los -> (List.length los < 2 ^ 31)%Z -> n < 2 ^ 31 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo los -∗ word_string DfracDiscarded pfx pxs -∗ word_string DfracDiscarded p os -∗
  flags_own F -∗ M -∗ longind_own li -∗
  (∀ s s' w ps' i' f' l', ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l'⌝ -∗
     word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗ argv_strs ps' -∗
     w_ret_exits_arg b r av ar ps' los li F G M i' n 87 null (drop (opt_skip os) os) (nth (Z.to_nat i') ps' null) w 1 Φ) -∗
  scan_w_exit n av ar p os lo li lonly b r ps j G se sereg fp ks ks2 Φ.
Proof using Type.
  intros Hinc Hc8 Hinr Hr6 Hr8 Hrule Hse Hmid Hgp Hstr Hcut Hmal Hset Hlrule Hfree Hgn Hgl Hg Hgc H138 H139 H140 H141 Hlmid Hmid3 Hmid4 Hfl Hos Hn Hse0 Hsea Hsee Hser.
  iIntros "#Ht #Hpfx #Hos HF HM Hli HK".
  iIntros (e1 e2 e3 s s' w ps' i' f' l' k (Hfacts & Henv & Hk2 & Hk3 & H455 & Hk & Hkw & H459 & H137 & H87 & H59 & Hlo))
    "#Hws Hl Hib Her Hoo Hab Hini Hcur Hor Hfi Hla #Hsl #Hsc Ha Hcl #Hs HG".
  pose proof Hfacts as (Hst & Hj & Hini1 & Hord & Harg & Hp & Hlen & Hfl' & Hli' & Hii & Hw0 & Hw1 & Hb & Hal & Hend &
    Hr & Hav & Hala & Hda & Hra).
  rewrite Hkw in H87. pose proof (sbyte_in_len w 1 Hw1) as Hlw.
  assert (Hnq : ps' !! Z.to_nat i' = Some (nth (Z.to_nat i') ps' null)).
  { destruct (lookup_lt_is_Some_2 ps' (Z.to_nat i')) as [q Hq]; [lia|]. by rewrite (nth_lookup_Some _ _ _ _ Hq). }
  iDestruct "Her" as "[%Her0 Her]". rewrite (GetoptScanChar.entry_state_err _ _ Hst) in Her0.
  iPoseProof arg_cap_null as "Hca".
  iApply (w_exit_bridge_arg_with ks ks2 e1 e2 e3 n av ar p os lo li lonly (print_errors os (gs_err s)) b r ps' i'
    (nth (Z.to_nat i') ps' null) w 1 (gs_opt s') null (gs_err s') (gs_order s') f' l' G T fp dom M se sereg mid f138 f139 f140 f141 lmid mid3 mid4 los F pfx pxs Φ
    with "Ht Hws Hos Hpfx Hsl Hsc Hl Hib [Her] Hoo Hab Hini Hcur Hor Hfi Hla Ha Hcl Hs HG HF HM Hli Hca [HK]");
    try (assumption || lia || exact (print_errors_range os (gs_err s) Her0)).
  - rewrite (GetoptScanChar.entry_state_err _ _ Hst). by iSplit.
  - iApply ("HK" $! s s' w ps' i' f' l' with "[%] Hws Hs"). exact Hfacts.
Qed.

(** Callers that need no resource for the cutoff keep this form. *)
Lemma scan_w_ret_arg ks ks2 n av ar p os lo li lonly b r ps j (G : iProp Σ) T fp dom (M : iProp Σ) se sereg mid f138 f139 f140 f141 lmid mid3 mid4 los F pfx pxs Φ :
  incl char_ret_keys ks -> In (TAtom "v8") ks -> incl known_req_keys ks2 -> In (TAtom "v6") ks2 ->
  In (TAtom "v8") ks2 ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) los -> (List.length los < 2 ^ 31)%Z -> n < 2 ^ 31 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo los -∗ word_string DfracDiscarded pfx pxs -∗ word_string DfracDiscarded p os -∗
  flags_own F -∗ M -∗ longind_own li -∗
  (∀ s s' w ps' i' f' l', ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l'⌝ -∗
     word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗ argv_strs ps' -∗
     w_ret_exits_arg b r av ar ps' los li F G M i' n 87 null (drop (opt_skip os) os) (nth (Z.to_nat i') ps' null) w 1 Φ) -∗
  scan_w_exit n av ar p os lo li lonly b r ps j G se sereg fp ks ks2 Φ.
Proof using Type.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 Hcut.
  exact (scan_w_ret_arg_with ks ks2 n av ar p os lo li lonly b r ps j G T fp dom M se sereg mid f138 f139 f140 f141 lmid mid3 mid4 los F pfx pxs Φ H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 (getopt_cutoff_rule_with_any w0 registry ge G Hcut)).
Qed.

(** The same exit serves a caller that handles the cases without the relation. *)
Lemma scan_w_ret ks ks2 n av ar p os lo li lonly b r ps j (G : iProp Σ) T fp dom (M : iProp Σ) se sereg mid f138 f139 f140 f141 lmid mid3 mid4 los F pfx pxs Φ :
  incl char_ret_keys ks -> In (TAtom "v8") ks -> incl known_req_keys ks2 -> In (TAtom "v6") ks2 ->
  In (TAtom "v8") ks2 ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) los -> (List.length los < 2 ^ 31)%Z -> n < 2 ^ 31 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo los -∗ word_string DfracDiscarded pfx pxs -∗ word_string DfracDiscarded p os -∗
  flags_own F -∗ M -∗ longind_own li -∗
  (∀ s s' w ps' i' f' l', ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l'⌝ -∗
     word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗ argv_strs ps' -∗
     w_ret_exits b r av ar ps' los li F G M i' n 87 null (drop (opt_skip os) os) (nth (Z.to_nat i') ps' null) w 1 Φ) -∗
  scan_w_exit n av ar p os lo li lonly b r ps j G se sereg fp ks ks2 Φ.
Proof using Type.
  intros. iIntros "Ht Hpfx Hos HF HM Hli HK".
  iApply (scan_w_ret_arg ks ks2 n av ar p os lo li lonly b r ps j G T fp dom M se sereg mid f138 f139 f140 f141 lmid mid3 mid4 los F pfx pxs Φ with "Ht Hpfx Hos HF HM Hli");
    try eassumption.
  iIntros (s s' w ps' i' f' l' Hf) "Hws Hs". iApply w_ret_exits_weaken.
  iApply ("HK" $! s s' w ps' i' f' l' with "[%] Hws Hs"). exact Hf.
Qed.

(** In long-only mode, getopt first gives "-Wfoo" to the long-option
    parser. When the parser turns it down, getopt reads it as short
    options, and the W still works. Here the argument a' may come from
    the parser, so the exit lends its proof. *)
Lemma long_only_w_ret_with kc kr n av ar p os lo li lonly b r ps j (G : iProp Σ) T fp dom (M : iProp Σ) se sereg mid f138 f139 f140 f141 lmid mid3 mid4 los F pfx pxs Φ :
  incl char_ret_keys kc -> In (TAtom "v8") kc -> incl known_req_keys kr -> In (TAtom "v6") kr ->
  In (TAtom "v8") kr ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx ->
  getopt_cutoff_rule_with w0 registry ge G -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) los -> (List.length los < 2 ^ 31)%Z -> n < 2 ^ 31 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo los -∗ word_string DfracDiscarded pfx pxs -∗ word_string DfracDiscarded p os -∗
  (∀ s s' w ps' i' f' l' a',
     ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\ lonly mod 2 ^ 32 <> 0 /\ sbyte w 1 <> 45 /\
       (a' = null \/ a' = ptr_add (ptr_add (nth (Z.to_nat i') ps' null) 1) (Z.of_nat (eq_len (drop 1 w)) + 1) \/
        a' = nth (Z.to_nat (i' + 1)) ps' null)⌝ -∗
     word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗ argv_strs ps' -∗
     w_ret_exits b r av ar ps' los li F G M i' n 87 a' (drop (opt_skip os) os) (nth (Z.to_nat i') ps' null) w 1 Φ) -∗
  long_only_w_exit n av ar p os lo li lonly b r ps j G se sereg fp kc kr F M Φ.
Proof using Type.
  intros Hinc Hc8 Hinr Hr6 Hr8 Hrule Hse Hmid Hgp Hstr Hcut Hmal Hset Hlrule Hfree Hgn Hgl Hg Hgc H138 H139 H140 H141 Hlmid Hmid3 Hmid4 Hfl Hos Hn Hse0 Hsea Hsee Hser.
  iIntros "#Ht #Hpfx #Hos HK".
  iIntros (e3 e4 e5 s s' w ps' i' f' l' oo' a' k (Hfacts & Hlo0 & H45 & Ha' & Henv & Hk2 & Hk3 & H455 & Hk & Hkw &
    H459 & H137 & H87 & H59 & Hlo)) "#Hws Hl Hib Her Hoo Hab Hini Hcur Hor Hfi Hla #Hsl #Hsc Ha Hcl #Hs HG HF HM Hli Hca".
  pose proof Hfacts as (Hst & Hj & Hini1 & Hord & Harg & Hp & Hlen & Hfl' & Hli' & Hii & Hw0 & Hw1 & Hb & Hal & Hend &
    Hr & Hav & Hala & Hda & Hra).
  rewrite Hkw in H87. pose proof (sbyte_in_len w 1 Hw1) as Hlw.
  assert (Hnq : ps' !! Z.to_nat i' = Some (nth (Z.to_nat i') ps' null)).
  { destruct (lookup_lt_is_Some_2 ps' (Z.to_nat i')) as [q Hq]; [lia|]. by rewrite (nth_lookup_Some _ _ _ _ Hq). }
  iDestruct "Her" as "[%Her0 Her]". rewrite (GetoptScanChar.entry_state_err _ _ Hst) in Her0.
  iApply (w_exit_bridge_with kc kr e3 e4 e5 n av ar p os lo li lonly (print_errors os (gs_err s)) b r ps' i'
    (nth (Z.to_nat i') ps' null) w 1 oo' a' (gs_err s') (gs_order s') f' l' G T fp dom M se sereg mid f138 f139 f140 f141 lmid mid3 mid4 los F pfx pxs Φ
    with "Ht Hws Hos Hpfx Hsl Hsc Hl Hib [Her] Hoo Hab Hini Hcur Hor Hfi Hla Ha Hcl Hs HG HF HM Hli Hca [HK]");
    try (assumption || lia || exact (print_errors_range os (gs_err s) Her0)).
  - rewrite (GetoptScanChar.entry_state_err _ _ Hst). by iSplit.
  - iApply ("HK" $! s s' w ps' i' f' l' a' with "[%] Hws Hs"). exact (conj Hfacts (conj Hlo0 (conj H45 Ha'))).
Qed.

(** Callers that need no resource for the cutoff keep this form. *)
Lemma long_only_w_ret kc kr n av ar p os lo li lonly b r ps j (G : iProp Σ) T fp dom (M : iProp Σ) se sereg mid f138 f139 f140 f141 lmid mid3 mid4 los F pfx pxs Φ :
  incl char_ret_keys kc -> In (TAtom "v8") kc -> incl known_req_keys kr -> In (TAtom "v6") kr ->
  In (TAtom "v8") kr ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some pfx ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) los -> (List.length los < 2 ^ 31)%Z -> n < 2 ^ 31 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo los -∗ word_string DfracDiscarded pfx pxs -∗ word_string DfracDiscarded p os -∗
  (∀ s s' w ps' i' f' l' a',
     ⌜scan_cluster_facts n av ar b r ps j s s' w ps' i' f' l' /\ lonly mod 2 ^ 32 <> 0 /\ sbyte w 1 <> 45 /\
       (a' = null \/ a' = ptr_add (ptr_add (nth (Z.to_nat i') ps' null) 1) (Z.of_nat (eq_len (drop 1 w)) + 1) \/
        a' = nth (Z.to_nat (i' + 1)) ps' null)⌝ -∗
     word_string DfracDiscarded (nth (Z.to_nat i') ps' null) w -∗ argv_strs ps' -∗
     w_ret_exits b r av ar ps' los li F G M i' n 87 a' (drop (opt_skip os) os) (nth (Z.to_nat i') ps' null) w 1 Φ) -∗
  long_only_w_exit n av ar p os lo li lonly b r ps j G se sereg fp kc kr F M Φ.
Proof using Type.
  intros H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 Hcut.
  exact (long_only_w_ret_with kc kr n av ar p os lo li lonly b r ps j G T fp dom M se sereg mid f138 f139 f140 f141 lmid mid3 mid4 los F pfx pxs Φ H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 (getopt_cutoff_rule_with_any w0 registry ge G Hcut)).
Qed.

End w_exit_ret.
