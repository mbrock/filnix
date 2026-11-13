(** glibc's long-option parser reports a bad long option on stderr when
    its caller lets it print errors. Most reports take two calls, as the
    short-option reports do: __GI___dcgettext translates the message,
    and __fxprintf_nocancel writes the translation with the program
    name, the option prefix and a name. The report of an ambiguous
    option also writes two untranslated formats. This file does not
    prove the two callees. It states the rule that a caller supplies
    for them, and it proves the parser's own part of the two reports
    about an option that it found in the table. Proving the rule for
    the real callees remains an open proof obligation of the caller
    about locale translation and formatting. It is not part of the OS
    boundary. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrlenBits StrlenLogic StrlenLoop StrlenWord
  StrncmpCode StrcmpBits StrcmpLoop StrncmpBits StrncmpLoop StrncmpWords StrncmpLogic
  GetoptModule GetoptState GetoptBytes GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor
  GetoptDiag GetoptReqTail GetoptLongScan GetoptLongExact.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The two reports below assign these names: an argument given to an
    option without one, and a missing argument. *)
Definition ldiag_names : list name := Eval vm_compute in
  List.map TAtom ["v415"; "chk53"; "v416"; "v417"; "v418"; "v419"; "chk54"; "v422"; "chk55"; "v425"; "v426";
    "v460"; "chk64"; "v461"; "v462"; "v463"; "v464"; "chk65"; "v467"; "chk66"; "v470"; "v471"]%string.

(** The parser translates five messages, the format strings str.138,
    str.139, str.142, str.143 and str.144. *)
Definition ldiag_msg (ge : genv) (mid : ptr) : Prop :=
  List.Exists (fun n => lookup (TAtom n) (ge_globals ge) = Some mid)
    ["glibc_getopt#str.138"; "glibc_getopt#str.139"; "glibc_getopt#str.142"; "glibc_getopt#str.143";
     "glibc_getopt#str.144"]%string.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptLongDiagOn (R : Runtime) (LG0 : LogicSig R).
(** The exact search module supplies the option table and the tactics. *)
Module LE := GetoptLongExactOn R LG0.
Import LE LE.LS LE.LS.RT LE.LS.RT.D LE.LS.RT.D.X LE.LS.RT.D.X.I LE.LS.RT.D.X.I.S LE.LS.RT.D.X.I.S.FI
  LE.LS.RT.D.X.I.S.FI.ML LE.LS.RT.D.X.I.S.FI.LG LE.LS.RT.D.X.I.S.FI.L LE.LS.RT.D.X.I.ST LE.LS.RT.D.X.I.GB
  LE.LS.RT.D.X.A.

Section ldiag.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance ldiag_stable : SafepointStable (os_wi w0) := LE.LS.RT.D.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance ldiag_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** When the parser reports a bad long option, it translates the
    message and writes the translation to the error stream. This file
    does not prove those two calls. A caller that wants the parser
    proved supplies a rule for them. The caller's resource G holds the
    error stream fp that stderr points at. G must keep the lock on that
    stream exactly as the caller holds it. G must also keep the stream's
    fixed fields. G must let the buffer, errno and the OS state change,
    because the real calls change them. The rule lends a share of the
    stream's lifetime while the parser reads fp. It names the message
    domain dom. Translating one of the five messages takes G and gives
    back T, which holds the stream and the translation. Output then
    gives back G. The output of the two formats that the parser does not
    translate keeps G. *)
Definition getopt_ldiag_rule (G : iProp Σ) (T : ptr -> ptr -> iProp Σ) (fp dom : ptr) : Prop :=
  lookup (TAtom "__GI__libc_intl_domainname") (ge_globals ge) = Some dom /\ 0 <= ptr_addr fp < 2 ^ 64 /\
  (⊢ G -∗ ∃ dq reg, live_capq dq (ptr_cap fp) reg ∗ (live_capq dq (ptr_cap fp) reg -∗ G)) /\
  (forall f e ls l d args rest j mid Φ, ldiag_msg ge mid ->
     map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] ->
     ⊢ G -∗ ▷ (∀ q, T mid q -∗ WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
       WP (ERun (mkFrame f e ls None
            (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}) /\
  (forall f e ls l d args rest j mid q a0 s0 pfx sp nm sn Φ, ldiag_msg ge mid ->
     map_option (arg_x ge e) args = Some [WPtr fp; WPtr q; WPtr a0; WPtr pfx; WPtr nm] ->
     ⊢ T mid q -∗ word_string DfracDiscarded a0 s0 -∗ word_string DfracDiscarded pfx sp -∗
       word_string DfracDiscarded nm sn -∗
       ▷ (∀ x, G -∗ WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
       WP (ERun (mkFrame f e ls None
            (Exec l (Call (CResult d W) (Global (TAtom "__fxprintf_nocancel")) args :: rest) j)) : gexpr) {{ Φ }}) /\
  (forall f e ls l d args rest j fmt pfx sp nm sn Φ,
     lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some fmt ->
     map_option (arg_x ge e) args = Some [WPtr fp; WPtr fmt; WPtr pfx; WPtr nm] ->
     ⊢ G -∗ word_string DfracDiscarded pfx sp -∗ word_string DfracDiscarded nm sn -∗
       ▷ (∀ x, G -∗ WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
       WP (ERun (mkFrame f e ls None
            (Exec l (Call (CResult d W) (Global (TAtom "__fxprintf_nocancel")) args :: rest) j)) : gexpr) {{ Φ }}) /\
  (forall f e ls l d args rest j fmt Φ,
     lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some fmt ->
     map_option (arg_x ge e) args = Some [WPtr fp; WPtr fmt] ->
     ⊢ G -∗ ▷ (∀ x, G -∗ WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
       WP (ERun (mkFrame f e ls None
            (Exec l (Call (CResult d W) (Global (TAtom "__fxprintf_nocancel")) args :: rest) j)) : gexpr) {{ Φ }}).

(** This tactic shows that the message of a report is one of the five. *)
Ltac lmsg := unfold ldiag_msg; repeat first [apply List.Exists_cons_hd; eassumption | apply List.Exists_cons_tl].

(** This tactic proves a report about the found entry x at pr.7: it reads
    stderr and the program name, translates the message, reads the
    entry's name and writes the report. *)
Ltac ldiag_entry_block Htc Hn0 :=
  let Hdom := fresh "Hdom" in let Hfp := fresh "Hfp" in let Hlend := fresh "Hlend" in
  let Hgt := fresh "Hgt" in let Hfx := fresh "Hfx" in
  match goal with Hr : getopt_ldiag_rule _ _ _ _ |- _ => destruct Hr as (Hdom & Hfp & Hlend & Hgt & Hfx & _) end;
  let q0 := fresh "q0" in let ps' := fresh "ps" in
  match goal with Hps : ?ps <> [] |- _ => destruct ps as [|q0 ps']; [congruence|] end;
  iAssert (∃ s0, word_string DfracDiscarded q0 s0)%I as (s0) "#Hws";
  [unfold argv_strs; rewrite big_sepL_cons; iDestruct "Hs" as "[H _]"; iExact "H"|];
  iDestruct (argv_str_cap with "Hws") as (rq) "[#Hcapq %Hq0]";
  en; st;
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hsl");
    [reflexivity | vx | left; reflexivity | arith | arith | arith |];
  iNext; iIntros "_";
  iDestruct (Hlend with "HG") as (dq freg) "[Hcf HG]";
  iApply (wp_raw_load_pointer_dq with "Hsl Hsc Hcf"); [reflexivity | vx | left; reflexivity | arith | arith | exact Hfp |];
  iNext; iIntros "_ _ Hcf"; iSpecialize ("HG" with "Hcf"); st; st;
  iApply (Hgt with "HG"); [lmsg | vx |]; iNext; iIntros (q) "HT";
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Ha");
    [reflexivity | vx | left; reflexivity | arith | arith | arith |];
  iNext; iIntros "Ha"; iDestruct "Hcl" as "[Hc0 Hcl]";
  iApply (wp_raw_load_pointer_dq with "Ha Hc0 Hcapq"); [reflexivity | vx | left; reflexivity | arith | arith | lia |];
  iNext; iIntros "Ha Hc0 _";
  iApply (wp_half_check_read_dq w0 registry ge with "Htl");
    [reflexivity | vx | assumption | exact Htc | al8 | al8 | lia | lia | al8 |];
  iNext; iIntros "_";
  iApply (wp_raw_load_pointer_dq with "Htl Hn Hcapn"); [reflexivity | vx | exact Htc | rawa | al8 | exact Hn0 |];
  iNext; iIntros "_ _ _";
  iApply (Hfx with "HT Hws Hpfx Hnws"); [lmsg | vx |];
  iNext; iIntros (r0) "HG"; st;
  iApply ("HK" with "[%] Ha [Hc0 Hcl] HG"); [xkeep | iFrame].

(** The parser rejects an argument given to the found entry x when x
    takes none. The report reads the stream pointer from the global
    stderr, which the caller shares, and the program name from the first
    entry of the argument vector, which is not empty. It translates the
    message str.143 and writes it with the prefix pfx and the name of x.
    The report keeps the vector and gives back G. *)
Lemma wp_getopt_ldiag_noarg ks e fr (G : iProp Σ) T fp dom se sereg mid av ar ps lo os j x p1 pfx sp Φ :
  avoids ks ldiag_names = true -> getopt_ldiag_rule G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v16") e = Some (WPtr pfx) ->
  lookup (TAtom "pr.7") e = Some (WPtr (ptr_add lo (32 * Z.of_nat j))) ->
  lookup (TAtom "chk51") e = Some (WPtr p1) -> ptr_cap p1 = ptr_cap lo -> os !! j = Some x ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 <= r_end ar -> r_end ar <= 2 ^ 48 -> ps <> [] ->
  opt_table lo os -∗ word_string DfracDiscarded pfx sp -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗
  (∀ e', ⌜keeps ks e e'⌝ -∗ live av ar -∗ argv_cells av ps -∗ G -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L413") (Some (TAtom "L411")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L411") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hrule Hse Hmid H2 H16 H7 Hc51 Hp1 Hx Hse0 Hsea Hsee Hser Hav Hala Hda Hra Hps.
  pose proof (lookup_lt_Some _ _ _ Hx) as Hjl.
  iIntros "#Ht #Hpfx #Hsl #Hsc Ha Hcl #Hs HG HK".
  iDestruct "Ht" as (tb treg) "(%Ht & #Htl & #Hes & _)". destruct Ht as (Htc & Htb & Htlo & Hta & Hte & Htr).
  iDestruct (big_sepL_lookup with "Hes") as "(#Hn & #Hnws & _)"; [exact Hx|].
  iDestruct (argv_str_cap with "Hnws") as (rn) "[#Hcapn %Hn0]".
  ldiag_entry_block Htc Hn0.
Qed.

(** The parser reports a missing argument of the found entry x, which
    requires one, in the same way with the message str.144. *)
Lemma wp_getopt_ldiag_missing ks e fr (G : iProp Σ) T fp dom se sereg mid av ar ps lo os j x p1 pfx sp Φ :
  avoids ks ldiag_names = true -> getopt_ldiag_rule G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v16") e = Some (WPtr pfx) ->
  lookup (TAtom "pr.7") e = Some (WPtr (ptr_add lo (32 * Z.of_nat j))) ->
  lookup (TAtom "chk58") e = Some (WPtr p1) -> ptr_cap p1 = ptr_cap lo -> os !! j = Some x ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 <= r_end ar -> r_end ar <= 2 ^ 48 -> ps <> [] ->
  opt_table lo os -∗ word_string DfracDiscarded pfx sp -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗
  (∀ e', ⌜keeps ks e e'⌝ -∗ live av ar -∗ argv_cells av ps -∗ G -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L458") (Some (TAtom "L456")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L456") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hrule Hse Hmid H2 H16 H7 Hc51 Hp1 Hx Hse0 Hsea Hsee Hser Hav Hala Hda Hra Hps.
  pose proof (lookup_lt_Some _ _ _ Hx) as Hjl.
  iIntros "#Ht #Hpfx #Hsl #Hsc Ha Hcl #Hs HG HK".
  iDestruct "Ht" as (tb treg) "(%Ht & #Htl & #Hes & _)". destruct Ht as (Htc & Htb & Htlo & Hta & Hte & Htr).
  iDestruct (big_sepL_lookup with "Hes") as "(#Hn & #Hnws & _)"; [exact Hx|].
  iDestruct (argv_str_cap with "Hnws") as (rn) "[#Hcapn %Hn0]".
  ldiag_entry_block Htc Hn0.
Qed.

End ldiag.
End GetoptLongDiagOn.
