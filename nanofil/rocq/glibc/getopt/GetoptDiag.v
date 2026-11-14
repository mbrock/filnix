(** glibc's scanner reports a bad option on stderr when the caller lets
    it print errors. The report takes two calls. __GI___dcgettext
    translates the message through the C library's message domain, and
    __fxprintf_nocancel writes the translation to stderr with the
    program name and the option character. This file does not prove
    either callee. It states the rule that a caller supplies for the
    pair, and it proves the scanner's own part of the report: the read
    of the stderr pointer, the read of the program name from the
    argument vector, and the arguments that it passes. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString GetoptModule GetoptState GetoptBytes
  GetoptInitialize GetoptEntry GetoptArgv GetoptExchange.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptExchange GetoptInitialize GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The three reports assign these names: an unknown option, a missing
    argument of "-W", and a missing argument of a short option. *)
Definition diag_names : list name := Eval vm_compute in
  List.map TAtom ["v494"; "chk141"; "v495"; "v496"; "v497"; "v498"; "chk142"; "v501"; "v503";
    "v555"; "chk151"; "v556"; "v557"; "v558"; "v559"; "chk152"; "v562"; "v564";
    "v664"; "chk178"; "v665"; "v666"; "v667"; "v668"; "chk179"; "v671"; "v673"]%string.

(** The scanner's two messages are the format strings str.148, for an
    unknown option, and str.149, for a missing argument. *)
Definition diag_msg (ge : genv) (mid : ptr) : Prop :=
  lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid \/
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid.


(** The exchange module supplies the argument vector and its tactics. *)
Import GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

(** This tactic enters a block and evaluates its phi assignments. *)


Section diag.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance diag_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance diag_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The report calls two functions that this file does not prove, so a
    caller that wants the scanner proved must supply a rule for them.
    The rule names the stream fp that stderr points at and the message
    domain dom. The caller's resource G holds the stream. The caller must
    choose G so that it keeps the stderr lock exactly as the caller holds
    it and keeps the stream's fixed fields, but lets the buffer, errno
    and the OS state change, because the real callees change them. The
    rule lends a share of the stream's lifetime while the scanner reads
    fp. Translating one of the two messages takes G and gives back T,
    which holds the stream and what output needs to know about the
    translation. Output then gives back G. Proving the rule for the real
    callees remains an open proof obligation of the caller about locale
    translation and formatting. It is not part of the OS boundary. *)
Definition getopt_diag_rule (G : iProp Σ) (T : ptr -> ptr -> iProp Σ) (fp dom : ptr) : Prop :=
  lookup (TAtom "__GI__libc_intl_domainname") (ge_globals ge) = Some dom /\ 0 <= ptr_addr fp < 2 ^ 64 /\
  (⊢ G -∗ ∃ dq reg, live_capq dq (ptr_cap fp) reg ∗ (live_capq dq (ptr_cap fp) reg -∗ G)) /\
  (forall f e ls l d args rest j mid Φ, diag_msg ge mid ->
     map_option (arg_x ge e) args = Some [WPtr dom; WPtr mid; WInt 5] ->
     ⊢ G -∗ ▷ (∀ q, T mid q -∗ WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
       WP (ERun (mkFrame f e ls None
            (Exec l (Call (CResult d P) (Global (TAtom "__GI___dcgettext")) args :: rest) j)) : gexpr) {{ Φ }}) /\
  (forall f e ls l d args rest j mid q a0 s0 c Φ, diag_msg ge mid -> 0 <= c < 2 ^ 32 ->
     map_option (arg_x ge e) args = Some [WPtr fp; WPtr q; WPtr a0; WInt c] ->
     ⊢ T mid q -∗ word_string DfracDiscarded a0 s0 -∗
       ▷ (∀ x, G -∗ WP (ERun (mkFrame f (put d (WInt x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
       WP (ERun (mkFrame f e ls None
            (Exec l (Call (CResult d W) (Global (TAtom "__fxprintf_nocancel")) args :: rest) j)) : gexpr) {{ Φ }}).

(** This tactic computes call arguments whose last one is the option character c. *)
Ltac vxc c := cbn -[put];
  repeat match goal with |- context [lookup ?k ?E] =>
    let H := fresh "Hlk" in assert (H : lookup k E = _) by lk_prove; rewrite H; clear H end;
  cbn; rewrite (Z.mod_small c); [reflexivity | lia].

(** This tactic shows that the message of a report is one of the two. *)
Ltac msg := unfold diag_msg; first [left; eassumption | right; eassumption].

(** This tactic proves one report block. *)
Ltac diag_block :=
  let Hdom := fresh "Hdom" in let Hfp := fresh "Hfp" in let Hlend := fresh "Hlend" in
  let Hgt := fresh "Hgt" in let Hfx := fresh "Hfx" in
  match goal with H : getopt_diag_rule _ _ _ _ |- _ => destruct H as (Hdom & Hfp & Hlend & Hgt & Hfx) end;
  iIntros "#Hsl #Hsc Ha Hcl #Hs HG HK";
  let q0 := fresh "q0" in let ps' := fresh "ps" in
  match goal with Hps : ?ps <> [] |- _ => destruct ps as [|q0 ps']; [congruence|] end;
  iAssert (∃ s0, word_string DfracDiscarded q0 s0)%I as (s0) "#Hws";
  [unfold argv_strs; rewrite big_sepL_cons; iDestruct "Hs" as "[H _]"; iExact "H"|];
  iDestruct (argv_str_cap with "Hws") as (rq) "[#Hcapq %Hq0]";
  step; step;
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hsl");
    [reflexivity | vx | left; reflexivity | arith | arith | arith |];
  iNext; iIntros "_";
  iDestruct (Hlend with "HG") as (dq freg) "[Hcf HG]";
  iApply (wp_raw_load_pointer_dq with "Hsl Hsc Hcf"); [reflexivity | vx | left; reflexivity | arith | arith | exact Hfp |];
  iNext; iIntros "_ _ Hcf"; iSpecialize ("HG" with "Hcf"); step; step;
  iApply (Hgt with "HG"); [msg | vx |]; iNext; iIntros (q) "HT";
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Ha");
    [reflexivity | vx | left; reflexivity | arith | arith | arith |];
  iNext; iIntros "Ha"; iDestruct "Hcl" as "[Hc0 Hcl]";
  iApply (wp_raw_load_pointer_dq with "Ha Hc0 Hcapq"); [reflexivity | vx | left; reflexivity | arith | arith | lia |];
  iNext; iIntros "Ha Hc0 _";
  match goal with Hc : lookup (TAtom "v455") _ = Some (WInt ?c) |- _ =>
    iApply (Hfx _ _ _ _ _ _ _ _ _ _ _ _ c with "HT Hws"); [msg | assumption | vxc c |] end;
  iNext; iIntros (x) "HG"; step;
  iApply ("HK" with "[%] Ha [Hc0 Hcl] HG"); [xkeep | iFrame].

(** Each report reads the stream pointer from the global stderr, which
    the caller shares, and the program name from the first entry of the
    argument vector, which is not empty. It passes the option character
    c to the output call. The report keeps the vector and returns G. The
    unknown-option report uses the message str.148. *)
Lemma wp_getopt_diag_unknown ks e fr (G : iProp Σ) T fp dom se sereg mid c av ar ps Φ :
  avoids ks diag_names = true -> getopt_diag_rule G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v455") e = Some (WInt c) -> 0 <= c < 2 ^ 32 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 <= r_end ar -> r_end ar <= 2 ^ 48 -> ps <> [] ->
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗
  (∀ e', ⌜keeps ks e e'⌝ -∗ live av ar -∗ argv_cells av ps -∗ G -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L492") (Some (TAtom "L490")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L490") (Some fr))) : gexpr) {{ Φ }}.
Proof. intros. diag_block. Qed.

(** The missing-argument report of "-W" uses the message str.149. *)
Lemma wp_getopt_diag_wmissing ks e fr (G : iProp Σ) T fp dom se sereg mid c av ar ps Φ :
  avoids ks diag_names = true -> getopt_diag_rule G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v455") e = Some (WInt c) -> 0 <= c < 2 ^ 32 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 <= r_end ar -> r_end ar <= 2 ^ 48 -> ps <> [] ->
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗
  (∀ e', ⌜keeps ks e e'⌝ -∗ live av ar -∗ argv_cells av ps -∗ G -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L553") (Some (TAtom "L551")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L551") (Some fr))) : gexpr) {{ Φ }}.
Proof. intros. diag_block. Qed.

(** The missing-argument report of a short option uses str.149 too. *)
Lemma wp_getopt_diag_missing ks e fr (G : iProp Σ) T fp dom se sereg mid c av ar ps Φ :
  avoids ks diag_names = true -> getopt_diag_rule G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v455") e = Some (WInt c) -> 0 <= c < 2 ^ 32 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 <= r_end ar -> r_end ar <= 2 ^ 48 -> ps <> [] ->
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗
  (∀ e', ⌜keeps ks e e'⌝ -∗ live av ar -∗ argv_cells av ps -∗ G -∗
     WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L662") (Some (TAtom "L660")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L660") (Some fr))) : gexpr) {{ Φ }}.
Proof. intros. diag_block. Qed.

End diag.
