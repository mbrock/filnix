(** GNU Hello's version and help helpers through the program logic.
    The output contracts are supplied by the caller's stdio world;
    stdout remains world-owned. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run StepRules Symbolic
  ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic MemLogic
  HelloModule HelloLeaf.
Open Scope Z_scope.
Open Scope list_scope.

(** The compiled proper-name helper returns its argument unchanged. *)
Definition proper_name_fn : func := Eval vm_compute in hello_fn "proper_name".
(** Its empty entry block returns the pointer. *)
Definition proper_name_start : block := Eval vm_compute in hblk proper_name_fn "start".
(** The entry block is present in the compiled function. *)
Lemma find_proper_name_start :
  find_block (TAtom "start") (fn_blocks proper_name_fn) = Some proper_name_start.
Proof. vm_compute. reflexivity. Qed.
(** Its call frame binds the sole pointer argument. *)
Lemma proper_name_entry p : invocation proper_name_fn [WPtr p] =
  mkFrame proper_name_fn [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** The help footer prints the bug-reporting addresses. *)
Definition emit_bug_reporting_address_fn : func := Eval vm_compute in hello_fn "emit_bug_reporting_address".
(** Its single block loads stdout and makes four output calls. *)
Definition emit_bug_reporting_address_start : block := Eval vm_compute in
  hblk emit_bug_reporting_address_fn "start".
(** The footer's entry block is present. *)
Lemma find_emit_bug_reporting_address_start :
  find_block (TAtom "start") (fn_blocks emit_bug_reporting_address_fn) =
    Some emit_bug_reporting_address_start.
Proof. vm_compute. reflexivity. Qed.

(** A version-etc literal's pointer in the linked fixture. *)
Definition version_literal (s : String.string) : ptr := Eval vm_compute in
  match lookup (TAtom s) hello_globals with Some p => p | None => mkPtr 0 CNone end.

(** The four exact output argument lists in the help footer: the newline,
    bug address, home-page line, and general-help line. *)
Definition emit_output_args (stdout : ptr) : list (name * list word) :=
  [(TAtom "fputs", [WPtr (version_literal "version-etc#str.45"); WPtr stdout]);
   (TAtom "printf", [WPtr (version_literal "version-etc#str.58");
                     WPtr (version_literal "version-etc#str.59")]);
   (TAtom "printf", [WPtr (version_literal "version-etc#str.60");
                     WPtr (version_literal "version-etc#str.61");
                     WPtr (version_literal "version-etc#str.62")]);
   (TAtom "printf", [WPtr (version_literal "version-etc#str.63");
                     WPtr (version_literal "version-etc#str.64")])].

(** For promotion: reading the hidden variadic snapshot is a pure
    instruction. Its pointer is frame state, not a new heap resource.
    This equation follows [rule_inst] and [inst_step]. *)
Lemma rule_va_args ge f e ls l d off rest j cs m fuel p :
  lookup va_snapshot e = Some (WPtr p) ->
  Semantics.step ge
    (mkConfig (mkFrame f e ls None (Exec l (Let d P VaArgs [Const off] :: rest) j)) cs m fuel) =
  Next (mkConfig
    (mkFrame f (put d (WPtr (mkPtr ((ptr_addr p + off) mod 2 ^ 64) (ptr_cap p))) e)
      ls None (Exec l rest j)) cs m fuel).
Proof.
  intros Hp. apply (rule_inst ge f e ls l (Let d P VaArgs [Const off]) rest j cs m fuel
    (IContinue (put d (WPtr (mkPtr ((ptr_addr p + off) mod 2 ^ 64) (ptr_cap p))) e) ls m)).
  - cbn [inst_step fr_env fr_locals]. rewrite Hp. reflexivity.
  - apply doomed_result_continue. reflexivity.
Qed.

(** The helpers over any runtime and caller-supplied world. *)
Module HelloVersion (R : Runtime).
Module HL := HelloLeaf R.
Module ML := HL.ML.
Module SL := ML.SL.
Module LG := ML.LG.
Module L := LG.L.
Import L LG SL ML HL.

Section version.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The Iris instance uses exactly the caller's registry and world. *)
Local Instance version_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.
(** Expressions in that language. *)
Local Notation hexpr := (language.expr (nanofil_lang registry ge)).

(** For promotion: the Iris rule for [VaArgs], lifted directly from
    [rule_va_args] through [wp_pure_next]. *)
Lemma wp_va_args f e ls l d off rest j p Φ :
  lookup va_snapshot e = Some (WPtr p) ->
  ▷ WP (ERun (mkFrame f
      (put d (WPtr (mkPtr ((ptr_addr p + off) mod 2 ^ 64) (ptr_cap p))) e)
      ls None (Exec l rest j)) : hexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None
      (Exec l (Let d P VaArgs [Const off] :: rest) j)) : hexpr) {{ Φ }}.
Proof.
  intros Hp. apply (wp_pure_next registry wi ge _ _ []).
  intros m fuel. apply rule_va_args. exact Hp.
Qed.

(** For promotion: a memory-reading operation justified by the world
    interpretation, without claiming ownership of a world-owned cell.
    It is [rule_let] lifted through [wp_read_with]. *)
Lemma wp_world_let f e ls l d k o args rest j classes xs x Φ :
  general_op o = true -> op_arg_classes o k = Some classes ->
  map2_option (value_x ge e) classes args = Some xs ->
  (forall m w h, wi m w h -> op_res o k xs m = Some (OpRes (RVal x) m)) ->
  ▷ WP (ERun (mkFrame f (put d x e) ls None (Exec l rest j)) : hexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k o args :: rest) j)) : hexpr) {{ Φ }}.
Proof.
  intros Hg Hc Hargs Hop. iIntros "HK".
  iApply (wp_read_with _ _ _ emp
    (fun m => op_res o k xs m = Some (OpRes (RVal x) m)) _ _ [] with "[] [HK]").
  - iIntros (σ) "(%h & _ & %Hf) _". destruct Hf as (_ & _ & _ & Hw).
    iPureIntro. exact (Hop _ _ _ Hw).
  - intros m fuel Hm. exact (rule_let _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg Hc Hargs Hm).
  - done.
  - iNext. iIntros "_". iExact "HK".
Qed.

(** The compiled proper-name helper preserves every framed resource:
    it never dereferences the pointer or calls an external function. *)
Lemma proper_name_spec p Φ :
  ▷ Φ (Ret (WPtr p)) -∗
  WP (ERun (invocation proper_name_fn [WPtr p]) : hexpr) {{ Φ }}.
Proof.
  iIntros "HΦ". rewrite proper_name_entry.
  iApply wp_enter; [exact find_proper_name_start | reflexivity |].
  iNext. cbn [b_insts b_jump proper_name_start].
  iApply wp_ret; [reflexivity | reflexivity |]. iNext. iExact "HΦ".
Qed.

Section emit.
(** The footer links the fixture's literals, but libc supplies stdout. *)
Context (Hlinked : hello_linked ge) (stdout_cell stdout : ptr)
  (Hstdout_global : lookup (TAtom "stdout") (ge_globals ge) = Some stdout_cell).

(** The stdio world owns the stdout cell and guarantees its read, not
    an Iris piece owned by the program. *)
Context (wi_stdout : forall m w h, wi m w h ->
  access_res m (raw_address (ptr_addr stdout_cell) 0) (ptr_cap stdout_cell) 8 Read 8 = Some ok /\
  pointer_load_effects m (raw_address (ptr_addr stdout_cell) 0)
    [AuxRead; LowerResolve; AddressRead] = Some stdout).

(** The program-owned pieces containing the footer's format and string
    literals. The stdio precondition reads them through [pts_lookup];
    the world does not have to own them. *)
Context (literal_ps : list (piece * pval)).

(** Output specs supplied by the stdio package. The preconditions are
    required for these four exact calls, including the NUL-terminated
    format and string arguments; output failure cannot waive them. *)
Context (output_spec : name -> contract world)
  (Houtput_reg : forall g xs, In (g, xs) (emit_output_args stdout) -> registry g = Some (output_spec g))
  (Houtput_ret : forall g xs, In (g, xs) (emit_output_args stdout) ->
     contract_returns (output_spec g) = RClass W)
  (Houtput_abi : forall g xs d args, In (g, xs) (emit_output_args stdout) ->
     map (fun a => match a with Arg k _ => k end) args = replicate (length xs) P ->
     contract_abi (output_spec g) (CResult d W) args)
  (Houtput_pre : forall g xs m w h, In (g, xs) (emit_output_args stdout) ->
     (forall l v, (l, v) ∈ literal_ps -> h !! l = Some v) ->
     agrees m h -> wi m w h -> contract_pre (output_spec g) xs m w)
  (Houtput_frame : forall g xs r args s m w h trace values s' m' w',
     In (g, xs) (emit_output_args stdout) ->
     agrees m h -> live_disjoint m -> R.ready s m -> wi m w h ->
     M.E.invoke (output_spec g) r args xs s m w trace (CallReturn values) s' m' w' ->
     agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ wi m' w' h /\
       exists n, values = [WInt n] /\ 0 <= n < 2 ^ 32).

(** The footer's pure symbol copies find the same literal in ge. *)
Lemma emit_literal_lookup s :
  In s ["version-etc#str.43"; "version-etc#str.45"; "version-etc#str.58";
        "version-etc#str.59"; "version-etc#str.60"; "version-etc#str.61";
        "version-etc#str.62"; "version-etc#str.63"; "version-etc#str.64"] ->
  lookup (TAtom s) (ge_globals ge) = Some (version_literal s).
Proof.
  intros Hin. apply (proj1 (proj2 Hlinked)).
  repeat destruct Hin as [<- | Hin]; try contradiction; vm_compute; reflexivity.
Qed.

(** The output call is safe and returns an arbitrary canonical int,
    retaining the caller's heap and stdio interpretation on errors too. *)
Lemma wp_emit_output f e ls lab d g args rest j xs Φ :
  In (g, xs) (emit_output_args stdout) ->
  map_option (arg_x ge e) args = Some xs ->
  map (fun a => match a with Arg k _ => k end) args = replicate (length xs) P ->
  pts literal_ps -∗
  ▷ (∀ n, pts literal_ps -∗
    WP (ERun (mkFrame f (put d (WInt n) e) ls None (Exec lab rest j)) : hexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec lab (Call (CResult d W) (Global g) args :: rest) j)) : hexpr) {{ Φ }}.
Proof.
  intros Hin Hargs Hclasses. iIntros "Hps HK".
  assert (Hg : g = TAtom "fputs" \/ g = TAtom "printf").
  { unfold emit_output_args in Hin. repeat destruct Hin as [H | Hin];
      try contradiction; inversion H; auto. }
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (output_spec g) xs (pts literal_ps) with "Hps [HK]").
  - destruct Hg as [-> | ->]; apply hello_outside; try exact (proj1 Hlinked); reflexivity.
  - destruct Hg as [-> | ->]; apply (proj2 (proj2 Hlinked)); reflexivity.
  - destruct Hg as [-> | ->]; reflexivity.
  - exact (Houtput_reg _ _ Hin).
  - exact Hargs.
  - exact (Houtput_abi _ _ _ _ Hin Hclasses).
  - iIntros (σ) "(%h & Hh & %Hf) Hps". destruct Hf as (Ha & _ & _ & Hw).
    iDestruct (pts_lookup with "Hh Hps") as %Hps.
    iPureIntro. exact (Houtput_pre _ _ _ _ _ Hin Hps Ha Hw).
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) Hps".
    destruct Hf as (Ha & Hd & Hr & Hw).
    destruct (Houtput_frame _ _ _ _ _ _ _ _ _ _ _ _ _ Hin Ha Hd Hr Hw Hinv)
      as (Ha' & Hd' & Hr' & Hw' & n & -> & Hn).
    iModIntro. iExists (put d (WInt n) e). iSplit.
    + iPureIntro. unfold external_env. cbn [site_result]. rewrite (Houtput_ret _ _ Hin).
      cbn. rewrite Z.mod_small; [reflexivity | exact Hn].
    + iSplitL "Hh"; [iExists h; iFrame; iPureIntro; auto |]. iApply ("HK" with "Hps").
Qed.

(** The complete help footer, including failed and partial output:
    every stdio result is ignored and every framed resource survives. *)
Lemma emit_bug_reporting_address_spec Φ :
  pts literal_ps -∗ ▷ (pts literal_ps -∗ Φ RetVoid) -∗
  WP (ERun (invocation emit_bug_reporting_address_fn []) : hexpr) {{ Φ }}.
Proof.
  pose proof (emit_literal_lookup "version-etc#str.43" ltac:(simpl; tauto)) as H43.
  pose proof (emit_literal_lookup "version-etc#str.45" ltac:(simpl; tauto)) as H45.
  pose proof (emit_literal_lookup "version-etc#str.58" ltac:(simpl; tauto)) as H58.
  pose proof (emit_literal_lookup "version-etc#str.59" ltac:(simpl; tauto)) as H59.
  pose proof (emit_literal_lookup "version-etc#str.60" ltac:(simpl; tauto)) as H60.
  pose proof (emit_literal_lookup "version-etc#str.61" ltac:(simpl; tauto)) as H61.
  pose proof (emit_literal_lookup "version-etc#str.62" ltac:(simpl; tauto)) as H62.
  pose proof (emit_literal_lookup "version-etc#str.63" ltac:(simpl; tauto)) as H63.
  pose proof (emit_literal_lookup "version-etc#str.64" ltac:(simpl; tauto)) as H64.
  iIntros "Hps HΦ". change (invocation emit_bug_reporting_address_fn []) with
    (mkFrame emit_bug_reporting_address_fn [] [] None (Enter (TAtom "start") None)).
  iApply wp_enter; [exact find_emit_bug_reporting_address_start | reflexivity |]. iNext.
  cbn [b_insts b_jump emit_bug_reporting_address_start].
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply wp_world_let; [reflexivity | reflexivity | word_premise | |].
  { intros m w h Hw. apply op_check. exact (proj1 (wi_stdout _ _ _ Hw)). }
  iNext.
  iApply wp_world_let; [reflexivity | reflexivity | word_premise | |].
  { intros m w h Hw. apply op_raw_load_pointer; apply (wi_stdout _ _ _ Hw). }
  iNext.
  iApply (wp_emit_output with "Hps");
    [unfold emit_output_args; left; reflexivity | word_premise | reflexivity |].
  iNext. iIntros (n0) "Hps".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply (wp_emit_output with "Hps");
    [unfold emit_output_args; right; left; reflexivity | word_premise | reflexivity |].
  iNext. iIntros (n1) "Hps".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply (wp_emit_output with "Hps");
    [unfold emit_output_args; right; right; left; reflexivity | word_premise | reflexivity |].
  iNext. iIntros (n2) "Hps".
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; reflexivity |]. iNext.
  iApply (wp_emit_output with "Hps");
    [unfold emit_output_args; right; right; right; left; reflexivity | word_premise | reflexivity |].
  iNext. iIntros (n3) "Hps". iApply wp_ret_void. iNext. iApply ("HΦ" with "Hps").
Qed.

End emit.

End version.
End HelloVersion.
