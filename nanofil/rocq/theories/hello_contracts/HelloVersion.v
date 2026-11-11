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
  HelloModule HelloLeaf Identity Machine Panics.
From Nanofil Require Export VariadicLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** Keep symbolic address arithmetic folded while computing IR operands. *)
Local Arguments Z.add : simpl nomatch.
(** Keep symbolic offsets folded while computing IR operands. *)
Local Arguments Z.sub : simpl nomatch.
(** Keep symbolic scaled indices folded while computing IR operands. *)
Local Arguments Z.mul : simpl nomatch.

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

(** The array-based version helper reached by Hello's single version call. *)
Definition version_etc_arn_fn : func := Eval vm_compute in hello_fn "version_etc_arn".
(** Its entry selects the format with a command name. *)
Definition arn_start : block := Eval vm_compute in hblk version_etc_arn_fn "start".
(** The command-name version heading. *)
Definition arn_L12 : block := Eval vm_compute in hblk version_etc_arn_fn "L12".
(** The copyright and license lines precede author dispatch. *)
Definition arn_L14 : block := Eval vm_compute in hblk version_etc_arn_fn "L14".
(** The first dispatch compares the count with two. *)
Definition arn_L263 : block := Eval vm_compute in hblk version_etc_arn_fn "L263".
(** The second dispatch tests for two authors. *)
Definition arn_L267 : block := Eval vm_compute in hblk version_etc_arn_fn "L267".
(** The third dispatch tests for three authors. *)
Definition arn_L273 : block := Eval vm_compute in hblk version_etc_arn_fn "L273".
(** The last reachable dispatch tests for four authors. *)
Definition arn_L275 : block := Eval vm_compute in hblk version_etc_arn_fn "L275".
(** The four-author output reads four cells of the array. *)
Definition arn_L82 : block := Eval vm_compute in hblk version_etc_arn_fn "L82".
(** The shared return after author output. *)
Definition arn_L47 : block := Eval vm_compute in hblk version_etc_arn_fn "L47".

(** Every block on the reachable four-author path occurs in the fixture. *)
Lemma find_arn_blocks :
  Forall (fun lb => find_block (TAtom lb.1) (fn_blocks version_etc_arn_fn) = Some lb.2)
    [("start", arn_start); ("L12", arn_L12); ("L14", arn_L14); ("L263", arn_L263);
     ("L267", arn_L267); ("L273", arn_L273); ("L275", arn_L275);
     ("L82", arn_L82); ("L47", arn_L47)].
Proof. vm_compute. repeat constructor. Qed.

(** The array helper's entry for main's three heading literals and
    four authors. The count is the result the variadic loop must prove. *)
Lemma version_etc_arn_entry stream authors :
  invocation version_etc_arn_fn
    [WPtr stream; WPtr (version_literal "hello#str.70");
     WPtr (version_literal "hello#str.63"); WPtr (version_literal "hello#str.71");
     WPtr authors; WInt 4] =
  mkFrame version_etc_arn_fn
    [(TAtom "v10", WInt 4); (TAtom "v8", WPtr authors);
     (TAtom "v6", WPtr (version_literal "hello#str.71"));
     (TAtom "v4", WPtr (version_literal "hello#str.63"));
     (TAtom "v2", WPtr (version_literal "hello#str.70")); (TAtom "v0", WPtr stream)]
    [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** The six exact output calls on the four-author path; the copyright
    year is a promoted W argument, not a pointer or a 64-bit integer. *)
Definition version_output_args (stream : ptr) : list (name * list word) :=
  [(TAtom "fprintf", [WPtr stream; WPtr (version_literal "version-etc#str.41");
      WPtr (version_literal "hello#str.70"); WPtr (version_literal "hello#str.63");
      WPtr (version_literal "hello#str.71")]);
   (TAtom "fprintf", [WPtr stream; WPtr (version_literal "version_etc_copyright");
      WPtr (version_literal "version-etc#str.44"); WInt 2026]);
   (TAtom "fputs", [WPtr (version_literal "version-etc#str.45"); WPtr stream]);
   (TAtom "fprintf", [WPtr stream; WPtr (version_literal "version-etc#str.46");
      WPtr (version_literal "version-etc#str.47")]);
   (TAtom "fputs", [WPtr (version_literal "version-etc#str.45"); WPtr stream]);
   (TAtom "fprintf", [WPtr stream; WPtr (version_literal "version-etc#str.51");
      WPtr (version_literal "hello#str.72"); WPtr (version_literal "hello#str.73");
      WPtr (version_literal "hello#str.74"); WPtr (version_literal "hello#str.75")])].

(** The promoted classes at these output sites: pointers and int words. *)
Definition version_output_classes (xs : list word) : list class :=
  (fun x => match x with WPtr _ => P | _ => W end) <$> xs.

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

(** The helpers over any runtime and caller-supplied world. *)
Module HelloVersionOn (R : Runtime) (LG0 : LogicSig R).
Module HL := HelloLeafOn R LG0.
Module ML := HL.ML.
Module SL := ML.SL.
Module LG := ML.LG.
Module L := LG.L.
Module VL := VariadicLogicOn R LG0.
Import L LG SL ML HL VL.

Section version.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The Iris instance uses exactly the caller's registry and world. *)
Local Instance version_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.
(** Expressions in that language. *)
Local Notation hexpr := (language.expr (nanofil_lang registry ge)).

(** For promotion: a pointer load can return a read-only literal.
    Its life comes from the caller's existing pieces rather than a new
    token. This lifts [rule_let] and [op_raw_load_pointer] through
    [wp_read_with], and preserves those pieces. *)
Lemma wp_raw_load_literal f e ls l d off args rest j classes p b reg o x xb xr ps Φ :
  op_arg_classes (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) P = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o -> (b + o) mod 8 = 0 ->
  0 <= ptr_addr x < 2 ^ 64 -> ptr_cap x = Ro xb -> (PLive xb, VLive xr) ∈ ps ->
  live b reg -∗ pcell b o x -∗ pts ps -∗
  ▷ (live b reg -∗ pcell b o x -∗ pts ps -∗
    WP (ERun (mkFrame f (put d (WPtr x) e) ls None (Exec l rest j)) : hexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec l (Let d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) args :: rest) j))
    : hexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp Ha Hal Hrange Hcap Hmember. iIntros "Hl Hc Hps HK".
  iApply (wp_read_with registry wi ge (live b reg ∗ pcell b o x ∗ pts ps)
    (fun m => live_at m b reg /\ agree_piece m (PAux b o) (VAux (ptr_cap x)) /\
      all_agree m (cell b o (ptr_addr x)) /\ live_at m xb xr)
    _ _ [] with "[$Hl $Hc $Hps] [HK]").
  - iIntros (σ) "Hσ (Hl & Hc & Hps)".
    iDestruct (pts_facts with "Hσ Hl") as %([Hlv _] & _).
    iDestruct (pts_facts with "Hσ Hc") as %([Hax Hcl] & _).
    iDestruct (pts_facts with "Hσ Hps") as %(Hps & _).
    pose proof (all_agree_elem _ _ _ _ Hps Hmember) as Htarget. iPureIntro. auto.
  - intros m fuel (Hlv & Hax & Hcl & Htarget).
    destruct (cell_bounds _ _ _ _ _ Hlv Hcl) as [Ho He].
    apply rule_let with (classes := classes) (xs := [WPtr p]);
      [reflexivity | exact Hc | exact Hx |].
    apply op_raw_load_pointer.
    + rewrite Hp Ha. apply (access_obj _ _ reg); [exact (proj1 Hlv) | lia | lia | exact Hal].
    + rewrite pointer_load_plain Ha (cell_load m b reg o (ptr_addr x) (b + o) Hlv Hcl eq_refl).
      rewrite Z.mod_small; [|exact Hrange]. unfold aux_at.
      pose proof (aux_piece_holds _ _ _ _ _ Hlv Hax) as Haux. rewrite Hcap in Haux.
      rewrite (aux_holds_ro _ _ _ _ Haux Htarget). rewrite <- Hcap. destruct x. reflexivity.
  - iNext. iIntros "(Hl & Hc & Hps)". iApply ("HK" with "Hl Hc Hps").
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

Section arn.
(** The reachable version path uses the linked heading, author, and
    format literals; the stream itself belongs to the stdio world. *)
Context (Hlinked : hello_linked ge) (stream : ptr) (literal_ps : list (piece * pval)).

(** The existing literal resources include each author's live object;
    this prevents the collector from rewriting its read-only capability. *)
Context (author_reg : String.string -> region)
  (Hauthor_live : forall s, In s ["hello#str.72"; "hello#str.73"; "hello#str.74"; "hello#str.75"] ->
    (PLive (ptr_addr (version_literal s)), VLive (author_reg s)) ∈ literal_ps).

(** The four initialized array cells that the counting loop passes on. *)
Definition version_author_cells (b : Z) : iProp Σ :=
  pcell b 0 (version_literal "hello#str.72") ∗
  pcell b 8 (version_literal "hello#str.73") ∗
  pcell b 16 (version_literal "hello#str.74") ∗
  pcell b 24 (version_literal "hello#str.75").

(** The pure literal copies in the reachable array helper are linked. *)
Lemma arn_literal_lookup s :
  In s ["version-etc#str.41"; "version_etc_copyright"; "version-etc#str.43";
    "version-etc#str.44"; "version-etc#str.45"; "version-etc#str.46";
    "version-etc#str.47"; "version-etc#str.51"] ->
  lookup (TAtom s) (ge_globals ge) = Some (version_literal s).
Proof.
  intros Hin. apply (proj1 (proj2 Hlinked)).
  repeat destruct Hin as [<- | Hin]; try contradiction; vm_compute; reflexivity.
Qed.

(** Advance one memory-independent IR let on the fixed version path. *)
Local Ltac version_let :=
  iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |];
  iNext; gen_env.

(** These are the stdio contracts for the six exact version calls.
    The mixed pointer/int classes are checked before any output result;
    partial output and negative results retain the caller's resources. *)
Context (version_spec : name -> contract world)
  (Hversion_reg : forall g xs, In (g, xs) (version_output_args stream) -> registry g = Some (version_spec g))
  (Hversion_ret : forall g xs, In (g, xs) (version_output_args stream) ->
    contract_returns (version_spec g) = RClass W)
  (Hversion_abi : forall g xs d args, In (g, xs) (version_output_args stream) ->
    map (fun a => match a with Arg k _ => k end) args = version_output_classes xs ->
    contract_abi (version_spec g) (CResult d W) args)
  (Hversion_pre : forall g xs m w h, In (g, xs) (version_output_args stream) ->
    (forall l v, (l, v) ∈ literal_ps -> h !! l = Some v) ->
    agrees m h -> wi m w h -> contract_pre (version_spec g) xs m w)
  (Hversion_frame : forall g xs r args s m w h trace values s' m' w',
    In (g, xs) (version_output_args stream) ->
    agrees m h -> live_disjoint m -> R.ready s m -> wi m w h ->
    M.E.invoke (version_spec g) r args xs s m w trace (CallReturn values) s' m' w' ->
    agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ wi m' w' h /\
      exists n, values = [WInt n] /\ 0 <= n < 2 ^ 32).

(** The reachable version calls preserve their literals and ignore
    every canonical int result, including negative and partial output. *)
Lemma wp_version_output f e ls lab d g args rest j xs Φ :
  In (g, xs) (version_output_args stream) ->
  map_option (arg_x ge e) args = Some xs ->
  map (fun a => match a with Arg k _ => k end) args = version_output_classes xs ->
  pts literal_ps -∗
  ▷ (∀ n, pts literal_ps -∗
    WP (ERun (mkFrame f (put d (WInt n) e) ls None (Exec lab rest j)) : hexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
    (Exec lab (Call (CResult d W) (Global g) args :: rest) j)) : hexpr) {{ Φ }}.
Proof.
  intros Hin Hargs Hclasses. iIntros "Hps HK".
  assert (Hg : g = TAtom "fputs" \/ g = TAtom "fprintf").
  { unfold version_output_args in Hin. repeat destruct Hin as [H | Hin];
      try contradiction; inversion H; auto. }
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (version_spec g) xs (pts literal_ps) with "Hps [HK]").
  - destruct Hg as [-> | ->]; apply hello_outside; try exact (proj1 Hlinked); reflexivity.
  - destruct Hg as [-> | ->]; apply (proj2 (proj2 Hlinked)); reflexivity.
  - destruct Hg as [-> | ->]; reflexivity.
  - exact (Hversion_reg _ _ Hin).
  - exact Hargs.
  - exact (Hversion_abi _ _ _ _ Hin Hclasses).
  - iIntros (σ) "(%h & Hh & %Hf) Hps". destruct Hf as (Ha & _ & _ & Hw).
    iDestruct (pts_lookup with "Hh Hps") as %Hps.
    iPureIntro. exact (Hversion_pre _ _ _ _ _ Hin Hps Ha Hw).
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) Hps".
    destruct Hf as (Ha & Hd & Hr & Hw).
    destruct (Hversion_frame _ _ _ _ _ _ _ _ _ _ _ _ _ Hin Ha Hd Hr Hw Hinv)
      as (Ha' & Hd' & Hr' & Hw' & n & -> & Hn).
    iModIntro. iExists (put d (WInt n) e). iSplit.
    + iPureIntro. unfold external_env. cbn [site_result]. rewrite (Hversion_ret _ _ Hin).
      cbn. rewrite Z.mod_small; [reflexivity | exact Hn].
    + iSplitL "Hh"; [iExists h; iFrame; iPureIntro; auto |]. iApply ("HK" with "Hps").
Qed.

(** The reachable array helper prints the heading and four authors,
    preserving the array and literal resources for every stdio result.
    Its fixed count is discharged by [version_etc_va], not assumed by main. *)
Lemma version_etc_arn_spec b Φ :
  0 < b -> b mod 16 = 0 -> b + 80 <= 2 ^ 48 ->
  pts literal_ps -∗ live b (mkRegion b (b + 80) Heap Live) -∗ version_author_cells b -∗
  ▷ (pts literal_ps -∗ live b (mkRegion b (b + 80) Heap Live) -∗
    version_author_cells b -∗ Φ RetVoid) -∗
  WP (ERun (invocation version_etc_arn_fn
    [WPtr stream; WPtr (version_literal "hello#str.70");
     WPtr (version_literal "hello#str.63"); WPtr (version_literal "hello#str.71");
     WPtr (mkPtr b (Obj b)); WInt 4]) : hexpr) {{ Φ }}.
Proof.
  intros Hb Hmod Hend.
  assert (Hmod8 : b mod 8 = 0).
  { apply Z.mod_divide; [lia |]. apply (Z.divide_trans 8 16 b).
    - exists 2. reflexivity.
    - apply Z.mod_divide; [lia | exact Hmod]. }
  pose proof (arn_literal_lookup "version-etc#str.41" ltac:(simpl; tauto)) as H41.
  pose proof (arn_literal_lookup "version_etc_copyright" ltac:(simpl; tauto)) as Hcopyright.
  pose proof (arn_literal_lookup "version-etc#str.43" ltac:(simpl; tauto)) as H43.
  pose proof (arn_literal_lookup "version-etc#str.44" ltac:(simpl; tauto)) as H44.
  pose proof (arn_literal_lookup "version-etc#str.45" ltac:(simpl; tauto)) as H45.
  pose proof (arn_literal_lookup "version-etc#str.46" ltac:(simpl; tauto)) as H46.
  pose proof (arn_literal_lookup "version-etc#str.47" ltac:(simpl; tauto)) as H47.
  pose proof (arn_literal_lookup "version-etc#str.51" ltac:(simpl; tauto)) as H51.
  iIntros "Hps Hl (H0 & H1 & H2 & H3) HΦ". rewrite version_etc_arn_entry.
  set (e := [(TAtom "v10", WInt 4); (TAtom "v8", WPtr (mkPtr b (Obj b)));
    (TAtom "v6", WPtr (version_literal "hello#str.71"));
    (TAtom "v4", WPtr (version_literal "hello#str.63"));
    (TAtom "v2", WPtr (version_literal "hello#str.70")); (TAtom "v0", WPtr stream)]).
  assert (Hv0 : lookup (TAtom "v0") e = Some (WPtr stream)) by reflexivity.
  assert (Hv2 : lookup (TAtom "v2") e = Some (WPtr (version_literal "hello#str.70"))) by reflexivity.
  assert (Hv4 : lookup (TAtom "v4") e = Some (WPtr (version_literal "hello#str.63"))) by reflexivity.
  assert (Hv6 : lookup (TAtom "v6") e = Some (WPtr (version_literal "hello#str.71"))) by reflexivity.
  assert (Hv8 : lookup (TAtom "v8") e = Some (WPtr (mkPtr b (Obj b)))) by reflexivity.
  assert (Hv10 : lookup (TAtom "v10") e = Some (WInt 4)) by reflexivity.
  clearbody e.
  iApply wp_enter; [vm_compute; reflexivity | reflexivity |]. iNext.
  cbn [b_insts b_jump arn_start]. version_let. version_let.
  iApply wp_branch; [word_premise |]. iNext. cbn [Z.eqb edge_label].
  iApply wp_enter; [vm_compute; reflexivity | reflexivity |]. iNext.
  cbn [b_insts b_jump arn_L12]. version_let.
  iApply (wp_version_output with "Hps");
    [unfold version_output_args; left; reflexivity | word_premise | reflexivity |].
  iNext. iIntros (n0) "Hps". gen_env. iApply wp_goto. iNext.
  iApply wp_enter; [vm_compute; reflexivity | reflexivity |]. iNext.
  cbn [b_insts b_jump arn_L14]. version_let. version_let. version_let.
  iApply (wp_version_output with "Hps");
    [unfold version_output_args; right; left; reflexivity | word_premise | reflexivity |].
  iNext. iIntros (n1) "Hps". gen_env. version_let.
  iApply (wp_version_output with "Hps");
    [unfold version_output_args; right; right; left; reflexivity | word_premise | reflexivity |].
  iNext. iIntros (n2) "Hps". gen_env. version_let. version_let. version_let.
  iApply (wp_version_output with "Hps");
    [unfold version_output_args; right; right; right; left; reflexivity | word_premise | reflexivity |].
  iNext. iIntros (n3) "Hps". gen_env. version_let.
  iApply (wp_version_output with "Hps");
    [unfold version_output_args; right; right; right; right; left; reflexivity | word_premise | reflexivity |].
  iNext. iIntros (n4) "Hps". gen_env. version_let.
  iApply wp_branch; [word_premise |]. iNext. cbn [Z.eqb edge_label].
  iApply wp_enter; [vm_compute; reflexivity | reflexivity |]. iNext.
  cbn [b_insts b_jump arn_L263]. version_let.
  iApply wp_branch; [word_premise |]. iNext. cbn [Z.eqb edge_label].
  iApply wp_enter; [vm_compute; reflexivity | reflexivity |]. iNext.
  cbn [b_insts b_jump arn_L267]. version_let.
  iApply wp_branch; [word_premise |]. iNext. cbn [Z.eqb edge_label].
  iApply wp_enter; [vm_compute; reflexivity | reflexivity |]. iNext.
  cbn [b_insts b_jump arn_L273]. version_let.
  iApply wp_branch; [word_premise |]. iNext. cbn [Z.eqb edge_label].
  iApply wp_enter; [vm_compute; reflexivity | reflexivity |]. iNext.
  cbn [b_insts b_jump arn_L275]. version_let.
  iApply wp_branch; [word_premise |]. iNext. cbn [Z.eqb edge_label].
  iApply wp_enter; [vm_compute; reflexivity | reflexivity |]. iNext.
  cbn [b_insts b_jump arn_L82]. version_let. version_let.
  iApply (wp_check with "Hl");
    [reflexivity | word_premise | reflexivity | addr_premise | cbn [r_end]; addr_premise | addr_premise |].
  iNext. iIntros "Hl". gen_env.
  iApply (wp_raw_load_literal with "Hl H0 Hps");
    [reflexivity | word_premise | reflexivity | addr_premise | addr_premise |
     vm_compute; split; congruence | vm_compute; reflexivity |
     apply (Hauthor_live "hello#str.72"); simpl; tauto |].
  iNext. iIntros "Hl H0 Hps". gen_env.
  iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (b + 8));
    [word_premise | cbn; f_equal; f_equal; addr_premise | word_premise |]. iNext. gen_env.
  iApply (wp_half_check with "Hl");
    [reflexivity | word_premise | reflexivity | reflexivity | addr_premise |
     cbn [r_end]; addr_premise | lia | cbn; lia | addr_premise |]. iNext. iIntros "Hl". gen_env.
  iApply (wp_raw_load_literal with "Hl H1 Hps");
    [reflexivity | word_premise | reflexivity | addr_premise | addr_premise |
     vm_compute; split; congruence | vm_compute; reflexivity |
     apply (Hauthor_live "hello#str.73"); simpl; tauto |].
  iNext. iIntros "Hl H1 Hps". gen_env.
  iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (b + 16));
    [word_premise | cbn; f_equal; f_equal; addr_premise | word_premise |]. iNext. gen_env.
  iApply (wp_half_check with "Hl");
    [reflexivity | word_premise | reflexivity | reflexivity | addr_premise |
     cbn [r_end]; addr_premise | lia | cbn; lia | addr_premise |]. iNext. iIntros "Hl". gen_env.
  iApply (wp_raw_load_literal with "Hl H2 Hps");
    [reflexivity | word_premise | reflexivity | addr_premise | addr_premise |
     vm_compute; split; congruence | vm_compute; reflexivity |
     apply (Hauthor_live "hello#str.74"); simpl; tauto |].
  iNext. iIntros "Hl H2 Hps". gen_env.
  iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (b + 24));
    [word_premise | cbn; f_equal; f_equal; addr_premise | word_premise |]. iNext. gen_env.
  iApply (wp_half_check with "Hl");
    [reflexivity | word_premise | reflexivity | reflexivity | addr_premise |
     cbn [r_end]; addr_premise | lia | cbn; lia | addr_premise |]. iNext. iIntros "Hl". gen_env.
  iApply (wp_raw_load_literal with "Hl H3 Hps");
    [reflexivity | word_premise | reflexivity | addr_premise | addr_premise |
     vm_compute; split; congruence | vm_compute; reflexivity |
     apply (Hauthor_live "hello#str.75"); simpl; tauto |].
  iNext. iIntros "Hl H3 Hps". gen_env.
  iApply (wp_version_output with "Hps");
    [unfold version_output_args; right; right; right; right; right; left; reflexivity |
     word_premise | reflexivity |].
  iNext. iIntros (n5) "Hps". iApply wp_goto. iNext.
  iApply wp_enter; [vm_compute; reflexivity | reflexivity |]. iNext.
  cbn [b_insts b_jump arn_L47]. iApply wp_ret_void. iNext.
  iApply ("HΦ" with "Hps Hl [H0 H1 H2 H3]"). rewrite /version_author_cells. iFrame.
Qed.

(** The variadic counting helper in the linked program. *)
Definition version_etc_va_fn : func := Eval vm_compute in hello_fn "version_etc_va".
(** The allocation block of the counting helper. *)
Definition va_start : block := Eval vm_compute in hblk version_etc_va_fn "start".
(** The loop header binds the current author count. *)
Definition va_L12 : block := Eval vm_compute in hblk version_etc_va_fn "L12".
(** The loop body consumes and stores one variadic pointer. *)
Definition va_L18 : block := Eval vm_compute in hblk version_etc_va_fn "L18".
(** The null test selects another iteration or the array helper. *)
Definition va_L19 : block := Eval vm_compute in hblk version_etc_va_fn "L19".
(** The back edge increments the count of non-null authors. *)
Definition va_L14 : block := Eval vm_compute in hblk version_etc_va_fn "L14".
(** The exit block passes the derived count to the array helper. *)
Definition va_L15 : block := Eval vm_compute in hblk version_etc_va_fn "L15".

(** Split off one zero pointer cell without expanding the rest of its
    allocation into individually searched heap pieces: VariadicLogic's
    [zero_cell_prefix] over [bytes] and [auxes]. *)
Lemma version_zero_cell_prefix b o n :
  bytes b o (replicate (8 + n) 0) -∗ auxes b o (replicate (8 + n) CNone) -∗
  pcell b o null ∗ bytes b (o + 8) (replicate n 0) ∗ auxes b (o + 8) (replicate n CNone).
Proof. exact (zero_cell_prefix b o n). Qed.

(** Five zero cells suffice for the four authors and their terminator;
    the rest of the allocated array is unused. *)
Lemma version_array_zero b :
  obj b (heap_req 8 80) -∗ live b (mkRegion b (b + 80) Heap Live) ∗
    pcell b 0 null ∗ pcell b 8 null ∗ pcell b 16 null ∗ pcell b 24 null ∗ pcell b 32 null.
Proof.
  iIntros "Hobj". iDestruct (obj_zero_block with "Hobj") as "(Hl & Hx & Ha)";
    [compute; discriminate |].
  iSplitL "Hl"; [iExact "Hl" |].
  iDestruct (version_zero_cell_prefix b 0 72 with "Hx Ha") as "(H0 & Hx & Ha)".
  iDestruct (version_zero_cell_prefix b 8 64 with "Hx Ha") as "(H1 & Hx & Ha)".
  iDestruct (version_zero_cell_prefix b 16 56 with "Hx Ha") as "(H2 & Hx & Ha)".
  iDestruct (version_zero_cell_prefix b 24 48 with "Hx Ha") as "(H3 & Hx & Ha)".
  iDestruct (version_zero_cell_prefix b 32 40 with "Hx Ha") as "(H4 & _ & _)".
  iFrame "H0 H1 H2 H3 H4".
Qed.

(** The entry binds the heading literals and the caller's va_list. *)
Lemma version_etc_va_entry cb :
  invocation version_etc_va_fn
    [WPtr stream; WPtr (version_literal "hello#str.70");
     WPtr (version_literal "hello#str.63"); WPtr (version_literal "hello#str.71");
     WPtr (mkPtr cb (Obj cb))] =
  mkFrame version_etc_va_fn
    [(TAtom "v8", WPtr (mkPtr cb (Obj cb)));
     (TAtom "v6", WPtr (version_literal "hello#str.71"));
     (TAtom "v4", WPtr (version_literal "hello#str.63"));
     (TAtom "v2", WPtr (version_literal "hello#str.70")); (TAtom "v0", WPtr stream)]
    [] None (Enter (TAtom "start") None).
Proof. reflexivity. Qed.

(** Program-local allocations preserve the caller's opaque world. *)
Context (Kversion_alloc : forall size m wd h base,
  In size [24; 80] -> fresh m (heap_req 8 size) base -> wi m wd h ->
  wi (allocated m (heap_req 8 size) base) wd
    (overwrite (obj_ps base (heap_req 8 size)) h)).

(** Storing a pointer in an owned program cell preserves that world;
    no ownership of the output stream is introduced. *)
Context (Kversion_store : forall b reg o x xp m wd h,
  (forall k v, (k, v) ∈ [(PLive b, VLive reg)] ++
    (PAux b o, VAux (ptr_cap x)) :: cell b o (ptr_addr x) -> h !! k = Some v) ->
  wi m wd h ->
  wi (store_bytes (store_aux m (b + o) (ptr_cap xp)) (b + o) 8 (ptr_addr xp)) wd
    (overwrite ([(PLive b, VLive reg)] ++
      (PAux b o, VAux (ptr_cap xp)) :: cell b o (ptr_addr xp)) h)).

(** Advancing an owned va_list cursor preserves the caller's world. *)
Context (Kversion_cursor : forall cb cr sb off m wd h,
  (forall k v, (k, v) ∈ va_cursor_ps cb cr (mkPtr (sb + off) (Ro sb)) ->
    h !! k = Some v) -> wi m wd h ->
  wi (store_bytes m cb 8 (sb + off + 8)) wd
    (overwrite (va_cursor_ps cb cr (mkPtr (sb + off + 8) (Ro sb))) h)).

(** The heading, cursor and array registers survive every loop round. *)
Definition version_va_saved e cb b : Prop :=
  lookup (TAtom "v0") e = Some (WPtr stream) /\
  lookup (TAtom "v2") e = Some (WPtr (version_literal "hello#str.70")) /\
  lookup (TAtom "v4") e = Some (WPtr (version_literal "hello#str.63")) /\
  lookup (TAtom "v6") e = Some (WPtr (version_literal "hello#str.71")) /\
  lookup (TAtom "v8") e = Some (WPtr (mkPtr cb (Obj cb))) /\
  lookup (TAtom "v11") e = Some (WPtr (mkPtr b (Obj b))).

(** The common loop body begins after the scalar index and flight. *)
Definition va_read_body : list inst := Eval vm_compute in skipn 2 (b_insts va_L18).

(** Check the non-null body once, with an abstract incoming and outgoing
    environment, rather than expanding its proof at every author. *)
Lemma version_va_round_step e i cb cr sb sr off b o x Φ :
  version_va_saved e cb b -> lookup (TAtom "pr.1") e = Some (WInt i) ->
  lookup (TAtom "v22") e = Some (WPtr (mkPtr (b + o) (Obj b))) ->
  0 <= i < 4 -> cb mod 8 = 0 -> 0 < sb -> 0 <= off ->
  sb + off + 8 <= r_end sr -> r_end sr <= 2 ^ 48 -> (sb + off) mod 8 = 0 ->
  0 < b -> 0 <= o -> o + 8 <= 80 -> b + 80 <= 2 ^ 48 -> (b + o) mod 8 = 0 ->
  0 < ptr_addr x < 2 ^ 64 ->
  (ptr_cap x = CNone \/ exists xb xr,
    (ptr_cap x = Obj xb \/ ptr_cap x = Ro xb) /\ (PLive xb, VLive xr) ∈ literal_ps) ->
  pts literal_ps -∗ pts (va_cursor_ps cb cr (mkPtr (sb + off) (Ro sb))) -∗
  live sb sr -∗ pcell sb off x -∗
  live b (mkRegion b (b + 80) Heap Live) -∗ pcell b o null -∗
  ▷ (∀ e', ⌜version_va_saved e' cb b /\ lookup (TAtom "v31") e' = Some (WInt (i + 1))⌝ -∗
    pts literal_ps -∗ pts (va_cursor_ps cb cr (mkPtr (sb + off + 8) (Ro sb))) -∗
    live sb sr -∗ pcell sb off x -∗
    live b (mkRegion b (b + 80) Heap Live) -∗ pcell b o x -∗
    WP (ERun (mkFrame version_etc_va_fn e' [] None
      (Exec (TAtom "L14") [] (JGoto (Poll (TAtom "L12"))))) : hexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame version_etc_va_fn e [] None
    (Exec (TAtom "L18") va_read_body (JGoto (To (TAtom "L19"))))) : hexpr) {{ Φ }}.
Proof.
  intros Hsaved Hcount Hflight Hi Hcb Hsb Hoff Hsend Hsmax Hsal Hb Ho Hoend Hbend Hbal Hx Htarget.
  destruct Hsaved as (Hv0 & Hv2 & Hv4 & Hv6 & Hv8 & Hv11).
  assert (Hxmod : ptr_addr x mod 2 ^ 64 = ptr_addr x) by (apply Z.mod_small; lia).
  assert (Hxne : (ptr_addr x =? 0) = false) by (apply Z.eqb_neq; lia).
  iIntros "Hps Hcursor Hsl Hsource Hl Hdest HK". cbn [va_read_body].
  iApply (wp_va_arg_pointer with "Hcursor Hsl Hsource Hps");
    [word_premise | exact Hcb | exact Hsb | exact Hoff | exact Hsend | exact Hsmax |
     exact Hsal | lia | exact Htarget | apply Kversion_cursor |].
  iNext. iIntros "Hcursor Hsl Hsource Hps". gen_env.
  iApply (wp_check with "Hl");
    [reflexivity | word_premise | reflexivity | addr_premise |
     cbn [r_end]; addr_premise | addr_premise |]. iNext. iIntros "Hl". gen_env.
  iApply (wp_raw_store_pointer with "Hl Hdest");
    [word_premise | word_premise | reflexivity | addr_premise | addr_premise |
     apply Kversion_store |]. iNext. iIntros "Hl Hdest".
  version_let. rewrite ?Hxmod. gen_env.
  version_let. gen_env.
  version_let. rewrite ?Hxmod ?Hxne. gen_env.
  iApply wp_goto. iNext.
  iApply wp_enter; [vm_compute; reflexivity | word_premise |]. iNext. gen_env.
  cbn [b_insts b_jump va_L19].
  iApply wp_branch; [word_premise |]. iNext. cbn [Z.eqb edge_label].
  iApply wp_enter; [vm_compute; reflexivity | reflexivity |]. iNext.
  cbn [b_insts b_jump va_L14]. version_let. gen_env.
  iApply ("HK" with "[%] Hps Hcursor Hsl Hsource Hl Hdest").
  split; [unfold version_va_saved; repeat split; word_premise | word_premise].
Qed.

(** Select the concrete index, then reuse the opaque non-null body. *)
Local Ltac version_va_round addr src dst text :=
  iRename src into "Hsource"; iRename dst into "Hdest";
  iApply wp_goto; iNext;
  iApply wp_enter; [vm_compute; reflexivity | word_premise |]; iNext; gen_env;
  cbn [b_insts b_jump va_L12]; version_let; gen_env;
  iApply wp_branch; [word_premise |]; iNext; cbn [Z.eqb edge_label];
  iApply wp_enter; [vm_compute; reflexivity | reflexivity |]; iNext;
  cbn [b_insts b_jump va_L18]; version_let; gen_env;
  iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ addr);
    [word_premise | cbn; f_equal; f_equal; addr_premise | word_premise |]; iNext; gen_env;
  iApply (version_va_round_step with "Hps Hcursor Hsl Hsource Hl Hdest");
    [unfold version_va_saved; repeat split; word_premise | word_premise |
     repeat progress (cbn -[load_bytes store_bytes]; use_facts_goal);
       repeat (f_equal; try lia) |
     vm_compute; split; congruence | assumption | assumption | lia | lia | assumption |
     addr_premise | assumption | lia | lia | assumption | addr_premise |
     vm_compute; split; congruence |
     right; exists (ptr_addr (version_literal text)), (author_reg text);
       split; [right; vm_compute; reflexivity | apply Hauthor_live; simpl; tauto] |];
  iNext; iIntros (e' Hsaved) "Hps Hcursor Hsl Hsource Hl Hdest";
  match goal with
  | H : version_va_saved _ _ _ /\ _ |- _ => destruct H as ((? & ? & ? & ? & ? & ?) & ?)
  end;
  iRename "Hsource" into src; iRename "Hdest" into dst.

(** The counting loop reads four literal authors and the actual null
    terminator, then calls the array helper with the derived count four.
    It returns the caller's literals, snapshot cells, and advanced cursor. *)
Lemma version_etc_va_spec cb cr sb sr Φ :
  cb mod 8 = 0 -> 0 < sb -> sb mod 16 = 0 ->
  sb + 72 <= r_end sr -> r_end sr <= 2 ^ 48 ->
  pts literal_ps -∗ pts (va_cursor_ps cb cr (mkPtr (sb + 32) (Ro sb))) -∗
  live sb sr -∗
  pcell sb 32 (version_literal "hello#str.72") -∗
  pcell sb 40 (version_literal "hello#str.73") -∗
  pcell sb 48 (version_literal "hello#str.74") -∗
  pcell sb 56 (version_literal "hello#str.75") -∗ pcell sb 64 null -∗
  ▷ (pts literal_ps -∗ pts (va_cursor_ps cb cr (mkPtr (sb + 72) (Ro sb))) -∗
    live sb sr -∗
    pcell sb 32 (version_literal "hello#str.72") -∗
    pcell sb 40 (version_literal "hello#str.73") -∗
    pcell sb 48 (version_literal "hello#str.74") -∗
    pcell sb 56 (version_literal "hello#str.75") -∗ pcell sb 64 null -∗ Φ RetVoid) -∗
  WP (ERun (invocation version_etc_va_fn
    [WPtr stream; WPtr (version_literal "hello#str.70");
     WPtr (version_literal "hello#str.63"); WPtr (version_literal "hello#str.71");
     WPtr (mkPtr cb (Obj cb))]) : hexpr) {{ Φ }}.
Proof.
  intros Hcb Hsb Hsmod Hsend Hsmax.
  assert (Hs8 : sb mod 8 = 0).
  { apply Z.mod_divide; [lia |]. apply (Z.divide_trans 8 16 sb).
    - exists 2. reflexivity.
    - apply Z.mod_divide; [lia | exact Hsmod]. }
  iIntros "Hps Hcursor Hsl Hs0 Hs1 Hs2 Hs3 Hs4 HK".
  rewrite version_etc_va_entry.
  iApply wp_enter; [vm_compute; reflexivity | reflexivity |]. iNext.
  cbn [b_insts b_jump va_start].
  iApply (wp_alloc _ _ _ _ _ _ _ _ _ _ _ _ _ 80);
    [reflexivity | lia | unfold max_allocation_size; lia |
     intros m wd h base Hf Hw; apply Kversion_alloc; [simpl; tauto | exact Hf | exact Hw] |].
  iNext. iIntros (b [Hb [Hbmod Hbend]]) "Hobj".
  change (b mod 16 = 0) in Hbmod. change (b + 80 <= 2 ^ 48) in Hbend.
  assert (Hb8 : b mod 8 = 0).
  { apply Z.mod_divide; [lia |]. apply (Z.divide_trans 8 16 b).
    - exists 2. reflexivity.
    - apply Z.mod_divide; [lia | exact Hbmod]. }
  iDestruct (version_array_zero with "Hobj") as "(Hl & H0 & H1 & H2 & H3 & H4)".
  assert (H40 : sb + 32 + 8 = sb + 40) by lia.
  assert (H48 : sb + 40 + 8 = sb + 48) by lia.
  assert (H56 : sb + 48 + 8 = sb + 56) by lia.
  assert (H64 : sb + 56 + 8 = sb + 64) by lia.
  version_va_round b "Hs0" "H0" "hello#str.72".
  iEval (rewrite H40) in "Hcursor".
  version_va_round (b + 8) "Hs1" "H1" "hello#str.73".
  iEval (rewrite H48) in "Hcursor".
  version_va_round (b + 16) "Hs2" "H2" "hello#str.74".
  iEval (rewrite H56) in "Hcursor".
  version_va_round (b + 24) "Hs3" "H3" "hello#str.75".
  iEval (rewrite H64) in "Hcursor".
  iApply wp_goto. iNext.
  iApply wp_enter; [vm_compute; reflexivity | word_premise |]. iNext. gen_env.
  cbn [b_insts b_jump va_L12]. version_let. gen_env.
  iApply wp_branch; [word_premise |]. iNext. cbn [Z.eqb edge_label].
  iApply wp_enter; [vm_compute; reflexivity | reflexivity |]. iNext.
  cbn [b_insts b_jump va_L18]. version_let. gen_env.
  iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (b + 32));
    [word_premise | cbn; f_equal; f_equal; addr_premise | word_premise |]. iNext. gen_env.
  iApply (wp_va_arg_pointer with "Hcursor Hsl Hs4 Hps");
    [word_premise | exact Hcb | exact Hsb | lia | lia | exact Hsmax |
     addr_premise | vm_compute; split; congruence | left; reflexivity | apply Kversion_cursor |].
    iNext. iIntros "Hcursor Hsl Hs4 Hps". gen_env.
    iApply (wp_check with "Hl");
      [reflexivity | word_premise | reflexivity | addr_premise |
       cbn [r_end]; addr_premise | addr_premise |]. iNext. iIntros "Hl". gen_env.
    iApply (wp_raw_store_pointer with "Hl H4");
      [word_premise | word_premise | reflexivity | addr_premise | addr_premise |
       apply Kversion_store |]. iNext. iIntros "Hl H4".
    version_let. gen_env. version_let. gen_env. version_let. gen_env.
    iApply wp_goto. iNext.
    iApply wp_enter; [vm_compute; reflexivity | word_premise |]. iNext. gen_env.
    cbn [b_insts b_jump va_L19].
    iApply wp_branch; [word_premise |]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [vm_compute; reflexivity | reflexivity |]. iNext.
    cbn [b_insts b_jump va_L15].
    iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ version_etc_arn_fn
      (invocation version_etc_arn_fn
        [WPtr stream; WPtr (version_literal "hello#str.70");
         WPtr (version_literal "hello#str.63"); WPtr (version_literal "hello#str.71");
         WPtr (mkPtr b (Obj b)); WInt 4]));
      [word_premise | unfold find_fn; rewrite (proj1 Hlinked); vm_compute; reflexivity | reflexivity |].
    iNext. iApply (version_etc_arn_spec with "Hps Hl [H0 H1 H2 H3]");
      [exact Hb | exact Hbmod | exact Hbend |
       rewrite /version_author_cells; iFrame |].
    iNext. iIntros "Hps Hl Ha". iExists _. iSplit; [iPureIntro; reflexivity |].
    iNext. iApply wp_ret_void. iNext.
    assert (H72 : sb + 64 + 8 = sb + 72) by lia.
    iEval (rewrite H72) in "Hcursor".
    iApply ("HK" with "Hps Hcursor Hsl Hs0 Hs1 Hs2 Hs3 Hs4").
Qed.

(** The only version invocation in main: four literal author pointers,
    followed by the pointer-class interpretation of const zero. *)
Definition version_main_args : list word :=
  [WPtr stream; WPtr (version_literal "hello#str.70");
   WPtr (version_literal "hello#str.63"); WPtr (version_literal "hello#str.71");
   WPtr (version_literal "hello#str.72"); WPtr (version_literal "hello#str.73");
   WPtr (version_literal "hello#str.74"); WPtr (version_literal "hello#str.75"); WPtr null].

(** The five pointer cells selected from main's actual snapshot. *)
Definition version_snapshot_cells sb : list (piece * pval) :=
  [(PLive sb, VLive (mkRegion sb (sb + 80) Heap Live))] ++
  ((PAux sb 32, VAux (ptr_cap (version_literal "hello#str.72"))) ::
    cell sb 32 (ptr_addr (version_literal "hello#str.72"))) ++
  ((PAux sb 40, VAux (ptr_cap (version_literal "hello#str.73"))) ::
    cell sb 40 (ptr_addr (version_literal "hello#str.73"))) ++
  ((PAux sb 48, VAux (ptr_cap (version_literal "hello#str.74"))) ::
    cell sb 48 (ptr_addr (version_literal "hello#str.74"))) ++
  ((PAux sb 56, VAux (ptr_cap (version_literal "hello#str.75"))) ::
    cell sb 56 (ptr_addr (version_literal "hello#str.75"))) ++
  ((PAux sb 64, VAux CNone) :: cell sb 64 0).

(** The selected cells have distinct life, byte, and capability keys. *)
Lemma version_snapshot_cells_nodup sb : NoDup (version_snapshot_cells sb).*1.
Proof.
  unfold version_snapshot_cells, cell. cbn.
  repeat constructor; intros Hin;
    repeat (apply elem_of_cons in Hin; destruct Hin as [Hin | Hin]); inversion Hin.
Qed.

(** The selected cells are populated by argument indices four through
    eight of the actual snapshot, not supplied as new initial memory. *)
Lemma version_snapshot_cells_member sb lv :
  lv ∈ version_snapshot_cells sb ->
  lv ∈ snapshot_ps version_main_args sb (heap_req 16 72).
Proof.
  destruct lv as [l v]. unfold version_snapshot_cells.
  rewrite !elem_of_app. intros [Hlive | [H0 | [H1 | [H2 | [H3 | H4]]]]].
  - apply elem_of_cons in Hlive as [Hlive | Hfalse]; [|inversion Hfalse].
    injection Hlive as -> ->.
    unfold snapshot_ps, obj_ps. apply list_elem_of_fmap.
    exists (PLive sb, VLive (mkRegion sb (sb + 80) Heap Live)).
    split; [reflexivity | left; reflexivity].
  - apply (snapshot_ps_pointer version_main_args 4 (version_literal "hello#str.72"));
      [reflexivity | vm_compute; congruence | exact H0].
  - apply (snapshot_ps_pointer version_main_args 5 (version_literal "hello#str.73"));
      [reflexivity | vm_compute; congruence | exact H1].
  - apply (snapshot_ps_pointer version_main_args 6 (version_literal "hello#str.74"));
      [reflexivity | vm_compute; congruence | exact H2].
  - apply (snapshot_ps_pointer version_main_args 7 (version_literal "hello#str.75"));
      [reflexivity | vm_compute; congruence | exact H3].
  - apply (snapshot_ps_pointer version_main_args 8 null);
      [reflexivity | vm_compute; congruence | exact H4].
Qed.

(** Extracting only the used cells discards unused snapshot padding. *)
Lemma version_snapshot_authors sb :
  pts (snapshot_ps version_main_args sb (heap_req 16 72)) -∗
  live sb (mkRegion sb (sb + 80) Heap Live) ∗
  pcell sb 32 (version_literal "hello#str.72") ∗
  pcell sb 40 (version_literal "hello#str.73") ∗
  pcell sb 48 (version_literal "hello#str.74") ∗
  pcell sb 56 (version_literal "hello#str.75") ∗ pcell sb 64 null.
Proof.
  iIntros "Hps".
  iAssert (pts (version_snapshot_cells sb)) with "[Hps]" as "Hps".
  { iApply (big_sepL_submseteq with "Hps"). apply NoDup_submseteq.
    - apply (NoDup_fmap_1 fst). apply version_snapshot_cells_nodup.
    - apply version_snapshot_cells_member. }
  rewrite /version_snapshot_cells !pts_app /pcell /live. iExact "Hps".
Qed.

(** The public variadic wrapper in the linked program. *)
Definition version_etc_fn : func := Eval vm_compute in hello_fn "version_etc".
(** Its single block constructs a va_list and calls the counting helper. *)
Definition version_start : block := Eval vm_compute in hblk version_etc_fn "start".

(** The variadic entry retains every actual argument for Snapshot. *)
Lemma version_etc_entry : invocation version_etc_fn version_main_args =
  mkFrame version_etc_fn
    [(TAtom "v6", WPtr (version_literal "hello#str.71"));
     (TAtom "v4", WPtr (version_literal "hello#str.63"));
     (TAtom "v2", WPtr (version_literal "hello#str.70")); (TAtom "v0", WPtr stream)]
    [] None (Snapshot version_main_args (TAtom "start")).
Proof. reflexivity. Qed.

(** The local va_list begins with one zero pointer cell. *)
Lemma version_cursor_zero cb :
  obj cb (heap_req 8 24) -∗ live cb (mkRegion cb (cb + 32) Heap Live) ∗ pcell cb 0 null.
Proof.
  iIntros "Hobj". iDestruct (obj_zero_block with "Hobj") as "(Hl & Hx & Ha)";
    [compute; discriminate |].
  iSplitL "Hl"; [iExact "Hl" |].
  iDestruct (version_zero_cell_prefix cb 0 24 with "Hx Ha") as "(Hc & _ & _)".
  iExact "Hc".
Qed.

(** Snapshot population preserves the same opaque world under the
    already proved fresh-object and exact-store frame facts. *)
Context (Kversion_snapshot : forall m wd h sb,
  fresh m (heap_req 16 72) sb -> wi m wd h ->
  wi (snapshot_values version_main_args sb (allocated m (heap_req 16 72) sb)) wd
    (overwrite (snapshot_ps version_main_args sb (heap_req 16 72)) h)).

(** Main can apply this triple directly after the four proper_name
    identities. The snapshot and the counting loop derive the count;
    neither the count nor the array contents are caller premises. *)
Lemma version_etc_spec Φ :
  pts literal_ps -∗ ▷ (pts literal_ps -∗ Φ RetVoid) -∗
  WP (ERun (invocation version_etc_fn version_main_args) : hexpr) {{ Φ }}.
Proof.
  iIntros "Hps HK". rewrite version_etc_entry.
  iApply wp_snapshot;
    [discriminate | reflexivity | exact Kversion_snapshot |].
  iNext. iIntros (sb [Hsb [Hsmod Hsend]]) "Hsnapshot".
  change (sb mod 16 = 0) in Hsmod. change (sb + 80 <= 2 ^ 48) in Hsend.
  iDestruct (version_snapshot_authors with "Hsnapshot") as "(Hsl & Hs0 & Hs1 & Hs2 & Hs3 & Hs4)".
  iApply wp_enter; [vm_compute; reflexivity | reflexivity |]. iNext.
  cbn [b_insts b_jump version_start].
  iApply (wp_alloc _ _ _ _ _ _ _ _ _ _ _ _ _ 24);
    [reflexivity | lia | unfold max_allocation_size; lia |
     intros m wd h base Hf Hw; apply Kversion_alloc; [simpl; tauto | exact Hf | exact Hw] |].
  iNext. iIntros (cb [Hcb [Hcmod Hcend]]) "Hobj".
  change (cb mod 16 = 0) in Hcmod. change (cb + 32 <= 2 ^ 48) in Hcend.
  assert (Hc8 : cb mod 8 = 0).
  { apply Z.mod_divide; [lia |]. apply (Z.divide_trans 8 16 cb).
    - exists 2. reflexivity.
    - apply Z.mod_divide; [lia | exact Hcmod]. }
  iDestruct (version_cursor_zero with "Hobj") as "[Hcl Hc]".
  iApply wp_va_args; [reflexivity |]. iNext.
  iApply (wp_check with "Hcl");
    [reflexivity | word_premise | reflexivity | addr_premise |
     cbn [r_end]; addr_premise | addr_premise |]. iNext. iIntros "Hcl".
  iApply (wp_raw_store_pointer with "Hcl Hc");
    [word_premise | word_premise | reflexivity | addr_premise | addr_premise |
     apply Kversion_store |]. iNext. iIntros "Hcl Hc".
  assert (Hwrap : (sb + 32) mod 2 ^ 64 = sb + 32) by (apply Z.mod_small; lia).
  iEval (cbn [ptr_addr]; rewrite Hwrap) in "Hc".
  iAssert (pts (va_cursor_ps cb (mkRegion cb (cb + 32) Heap Live)
    (mkPtr (sb + 32) (Ro sb)))) with "[Hcl Hc]" as "Hcursor".
  { replace (va_cursor_ps cb (mkRegion cb (cb + 32) Heap Live)
      (mkPtr (sb + 32) (Ro sb))) with
      ([(PLive cb, VLive (mkRegion cb (cb + 32) Heap Live))] ++
        ((PAux cb 0, VAux (Ro sb)) :: cell cb 0 (sb + 32))) by reflexivity.
    rewrite pts_app.
    iFrame "Hcl Hc". }
  iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ _ version_etc_va_fn
    (invocation version_etc_va_fn
      [WPtr stream; WPtr (version_literal "hello#str.70");
       WPtr (version_literal "hello#str.63"); WPtr (version_literal "hello#str.71");
       WPtr (mkPtr cb (Obj cb))]));
    [word_premise | unfold find_fn; rewrite (proj1 Hlinked); vm_compute; reflexivity | reflexivity |].
  iNext. iApply (version_etc_va_spec with "Hps Hcursor Hsl Hs0 Hs1 Hs2 Hs3 Hs4");
    [exact Hc8 | exact Hsb | exact Hsmod | cbn [r_end]; lia | cbn [r_end]; lia |].
  iNext. iIntros "Hps Hcursor Hsl Hs0 Hs1 Hs2 Hs3 Hs4".
  iExists _. iSplit; [iPureIntro; reflexivity |].
  iNext. iApply wp_ret_void. iNext. iApply ("HK" with "Hps").
Qed.

End arn.

End version.
End HelloVersionOn.

(** [HelloVersionOn] over a Logic instance of its own. *)
Module HelloVersion (R : Runtime).
Module LG0 := Logic R.
Include HelloVersionOn R LG0.
End HelloVersion.
