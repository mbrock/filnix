(** rocq/glibc/len.c, linked with nanofil's IR of user glibc's
    string/strlen.c, through the program logic of Logic.v
    (docs/glibc-ir.md).

    `main` returns `strlen(msg)` for the 13-byte literal "hello, glibc".
    No contract describes strlen here: the linked module defines
    `__strlen`, glibc's word-at-a-time scan, and the weak alias
    `strlen` that names it, so the call is an ordinary direct call
    ([wp_call_bind]) and the proof walks glibc's own IR. The module
    calls nothing outside itself; the registry is empty.

    The call is taken by StrlenLogic.v's [wp_glibc_strlen], the triple
    of glibc's strlen for any string: the literal's object is 8-aligned
    and 16 bytes, its 13 bytes rounded up to whole words (Run.v's
    [layout]; filcc's literal object is also 16 bytes, probed in
    docs/glibc-ir.md), and the program owns its life and both words
    ([msg_ps]), which is the triple's precondition. Its first zero is
    12 bytes in, so strlen returns 12.

    [len_never_panics] is [never_panics] for `main`, through
    GlibcLogic.v's [pieces_never_panics]: Iris [[adequacy]] where the
    program starts owning pieces of its initial memory, here the
    literal's. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules ExternalCalls ExternalMachine Transport Pieces Heap Language Logic.
From Glibc Require Import LenCode GlibcLogic StrlenBits StrlenLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The module *)

(** The checked module: len.c's `main` and its literal, glibc's
    `__strlen` and its alias `strlen` ([len_term]). *)
Definition len_module : module :=
  match decode_module len_term with Some md => md | None => [] end.

(** The fixture decodes to [len_module]. *)
Lemma len_decodes : decode_module len_term = Some len_module.
Proof. vm_compute. reflexivity. Qed.

(** The address of the literal `msg`, renamed `len#msg` by link.pl. *)
Definition msg_base : Z := 65552.

(** The literal's capability, read-only. *)
Definition msg_ptr : ptr := mkPtr msg_base (Ro msg_base).

(** The literal's region: its 13 bytes rounded up to 16. *)
Definition msg_reg : region := mkRegion msg_base (msg_base + 16) GlobalData Live.

(** The module's symbols: `strlen` is `__strlen`'s address. *)
Definition len_globals : list (name * ptr) :=
  [(TAtom "strlen", mkPtr 65584 (Fn (TAtom "__strlen")));
   (TAtom "__strlen", mkPtr 65584 (Fn (TAtom "__strlen")));
   (TAtom "len#msg", msg_ptr);
   (TAtom "main", mkPtr 65536 (Fn (TAtom "main")))].

(** The module's initial memory. *)
Definition len_mem : mem :=
  match initial_memory len_module with Some (_, m) => m | None => empty_mem end.

(** Laying out the module gives [len_globals] and [len_mem]. *)
Lemma len_initial : initial_memory len_module = Some (len_globals, len_mem).
Proof.
  assert (H : option_map fst (initial_memory len_module) = Some len_globals) by (vm_compute; reflexivity).
  unfold len_mem. destruct (initial_memory len_module) as [[g m]|]; inversion H; reflexivity.
Qed.

(** The function named n of the module, or an empty one. *)
Definition len_fn (n : string) : func :=
  match find_direct (TAtom n) len_module with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "export") (RClass W) [] []
  end.

(** len.c's `main`. *)
Definition main_fn : func := Eval vm_compute in len_fn "main".
(** glibc's `__strlen`. *)
Definition strlen_fn : func := Eval vm_compute in len_fn "__strlen".

(** ## The literal's pieces *)

(** The literal's first word, "hello, g", little-endian. *)
Definition msg_w0 : Z := 7430988242233353576.
(** Its second word, "libc" and the NUL, then the three zero bytes
    the layout's rounding adds. *)
Definition msg_w1 : Z := 1667393900.

(** The pieces the program owns: the literal's life and its two words. *)
Definition msg_ps : list (piece * pval) :=
  [(PLive msg_base, VLive msg_reg)] ++ cell msg_base 0 msg_w0 ++ cell msg_base 8 msg_w1.

(** The pieces' keys are distinct. *)
Lemma msg_ps_nodup : NoDup msg_ps.*1.
Proof.
  cbn. repeat (apply NoDup_cons_2;
    [ intros H; apply list_elem_of_In in H; cbn in H;
      repeat destruct H as [H|H]; first [discriminate | injection H; unfold msg_base; lia | exact H] |]).
  apply NoDup_nil_2.
Qed.

(** The literal's object is registered with its region. *)
Lemma msg_region : object_region msg_base (m_regions len_mem) = Some msg_reg.
Proof. vm_compute. reflexivity. Qed.

(** The initial memory holds the literal as [msg_ps] says. *)
Lemma msg_ps_agree : all_agree len_mem msg_ps.
Proof.
  unfold msg_ps, cell. cbn [all_agree map app fst snd agree_piece].
  unfold live_at, registered, in_live. rewrite !msg_region.
  repeat first [ split | intro | discriminate
               | match goal with H : Some _ = Some _ |- _ => injection H as <- end ];
    cbn [r_end msg_reg]; unfold msg_base; try lia; vm_compute; reflexivity.
Qed.

(** The initial memory's one live object is apart from itself. *)
Lemma len_disjoint : live_disjoint len_mem.
Proof.
  intros b1 r1 b2 r2 [E1 _] [E2 _] Hne.
  assert (Hr : m_regions len_mem = [msg_reg]) by (vm_compute; reflexivity).
  rewrite Hr in E1, E2. cbn [object_region r_base msg_reg] in E1, E2.
  destruct (Z.eqb msg_base b1) eqn:H1; [|discriminate]. destruct (Z.eqb msg_base b2) eqn:H2; [|discriminate].
  apply Z.eqb_eq in H1, H2. congruence.
Qed.

(** ## Over any runtime *)

(** The proof over the [[runtime]] R. *)
Module LenLogic (R : Runtime).
Module LG := Logic R.
Module GL := GlibcLogicOn R LG.
Module SO := StrlenOn R LG.
Module L := LG.L.
Module P := LG.P.
Import L LG GL.

(** The linked genv, whose free is R's. *)
Local Notation lge := (P.program_genv len_module len_globals).
(** The expressions of its language. *)
Local Notation lexpr := (language.expr (nanofil_lang no_contracts lge)).

(** A call of `strlen` runs `__strlen`, through the alias. *)
Lemma find_strlen : find_fn lge (TAtom "strlen") = Some (Defined strlen_fn).
Proof. vm_compute. reflexivity. Qed.

(** `main` is a function of the module. *)
Lemma find_main : find_fn lge (TAtom "main") = Some (Defined main_fn).
Proof. vm_compute. reflexivity. Qed.

Section wp.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** The Iris instance of the module: no contracts, no world. *)
Local Instance len_irisGS : irisGS_gen hlc (nanofil_lang no_contracts lge) Σ :=
  nanofil_irisGS no_contracts no_world lge.

(** glibc's strlen, called with the literal, owning its pieces:
    [wp_glibc_strlen] with its two words, returning 12 and handing the
    pieces back. *)
Lemma strlen_msg_spec Φ :
  pts msg_ps -∗ (pts msg_ps -∗ Φ (Ret (WInt 12))) -∗
  WP (ERun (mkFrame strlen_fn [(TAtom "v0", WPtr msg_ptr)] [] None (Enter (TAtom "start") None)) : lexpr)
    {{ Φ }}.
Proof.
  iIntros "Hps HΦ". rewrite /msg_ps !pts_app. iDestruct "Hps" as "(Hl & H0 & H1)".
  iApply (SO.wp_glibc_strlen no_contracts no_world lge msg_ptr msg_base msg_reg [msg_w0; msg_w1] 12
            with "Hl [H0 H1]").
  - right. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. congruence.
  - vm_compute. congruence.
  - vm_compute. congruence.
  - repeat constructor; vm_compute; congruence.
  - split; [vm_compute; reflexivity|]. intros u Hu. do 12 (destruct u as [|u]; [vm_compute; congruence|]). lia.
  - cbn [words_ps]. rewrite app_nil_r pts_app. iFrame.
  - iIntros "Hl Hps". cbn [words_ps]. rewrite app_nil_r pts_app. iDestruct "Hps" as "[H0 H1]".
    iApply "HΦ". iFrame.
Qed.

(** `main`, owning the literal, returns 12: glibc's strlen of it. *)
Lemma main_spec :
  pts msg_ps -∗
  WP (ERun (mkFrame main_fn [] [] None (Enter (TAtom "start") None)) : lexpr) {{ o, ⌜o = Ret (WInt 12)⌝ }}.
Proof.
  iIntros "Hps". repeat step.
  iApply wp_call_bind; [side | exact find_strlen | side |]. iNext.
  iApply (strlen_msg_spec with "Hps"). iIntros "_".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  iApply wp_ret; [side | side |]. iNext. done.
Qed.

End wp.

(** len.c linked with glibc's strlen never panics: called with any
    arguments, with any fuel and whatever the runtime does at its
    safepoints, no state of its run [fails]. By [pieces_never_panics]
    from [main_spec], the program owning the literal's pieces. *)
Theorem len_never_panics : P.never_panics len_module (TAtom "main") (fun _ => True).
Proof.
  apply (pieces_never_panics glibcΣ len_module (TAtom "main") _ len_globals len_mem main_fn msg_ps).
  - exact len_initial.
  - exact find_main.
  - exact len_disjoint.
  - exact msg_ps_agree.
  - exact msg_ps_nodup.
  - intros xs _. eexists. split; [reflexivity|]. intros HinvG HheapG.
    iIntros "Hps". iApply (wp_wand with "[Hps]"); [iApply (main_spec with "Hps") | by iIntros (o) "_"].
Qed.

End LenLogic.

(** The theorem for the interpreter's runtime. *)
Module InterpLenLogic := LenLogic InterpRuntime.

(** len.c with glibc's strlen never panics under the interpreter's
    runtime. *)
Theorem interp_len_never_panics :
  InterpLenLogic.P.never_panics len_module (TAtom "main") (fun _ => True).
Proof. exact InterpLenLogic.len_never_panics. Qed.
