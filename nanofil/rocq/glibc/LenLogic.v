(** A C program that calls `c: strlen` on a string literal usually
    treats `c: strlen` as a primitive with an external specification.
    Here we link `c: len.c` directly with the intermediate
    representation of userland glibc's `c: string/strlen.c` and prove
    memory safety through the program logic in [Logic](Logic.v).

    In `c: len.c`, `c: main` returns `c: strlen(msg)` for the 13-byte
    string literal `"hello, glibc"`. Because the linked module defines
    glibc's `__strlen` and exports `c: strlen` as an alias for it, the
    call resolves directly inside the module through [wp_call_bind]. The
    program makes no external calls, so the [[runtime]] registry stays
    empty.

    Glibc's string scan reads aligned 8-byte words rather than single
    bytes, so the proof requires the literal's [[region]] to be 8-byte
    aligned and padded to a whole number of words. In memory, the
    13-byte literal occupies 16 bytes, and the program starts owning its
    liveness token and both words in [msg_ps] so [wp_glibc_strlen] in
    [StrlenLogic](StrlenLogic.v) can discharge the call. Its first zero
    byte lies 12 bytes in, so `c: strlen` returns 12.

    Finally, the Iris [[adequacy]] theorem turns this weakest
    precondition into an operational safety guarantee. Starting from
    initial memory where the program owns the literal's pieces,
    [len_never_panics] applies [pieces_never_panics] from
    [GlibcLogic](GlibcLogic.v) to show that `c: main` never fails at any
    [[check]] or safepoint. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules ExternalCalls ExternalMachine Transport Pieces Heap Language Logic.
From Glibc Require Import LenCode GlibcLogic StrlenBits StrlenLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The module

    The compiled fixture [len_term] bundles `c: main`, its string
    literal, glibc's `__strlen`, and the `c: strlen` alias into one
    linked module. Before reasoning about any call, we decode the
    module, fix the addresses and [[capability]] metadata that the
    initial layout assigns, and extract the function bodies we step
    through. *)

(** [len_module] holds the decoded IR module for `c: len.c` linked with
    glibc's `__strlen` and its exported `c: strlen` alias. *)
Definition len_module : module :=
  match decode_module len_term with Some md => md | None => [] end.

(** [len_decodes] verifies by computation that [len_term] decodes to
    [len_module]. *)
Lemma len_decodes : decode_module len_term = Some len_module.
Proof. vm_compute. reflexivity. Qed.

(** [msg_base] is the base address assigned to the string literal `msg`,
    which `c: link.pl` renames to `len#msg`. *)
Definition msg_base : Z := 65552.

(** [msg_ptr] pairs [msg_base] with a read-only [[capability]] for the
    literal object. *)
Definition msg_ptr : ptr := mkPtr msg_base (Ro msg_base).

(** [msg_reg] describes the literal's 16-byte global [[region]],
    rounding its 13 bytes up to two 8-byte words. *)
Definition msg_reg : region := mkRegion msg_base (msg_base + 16) GlobalData Live.

(** [len_globals] lists the module's global symbols, mapping both
    `c: strlen` and `__strlen` to the same function pointer. *)
Definition len_globals : list (name * ptr) :=
  [(TAtom "strlen", mkPtr 65584 (Fn (TAtom "__strlen")));
   (TAtom "__strlen", mkPtr 65584 (Fn (TAtom "__strlen")));
   (TAtom "len#msg", msg_ptr);
   (TAtom "main", mkPtr 65536 (Fn (TAtom "main")))].

(** [len_mem] is the initial memory produced by laying out
    [len_module]. *)
Definition len_mem : mem :=
  match initial_memory len_module with Some (_, m) => m | None => empty_mem end.

(** [len_initial] confirms that laying out [len_module] yields
    [len_globals] and [len_mem]. *)
Lemma len_initial : initial_memory len_module = Some (len_globals, len_mem).
Proof.
  assert (H : option_map fst (initial_memory len_module) = Some len_globals) by (vm_compute; reflexivity).
  unfold len_mem. destruct (initial_memory len_module) as [[g m]|]; inversion H; reflexivity.
Qed.

(** [len_fn] looks up a defined function named n in [len_module],
    falling back to an empty stub when missing. *)
Definition len_fn (n : string) : func :=
  match find_direct (TAtom n) len_module with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "export") (RClass W) [] []
  end.

(** [main_fn] is the decoded body of `c: main` from `c: len.c`. *)
Definition main_fn : func := Eval vm_compute in len_fn "main".
(** [strlen_fn] is the decoded body of glibc's `__strlen`. *)
Definition strlen_fn : func := Eval vm_compute in len_fn "__strlen".

(** ## The literal's pieces

    A proof in the program logic tracks each byte and liveness token of
    the string literal separately, rather than treating the initial
    memory image as one block. Before stepping through `c: main`, we
    encode the literal's two 64-bit words and check that their
    [[separation-logic]] pieces have distinct keys and match [len_mem]. *)

(** [msg_w0] encodes the first eight bytes `"hello, g"` as a
    little-endian 64-bit integer. *)
Definition msg_w0 : Z := 7430988242233353576.
(** [msg_w1] encodes `"libc"`, the terminating NUL byte, and the three
    zero padding bytes added by 8-byte alignment. *)
Definition msg_w1 : Z := 1667393900.

(** [msg_ps] collects the [[ghost-state|ghost pieces]] owned by the
    program: the literal's liveness token followed by its two aligned
    words. *)
Definition msg_ps : list (piece * pval) :=
  [(PLive msg_base, VLive msg_reg)] ++ cell msg_base 0 msg_w0 ++ cell msg_base 8 msg_w1.

(** [msg_ps_nodup] proves that no two entries in [msg_ps] share the same
    piece key. *)
Lemma msg_ps_nodup : NoDup msg_ps.*1.
Proof.
  cbn. repeat (apply NoDup_cons_2;
    [ intros H; apply list_elem_of_In in H; cbn in H;
      repeat destruct H as [H|H]; first [discriminate | injection H; unfold msg_base; lia | exact H] |]).
  apply NoDup_nil_2.
Qed.

(** [msg_region] checks that [len_mem] registers the literal object at
    [msg_base] with region [msg_reg]. *)
Lemma msg_region : object_region msg_base (m_regions len_mem) = Some msg_reg.
Proof. vm_compute. reflexivity. Qed.

(** [msg_ps_agree] verifies that every piece in [msg_ps] matches the
    actual bytes and region stored in [len_mem]. *)
Lemma msg_ps_agree : all_agree len_mem msg_ps.
Proof.
  unfold msg_ps, cell. cbn [all_agree map app fst snd agree_piece].
  unfold live_at, registered, in_live. rewrite !msg_region.
  repeat first [ split | intro | discriminate
               | match goal with H : Some _ = Some _ |- _ => injection H as <- end ];
    cbn [r_end msg_reg]; unfold msg_base; try lia; vm_compute; reflexivity.
Qed.

(** Live objects in initial memory must not overlap one another. Since
    [len_mem] has only one live object, [len_disjoint] establishes
    [live_disjoint] trivially. *)
Lemma len_disjoint : live_disjoint len_mem.
Proof.
  intros b1 r1 b2 r2 [E1 _] [E2 _] Hne.
  assert (Hr : m_regions len_mem = [msg_reg]) by (vm_compute; reflexivity).
  rewrite Hr in E1, E2. cbn [object_region r_base msg_reg] in E1, E2.
  destruct (Z.eqb msg_base b1) eqn:H1; [|discriminate]. destruct (Z.eqb msg_base b2) eqn:H2; [|discriminate].
  apply Z.eqb_eq in H1, H2. congruence.
Qed.

(** ## Over any runtime

    Because the module makes no external calls, the safety proof works
    over any Fil-C [[runtime]] R. We parameterize the proof by R,
    establish a [[weakest-precondition]] specification for `c: strlen`
    on the literal and for `c: main`, and then instantiate R with the
    interpreter's runtime at the end. *)

(** The module [LenLogic] packages the verification of `c: len.c` over
    an arbitrary runtime R. *)
Module LenLogic (R : Runtime).
Module LG := Logic R.
Module GL := GlibcLogicOn R LG.
Module SO := StrlenOn R LG.
Module L := LG.L.
Module P := LG.P.
Import L LG GL.

(** [lge] is the [[genv|global environment]] built from [len_module]
    and [len_globals]. *)
Local Notation lge := (P.program_genv len_module len_globals).
(** [lexpr] abbreviates the expression type of the program's language
    with no external contracts. *)
Local Notation lexpr := (language.expr (nanofil_lang no_contracts lge)).

(** [find_strlen] confirms that looking up `c: strlen` in [lge]
    resolves through the alias to [strlen_fn]. *)
Lemma find_strlen : find_fn lge (TAtom "strlen") = Some (Defined strlen_fn).
Proof. vm_compute. reflexivity. Qed.

(** [find_main] confirms that looking up `c: main` in [lge] returns
    [main_fn]. *)
Lemma find_main : find_fn lge (TAtom "main") = Some (Defined main_fn).
Proof. vm_compute. reflexivity. Qed.

Section wp.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** [len_irisGS] supplies the Iris [[state-interpretation]] for
    [len_module] with an empty contract registry and an empty world. *)
Local Instance len_irisGS : irisGS_gen hlc (nanofil_lang no_contracts lge) Σ :=
  nanofil_irisGS no_contracts no_world lge.

(** Calling `c: strlen` on the 13-byte literal `"hello, glibc"`
    returns 12 and leaves the string's memory intact. Lemma
    [strlen_msg_spec] establishes this specification for `__strlen` by
    applying [wp_glibc_strlen] to the two aligned words in [msg_ps]. *)
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

(** [main_spec] proves that `c: main` returns 12 when given ownership of
    the literal's pieces [msg_ps]. *)
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

(** [len_never_panics] proves by [pieces_never_panics] that `c: len.c`
    linked with glibc's `c: strlen` never traps or fails for any
    arguments, any fuel bound, or any runtime behavior at safepoints. *)
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

(** [InterpLenLogic] instantiates [LenLogic] with the interpreter's
    runtime. *)
Module InterpLenLogic := LenLogic InterpRuntime.

(** [interp_len_never_panics] states that `c: len.c` linked with glibc's
    `c: strlen` never panics under the interpreter's runtime. *)
Theorem interp_len_never_panics :
  InterpLenLogic.P.never_panics len_module (TAtom "main") (fun _ => True).
Proof. exact InterpLenLogic.len_never_panics. Qed.
