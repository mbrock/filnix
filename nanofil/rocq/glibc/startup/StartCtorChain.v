(** The runner may call hi_atexit's three constructors in any order, and
    each call must leave memory as the next call expects it. This module
    names the memory between calls and shows that each constructor keeps
    it, whichever constructors ran before. The runner's contract in
    [StartCtorRunnerSpec](StartCtorRunnerSpec.v) then gives the whole
    run for every order.

    ## What the memory holds between calls

    Two of the constructors change memory and one only reads it.
    `c: _IO_stdfiles_init` and `c: _init_first` each start from their own
    memory and leave a result in it, so between calls that memory is in
    one state or the other, depending on whether the constructor has run.
    `c: check_stdfiles_vtables` reads its cells and leaves them as they
    were. It also reads the three standard streams, which belong to
    `c: _IO_stdfiles_init` before and after that call. So it borrows them
    while it runs and gives them back. *)

From Glibc Require Fix.
From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia Permutation.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic MemLogic.
From Glibc Require Import FileInv LibioStdfiles LibioCloseSteps StartCode StartCtorRunnerSpec
  StartStdfilesInitSpec StartCtorVtablesSpec StartInitMiscSpec StartInitFirstSpec StartInitFirst StartCtorCalls.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioCloseSteps.
Open Scope Z_scope.

(** Whether a constructor has run is decidable, because names have
    decidable equality. *)
Local Instance name_eq_dec : EqDecision name.
Proof.
  intros x y. destruct (term_eqb x y) eqn:E.
  - left. apply term_eqb_eq. exact E.
  - right. intros ->. rewrite term_eqb_refl in E. discriminate.
Defined.

(** These names are the symbols of the three constructors. *)
Definition ctor_stdfiles : name := TAtom "glibc_stdfiles#_IO_stdfiles_init".
Definition ctor_vtables : name := TAtom "glibc_vtables#check_stdfiles_vtables".
Definition ctor_init_first : name := TAtom "glibc_init_first#_init_first".

(** The first i + 1 names are the first i names followed by the i-th. *)
Lemma firstn_snoc {A} (l : list A) i g : nth_error l i = Some g -> firstn (S i) l = (firstn i l ++ [g])%list.
Proof using Type.
  revert i. induction l as [|x l IH]; intros [|i] H; cbn in H |- *; try discriminate.
  - injection H as ->. reflexivity.
  - rewrite (IH i H). reflexivity.
Qed.

(** In a list without repeats, the i-th name is not among the names
    before it. *)
Lemma nodup_not_before {A} (l : list A) i g : List.NoDup l -> nth_error l i = Some g -> ~ In g (firstn i l).
Proof using Type.
  revert i. induction l as [|x l IH]; intros [|i] Hn H; cbn in H |- *; try discriminate; [tauto|].
  inversion Hn as [|? ? Hx Hn']; subst. intros [<-|Hi].
  - apply Hx. exact (nth_error_In _ _ H).
  - exact (IH i Hn' H Hi).
Qed.

Section chain.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** ## Calls with more memory

    A constructor's promise about its own memory carries over when more
    memory is held, and when its memory is written in another form. *)

(** A call leaves memory it does not use alone. *)
Lemma ctor_call_ok_frame g xs P Q R : ctor_call_ok g xs P Q -> ctor_call_ok g xs (P ∗ R) (Q ∗ R).
Proof using Type.
  intros H f e ls lab callee rest j p Ψ args Hv Hp Hc Hx. iIntros "[HP HR] HK".
  iApply (H with "HP"); [exact Hv | exact Hp | exact Hc | exact Hx |].
  iNext. iIntros "HQ". iApply "HK". iFrame.
Qed.

(** The same holds when the extra memory sits on both sides. *)
Lemma ctor_call_ok_frame_mid g xs P Q R R' :
  ctor_call_ok g xs P Q -> ctor_call_ok g xs (R ∗ P ∗ R') (R ∗ Q ∗ R').
Proof using Type.
  intros H f e ls lab callee rest j p Ψ args Hv Hp Hc Hx. iIntros "(HR & HP & HR') HK".
  iApply (H with "HP"); [exact Hv | exact Hp | exact Hc | exact Hx |].
  iNext. iIntros "HQ". iApply "HK". iFrame.
Qed.

(** A promise holds for a stronger precondition and a weaker
    postcondition. *)
Lemma ctor_call_ok_mono g xs P P' Q Q' :
  (P' ⊢ P) -> (Q ⊢ Q') -> ctor_call_ok g xs P Q -> ctor_call_ok g xs P' Q'.
Proof using Type.
  intros HP HQ H f e ls lab callee rest j p Ψ args Hv Hp Hc Hx. iIntros "HP HK".
  iApply (H with "[HP]"); [exact Hv | exact Hp | exact Hc | exact Hx | by iApply HP |].
  iNext. iIntros "HQ". iApply "HK". by iApply HQ.
Qed.

(** Owning a whole life or a whole cell is the same as owning a share
    of size one. *)
Lemma live_one b reg : live b reg ⊣⊢ liveq (DfracOwn 1) b reg.
Proof using Type. rewrite /live /liveq. apply pts_ptsq. Qed.

Lemma pcell_one b o x : pcell b o x ⊣⊢ pcellq (DfracOwn 1) b o x.
Proof using Type. rewrite /pcell /pcellq. apply pts_ptsq. Qed.

(** ## How the check gets the streams

    The check reads each standard stream, so it needs the stream's
    object to stay alive while it runs. That object belongs to
    `c: _IO_stdfiles_init` whether or not that constructor has run. In
    either state the stream can lend its life to the check and take it
    back afterwards. *)

(** Both states record the same facts about a stream's object: where it
    lies and that it is large enough. *)
Definition stream_fits (fb : Z) (freg : region) : Prop :=
  0 < fb /\ fb mod 8 = 0 /\ fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63.

(** A stream can lend its life before `c: _IO_stdfiles_init` runs. *)
Lemma stdfile_pre_lend fb n :
  stdfile_pre (mkPtr fb (Obj fb)) n ⊢
  ∃ freg, ⌜stream_fits fb freg⌝ ∗ live fb freg ∗ (live fb freg -∗ stdfile_pre (mkPtr fb (Obj fb)) n).
Proof using Type.
  iIntros "(%b & %freg & %Hf & Hl & Hp & Hc)". destruct Hf as (Hb & H0 & Ha & He & Hr). injection Hb as <-.
  iExists freg. iSplit; [iPureIntro; repeat split; assumption|]. iFrame "Hl". iIntros "Hl".
  iExists fb, freg. iFrame. iPureIntro. auto.
Qed.

(** A stream can also lend its life after `c: _IO_stdfiles_init` has run. *)
Lemma stream_live_lend fb :
  stream_live (mkPtr fb (Obj fb)) ⊢
  ∃ freg, ⌜stream_fits fb freg⌝ ∗ live fb freg ∗ (live fb freg -∗ stream_live (mkPtr fb (Obj fb))).
Proof using Type.
  iIntros "(%b & %freg & %Hf & Hl)". destruct Hf as (Hb & H0 & Ha & He & Hr). injection Hb as <-.
  iExists freg. iSplit; [iPureIntro; repeat split; assumption|]. iFrame "Hl". iIntros "Hl".
  iExists fb, freg. iFrame. iPureIntro. auto.
Qed.

(** ## The memory between calls *)

Context `{!HasSpec registry (os_wi w0) ge ctor_stdfiles stdfiles_init_spec}
  `{!Defines ge "glibc_stdfiles#_IO_stdfiles_init" glibc_stdfiles_init}
  `{!HasSpec registry (os_wi w0) ge ctor_vtables check_vtables_spec}
  `{!Defines ge "glibc_vtables#check_stdfiles_vtables" start_check_vtables_fn}
  `{!HasSpec registry (os_wi w0) ge ctor_init_first init_first_spec}
  `{!Defines ge "glibc_init_first#_init_first" start_init_first_fn}.

(** The section fixes the inputs of the three contracts. The streams'
    objects start at ve, vo and vi for stderr, stdout and stdin, and the
    array of tables starts at vb. *)
Context (ve vo vi la : Z) (lareg : region) (lk : Z) (lkreg : region) (rf : Z) (rfreg : region).
Context (vb : Z) (vreg : region).
Context (xf : if_objs * im_objs * dfrac * Z * ptr * ptr * list Z * ptr * ptr * ptr * ptr).

(** The streams and the array are the image's globals. *)
Context (Hvg : vtables_globals vi vo ve vb).

(** These notations write the three streams as pointers. *)
Local Notation fe := (mkPtr ve (Obj ve)).
Local Notation fo := (mkPtr vo (Obj vo)).
Local Notation fi := (mkPtr vi (Obj vi)).

(** This value gives the inputs of the contract of
    `c: _IO_stdfiles_init`. *)
Definition chain_xs : ptr * ptr * ptr * Z * region * Z * region * Z * region :=
  (fe, fo, fi, la, lareg, lk, lkreg, rf, rfreg).

(** This assertion is what `c: _IO_stdfiles_init` leaves after its call. *)
Definition stdfiles_done : iProp Σ := io_list_inv ge [fe; fo; fi] ∗ [∗ list] f ∈ [fe; fo; fi], stream_live f.

(** When `c: _init_first` returns, it has written argc, argv, environ
    and the program's names, and this assertion describes that memory. *)
Definition init_first_done : iProp Σ :=
  let '(f, o, dq, argc, envp, a, s, _, _, _, _) := xf in
  if_lives f ∗ int_cell (if_ac f) 0 argc ∗ pcell (if_lv f) 0 (mkPtr (im_av o) (Obj (im_av o))) ∗
  pcell (if_en f) 0 envp ∗ im_names o (short_name a s) a ∗ im_args o dq a s.

(** The check reads one table pointer in each stream and the array that
    those pointers point into. This assertion owns those cells. *)
Definition vtables_cells : iProp Σ :=
  pcell vi 216 (mkPtr (vb + 336) (Ro vb)) ∗ pcell vo 216 (mkPtr (vb + 336) (Ro vb)) ∗
  pcell ve 216 (mkPtr (vb + 336) (Ro vb)) ∗ live vb vreg.

(** This assertion describes memory after the constructors listed in
    ran have run, and before the others have. *)
Definition ctor_mem (ran : list name) : iProp Σ :=
  (if decide (ctor_stdfiles ∈ ran) then stdfiles_done else fs_pre stdfiles_init_spec chain_xs) ∗
  (if decide (ctor_init_first ∈ ran) then init_first_done else fs_pre init_first_spec xf) ∗
  vtables_cells.

(** The runner passes argc, argv and environ, and these words are the
    ones that `c: _init_first` expects. *)
Definition chain_args : list word :=
  let '(_, o, _, argc, envp, _, _, _, _, _, _) := xf in
  [WInt argc; WPtr (mkPtr (im_av o) (Obj (im_av o))); WPtr envp].

(** Both forms of the stdfiles memory lend the three streams' lives. *)
Lemma stdfiles_lend (b : bool) :
  (if b then stdfiles_done else fs_pre stdfiles_init_spec chain_xs) ⊢
  ∃ re ro ri, ⌜stream_fits ve re /\ stream_fits vo ro /\ stream_fits vi ri⌝ ∗
    live ve re ∗ live vo ro ∗ live vi ri ∗
    (live ve re -∗ live vo ro -∗ live vi ri -∗ if b then stdfiles_done else fs_pre stdfiles_init_spec chain_xs).
Proof using Type.
  destruct b.
  - unfold stdfiles_done at 1. iIntros "(Hl & He & Ho & Hi & _)".
    iDestruct (stream_live_lend with "He") as (re He) "[Le Ke]".
    iDestruct (stream_live_lend with "Ho") as (ro Ho) "[Lo Ko]".
    iDestruct (stream_live_lend with "Hi") as (ri Hi) "[Li Ki]".
    iExists re, ro, ri. iSplit; [done|]. iFrame. iIntros "Le Lo Li". rewrite /stdfiles_done.
    iDestruct ("Ke" with "Le") as "$". iDestruct ("Ko" with "Lo") as "$". iDestruct ("Ki" with "Li") as "$".
    done.
  - cbn [fs_pre stdfiles_init_spec chain_xs].
    iIntros "(% & Hla & Hc & He & Ho & Hi & Hk & Hrf & Hrc)".
    iDestruct (stdfile_pre_lend with "He") as (re He) "[Le Ke]".
    iDestruct (stdfile_pre_lend with "Ho") as (ro Ho) "[Lo Ko]".
    iDestruct (stdfile_pre_lend with "Hi") as (ri Hi) "[Li Ki]".
    iExists re, ro, ri. iSplit; [done|]. iFrame. iIntros "Le Lo Li". iSplit; [done|].
    iDestruct ("Ke" with "Le") as "$". iDestruct ("Ko" with "Lo") as "$". iDestruct ("Ki" with "Li") as "$".
Qed.

(** The three constructors differ from each other. *)
Lemma ctor_names_differ :
  ctor_stdfiles <> ctor_vtables /\ ctor_stdfiles <> ctor_init_first /\ ctor_vtables <> ctor_init_first.
Proof using Type. split; [|split]; discriminate. Qed.

(** ## Each call keeps the memory *)

(** Adding the name g to the list leaves another name's membership
    unchanged. *)
Lemma in_snoc_other (h g : name) (ran : list name) : h <> g -> h ∈ (ran ++ [g])%list <-> h ∈ ran.
Proof using Type.
  intros Hd. rewrite elem_of_app list_elem_of_singleton. split; [intros [?|?]; [done|contradiction] | auto].
Qed.

(** The name g is in the list once it is added. *)
Lemma in_snoc_self (g : name) (ran : list name) : g ∈ (ran ++ [g])%list.
Proof using Type. apply elem_of_app. right. apply list_elem_of_singleton. reflexivity. Qed.


(** `c: _IO_stdfiles_init`, called when it has not run yet, turns its
    part of the memory into its result. *)
Lemma stdfiles_keeps ran :
  ctor_stdfiles ∉ ran -> ctor_call_ok ctor_stdfiles chain_args (ctor_mem ran) (ctor_mem ((ran ++ [ctor_stdfiles])%list)).
Proof using Type*.
  intros Hn. unfold ctor_mem.
  rewrite (decide_False _ _ Hn) (decide_True _ _ (in_snoc_self _ ran)).
  pose proof (in_snoc_other ctor_init_first ctor_stdfiles ran ltac:(discriminate)) as Hf.
  destruct (decide (ctor_init_first ∈ ran)) as [Hi|Hi].
  - rewrite (decide_True _ _ (proj2 Hf Hi)).
    apply ctor_call_ok_frame. unfold chain_args.
    destruct xf as [[[[[[[[[[? o] ?] argc] envp] ?] ?] ?] ?] ?] ?]. apply (stdfiles_ctor_ok chain_xs).
  - rewrite (decide_False _ _ (fun H => Hi (proj1 Hf H))).
    apply ctor_call_ok_frame. unfold chain_args.
    destruct xf as [[[[[[[[[[? o] ?] argc] envp] ?] ?] ?] ?] ?] ?]. apply (stdfiles_ctor_ok chain_xs).
Qed.

(** `c: _init_first`, called when it has not run yet, turns its part of
    the memory into its result. *)
Lemma init_first_keeps ran :
  ctor_init_first ∉ ran ->
  ctor_call_ok ctor_init_first chain_args (ctor_mem ran) (ctor_mem ((ran ++ [ctor_init_first])%list)).
Proof using Type*.
  intros Hn. unfold ctor_mem.
  rewrite (decide_False _ _ Hn) (decide_True _ _ (in_snoc_self _ ran)).
  pose proof (in_snoc_other ctor_stdfiles ctor_init_first ran ltac:(discriminate)) as Hs.
  assert (Hk : ctor_call_ok ctor_init_first chain_args (fs_pre init_first_spec xf) init_first_done).
  { unfold chain_args, init_first_done. pose proof (init_first_ctor_ok xf) as H.
    destruct xf as [[[[[[[[[[f o] dq] argc] envp] a] s] u1] u2] u3] u4]. exact H. }
  destruct (decide (ctor_stdfiles ∈ ran)) as [Hi|Hi];
    [rewrite (decide_True _ _ (proj2 Hs Hi)) | rewrite (decide_False _ _ (fun H => Hi (proj1 Hs H)))].
  all: apply ctor_call_ok_frame_mid; exact Hk.
Qed.

(** `c: check_stdfiles_vtables` runs at any point. It borrows the three
    streams' lives from whichever form the stdfiles memory is in. *)
Lemma vtables_keeps ran :
  ctor_call_ok ctor_vtables chain_args (ctor_mem ran) (ctor_mem ((ran ++ [ctor_vtables])%list)).
Proof using Type* Hvg.
  pose proof (in_snoc_other ctor_stdfiles ctor_vtables ran ltac:(discriminate)) as Hs.
  pose proof (in_snoc_other ctor_init_first ctor_vtables ran ltac:(discriminate)) as Hf.
  assert (Es : (if decide (ctor_stdfiles ∈ (ran ++ [ctor_vtables])%list) then stdfiles_done
                else fs_pre stdfiles_init_spec chain_xs) =
               (if decide (ctor_stdfiles ∈ ran) then stdfiles_done else fs_pre stdfiles_init_spec chain_xs)).
  { destruct (decide (ctor_stdfiles ∈ ran)) as [Hi|Hi];
      [apply (decide_True _ _ (proj2 Hs Hi)) | apply (decide_False _ _ (fun H => Hi (proj1 Hs H)))]. }
  assert (Ef : (if decide (ctor_init_first ∈ (ran ++ [ctor_vtables])%list) then init_first_done
                else fs_pre init_first_spec xf) =
               (if decide (ctor_init_first ∈ ran) then init_first_done else fs_pre init_first_spec xf)).
  { destruct (decide (ctor_init_first ∈ ran)) as [Hi|Hi];
      [apply (decide_True _ _ (proj2 Hf Hi)) | apply (decide_False _ _ (fun H => Hi (proj1 Hf H)))]. }
  rewrite /ctor_mem Es Ef.
  pose (b := if decide (ctor_stdfiles ∈ ran) then true else false).
  assert (ES : (if decide (ctor_stdfiles ∈ ran) then stdfiles_done else fs_pre stdfiles_init_spec chain_xs) =
               (if b then stdfiles_done else fs_pre stdfiles_init_spec chain_xs))
    by (unfold b; destruct (decide (ctor_stdfiles ∈ ran)); reflexivity).
  rewrite ES. clearbody b.
  intros f e ls lab callee rest j p Ψ args Hv Hp Hc Hx. iIntros "(HS & HF & Ci & Co & Ce & Lv) HK".
  iDestruct (stdfiles_lend b with "HS") as (re ro ri (Fe & Fo & Fi)) "(Le & Lo & Li & HS)".
  iApply (wp_live_fit1 with "Le"). iIntros ([_ He48]) "Le".
  iApply (wp_live_fit1 with "Lo"). iIntros ([_ Ho48]) "Lo".
  iApply (wp_live_fit1 with "Li"). iIntros ([_ Hi48]) "Li".
  assert (Hfs : 224 <= file_size) by (vm_compute; intros Hc'; discriminate Hc').
  destruct Fe as (Fe0 & Fe8 & Fee & _), Fo as (Fo0 & Fo8 & Foe & _), Fi as (Fi0 & Fi8 & Fie & _).
  unfold chain_args in Hx. destruct xf as [[[[[[[[[[f0 o] dq] argc] envp] a] s] u1] u2] u3] u4].
  pose proof (vtables_ctor_ok (vi, ri, vo, ro, ve, re, vb, vreg, DfracOwn 1) argc
                (mkPtr (im_av o) (Obj (im_av o))) envp) as Hvt.
  iApply (Hvt _ _ _ _ _ _ _ _ Ψ Hv Hp Hc Hx with "[Le Lo Li Ci Co Ce Lv]").
  - cbn [fs_pre check_vtables_spec]. rewrite /vt_ok -!live_one -!pcell_one. iFrame. iPureIntro.
    split; [exact Hvg|]. rewrite /stream_ok. lia.
  - iNext. iIntros "(Vi & Vo & Ve & Lv)". rewrite /vt_ok -!live_one -!pcell_one.
    iDestruct "Vi" as "[Li Ci]". iDestruct "Vo" as "[Lo Co]". iDestruct "Ve" as "[Le Ce]".
    iApply "HK". iDestruct ("HS" with "Le Lo Li") as "$". iFrame.
Qed.

(** ## Every order

    The runner calls the constructors in the order of its table, which
    may be any order of the three names. Each call finds its own
    constructor not yet run, because no name appears twice. *)

(** For any order of the three constructors, each call keeps the memory
    that the next call expects. *)
Lemma ctor_mem_chain order :
  Permutation order [ctor_stdfiles; ctor_vtables; ctor_init_first] ->
  ctor_chain_ok chain_args ctor_mem order.
Proof using Type* Hvg.
  intros Hp i g Hg. rewrite (firstn_snoc _ _ _ Hg).
  assert (Hnd : List.NoDup order).
  { apply (Permutation_NoDup (Permutation_sym Hp)).
    repeat constructor; cbn; intros H; repeat destruct H as [H|H]; try discriminate H; exact H. }
  assert (Hn : g ∉ firstn i order).
  { intros H. apply (nodup_not_before _ _ _ Hnd Hg). apply list_elem_of_In. exact H. }
  pose proof (Permutation_in _ Hp (nth_error_In _ _ Hg)) as Hin.
  destruct Hin as [<-|[<-|[<-|[]]]].
  - exact (stdfiles_keeps _ Hn).
  - exact (vtables_keeps _).
  - exact (init_first_keeps _ Hn).
Qed.

(** Before the first call, memory holds exactly what the three
    constructors need to start. *)
Lemma ctor_mem_start :
  ctor_mem [] ⊣⊢ fs_pre stdfiles_init_spec chain_xs ∗ fs_pre init_first_spec xf ∗ vtables_cells.
Proof using Type.
  unfold ctor_mem.
  destruct (decide (ctor_stdfiles ∈ _)) as [H|_]; [inversion H|].
  destruct (decide (ctor_init_first ∈ _)) as [H|_]; [inversion H|]. done.
Qed.

(** After all three calls, the memory is the three results. *)
Lemma ctor_mem_end order :
  Permutation order [ctor_stdfiles; ctor_vtables; ctor_init_first] ->
  ctor_mem order ⊣⊢ stdfiles_done ∗ init_first_done ∗ vtables_cells.
Proof using Type.
  intros Hp.
  assert (Y : forall g, In g [ctor_stdfiles; ctor_vtables; ctor_init_first] -> g ∈ order).
  { intros g H. apply list_elem_of_In. exact (Permutation_in _ (Permutation_sym Hp) H). }
  unfold ctor_mem.
  destruct (decide (ctor_stdfiles ∈ _)) as [_|H]; [|exfalso; apply H, Y; cbn; tauto].
  destruct (decide (ctor_init_first ∈ _)) as [_|H]; [|exfalso; apply H, Y; cbn; tauto]. done.
Qed.

End chain.
