(** rocq/glibc/say.c, linked with nanofil's IR of user glibc's
    string/strlen.c and io/write.c, through the program logic of
    Logic.v (docs/glibc-ir.md).

    `main` writes the literal "hello, glibc\n" to descriptor 1 with
    `write(1, msg, strlen(msg))`. Both calls run glibc's own IR:
    `strlen` is `__strlen`'s word-at-a-time scan, taken by StrlenLogic.v's
    triple [wp_glibc_strlen], and
    `write` is the alias of `__libc_write`, whose body calls libpizlo's
    `zsys_write` and returns what it returns. The linked module defines
    everything but `zsys_write`, so that one name is the registry's,
    with the trusted contract of ZsysWrite.v; the rest is proved.

    The world is ZsysWrite.v's [fd_world], interpreted by [fd_wi] for
    descriptor 1: errno a writable int apart from the literal, and
    descriptor 1 not libpizlo's log. ZsysWrite.v names what the world
    is trusted to be: the thread's own allocated errno, glibc's errno
    handler registered, no errno logging. [say_logic_safe] is the
    labelled machine's safety of `main` from any such memory and world
    holding the literal, with the result 0. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules ExternalCalls ExternalMachine Transport Pieces Heap ContractFrame Language Logic.
From Glibc Require Import SayCode GlibcLogic ZsysWrite StrlenLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The module *)

(** The checked module: say.c's `main` and its literal, glibc's
    `__strlen` and `__libc_write` with their aliases ([say_term]). *)
Definition say_module : module :=
  match decode_module say_term with Some md => md | None => [] end.

(** The fixture decodes to [say_module]. *)
Lemma say_decodes : decode_module say_term = Some say_module.
Proof. vm_compute. reflexivity. Qed.

(** The address of the literal `msg`, renamed `say#msg` by link.pl. *)
Definition msg_base : Z := 65552.

(** The literal's capability, read-only. *)
Definition msg_ptr : ptr := mkPtr msg_base (Ro msg_base).

(** The literal's region: its 14 bytes rounded up to 16. *)
Definition msg_reg : region := mkRegion msg_base (msg_base + 16) GlobalData Live.

(** The module's symbols, as laying it out places them. *)
Definition say_globals : list (name * ptr) :=
  [(TAtom "write", mkPtr 65600 (Fn (TAtom "__libc_write")));
   (TAtom "strlen", mkPtr 65584 (Fn (TAtom "__strlen")));
   (TAtom "__libc_write", mkPtr 65600 (Fn (TAtom "__libc_write")));
   (TAtom "__strlen", mkPtr 65584 (Fn (TAtom "__strlen")));
   (TAtom "say#msg", msg_ptr);
   (TAtom "main", mkPtr 65536 (Fn (TAtom "main")))].

(** Laying out the module gives [say_globals]. *)
Lemma say_layout : option_map fst (initial_memory say_module) = Some say_globals.
Proof. vm_compute. reflexivity. Qed.

(** The function named n of the module, or an empty one. *)
Definition say_fn (n : string) : func :=
  match find_direct (TAtom n) say_module with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "export") (RClass W) [] []
  end.

(** say.c's `main`. *)
Definition main_fn : func := Eval vm_compute in say_fn "main".
(** glibc's `__strlen`. *)
Definition strlen_fn : func := Eval vm_compute in say_fn "__strlen".
(** glibc's `__libc_write`. *)
Definition write_fn : func := Eval vm_compute in say_fn "__libc_write".

(** ## The literal's pieces *)

(** The literal's first word, "hello, g", little-endian. *)
Definition msg_w0 : Z := 7430988242233353576.
(** Its second word, "libc\n" and the NUL, then the two zero bytes the
    layout's rounding adds. *)
Definition msg_w1 : Z := 44617066860.

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

(** Every piece is of the literal's object. *)
Lemma msg_ps_id l v : (l, v) ∈ msg_ps -> piece_id l = msg_base.
Proof.
  intros H. apply list_elem_of_In in H. cbn in H.
  repeat destruct H as [H|H]; first [injection H as <- _; reflexivity | contradiction].
Qed.

(** Where the pieces agree, the literal's 13 bytes are readable through
    its capability: what zsys_write's precondition asks of the buffer. *)
Lemma msg_readable m : all_agree m msg_ps -> readable_bytes m msg_ptr 13.
Proof.
  intros Ha. unfold msg_ps in Ha. apply all_agree_app in Ha as [[Hl _] Ha].
  apply all_agree_app in Ha as [H0 H1]. rewrite all_agree_cell in H0. rewrite all_agree_cell in H1.
  cbn [agree_piece fst snd] in Hl. destruct Hl as [E Lv].
  split; [lia|]. split; [exists msg_base, msg_reg; auto|]. split.
  - apply (access_read _ msg_base msg_reg (ptr_cap msg_ptr)); [right; reflexivity | exact E | | | ];
      cbn [ptr_addr msg_ptr msg_reg r_end]; unfold msg_base; [lia | lia | apply Z.mod_1_r].
  - intros i Hi. cbn [ptr_addr msg_ptr]. destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + destruct (H0 i ltac:(lia)) as [_ Hin]. destruct (Hin msg_reg E Lv) as (_ & _ & Hb).
      replace (msg_base + i) with (msg_base + (0 + i)) by lia. rewrite Hb.
      unfold byte_of. apply Z.mod_pos_bound. lia.
    + destruct (H1 (i - 8) ltac:(lia)) as [_ Hin]. destruct (Hin msg_reg E Lv) as (_ & _ & Hb).
      replace (msg_base + i) with (msg_base + (8 + (i - 8))) by lia. rewrite Hb.
      unfold byte_of. apply Z.mod_pos_bound. lia.
Qed.

(** ## The contracts *)

(** The registry: zsys_write's contract alone; everything else the
    program calls is in the module. *)
Definition say_registry (symbol : name) : option (contract fd_world) :=
  if name_eqb symbol (TAtom "zsys_write") then Some zsys_write_contract else None.

(** `main` called with no arguments. *)
Definition main_entry : frame := mkFrame main_fn [] [] None (Enter (TAtom "start") None).

(** ## Over any runtime *)

(** The proof over the [[runtime]] R. *)
Module SayLogic (R : Runtime).
Module LG := Logic R.
Module GL := GlibcLogicOn R LG.
Module ZW := ZsysWriteOn R LG.
Module SO := StrlenOn R LG.
Module L := LG.L.
Import L LG GL ZW.

(** The linked genv: the module, its symbols, R's free. *)
Definition say_ge : genv := mkGenv say_module say_globals R.free.

(** A call of `strlen` runs `__strlen`. *)
Lemma find_strlen : find_fn say_ge (TAtom "strlen") = Some (Defined strlen_fn).
Proof. vm_compute. reflexivity. Qed.

(** A call of `write` runs `__libc_write`. *)
Lemma find_write : find_fn say_ge (TAtom "write") = Some (Defined write_fn).
Proof. vm_compute. reflexivity. Qed.

Section wp.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** The Iris instance of say.c: zsys_write's contract and [fd_wi] for
    descriptor 1. *)
Local Instance say_irisGS : irisGS_gen hlc (nanofil_lang say_registry say_ge) Σ :=
  nanofil_irisGS say_registry (fd_wi [1]) say_ge.

(** The expressions of say.c's language. *)
Local Notation sexpr := (language.expr (nanofil_lang say_registry say_ge)).

(** glibc's strlen, called with the literal, owning its pieces:
    [wp_glibc_strlen] with its two words, returning 13. *)
Lemma strlen_msg_spec Φ :
  pts msg_ps -∗ (pts msg_ps -∗ Φ (Ret (WInt 13))) -∗
  WP (ERun (mkFrame strlen_fn [(TAtom "v0", WPtr msg_ptr)] [] None (Enter (TAtom "start") None)) : sexpr)
    {{ Φ }}.
Proof.
  iIntros "Hps HΦ". rewrite /msg_ps !pts_app. iDestruct "Hps" as "(Hl & H0 & H1)".
  iApply (SO.wp_glibc_strlen say_registry (fd_wi [1]) say_ge msg_ptr msg_base msg_reg [msg_w0; msg_w1] 13
            with "Hl [H0 H1]").
  - right. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. congruence.
  - vm_compute. congruence.
  - vm_compute. congruence.
  - repeat constructor; vm_compute; congruence.
  - split; [vm_compute; reflexivity|]. intros u Hu. do 13 (destruct u as [|u]; [vm_compute; congruence|]). lia.
  - cbn [words_ps]. rewrite app_nil_r pts_app. iFrame.
  - iIntros "Hl Hps". cbn [words_ps]. rewrite app_nil_r pts_app. iDestruct "Hps" as "[H0 H1]".
    iApply "HΦ". iFrame.
Qed.

(** `main`, owning the literal, returns 0: glibc's strlen measures it,
    glibc's write hands it to zsys_write for descriptor 1, whatever
    that returns, and the pieces are still owned. *)
Lemma main_spec :
  pts msg_ps -∗ WP (ERun main_entry : sexpr) {{ o, ⌜o = Ret (WInt 0)⌝ }}.
Proof.
  iIntros "Hps". repeat step.
  iApply wp_call_bind; [side | exact find_strlen | side |]. iNext.
  iApply (strlen_msg_spec with "Hps"). iIntros "Hps".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. norm_env.
  iApply wp_call_bind; [side | exact find_write | side |]. iNext.
  step.
  iApply (wp_zsys_write [1] say_registry say_ge with "Hps");
    [reflexivity | side | side | side | left; reflexivity | exact msg_readable |].
  iNext. iIntros (k _) "Hps".
  iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext. done.
Qed.

End wp.

(** `main` is safe: from a ready runtime, live objects apart, a memory
    holding the literal as [msg_ps] says, and a world whose errno is a
    writable int outside the literal's object and whose log
    descriptor, if any, is not 1, with any fuel, no labelled run stops
    with a [failure_ending], and a run that returns returns 0. By
    [heap_labelled_safe] from [main_spec], the ghost heap starting with
    the literal's pieces. *)
Theorem say_logic_safe Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ} m s w fuel :
  R.ready s m -> live_disjoint m -> all_agree m msg_ps ->
  errno_cell m (errno_ptr w) -> log_fd w <> Some 1 ->
  (forall a, span_contains (errno_span w) a -> ~ (msg_base <= a < msg_base + 16)) ->
  labelled_safe say_registry say_ge main_entry m s w fuel (fun o => o = Ret (WInt 0)).
Proof.
  intros Hr Hd Ha Hw Hlog Hapart.
  apply (heap_labelled_safe Σ say_registry (fd_wi [1]) say_ge main_entry m s w (list_to_map msg_ps)).
  - exact Hr.
  - exact Hd.
  - intros l v Hl. exact (all_agree_elem _ _ _ _ Ha (elem_of_list_to_map_2 _ _ _ Hl)).
  - split; [exact Hw|]. split; [|constructor; [exact Hlog | constructor]].
    intros sp a Hin Hs (l & v & reg & Hl & _ & [E _] & Hb). destruct Hin as [<-|[]].
    apply elem_of_list_to_map_2 in Hl. rewrite (msg_ps_id _ _ Hl) in E, Hb.
    unfold msg_ps in Ha. apply all_agree_app in Ha as [[[E' _] _] _].
    cbn [fst snd] in E'. rewrite E' in E. injection E as <-. exact (Hapart a Hs Hb).
  - intros HinvG HheapG. rewrite big_sepM_list_to_map; [|exact msg_ps_nodup].
    iIntros "Hps". iApply (main_spec with "Hps").
Qed.

End SayLogic.

(** The theorem for the interpreter's runtime. *)
Module InterpSayLogic := SayLogic InterpRuntime.
