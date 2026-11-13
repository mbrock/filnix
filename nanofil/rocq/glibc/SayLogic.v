(** A small C program that writes a greeting to standard output still
    exercises both userland glibc and a system-call boundary. Here we
    link `c: say.c` with the intermediate representation of userland
    glibc's `c: string/strlen.c` and `c: io/write.c`, and prove safety
    through the program logic in [Logic](Logic.v).

    In `c: say.c`, `c: main` writes the 14-byte literal `"hello, glibc\n"`
    to file descriptor 1 with `c: write(1, msg, strlen(msg))`. Both calls
    step through glibc's own IR: `c: strlen` resolves to `__strlen` and
    uses [wp_glibc_strlen], while `c: write` calls `__GI___libc_write`,
    which forwards to `zsys_write`. Only `zsys_write` crosses outside
    the module, so its trusted contract from [OsWrite](zsys/OsWrite.v)
    is the only entry in the [[runtime]] registry.

    Because `zsys_write` writes bytes to a file descriptor and may
    update `c: errno` on failure, the proof must track both the thread's
    error cell and the open descriptors. We represent that
    operating-system state with [os_world] from [OsWorld](zsys/OsWorld.v)
    and connect it to memory through [os_wi]. In any valid state,
    `c: errno` is a permanent global cell separate from the literal, and
    file descriptor 1 is open without colliding with the runtime log.
    Theorem [say_logic_safe] proves that `c: main` never fails from such
    a state and returns 0 when it finishes. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules ExternalCalls ExternalMachine Transport Pieces Heap ContractFrame Language Logic
  StringLogic MemLogic.
From Glibc Require Import SayCode GlibcLogic OsBlocks OsWorld OsWrite StrlenLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The module

    The compiled fixture [say_term] links `c: main`, its string literal,
    glibc's `__strlen`, and `__GI___libc_write` together with their
    exported aliases. We decode that module, record the base addresses
    and [[capability]] descriptors assigned by layout, and extract the
    three defined functions we verify. *)

(** [say_module] holds the decoded IR module for `c: say.c` linked with
    glibc's `c: strlen` and `c: write`. *)
Definition say_module : module :=
  match decode_module say_term with Some md => md | None => [] end.

(** [say_decodes] verifies by computation that [say_term] decodes to
    [say_module]. *)
Lemma say_decodes : decode_module say_term = Some say_module.
Proof. vm_compute. reflexivity. Qed.

(** [msg_base] is the base address assigned to the string literal `msg`,
    which `c: link.pl` renames to `say#msg`. *)
Definition msg_base : Z := 65552.

(** [msg_ptr] pairs [msg_base] with a read-only [[capability]] for the
    literal object. *)
Definition msg_ptr : ptr := mkPtr msg_base (Ro msg_base).

(** [msg_reg] describes the literal's 16-byte global [[region]],
    rounding its 14 bytes up to two 8-byte words. *)
Definition msg_reg : region := mkRegion msg_base (msg_base + 16) GlobalData Live.

(** [say_globals] lists the module's global symbols and their initial
    pointers as produced by module layout. *)
Definition say_globals : list (name * ptr) :=
  [(TAtom "write", mkPtr 65600 (Fn (TAtom "__GI___libc_write")));
   (TAtom "strlen", mkPtr 65584 (Fn (TAtom "__strlen")));
   (TAtom "__GI___libc_write", mkPtr 65600 (Fn (TAtom "__GI___libc_write")));
   (TAtom "__strlen", mkPtr 65584 (Fn (TAtom "__strlen")));
   (TAtom "say#msg", msg_ptr);
   (TAtom "main", mkPtr 65536 (Fn (TAtom "main")))].

(** [say_layout] checks by computation that laying out [say_module]
    produces [say_globals]. *)
Lemma say_layout : option_map fst (initial_memory say_module) = Some say_globals.
Proof. vm_compute. reflexivity. Qed.

(** [say_fn] looks up a defined function named n in [say_module],
    falling back to an empty stub when missing. *)
Definition say_fn (n : string) : func :=
  match find_direct (TAtom n) say_module with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "export") (RClass W) [] []
  end.

(** [main_fn] is the decoded body of `c: main` from `c: say.c`. *)
Definition main_fn : func := Eval vm_compute in say_fn "main".
(** [strlen_fn] is the decoded body of glibc's `__strlen`. *)
Definition strlen_fn : func := Eval vm_compute in say_fn "__strlen".
(** [write_fn] is the decoded body of glibc's `__GI___libc_write`. *)
Definition write_fn : func := Eval vm_compute in say_fn "__GI___libc_write".

(** ## The literal's pieces

    A separation-logic proof tracks individual memory cells rather than a
    whole memory image. Before stepping through `c: main`, we spell out
    the literal's two 64-bit words and combine them with the caller's
    4-byte `c: errno` cell. We then verify that all piece keys are
    distinct, match initial memory, and satisfy the readability
    condition that `zsys_write` requires. *)

(** [msg_w0] encodes the first eight bytes `"hello, g"` as a
    little-endian 64-bit integer. *)
Definition msg_w0 : Z := 7430988242233353576.
(** [msg_w1] encodes `"libc\n"`, the terminating NUL byte, and the two
    zero padding bytes added by 8-byte alignment. *)
Definition msg_w1 : Z := 44617066860.

(** [msg_ps] collects the literal's liveness token and its two aligned
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

(** Every piece in [msg_ps] belongs to the literal's object at
    [msg_base], as [msg_ps_id] proves. *)
Lemma msg_ps_id l v : (l, v) ∈ msg_ps -> piece_id l = msg_base.
Proof.
  intros H. apply list_elem_of_In in H. cbn in H.
  repeat destruct H as [H|H]; first [injection H as <- _; reflexivity | contradiction].
Qed.

(** [say_ps] combines the literal's pieces with the 4-byte `c: errno`
    block at base eb in memory m. *)
Definition say_ps (m : mem) (eb : Z) : list (piece * pval) :=
  msg_ps ++ blk_now m eb 0 4.

(** A separation-logic heap cannot contain duplicate keys for the same
    memory cell. Whenever `c: errno` lives in a different object eb from
    [msg_base], [say_ps_nodup] proves that [say_ps] has distinct keys. *)
Lemma say_ps_nodup m eb : eb <> msg_base -> NoDup (say_ps m eb).*1.
Proof.
  intros Hne. unfold say_ps. rewrite fmap_app blk_now_keys; [|lia].
  apply NoDup_app; split; [exact msg_ps_nodup|]. split.
  - intros k H1 H2. apply list_elem_of_fmap in H1 as ([l v] & -> & Hin).
    pose proof (msg_ps_id l v Hin) as Hid. cbn [fst] in *.
    apply elem_of_app in H2 as [H2|H2]; apply list_elem_of_fmap in H2 as (i & -> & _);
      cbn [piece_id] in Hid; congruence.
  - cbn. repeat (apply NoDup_cons_2;
      [ intros H; apply list_elem_of_In in H; cbn in H;
        repeat destruct H as [H|H]; first [discriminate | injection H; lia | exact H] |]).
    apply NoDup_nil_2.
Qed.

(** A thread's `c: errno` cell must match physical memory before
    execution begins. Whenever eb holds a permanent `c: errno` object in
    memory m, [errno_blk_agree] shows that its 4-byte block agrees with
    m. *)
Lemma errno_blk_agree m eb :
  permanent_errno m (mkPtr eb (Obj eb)) -> all_agree m (blk_now m eb 0 4).
Proof.
  intros (eb' & reg & [= <-] & _ & _ & [E Lv] & _ & Hend).
  assert (Hreg : registered m eb) by (unfold registered; congruence).
  cbn [blk_now blk_bytes blk_caps seqZ Z.to_nat Pos.to_nat fmap list_fmap byte_ps aux_ps app all_agree agree_piece fst snd].
  repeat (split; [split; [exact Hreg | intros reg' E' _; rewrite E in E'; injection E' as <-;
                          split; [lia | split; [lia | first [reflexivity | left; reflexivity]]]] |]).
  exact I.
Qed.

(** An external write call checks that all 13 bytes of the greeting lie
    inside a live readable region. Lemma [msg_readable] proves
    [os_readable] for [msg_ptr] whenever [msg_ps] agrees with memory m. *)
Lemma msg_readable m : all_agree m msg_ps -> os_readable m msg_ptr 13.
Proof.
  intros Ha. split; [lia|]. right.
  unfold msg_ps in Ha. apply all_agree_app in Ha as [[Hl _] Ha].
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

(** ## The contracts

    Because `c: strlen` and `c: write` are defined inside [say_module],
    the only external symbol in the program is `zsys_write`. We place its
    contract in the module's registry and build the entry [[frame]] for
    `c: main`. *)

(** [say_registry] maps `zsys_write` to [os_write_contract] and leaves
    all other symbol names unbound. *)
Definition say_registry (symbol : name) : option (contract os_world) :=
  if name_eqb symbol (TAtom "zsys_write") then Some os_write_contract else None.

(** [main_entry] constructs the initial call frame that enters `c: main`
    with no arguments. *)
Definition main_entry : frame := mkFrame main_fn [] [] None (Enter (TAtom "start") None).

(** ## Over any runtime

    Because `zsys_write` is the only external call, the safety proof
    works over any Fil-C [[runtime]] R that implements its contract.
    Inside [SayLogic], we establish a specification for `c: strlen` on
    the literal, step through `c: main` and `c: write`, and conclude
    with a safety theorem for any ready runtime state. *)

(** The module [SayLogic] verifies `c: say.c` over an arbitrary runtime
    R. *)
Module SayLogic (R : Runtime).
Module LG := Logic R.
Module GL := GlibcLogicOn R LG.
Module OW := OsWriteOn R LG.
Module SO := StrlenOn R LG.
Module L := LG.L.
Import L LG GL OW OW.OW.

(** [say_ge] builds the [[genv|global environment]] from [say_module],
    [say_globals], and R's free-list relation. *)
Definition say_ge : genv := mkGenv say_module say_globals R.free.

(** [find_strlen] confirms that looking up `c: strlen` in [say_ge]
    resolves to [strlen_fn]. *)
Lemma find_strlen : find_fn say_ge (TAtom "strlen") = Some (Defined strlen_fn).
Proof. vm_compute. reflexivity. Qed.

(** [find_write] confirms that looking up `c: write` in [say_ge]
    resolves through the weak alias to [write_fn]. *)
Lemma find_write : find_fn say_ge (TAtom "write") = Some (Defined write_fn).
Proof. vm_compute. reflexivity. Qed.

Section wp.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world).

(** [say_irisGS] supplies the Iris [[state-interpretation]] for
    [say_module] using [say_registry] and the OS world w0. *)
Local Instance say_irisGS : irisGS_gen hlc (nanofil_lang say_registry say_ge) Σ :=
  nanofil_irisGS say_registry (os_wi w0) say_ge.

(** [sexpr] abbreviates the expression type of `c: say.c`'s language. *)
Local Notation sexpr := (language.expr (nanofil_lang say_registry say_ge)).

(** Calling `c: strlen` on `"hello, glibc\n"` returns 13 and restores
    ownership of [msg_ps]. Lemma [strlen_msg_spec] proves this by
    applying [wp_glibc_strlen] to the literal's two words. *)
Lemma strlen_msg_spec Φ :
  pts msg_ps -∗ (pts msg_ps -∗ Φ (Ret (WInt 13))) -∗
  WP (ERun (mkFrame strlen_fn [(TAtom "v0", WPtr msg_ptr)] [] None (Enter (TAtom "start") None)) : sexpr)
    {{ Φ }}.
Proof.
  iIntros "Hps HΦ". rewrite /msg_ps !pts_app. iDestruct "Hps" as "(Hl & H0 & H1)".
  iApply (SO.wp_glibc_strlen say_registry (os_wi w0) say_ge msg_ptr msg_base msg_reg [msg_w0; msg_w1] 13
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

(** When the program owns the literal's pieces [msg_ps] and the thread's
    `c: errno` cell at eb, `c: main` measures the greeting with
    `c: strlen`, passes it to `zsys_write` on descriptor 1, and returns
    0, as [main_spec] proves. *)
Lemma main_spec eb :
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In 1 (ow_fds w0) ->
  pts msg_ps -∗ errno_any eb -∗ WP (ERun main_entry : sexpr) {{ o, ⌜o = Ret (WInt 0)⌝ }}.
Proof.
  intros He Hfd. iIntros "Hps Herr". repeat step.
  iApply wp_call_bind; [side | exact find_strlen | side |]. iNext.
  iApply (strlen_msg_spec with "Hps"). iIntros "Hps".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. norm_env.
  iApply wp_call_bind; [side | exact find_write | side |]. iNext.
  step.
  iApply (wp_zsys_write w0 say_registry say_ge with "Hps Herr");
    [reflexivity | side | side | side | exact He | exact Hfd | exact msg_readable |].
  iNext. iIntros (k _) "Hps Herr".
  iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext. done.
Qed.

End wp.

(** Running `c: main` never reaches a failure state and always returns 0
    when it terminates, provided the runtime is ready, live objects are
    disjoint, initial memory holds [msg_ps], and the OS world w supplies
    a valid `c: errno`, a registered self pointer, and file descriptor 1
    separate from the log descriptor. Theorem [say_logic_safe] proves
    this via [heap_labelled_safe]. *)
Theorem say_logic_safe Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ} m s w eb fuel :
  R.ready s m -> live_disjoint m -> all_agree m msg_ps ->
  ow_errno w = Some (mkPtr eb (Obj eb)) -> permanent_errno m (mkPtr eb (Obj eb)) ->
  self_registered m (ow_self w) -> In 1 (ow_fds w) ->
  Forall (fun fd => ow_log_fd w <> Some fd) (ow_fds w) -> eb <> msg_base ->
  labelled_safe say_registry say_ge main_entry m s w fuel (fun o => o = Ret (WInt 0)).
Proof.
  intros Hr Hd Ha He Hpe Hself Hfd Hlog Hne.
  apply (heap_labelled_safe Σ say_registry (os_wi w) say_ge main_entry m s w (list_to_map (say_ps m eb))).
  - exact Hr.
  - exact Hd.
  - intros l v Hl. apply (all_agree_elem m (say_ps m eb)).
    + apply all_agree_app. split; [exact Ha | exact (errno_blk_agree m eb Hpe)].
    + exact (elem_of_list_to_map_2 _ _ _ Hl).
  - split; [reflexivity|]. split; [|split; [exact Hself | exact Hlog]].
    intros p Hp. rewrite He in Hp. injection Hp as <-. split; [exact Hpe|].
    intros reg Hl. apply elem_of_list_to_map_2 in Hl.
    apply elem_of_app in Hl as [Hl|Hl].
    + exfalso. pose proof (msg_ps_id _ _ Hl) as Hid. cbn [piece_id] in Hid. exact (Hne Hid).
    + exfalso. apply elem_of_app in Hl as [Hl|Hl];
        [apply byte_ps_elem in Hl as (? & ? & _ & [=] & _) |
         apply aux_ps_elem in Hl as (? & ? & _ & [=] & _)].
  - intros HinvG HheapG. rewrite big_sepM_list_to_map; [|exact (say_ps_nodup m eb Hne)].
    iIntros "Hps". iDestruct (pts_app msg_ps (blk_now m eb 0 4) with "Hps") as "[Hps Hb]".
    iApply (main_spec w eb He Hfd with "Hps [Hb]").
    iExists (blk_bytes m eb 0 4), (blk_caps m eb 0 4). iFrame "Hb".
    iPureIntro. split; reflexivity.
Qed.

End SayLogic.

(** [InterpSayLogic] instantiates [SayLogic] with the interpreter's
    runtime. *)
Module InterpSayLogic := SayLogic InterpRuntime.
