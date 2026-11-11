(** GNU Hello's `set_program_name` (HelloName.v's
    [set_program_name_fn], Hello's own IR from HelloCode.v) linked with
    glibc, over the [os_world] of [OsWorld](../zsys/OsWorld.v), with no
    premise about the world: [set_program_name_glibc].

    gnulib's progname.c finds the last `/` of argv[0] with glibc's own
    strrchr ([wp_call_glibc_strrchr]); if seven bytes precede the base
    name it compares them with "/.libs/" by Hello's `memeq`, which calls
    `memcmp` (HelloGlibcProgLibs.v's [spn_L8]); if they match, it
    compares the base name with "lt-" by glibc's own strncmp
    (HelloGlibcProgCells.v's [spn_L16]) and skips it on a match. Then
    it stores the chosen pointers into Hello's `program_name` and
    libc's `program_invocation_name` and
    `program_invocation_short_name` ([spn_L18]).

    Unlike HelloProgName.v's triple, the callees are glibc's code, not
    contracts with ghost names, so the answer is exact: the cells end up
    pointing at argv[0]'s bytes [name_idx] and [short_idx]. The cells
    are ordinary objects of the memory, and a store into one keeps
    [os_wi] ([os_keeps]), so no premise about the world is needed.
    argv[0] is a [word_string] at any fraction, or read-only; HelloName.v
    explains why the compiled code has no null check (gnulib declares
    the parameter nonnull, and `argc >= 1` makes `argv[0]` a string).
    The literals are read-only [word_string]s. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic StringLogic MemLogic HelloLeaf HelloName.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop OsWorld StrchrCode MemchrLast StrlenWord
  StrrchrLogic StrncmpCode HelloGlibcProgCells HelloGlibcProgLibs.
Open Scope Z_scope.
Open Scope list_scope.

(** Integer arithmetic on an unknown stays folded when a premise is
    computed (Symbolic.v). *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** `set_program_name` over the [[runtime]] R and the Logic instance LG0. *)
Module HelloGlibcProgNameOn (R : Runtime) (LG0 : LogicSig R).
(** The "/.libs/" test and what follows it. *)
Module PL := HelloGlibcProgLibsOn R LG0.
(** glibc's strrchr. *)
Module SR := StrrchrLogicOn R LG0.
(** The world's rules. *)
Module OW := PL.OW.
(** The Logic instance. *)
Module LG := LG0.
(** Its language. *)
Module L := LG.L.
Import L LG.

Section progname.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** Hello's callees: glibc's strrchr, which calls glibc's strlen,
    Hello's memeq, and glibc's strncmp. *)
Context (Hstrrchr : find_fn ge (TAtom "strrchr") = Some (Defined glibc_strrchr))
  (Hstrlen : find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen))
  (Hmemeq : find_fn ge (TAtom "memeq") = Some (Defined memeq_fn))
  (Hstrncmp : find_fn ge (TAtom "strncmp") = Some (Defined glibc_strncmp)).
(** The globals: the three cells, each its own 8-aligned object, and
    the literals "/.libs/" and "lt-". *)
Context (pb nb sb : Z) (preg nreg sreg : region) (lp tp : ptr)
  (Hpb : lookup (TAtom "program_name") (ge_globals ge) = Some (mkPtr pb (Obj pb)))
  (Hnb : lookup (TAtom "program_invocation_name") (ge_globals ge) = Some (mkPtr nb (Obj nb)))
  (Hsb : lookup (TAtom "program_invocation_short_name") (ge_globals ge) = Some (mkPtr sb (Obj sb)))
  (Hlp : lookup (TAtom "progname#str.3") (ge_globals ge) = Some lp)
  (Htp : lookup (TAtom "progname#str.4") (ge_globals ge) = Some tp)
  (Hpb_cell : 0 <= pb /\ pb mod 8 = 0 /\ pb + 8 <= r_end preg /\ r_end preg <= 2 ^ 48)
  (Hnb_cell : 0 <= nb /\ nb mod 8 = 0 /\ nb + 8 <= r_end nreg /\ r_end nreg <= 2 ^ 48)
  (Hsb_cell : 0 <= sb /\ sb mod 8 = 0 /\ sb + 8 <= r_end sreg /\ r_end sreg <= 2 ^ 48).

(** [os_wi] w0 survives safepoints. *)
Local Instance pn_stable : SafepointStable (os_wi w0) := OW.os_wi_stable w0.
(** The Iris instance of the registry and [os_wi] w0. *)
Local Instance pn_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry (os_wi w0) ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** HelloGlibcProgCells.v's [memcmp_spec] for this genv. *)
Local Notation memcmp_spec := (PL.PC.memcmp_spec w0 registry ge).
(** The three cells, holding x, y and z. *)
Local Notation name_cells := (PL.PC.name_cells pb nb sb preg nreg sreg).
(** From L8 on. *)
Local Notation spn_L8 := (PL.spn_L8 w0 registry ge Hmemeq Hstrncmp pb nb sb preg nreg sreg lp tp Hpb Hnb Hsb Hlp Htp
  Hpb_cell Hnb_cell Hsb_cell).

(** glibc and Hello's `set_program_name(argv0)`: on the string s at p,
    at any fraction or read-only, it stores into `program_name` and
    `program_invocation_name` a pointer to the byte [name_idx] of s,
    and into `program_invocation_short_name` one to its byte
    [short_idx], and hands the string back. *)
Lemma set_program_name_glibc (Hm : SR.memrchr_spec registry (os_wi w0) ge) (Hcmp : memcmp_spec)
    dq p s x0 y0 z0 Φ :
  (dq = DfracDiscarded \/ exists q, dq = DfracOwn q) ->
  word_string dq p s -∗ word_string DfracDiscarded lp libs_bytes -∗ word_string DfracDiscarded tp lt_bytes -∗
  name_cells x0 y0 z0 -∗
  ▷ (word_string dq p s -∗ name_cells (ptr_add p (Z.of_nat (name_idx s))) (ptr_add p (Z.of_nat (name_idx s)))
       (ptr_add p (Z.of_nat (short_idx s))) -∗ Φ RetVoid) -∗
  WP (ERun (invocation set_program_name_fn [WPtr p]) : gexpr) {{ Φ }}.
Proof.
  intros Hdq. iIntros "Hs #Hlibs #Hlt Hc HΦ". rewrite set_program_name_entry.
  iDestruct "Hs" as "(%b & %reg & %ws & %Hs & Hw)". iDestruct (word_string_intro with "Hw") as "Hs"; [exact Hs|].
  destruct (str_shape_addr _ _ _ _ _ Hs) as [Ha0 Ha48].
  iApply wp_enter; [exact find_s_start | reflexivity |]. iNext. cbn [b_insts b_jump s_start].
  iApply (SR.wp_call_glibc_strrchr registry (os_wi w0) ge Hm _ _ _ _ _ _ _ _ _ dq p s 47 with "Hs");
    [reflexivity | lia | exact Hstrrchr | exact Hstrlen | reflexivity |].
  iNext. iIntros "Hs". change (47 mod 256) with 47.
  destruct (last_byte 47 (s ++ [0])) as [t|] eqn:Ht; cbn [hit_ptr]; gen_env.
  - pose proof (last_slash s t Ht) as Ht'.
    assert (Hj : base_idx s = S t) by (unfold base_idx; rewrite Ht; reflexivity).
    do 2 (iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]; iNext; gen_env).
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 1); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_s_L6 | reflexivity |]. iNext. cbn [b_insts b_jump s_L6].
    iApply (wp_flight _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ptr_addr p + Z.of_nat (S t)));
      [word_premise | cbn; do 2 f_equal; rewrite !Z.mod_small; lia | word_premise |].
    iNext. iApply wp_goto. iNext. iApply wp_enter; [exact find_s_L8 | word_premise |]. iNext. gen_env.
    iApply (spn_L8 Hcmp with "Hs Hlibs Hlt Hc HΦ"); [exact Hdq | rewrite Hj; reflexivity | reflexivity].
  - assert (Hj : base_idx s = O) by (unfold base_idx; rewrite Ht; reflexivity).
    do 2 (iApply wp_let; [reflexivity | reflexivity | word_premise | intros m; word_premise |]; iNext; gen_env).
    iApply (wp_branch _ _ _ _ _ _ _ _ _ _ 0); [word_premise|]. iNext. cbn [Z.eqb edge_label].
    iApply wp_enter; [exact find_s_L8 | word_premise |]. iNext. gen_env.
    iApply (spn_L8 Hcmp with "Hs Hlibs Hlt Hc HΦ");
      [exact Hdq | rewrite Hj; change (Z.of_nat 0) with 0; rewrite ptr_add_0; reflexivity | reflexivity].
Qed.

End progname.
End HelloGlibcProgNameOn.
