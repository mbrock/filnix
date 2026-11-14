(** Programs call glibc's getopt through global cells: optind holds the
    index of the next argument, opterr says whether to print errors,
    optarg returns an option's argument, and optopt returns the option
    character. The parser itself keeps its state in a private object, so
    that a reentrant caller can pass its own. The wrapper
    _getopt_internal joins the two. It copies optind and opterr into the
    private object, calls the reentrant parser with that object, and
    copies the private index, argument and option character back into
    the public cells. This file proves those copies. The parser's own
    behaviour stays a premise, because its proof is not finished. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString GetoptModule GetoptState GetoptBytes
  GetoptInitialize GetoptEntry.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

Local Transparent glibc_getopt_internal glibc_getopt_internal_r.

(** ## The wrapper's shape

    A proof about the wrapper is useful only if it starts where a real
    call starts. A call of the wrapper enters its single block with no
    stack objects, and the wrapper returns a 32-bit integer. The facts
    below check this, and they locate the parser call inside the block. *)

(** The wrapper has no stack objects and returns a 32-bit integer. *)
Lemma getopt_internal_shape : local_objects glibc_getopt_internal = [] /\ fn_ret glibc_getopt_internal = RClass W.
Proof. vm_compute. split; reflexivity. Qed.

(** The wrapper's only block copies the cells, calls the parser and returns. *)
Definition getopt_wrap_blk : block := Eval vm_compute in
  match find_block (TAtom "start") (fn_blocks glibc_getopt_internal) with
  | Some b => b | None => mkBlock (TAtom "start") [] [] JUnreachable end.

(** These are the block's instructions after the call of the parser. *)
Definition getopt_wrap_after : list inst := Eval vm_compute in skipn 15 (b_insts getopt_wrap_blk).

(** The block's fifteenth instruction is the call, so the copies back
    start right after it, and nothing else in the block calls. *)
Lemma getopt_wrap_split : exists rd args,
  b_insts getopt_wrap_blk = (firstn 14 (b_insts getopt_wrap_blk) ++
    Call rd (Global (TAtom "_getopt_internal_r")) args :: getopt_wrap_after)%list.
Proof. do 2 eexists. vm_compute. reflexivity. Qed.

(** A caller may set optind to 0 to make getopt start over. The wrapper
    copies that 0 into the private index, and the parser's first blocks
    then treat the object as one that needs setting up and start at 1. *)
Lemma wrapper_ctl_reset : needs_init (mkGetoptState 0 1 0 null 1 null 0 0 0) /\ (if 0 =? 0 then 1 else 0) = 1.
Proof. split; [left; reflexivity | reflexivity]. Qed.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptWrapperOn (R : Runtime) (LG0 : LogicSig R).
(** The setup module supplies the private fields and the step tactics. *)
Module I := GetoptInitializeOn R LG0.
Import I I.S I.S.FI I.S.FI.ML I.S.FI.LG I.S.FI.L I.ST.

(** This tactic enters a block and evaluates its phi assignments. *)
Ltac en := iApply wp_enter; [reflexivity | reflexivity | iNext]; cbn [b_insts b_jump].

(** This tactic loads a four-byte cell as a signed 32-bit value. *)
Ltac ld H :=
  iApply (wp_raw_load_sub_bytes_dq with H);
    [reflexivity | vx | reflexivity | apply load_sw_int; assumption | left; reflexivity | arith |];
  iNext; iIntros H.

(** This tactic stores a 32-bit value into four owned bytes. *)
Ltac sw H :=
  iApply (wp_raw_store_w with H); [vx | vx | reflexivity | arith | reflexivity | wi_store |];
  iNext; iIntros H.

Section wrapper.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the wrapper's safepoints. *)
Local Instance wrap_stable : SafepointStable (os_wi w0) := I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance wrap_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** ## The copies around the parser

    The wrapper owns no state of its own; it moves values between two
    owners. The caller owns the four public cells, each in its own global
    object, and the private object's index and error fields. The parser
    receives the private fields with the public values in them, and it
    gives back the three private fields that the wrapper copies out. *)

(** The first half of the wrapper copies optind and opterr into the
    private index and error fields and calls the parser. When the parser
    returns, the wrapper's frame resumes right after the call with the
    parser's result in its environment. The caller gets the parser's
    returned resources and the two public cells unchanged. *)
Lemma wp_getopt_internal_in e n av p lo li lonly pc b r oi roi oe roe i err i0 e0
    (Ψ : Z -> Z -> Z -> ptr -> iProp Σ) Φ :
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr av) ->
  lookup (TAtom "v4") e = Some (WPtr p) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) -> lookup (TAtom "v10") e = Some (WInt lonly) ->
  lookup (TAtom "v12") e = Some (WInt pc) ->
  0 <= n < 2 ^ 32 -> 0 <= lonly < 2 ^ 32 -> 0 <= pc < 2 ^ 32 ->
  find_fn ge (TAtom "_getopt_internal_r") = Some (Defined glibc_getopt_internal_r) ->
  lookup (TAtom "glibc_getopt#getopt_data") (ge_globals ge) = Some (mkPtr b (Obj b)) ->
  lookup (TAtom "optind") (ge_globals ge) = Some (mkPtr oi (Obj oi)) ->
  lookup (TAtom "opterr") (ge_globals ge) = Some (mkPtr oe (Obj oe)) ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < oi -> oi + 4 <= r_end roi -> r_end roi <= 2 ^ 48 ->
  0 < oe -> oe + 4 <= r_end roe -> r_end roe <= 2 ^ 48 ->
  live oi roi -∗ int_cell oi 0 i -∗ live oe roe -∗ int_cell oe 0 err -∗
  live b r -∗ int_cell b 0 i0 -∗ int_cell b 4 e0 -∗
  (∀ cf, ⌜call_frame glibc_getopt_internal_r
            [WInt n; WPtr av; WPtr p; WPtr lo; WPtr li; WInt lonly; WPtr (mkPtr b (Obj b)); WInt pc] = Some cf⌝ -∗
     live b r -∗ int_cell b 0 i -∗ int_cell b 4 err -∗
     WP (ERun cf : gexpr) {{ o, ∃ x i' c' a' ra, ⌜o = Ret (WInt x) /\ 0 <= x < 2 ^ 32 /\ 0 <= ptr_addr a' < 2 ^ 64⌝ ∗
       live b r ∗ int_cell b 0 i' ∗ int_cell b 8 c' ∗ pcell b 16 a' ∗ live_capq DfracDiscarded (ptr_cap a') ra ∗
       Ψ x i' c' a' }}) -∗
  (∀ e2 x i' c' a' ra, ⌜0 <= x < 2 ^ 32 /\ 0 <= ptr_addr a' < 2 ^ 64⌝ -∗
     live b r -∗ int_cell b 0 i' -∗ int_cell b 8 c' -∗ pcell b 16 a' -∗ live_capq DfracDiscarded (ptr_cap a') ra -∗
     Ψ x i' c' a' -∗ live oi roi -∗ int_cell oi 0 i -∗ live oe roe -∗ int_cell oe 0 err -∗
     WP (ERun (mkFrame glibc_getopt_internal (put (TAtom "v30") (WInt x) e2) [] None
                 (Exec (TAtom "start") getopt_wrap_after (b_jump getopt_wrap_blk))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros H0 H2 H4 H6 H8 H10 H12 Hn Hlo Hpc Hfn Hgd Hgi Hge Hb Hal Hend Hr Hoi Hoie Hoir Hoe Hoee Hoer.
  iIntros "Hli [%Hi Hib] Hle [%He Heb] Hl [%Hi0 Hb0] [%He0 Hb4] HR HK".
  en. st. st. norm. chk "Hli". ld "Hli Hib". chk "Hl". sw "Hl Hb0".
  st. st. norm. st. chk "Hle". ld "Hle Heb". chk "Hl". sw "Hl Hb4".
  st. unwrap.
  set (xs := [WInt n; WPtr av; WPtr p; WPtr lo; WPtr li; WInt lonly; WPtr (mkPtr b (Obj b)); WInt pc]).
  assert (Hcf : exists cf, call_frame glibc_getopt_internal_r xs = Some cf) by (eexists; reflexivity).
  destruct Hcf as [cf Hcf].
  iApply (wp_call_bind registry (os_wi w0) ge _ _ _ _ _ _ _ _ _ xs _ cf);
    [ cbn -[put]; repeat (rewrite Symbolic.lookup_after_put; cbn -[put]);
      rewrite ?H0 ?H2 ?H4 ?H6 ?H8 ?H10 ?H12 ?Hgd; cbn;
      rewrite (Z.mod_small n); [|lia]; rewrite (Z.mod_small lonly); [|lia]; rewrite (Z.mod_small pc); [|lia];
      reflexivity
    | exact Hfn | exact Hcf |].
  iNext. iApply (wp_wand with "[HR Hl Hb0 Hb4]").
  { iApply ("HR" with "[%] Hl [Hb0] [Hb4]"); [exact Hcf | by iSplit | by iSplit]. }
  iIntros (o) "(%x & %i' & %c' & %a' & %ra & (-> & %Hx & %Ha') & Hl & Hb0 & Hb8 & Hb16 & Hcap & HΨ)".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at word_at_class].
  unwrap. iApply ("HK" with "[%] Hl Hb0 Hb8 Hb16 Hcap HΨ Hli [Hib] Hle [Heb]"); [lia | by iSplit | by iSplit].
Qed.

(** The second half copies the private index to optind, the argument to
    optarg and the option character to optopt, and returns the parser's
    result. It reads nothing of the frame but the result, so it holds
    for any environment the first half leaves. *)
Lemma wp_getopt_internal_out e x i' c' a' ra b r oi roi oa roa oo roo i a0 c0 Φ :
  0 <= x < 2 ^ 32 -> 0 <= ptr_addr a' < 2 ^ 64 ->
  lookup (TAtom "glibc_getopt#getopt_data") (ge_globals ge) = Some (mkPtr b (Obj b)) ->
  lookup (TAtom "optind") (ge_globals ge) = Some (mkPtr oi (Obj oi)) ->
  lookup (TAtom "optarg") (ge_globals ge) = Some (mkPtr oa (Obj oa)) ->
  lookup (TAtom "optopt") (ge_globals ge) = Some (mkPtr oo (Obj oo)) ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < oi -> oi + 4 <= r_end roi -> r_end roi <= 2 ^ 48 ->
  0 < oa -> oa mod 8 = 0 -> oa + 8 <= r_end roa -> r_end roa <= 2 ^ 48 ->
  0 < oo -> oo + 4 <= r_end roo -> r_end roo <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 i' -∗ int_cell b 8 c' -∗ pcell b 16 a' -∗ live_capq DfracDiscarded (ptr_cap a') ra -∗
  live oi roi -∗ int_cell oi 0 i -∗ live oa roa -∗ pcell oa 0 a0 -∗ live oo roo -∗ int_cell oo 0 c0 -∗
  (live b r -∗ int_cell b 0 i' -∗ int_cell b 8 c' -∗ pcell b 16 a' -∗
     live oi roi -∗ int_cell oi 0 i' -∗ live oa roa -∗ pcell oa 0 a' -∗ live oo roo -∗ int_cell oo 0 c' -∗
     Φ (Ret (WInt x))) -∗
  WP (ERun (mkFrame glibc_getopt_internal (put (TAtom "v30") (WInt x) e) [] None
              (Exec (TAtom "start") getopt_wrap_after (b_jump getopt_wrap_blk))) : gexpr) {{ Φ }}.
Proof.
  intros Hx Ha' Hgd Hgi Hga Hgo Hb Hal Hend Hr Hoi Hoie Hoir Hoa Hoaa Hoae Hoar Hoo Hooe Hoor.
  iIntros "Hl [%Hi' Hb0] [%Hc' Hb8] Hb16 Hcap Hli [%Hi Hib] Hla Hab Hlo [%Hc Hcb] HK".
  unfold getopt_wrap_after, getopt_wrap_blk. cbn [b_jump].
  st. st. norm. chk "Hl". ld "Hl Hb0". chk "Hli". sw "Hli Hib".
  st. st. st. norm. chk "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hb16 Hcap"); [reflexivity | vx | left; reflexivity | arith | arith | exact Ha' |].
  iNext. iIntros "Hl Hb16 _". chk "Hla".
  iApply (wp_raw_store_pointer with "Hla Hab"); [vx | vx | reflexivity | arith | arith | wi_store |].
  iNext. iIntros "Hla Hab".
  st. st. st. norm. chk "Hl". ld "Hl Hb8". chk "Hlo". sw "Hlo Hcb".
  iApply (wp_ret registry (os_wi w0) ge _ _ _ _ _ (WInt (x mod 2 ^ 32))); [reflexivity | vx |].
  unwrap. iNext.
  iApply ("HK" with "Hl [Hb0] [Hb8] Hb16 Hli [Hib] Hla Hab Hlo [Hcb]"); by iSplit.
Qed.

(** A program that calls the wrapper must know that each public cell
    ends up with the right private value, because it reads them right
    after the call. The caller supplies the parser's behaviour as a
    premise. That premise receives the exact frame of the reentrant
    parser with the wrapper's eight arguments, the private object's life,
    and the private index and error fields holding the public optind and
    opterr. The parser returns a 32-bit result, the private index, option
    character and argument, a share of the argument's object life, and
    the caller's own resources. The wrapper then writes the private index
    to optind, the argument to optarg and the option character to optopt,
    leaves opterr unchanged, and returns the parser's result. *)
Lemma wp_getopt_internal e n av p lo li lonly pc b r oi roi oe roe oa roa oo roo i err a0 c0 i0 e0
    (Ψ : Z -> Z -> Z -> ptr -> iProp Σ) Φ :
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr av) ->
  lookup (TAtom "v4") e = Some (WPtr p) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) -> lookup (TAtom "v10") e = Some (WInt lonly) ->
  lookup (TAtom "v12") e = Some (WInt pc) ->
  0 <= n < 2 ^ 32 -> 0 <= lonly < 2 ^ 32 -> 0 <= pc < 2 ^ 32 ->
  find_fn ge (TAtom "_getopt_internal_r") = Some (Defined glibc_getopt_internal_r) ->
  lookup (TAtom "glibc_getopt#getopt_data") (ge_globals ge) = Some (mkPtr b (Obj b)) ->
  lookup (TAtom "optind") (ge_globals ge) = Some (mkPtr oi (Obj oi)) ->
  lookup (TAtom "opterr") (ge_globals ge) = Some (mkPtr oe (Obj oe)) ->
  lookup (TAtom "optarg") (ge_globals ge) = Some (mkPtr oa (Obj oa)) ->
  lookup (TAtom "optopt") (ge_globals ge) = Some (mkPtr oo (Obj oo)) ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < oi -> oi + 4 <= r_end roi -> r_end roi <= 2 ^ 48 ->
  0 < oe -> oe + 4 <= r_end roe -> r_end roe <= 2 ^ 48 ->
  0 < oa -> oa mod 8 = 0 -> oa + 8 <= r_end roa -> r_end roa <= 2 ^ 48 ->
  0 < oo -> oo + 4 <= r_end roo -> r_end roo <= 2 ^ 48 ->
  live oi roi -∗ int_cell oi 0 i -∗ live oe roe -∗ int_cell oe 0 err -∗
  live oa roa -∗ pcell oa 0 a0 -∗ live oo roo -∗ int_cell oo 0 c0 -∗
  live b r -∗ int_cell b 0 i0 -∗ int_cell b 4 e0 -∗
  (∀ cf, ⌜call_frame glibc_getopt_internal_r
            [WInt n; WPtr av; WPtr p; WPtr lo; WPtr li; WInt lonly; WPtr (mkPtr b (Obj b)); WInt pc] = Some cf⌝ -∗
     live b r -∗ int_cell b 0 i -∗ int_cell b 4 err -∗
     WP (ERun cf : gexpr) {{ o, ∃ x i' c' a' ra, ⌜o = Ret (WInt x) /\ 0 <= x < 2 ^ 32 /\ 0 <= ptr_addr a' < 2 ^ 64⌝ ∗
       live b r ∗ int_cell b 0 i' ∗ int_cell b 8 c' ∗ pcell b 16 a' ∗ live_capq DfracDiscarded (ptr_cap a') ra ∗
       Ψ x i' c' a' }}) -∗
  (∀ x i' c' a', Ψ x i' c' a' -∗ live b r -∗ int_cell b 0 i' -∗ int_cell b 8 c' -∗ pcell b 16 a' -∗
     live oi roi -∗ int_cell oi 0 i' -∗ live oe roe -∗ int_cell oe 0 err -∗
     live oa roa -∗ pcell oa 0 a' -∗ live oo roo -∗ int_cell oo 0 c' -∗ Φ (Ret (WInt x))) -∗
  WP (ERun (mkFrame glibc_getopt_internal e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros H0 H2 H4 H6 H8 H10 H12 Hn Hlo Hpc Hfn Hgd Hgi Hge Hga Hgo
    Hb Hal Hend Hr Hoi Hoie Hoir Hoe Hoee Hoer Hoa Hoaa Hoae Hoar Hoo Hooe Hoor.
  iIntros "Hli Hi Hle He Hla Hab Hlo Hc Hl Hb0 Hb4 HR HK".
  iApply (wp_getopt_internal_in e n av p lo li lonly pc b r oi roi oe roe i err i0 e0 Ψ
            with "Hli Hi Hle He Hl Hb0 Hb4 HR [Hla Hab Hlo Hc HK]"); try assumption.
  iIntros (e2 x i' c' a' ra [Hx Ha']) "Hl Hb0 Hb8 Hb16 Hcap HΨ Hli Hi Hle He".
  iApply (wp_getopt_internal_out e2 x i' c' a' ra b r oi roi oa roa oo roo i a0 c0
            with "Hl Hb0 Hb8 Hb16 Hcap Hli Hi Hla Hab Hlo Hc"); try assumption.
  iIntros "Hl Hb0 Hb8 Hb16 Hli Hi Hla Hab Hlo Hc".
  iApply ("HK" with "HΨ Hl Hb0 Hb8 Hb16 Hli Hi Hle He Hla Hab Hlo Hc").
Qed.

End wrapper.
End GetoptWrapperOn.
