From Glibc Require Import GlibcProgram.
(** The parser in glibc's getopt_long calls free, malloc and memset when
    it collects the candidates for an ambiguous long option. Hello's
    safety theorem in HelloGetoptStart.v takes a rule for each of those
    calls as an assumption. Hello links glibc's own allocator and memset,
    and their proofs already exist, so this file proves the three rules
    from those proofs and states the theorem without them.

    A caller of the theorem should not have to lend the parser memory
    that Hello already shares. Malloc only reads a cache that Hello holds
    a read-only share of, so that share comes from Hello itself. Getenv
    and the warning printers still borrow from the streams and the
    private state, and their rules stay assumptions. The first theorem
    also assumes the rule for the alloca cutoff. The second proves it
    from glibc's code with a loan from G. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Run Machine
  ExternalCalls ExternalMachine Pieces Heap Language Logic StringLogic MemLogic HelloLeaf HelloMain.
From Glibc Require Import OsWorld OsRegistry WordString FileInv StrchrCode StrcmpCode StrncmpCode StrlenLogic
  MemFwdCode MemFwdLogic AllocLogic StdlibCode
  GetoptModule GetoptState GetoptInitialize GetoptDiag GetoptLongExact GetoptLongStore GetoptLongDiag
  GetoptLongPfxAlloc GetoptLongAmbTail GetoptLongSite GetoptWrapParse GetoptLongStr GetoptInitial
  AtexitLogic HelloGlibcLibsT HelloGetoptTable HelloGetoptState HelloGlibcDebts HelloGlibcMainLoop
  HelloGlibcMainFull HelloGetoptCall HelloGetoptStart.
From Glibc Require FileInv AllocLogic MemFwdLogic HelloGlibcDebts HelloGlibcJoin HelloGetoptCall CutoffCode CutoffLogic.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Import GetoptState FileInv FileInv.ML FileInv.LG FileInv.L HelloGlibcDebts.

Section backend.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (ge : genv) (o : hello_objs) (Hk : hello_link ge o).
(** The OS interpretation survives the allocator's safepoints. *)
Local Instance backend_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** These calls run with the concrete glibc OS registry. *)
Local Instance backend_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.

(** ## free and malloc

    Hello links glibc's free and malloc. Freeing hands back a live heap
    object, and allocation reads the idle thread cache and returns a
    fresh object. *)

(** This is Hello's share of the allocator's idle thread cache. *)
Definition hello_tcache : iProp Σ :=
  AL.tcache_idle DfracDiscarded (ho_mp o) (ho_tc o) (ho_dm o) (ho_mpreg o) (ho_tcreg o) (ho_dmreg o).

(** Hello's read-only promise includes that share. *)
Lemma hello_ro_tcache : hello_ro ge o ⊢ hello_tcache.
Proof. iIntros "(_ & _ & _ & _ & _ & _ & _ & Htc & _)". iExact "Htc". Qed.

(** glibc's free meets the parser's rule for free. *)
Lemma hello_free_rule : getopt_free_rule w0 glibc_os_registry ge.
Proof.
  intros f e ls l v rest j b reg Φ Hx Hheap Hb. iIntros "Hl HK".
  iApply wp_call_bind; [cbn [map_option]; rewrite Hx; reflexivity | exact (hk_free _ _ Hk) | reflexivity |].
  iNext. destruct (hk_frees _ _ Hk) as (Hfree & Hfn & Hglobal).
  iApply (AllocLogic.wp_glibc_free glibc_os_registry (os_wi w0) ge with "Hl");
    [exact Hfree | exact Hfn | exact Hglobal | exact Hheap | lia |
     intros m wd h rs Hlive Hrs Hw; exact (os_wi_free w0 m wd h b reg rs Hheap Hlive Hrs Hw) |].
  iExists _. iSplit; [iPureIntro; reflexivity | iExact "HK"].
Qed.

(** glibc's malloc meets the parser's rule for malloc with Hello's share
    of the thread cache. *)
Lemma hello_malloc_rule : getopt_malloc_rule w0 glibc_os_registry ge hello_tcache.
Proof.
  intros f e ls l d v rest j n Φ Hx Hn. iIntros "HM HK".
  iApply wp_call_bind; [cbn [map_option]; rewrite Hx; reflexivity | exact (hk_malloc _ _ Hk) | reflexivity |].
  iNext.
  iApply (AllocLogic.wp_glibc_malloc glibc_os_registry (os_wi w0) ge n with "HM [HK]");
    [exact Hn | | exact (hk_mp _ _ Hk) | exact (hk_tc _ _ Hk) | exact (hk_malloc2 _ _ Hk) |].
  - intros m wd h base Hfresh Hw. exact (os_wi_alloc w0 m wd h (heap_req 16 n) base Hfresh Hw).
  - iIntros (base Hb) "Ho HM". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
    iApply ("HK" with "HM"). iRight. iExists base. iSplit; [iPureIntro; split_and!; (reflexivity || lia) | iExact "Ho"].
Qed.

(** ## memset

    The parser clears its candidate buffer through glibc's internal name
    __GI_memset. Hello's link facts name only the public memset, so the
    internal name is a premise here. *)

(** glibc's memset meets the parser's rule for memset. *)
Lemma hello_memset_rule : find_fn ge (TAtom "__GI_memset") = Some (Defined glibc_memset) ->
  getopt_memset_rule w0 glibc_os_registry ge.
Proof.
  intros Hgm f e ls l d args rest j b reg xs cs nz Φ Hx -> Hn Hb8 Hend Hlen. iIntros "Hl Hx Hcs HK".
  destruct (hk_zmemset _ _ Hk) as [Hzf Hzs].
  replace (mkPtr b (Obj b)) with (mkPtr (b + 0) (Obj b)) in Hx by (rewrite Z.add_0_r; reflexivity).
  iApply (wp_call_glibc_memset (glibc_program := program_of w0 glibc_os_registry ge) ltac:(reflexivity) Hzf Hzs
    f e ls l (CResult d P) (TAtom "__GI_memset") args rest j b reg 0 xs cs 0
    (mkFrame f (put d (WPtr (mkPtr b (Obj b))) e) ls None (Exec l rest j)) Φ
    Hx Hgm ltac:(rewrite Z.add_0_r; reflexivity) ltac:(lia) ltac:(lia) Hb8 ltac:(reflexivity) ltac:(lia)
    ltac:(lia) Hlen with "Hl Hx Hcs").
  iNext. iIntros "Hl Hx Hcs". change (0 mod 256) with 0. iApply ("HK" with "Hl Hx Hcs").
Qed.

End backend.

(** ## The theorem

    Someone applying Hello's safety theorem should only have to discharge
    rules for code that is not yet proved. The theorem below therefore
    proves the rules for free, malloc and memset from glibc's code. It
    keeps the rules for getenv, the warning printers and the alloca
    cutoff, and adds one link fact: the internal name of memset. The
    streams and the private state lend only G, which getenv and the
    warning printers use. *)

(** Every allowed execution of Hello with glibc's getopt_long avoids
    panics, stuck steps and contract failures. Here free, malloc and
    memset are glibc's own code, and Hello's table and glibc's objects
    start as loaded. *)
Theorem hello_never_panics_getopt_backend Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    w0 ge o m s w h1 argc av ar p0 ps x y z a i c fuel gb greg oe roe oo roo bdd rdd b7 r7 b0 r0
    penv mid mid' f138 f139 f140 f141 lmid mid3 mid4 dom tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 :
  hello_link ge o -> hello_layout ge o -> hello_os_layout w0 o ->
  find_fn ge (TAtom "getopt_long") = Some (Defined glibc_getopt_long) ->
  find_fn ge (TAtom "_getopt_internal") = Some (Defined glibc_getopt_internal) ->
  find_fn ge (TAtom "_getopt_internal_r") = Some (Defined glibc_getopt_internal_r) ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  find_fn ge (TAtom "__GI_strcmp") = Some (Defined glibc_strcmp) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_memset") = Some (Defined glibc_memset) ->
  Term.lookup (TAtom "glibc_getopt#getopt_data") (ge_globals ge) = Some (mkPtr gb (Obj gb)) ->
  0 < gb -> gb mod 8 = 0 -> gb + 56 <= r_end greg -> r_end greg <= 2 ^ 48 ->
  Term.lookup (TAtom "opterr") (ge_globals ge) = Some (mkPtr oe (Obj oe)) ->
  0 < oe -> oe + 4 <= r_end roe -> r_end roe <= 2 ^ 48 ->
  Term.lookup (TAtom "optopt") (ge_globals ge) = Some (mkPtr oo (Obj oo)) ->
  0 < oo -> oo + 4 <= r_end roo -> r_end roo <= 2 ^ 48 ->
  0 < ho_oa o -> 0 < ho_oi o -> 0 < ho_se o ->
  Term.lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some (mkPtr bdd (Ro bdd)) ->
  0 < bdd -> bdd mod 8 = 0 -> bdd + 8 <= r_end rdd -> r_end rdd <= 2 ^ 48 ->
  Term.lookup (TAtom "glibc_getopt#str.147") (ge_globals ge) = Some (mkPtr b7 (Ro b7)) ->
  0 < b7 -> b7 mod 8 = 0 -> b7 + 8 <= r_end r7 -> r_end r7 <= 2 ^ 48 ->
  Term.lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some (mkPtr b0 (Ro b0)) ->
  0 < b0 -> b0 mod 8 = 0 -> b0 + 8 <= r_end r0 -> r_end r0 <= 2 ^ 48 ->
  Term.lookup (TAtom "hello#parse_options.longopts.64") (ge_globals ge) = Some (mkPtr tb (Ro tb)) ->
  0 < tb -> tb mod 8 = 0 -> tb + 136 <= r_end treg -> r_end treg <= 2 ^ 48 ->
  Term.lookup (TAtom "hello#str.69") (ge_globals ge) = Some (mkPtr b5 (Ro b5)) ->
  0 < b1 -> b1 mod 8 = 0 -> b1 + 16 <= r_end r1 -> r_end r1 <= 2 ^ 48 ->
  0 < b2 -> b2 mod 8 = 0 -> b2 + 16 <= r_end r2 -> r_end r2 <= 2 ^ 48 ->
  0 < b3 -> b3 mod 8 = 0 -> b3 + 8 <= r_end r3 -> r_end r3 <= 2 ^ 48 ->
  0 < b4 -> b4 mod 8 = 0 -> b4 + 8 <= r_end r4 -> r_end r4 <= 2 ^ 48 ->
  0 < b5 -> b5 mod 8 = 0 -> b5 + 8 <= r_end r5 -> r_end r5 <= 2 ^ 48 ->
  Term.lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv ->
  Term.lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid' ->
  Term.lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  Term.lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  Term.lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  Term.lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  Term.lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  Term.lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid ->
  Term.lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  Term.lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  argc = Z.of_nat (length (p0 :: ps)) -> 0 <= i <= argc ->
  R.ready s m -> live_disjoint m ->
  agrees m (h1 ∪ list_to_map (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++
    getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0)) ->
  os_wi w0 m w (h1 ∪ list_to_map (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++
    getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0)) ->
  NoDup (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++
    getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0).*1 ->
  map_disjoint h1 (list_to_map (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++
    getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0)) ->
  (forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
    exists (debt : HelloCore w0 ge o) (G : iProp Σ) (T : ptr -> ptr -> iProp Σ),
    getenv_rule w0 glibc_os_registry ge G /\ getopt_diag_rule w0 glibc_os_registry ge G T (ho_err o) dom /\
    getopt_ldiag_rule w0 glibc_os_registry ge G T (ho_err o) dom /\ getopt_cutoff_rule w0 glibc_os_registry ge /\
    (hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ⊢ G ∗ (G -∗ hello_stdio w0 ge o ∗ hd_priv w0 ge o debt)) /\
    (([∗ map] l ↦ v ∈ h1, pointsto l (DfracOwn 1) v) ==∗
      hello_ro_rest ge o ∗ ([∗ list] q ∈ p0 :: ps, str_ro q) ∗ argv_own av ar (p0 :: ps) ∗
      ncells o x y z ∗ (HelloGlibcJoin.AX.exit_funcs_inv (ho_x o) [] c ∗ HelloGlibcJoin.Libs.exit_lock o) ∗
      hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ∗ getopt_cells o a i)) ->
  labelled_safe glibc_os_registry ge (invocation main_fn [WInt argc; WPtr (mkPtr av (Obj av))])
    m s w fuel (fun _ => True).
Proof.
  intros Hk Hy Hos Hgl Hgi Hgr Hplo Hcmp Hchr Hchrn Hncmp Hgms Hgb Hgb0 Hgb8 Hgbe Hgbr Hoe Hoe0 Hoee Hoer
    Hoo Hoo0 Hooe Hoor Hoa0 Hoi0 Hse0 H146 Hd0 Hd8 Hde Hdr H147 H70 H78 H7e H7r H150 H00 H08 H0e H0r
    Htb Htb0 Htb8 Htbe Htbr H69 Hb10 Hb18 Hb1e Hb1r Hb20 Hb28 Hb2e Hb2r Hb30 Hb38 Hb3e Hb3r
    Hb40 Hb48 Hb4e Hb4r Hb50 Hb58 Hb5e Hb5r
    H145 H148 H149 H138 H139 H140 H141 H142 H143 H144 Hargc Hi Hr Hd Ha Hw Hnd Hdisj Hstart.
  apply (hello_getopt_table_core Σ w0 ge o m s w h1 argc av ar p0 ps x y z a i c fuel gb greg oe roe oo roo
    bdd rdd b7 r7 b0 r0 tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5); try assumption.
  intros HinvG HheapG.
  destruct (Hstart HinvG HheapG) as (debt & G & T & Hge & Hdg & Hld & Hcu & Hg & Hpre).
  exists debt. split; [|exact Hpre].
  exact (hello_getopt_ix_ro w0 ge o debt Hy Hgl Hgi Hgr Hplo Hcmp Hchr Hchrn Hncmp (hk_gi_strlen _ _ Hk)
    gb greg Hgb Hgb0 Hgb8 Hgbe Hgbr oe roe oo roo Hoe Hoe0 Hoee Hoer Hoo Hoo0 Hooe Hoor Hoa0 Hoi0 Hse0
    (mkPtr bdd (Ro bdd)) (mkPtr b7 (Ro b7)) (mkPtr b0 (Ro b0)) penv mid mid' f138 f139 f140 f141 lmid mid3 mid4 dom
    [45; 45] [45] [45; 87; 32] H146 H147 H150 H145 H148 H149 H138 H139 H140 H141 H142 H143 H144
    G (hello_tcache o) T Hge Hdg Hld Hcu (hello_malloc_rule w0 ge o Hk) (hello_memset_rule w0 ge o Hk Hgms)
    (hello_free_rule w0 ge o Hk)
    (mkPtr b1 (Ro b1)) (mkPtr b2 (Ro b2)) (mkPtr b3 (Ro b3)) (mkPtr b4 (Ro b4))
    (hello_ro_tcache ge o) Hg av ar).
Qed.

(** ## The alloca cutoff

    The parser asks glibc's __libc_alloca_cutoff whether a set of
    candidates may live in its frame. That function reads two things:
    the thread's descriptor, which it gets from the runtime's
    zthread_self_cookie, and the stack size stored in that descriptor.
    The theorem above takes a rule for the call that needs no resource
    at all. The theorem below proves the call from glibc's code instead.

    The cutoff decides how large an array the parser may keep on its
    stack, so it reads the stack size of the running thread. That size
    lives in the thread's descriptor, next to the cleanup state that the
    streams already own. Getenv and the warning printers borrow some
    memory G from the streams, and the parser leaves G alone while it
    searches the table. The cutoff borrows G during that search and
    gives it back before any warning. So G must include the cleanup
    state and a share of the stack size.

    The program must define __libc_alloca_cutoff. It must not define
    zthread_self_cookie, because the runtime provides that symbol. *)

(** Every allowed execution of Hello with glibc's getopt_long avoids
    panics, stuck steps and contract failures. Here free, malloc,
    memset and the alloca cutoff are glibc's own code. *)
Theorem hello_never_panics_getopt_cutoff Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    w0 ge o m s w h1 argc av ar p0 ps x y z a i c fuel gb greg oe roe oo roo bdd rdd b7 r7 b0 r0
    penv mid mid' f138 f139 f140 f141 lmid mid3 mid4 dom tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 :
  hello_link ge o -> hello_layout ge o -> hello_os_layout w0 o ->
  find_fn ge (TAtom "getopt_long") = Some (Defined glibc_getopt_long) ->
  find_fn ge (TAtom "_getopt_internal") = Some (Defined glibc_getopt_internal) ->
  find_fn ge (TAtom "_getopt_internal_r") = Some (Defined glibc_getopt_internal_r) ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  find_fn ge (TAtom "__GI_strcmp") = Some (Defined glibc_strcmp) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_memset") = Some (Defined glibc_memset) ->
  find_fn ge (TAtom "__GI___libc_alloca_cutoff") = Some (Defined CutoffCode.glibc_libc_alloca_cutoff) ->
  find_fn ge (TAtom "zthread_self_cookie") = None -> Term.lookup (TAtom "zthread_self_cookie") (ge_globals ge) = None ->
  Term.lookup (TAtom "glibc_getopt#getopt_data") (ge_globals ge) = Some (mkPtr gb (Obj gb)) ->
  0 < gb -> gb mod 8 = 0 -> gb + 56 <= r_end greg -> r_end greg <= 2 ^ 48 ->
  Term.lookup (TAtom "opterr") (ge_globals ge) = Some (mkPtr oe (Obj oe)) ->
  0 < oe -> oe + 4 <= r_end roe -> r_end roe <= 2 ^ 48 ->
  Term.lookup (TAtom "optopt") (ge_globals ge) = Some (mkPtr oo (Obj oo)) ->
  0 < oo -> oo + 4 <= r_end roo -> r_end roo <= 2 ^ 48 ->
  0 < ho_oa o -> 0 < ho_oi o -> 0 < ho_se o ->
  Term.lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some (mkPtr bdd (Ro bdd)) ->
  0 < bdd -> bdd mod 8 = 0 -> bdd + 8 <= r_end rdd -> r_end rdd <= 2 ^ 48 ->
  Term.lookup (TAtom "glibc_getopt#str.147") (ge_globals ge) = Some (mkPtr b7 (Ro b7)) ->
  0 < b7 -> b7 mod 8 = 0 -> b7 + 8 <= r_end r7 -> r_end r7 <= 2 ^ 48 ->
  Term.lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some (mkPtr b0 (Ro b0)) ->
  0 < b0 -> b0 mod 8 = 0 -> b0 + 8 <= r_end r0 -> r_end r0 <= 2 ^ 48 ->
  Term.lookup (TAtom "hello#parse_options.longopts.64") (ge_globals ge) = Some (mkPtr tb (Ro tb)) ->
  0 < tb -> tb mod 8 = 0 -> tb + 136 <= r_end treg -> r_end treg <= 2 ^ 48 ->
  Term.lookup (TAtom "hello#str.69") (ge_globals ge) = Some (mkPtr b5 (Ro b5)) ->
  0 < b1 -> b1 mod 8 = 0 -> b1 + 16 <= r_end r1 -> r_end r1 <= 2 ^ 48 ->
  0 < b2 -> b2 mod 8 = 0 -> b2 + 16 <= r_end r2 -> r_end r2 <= 2 ^ 48 ->
  0 < b3 -> b3 mod 8 = 0 -> b3 + 8 <= r_end r3 -> r_end r3 <= 2 ^ 48 ->
  0 < b4 -> b4 mod 8 = 0 -> b4 + 8 <= r_end r4 -> r_end r4 <= 2 ^ 48 ->
  0 < b5 -> b5 mod 8 = 0 -> b5 + 8 <= r_end r5 -> r_end r5 <= 2 ^ 48 ->
  Term.lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv ->
  Term.lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid' ->
  Term.lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  Term.lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  Term.lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  Term.lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  Term.lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  Term.lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid ->
  Term.lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  Term.lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  argc = Z.of_nat (length (p0 :: ps)) -> 0 <= i <= argc ->
  R.ready s m -> live_disjoint m ->
  agrees m (h1 ∪ list_to_map (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++
    getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0)) ->
  os_wi w0 m w (h1 ∪ list_to_map (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++
    getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0)) ->
  NoDup (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++
    getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0).*1 ->
  map_disjoint h1 (list_to_map (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++
    getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0)) ->
  (forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
    exists (debt : HelloCore w0 ge o) (G : iProp Σ) (T : ptr -> ptr -> iProp Σ) (dq : dfrac),
    getenv_rule w0 glibc_os_registry ge G /\ getopt_diag_rule w0 glibc_os_registry ge G T (ho_err o) dom /\
    getopt_ldiag_rule w0 glibc_os_registry ge G T (ho_err o) dom /\
    (G ⊢ CutoffLogic.cutoff_loan (glibc_program := program_of w0 glibc_os_registry ge) dq ∗
      (CutoffLogic.cutoff_loan (glibc_program := program_of w0 glibc_os_registry ge) dq -∗ G)) /\
    (hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ⊢ G ∗ (G -∗ hello_stdio w0 ge o ∗ hd_priv w0 ge o debt)) /\
    (([∗ map] l ↦ v ∈ h1, pointsto l (DfracOwn 1) v) ==∗
      hello_ro_rest ge o ∗ ([∗ list] q ∈ p0 :: ps, str_ro q) ∗ argv_own av ar (p0 :: ps) ∗
      ncells o x y z ∗ (HelloGlibcJoin.AX.exit_funcs_inv (ho_x o) [] c ∗ HelloGlibcJoin.Libs.exit_lock o) ∗
      hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ∗ getopt_cells o a i)) ->
  labelled_safe glibc_os_registry ge (invocation main_fn [WInt argc; WPtr (mkPtr av (Obj av))])
    m s w fuel (fun _ => True).
Proof.
  intros Hk Hy Hos Hgl Hgi Hgr Hplo Hcmp Hchr Hchrn Hncmp Hgms Hcf Hsf Hss Hgb Hgb0 Hgb8 Hgbe Hgbr Hoe Hoe0 Hoee Hoer
    Hoo Hoo0 Hooe Hoor Hoa0 Hoi0 Hse0 H146 Hd0 Hd8 Hde Hdr H147 H70 H78 H7e H7r H150 H00 H08 H0e H0r
    Htb Htb0 Htb8 Htbe Htbr H69 Hb10 Hb18 Hb1e Hb1r Hb20 Hb28 Hb2e Hb2r Hb30 Hb38 Hb3e Hb3r
    Hb40 Hb48 Hb4e Hb4r Hb50 Hb58 Hb5e Hb5r
    H145 H148 H149 H138 H139 H140 H141 H142 H143 H144 Hargc Hi Hr Hd Ha Hw Hnd Hdisj Hstart.
  apply (hello_getopt_table_core Σ w0 ge o m s w h1 argc av ar p0 ps x y z a i c fuel gb greg oe roe oo roo
    bdd rdd b7 r7 b0 r0 tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5); try assumption.
  intros HinvG HheapG.
  destruct (Hstart HinvG HheapG) as (debt & G & T & dq & Hge & Hdg & Hld & Hln & Hg & Hpre).
  exists debt. split; [|exact Hpre].
  exact (hello_getopt_ix_ro_with w0 ge o debt Hy Hgl Hgi Hgr Hplo Hcmp Hchr Hchrn Hncmp (hk_gi_strlen _ _ Hk)
    gb greg Hgb Hgb0 Hgb8 Hgbe Hgbr oe roe oo roo Hoe Hoe0 Hoee Hoer Hoo Hoo0 Hooe Hoor Hoa0 Hoi0 Hse0
    (mkPtr bdd (Ro bdd)) (mkPtr b7 (Ro b7)) (mkPtr b0 (Ro b0)) penv mid mid' f138 f139 f140 f141 lmid mid3 mid4 dom
    [45; 45] [45] [45; 87; 32] H146 H147 H150 H145 H148 H149 H138 H139 H140 H141 H142 H143 H144
    G (hello_tcache o) T Hge Hdg Hld (hello_malloc_rule w0 ge o Hk) (hello_memset_rule w0 ge o Hk Hgms)
    (hello_free_rule w0 ge o Hk)
    (mkPtr b1 (Ro b1)) (mkPtr b2 (Ro b2)) (mkPtr b3 (Ro b3)) (mkPtr b4 (Ro b4))
    (hello_ro_tcache ge o) Hg av ar
    (getopt_cutoff_rule_with_loan (glibc_program := program_of w0 glibc_os_registry ge) G dq
      ltac:(reflexivity) Hsf Hss Hcf Hln)).
Qed.

(** ## Where the stack size comes from

    Hello's streams do not own the bytes that hold the stack size, so
    the theorem above makes its caller lend them. The theorem below
    finds them in the starting memory instead. It splits off the eight
    bytes at offset 1720 of the thread's descriptor and freezes them
    once, and every call then copies the frozen share. The caller's loan
    only has to cover the cleanup state, which the streams already own.

    The stack size may hold any value sz. In the pinned glibc, startup
    stores the end of the initial stack there before main runs. The
    theorem does not rely on that store. It only asks that the starting
    memory holds those bytes and that nobody else owns them. *)

(** Every allowed execution of Hello with glibc's getopt_long avoids
    panics, stuck steps and contract failures, when the starting memory
    holds the thread's stack size beside glibc's objects and Hello's
    table. *)
Theorem hello_never_panics_getopt_stack Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    w0 ge o m s w h1 argc av ar p0 ps x y z a i c fuel gb greg oe roe oo roo bdd rdd b7 r7 b0 r0
    penv mid mid' f138 f139 f140 f141 lmid mid3 mid4 dom tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ts sz :
  hello_link ge o -> hello_layout ge o -> hello_os_layout w0 o ->
  find_fn ge (TAtom "getopt_long") = Some (Defined glibc_getopt_long) ->
  find_fn ge (TAtom "_getopt_internal") = Some (Defined glibc_getopt_internal) ->
  find_fn ge (TAtom "_getopt_internal_r") = Some (Defined glibc_getopt_internal_r) ->
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  find_fn ge (TAtom "__GI_strcmp") = Some (Defined glibc_strcmp) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_memset") = Some (Defined glibc_memset) ->
  find_fn ge (TAtom "__GI___libc_alloca_cutoff") = Some (Defined CutoffCode.glibc_libc_alloca_cutoff) ->
  find_fn ge (TAtom "zthread_self_cookie") = None -> Term.lookup (TAtom "zthread_self_cookie") (ge_globals ge) = None ->
  ow_self w0 = mkPtr ts (Obj ts) ->
  Term.lookup (TAtom "glibc_getopt#getopt_data") (ge_globals ge) = Some (mkPtr gb (Obj gb)) ->
  0 < gb -> gb mod 8 = 0 -> gb + 56 <= r_end greg -> r_end greg <= 2 ^ 48 ->
  Term.lookup (TAtom "opterr") (ge_globals ge) = Some (mkPtr oe (Obj oe)) ->
  0 < oe -> oe + 4 <= r_end roe -> r_end roe <= 2 ^ 48 ->
  Term.lookup (TAtom "optopt") (ge_globals ge) = Some (mkPtr oo (Obj oo)) ->
  0 < oo -> oo + 4 <= r_end roo -> r_end roo <= 2 ^ 48 ->
  0 < ho_oa o -> 0 < ho_oi o -> 0 < ho_se o ->
  Term.lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some (mkPtr bdd (Ro bdd)) ->
  0 < bdd -> bdd mod 8 = 0 -> bdd + 8 <= r_end rdd -> r_end rdd <= 2 ^ 48 ->
  Term.lookup (TAtom "glibc_getopt#str.147") (ge_globals ge) = Some (mkPtr b7 (Ro b7)) ->
  0 < b7 -> b7 mod 8 = 0 -> b7 + 8 <= r_end r7 -> r_end r7 <= 2 ^ 48 ->
  Term.lookup (TAtom "glibc_getopt#str.150") (ge_globals ge) = Some (mkPtr b0 (Ro b0)) ->
  0 < b0 -> b0 mod 8 = 0 -> b0 + 8 <= r_end r0 -> r_end r0 <= 2 ^ 48 ->
  Term.lookup (TAtom "hello#parse_options.longopts.64") (ge_globals ge) = Some (mkPtr tb (Ro tb)) ->
  0 < tb -> tb mod 8 = 0 -> tb + 136 <= r_end treg -> r_end treg <= 2 ^ 48 ->
  Term.lookup (TAtom "hello#str.69") (ge_globals ge) = Some (mkPtr b5 (Ro b5)) ->
  0 < b1 -> b1 mod 8 = 0 -> b1 + 16 <= r_end r1 -> r_end r1 <= 2 ^ 48 ->
  0 < b2 -> b2 mod 8 = 0 -> b2 + 16 <= r_end r2 -> r_end r2 <= 2 ^ 48 ->
  0 < b3 -> b3 mod 8 = 0 -> b3 + 8 <= r_end r3 -> r_end r3 <= 2 ^ 48 ->
  0 < b4 -> b4 mod 8 = 0 -> b4 + 8 <= r_end r4 -> r_end r4 <= 2 ^ 48 ->
  0 < b5 -> b5 mod 8 = 0 -> b5 + 8 <= r_end r5 -> r_end r5 <= 2 ^ 48 ->
  Term.lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv ->
  Term.lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid' ->
  Term.lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  Term.lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  Term.lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  Term.lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  Term.lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  Term.lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some lmid ->
  Term.lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  Term.lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  argc = Z.of_nat (length (p0 :: ps)) -> 0 <= i <= argc ->
  R.ready s m -> live_disjoint m ->
  agrees m (h1 ∪ list_to_map (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++
    getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0 ++
    cell ts CutoffLogic.off_stackblock_size sz)) ->
  os_wi w0 m w (h1 ∪ list_to_map (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++
    getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0 ++
    cell ts CutoffLogic.off_stackblock_size sz)) ->
  NoDup (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++
    getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0 ++
    cell ts CutoffLogic.off_stackblock_size sz).*1 ->
  map_disjoint h1 (list_to_map (hello_tab_ps tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 ++
    getopt_start_ps gb greg oe roe oo roo bdd rdd b7 r7 b0 r0 ++
    cell ts CutoffLogic.off_stackblock_size sz)) ->
  (forall (HinvG : invGS_gen HasNoLc Σ) (HheapG : gen_heapGS piece pval Σ),
    exists (debt : HelloCore w0 ge o) (G : iProp Σ) (T : ptr -> ptr -> iProp Σ),
    getenv_rule w0 glibc_os_registry ge G /\ getopt_diag_rule w0 glibc_os_registry ge G T (ho_err o) dom /\
    getopt_ldiag_rule w0 glibc_os_registry ge G T (ho_err o) dom /\
    (G ⊢ tcb_cleanup_inv (ow_self w0) ∗ (tcb_cleanup_inv (ow_self w0) -∗ G)) /\
    (hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ⊢ G ∗ (G -∗ hello_stdio w0 ge o ∗ hd_priv w0 ge o debt)) /\
    (([∗ map] l ↦ v ∈ h1, pointsto l (DfracOwn 1) v) ==∗
      hello_ro_rest ge o ∗ ([∗ list] q ∈ p0 :: ps, str_ro q) ∗ argv_own av ar (p0 :: ps) ∗
      ncells o x y z ∗ (HelloGlibcJoin.AX.exit_funcs_inv (ho_x o) [] c ∗ HelloGlibcJoin.Libs.exit_lock o) ∗
      hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ∗ getopt_cells o a i)) ->
  labelled_safe glibc_os_registry ge (invocation main_fn [WInt argc; WPtr (mkPtr av (Obj av))])
    m s w fuel (fun _ => True).
Proof.
  intros Hk Hy Hos Hgl Hgi Hgr Hplo Hcmp Hchr Hchrn Hncmp Hgms Hcf Hsf Hss Hts Hgb Hgb0 Hgb8 Hgbe Hgbr Hoe Hoe0 Hoee Hoer
    Hoo Hoo0 Hooe Hoor Hoa0 Hoi0 Hse0 H146 Hd0 Hd8 Hde Hdr H147 H70 H78 H7e H7r H150 H00 H08 H0e H0r
    Htb Htb0 Htb8 Htbe Htbr H69 Hb10 Hb18 Hb1e Hb1r Hb20 Hb28 Hb2e Hb2r Hb30 Hb38 Hb3e Hb3r
    Hb40 Hb48 Hb4e Hb4r Hb50 Hb58 Hb5e Hb5r
    H145 H148 H149 H138 H139 H140 H141 H142 H143 H144 Hargc Hi Hr Hd Ha Hw Hnd Hdisj Hstart.
  apply (hello_getopt_table_core_sep Σ w0 ge o m s w h1 argc av ar p0 ps x y z a i c fuel gb greg oe roe oo roo
    bdd rdd b7 r7 b0 r0 tb treg b1 b2 b3 b4 b5 r1 r2 r3 r4 r5 (cell ts CutoffLogic.off_stackblock_size sz));
    try assumption.
  intros HinvG HheapG.
  destruct (Hstart HinvG HheapG) as (debt & G & T & Hge & Hdg & Hld & Hln & Hg & Hpre).
  set (C := CutoffLogic.stack_size_cell (glibc_program := program_of w0 glibc_os_registry ge)
    (ow_self w0) DfracDiscarded sz).
  exists debt, C. split; [exact (CutoffLogic.stack_size_own (glibc_program := program_of w0 glibc_os_registry ge) ts sz Hts)|].
  split; [|exact Hpre].
  assert (Hloan : G ∗ □ C ⊢
    CutoffLogic.cutoff_loan (glibc_program := program_of w0 glibc_os_registry ge) DfracDiscarded ∗
    (CutoffLogic.cutoff_loan (glibc_program := program_of w0 glibc_os_registry ge) DfracDiscarded -∗ G ∗ □ C)).
  { iIntros "[HG #HC]". iDestruct (Hln with "HG") as "[Ht Hb]".
    iSplitL "Ht"; [iFrame "Ht"; iExists sz; iExact "HC"|].
    iIntros "[Ht _]". iSplitL; [iApply ("Hb" with "Ht") | iExact "HC"]. }
  assert (HgC : hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ∗ □ C ⊢
    (G ∗ □ C) ∗ (G ∗ □ C -∗ hello_stdio w0 ge o ∗ hd_priv w0 ge o debt ∗ □ C)).
  { iIntros "(Hio & Hpv & #HC)". iDestruct (Hg with "[$Hio $Hpv]") as "[HG Hb]".
    iSplitL "HG"; [iFrame "HG HC"|]. iIntros "[HG _]". iDestruct ("Hb" with "HG") as "[Hio Hpv]".
    iFrame "Hio Hpv HC". }
  exact (hello_getopt_ix_ro_sep w0 ge o debt Hy Hgl Hgi Hgr Hplo Hcmp Hchr Hchrn Hncmp (hk_gi_strlen _ _ Hk)
    gb greg Hgb Hgb0 Hgb8 Hgbe Hgbr oe roe oo roo Hoe Hoe0 Hoee Hoer Hoo Hoo0 Hooe Hoor Hoa0 Hoi0 Hse0
    (mkPtr bdd (Ro bdd)) (mkPtr b7 (Ro b7)) (mkPtr b0 (Ro b0)) penv mid mid' f138 f139 f140 f141 lmid mid3 mid4 dom
    [45; 45] [45] [45; 87; 32] H146 H147 H150 H145 H148 H149 H138 H139 H140 H141 H142 H143 H144
    (G ∗ □ C) (hello_tcache o) (fun mid q => T mid q ∗ □ C)%I
    (getenv_rule_sep w0 glibc_os_registry ge G (□ C) Hge)
    (getopt_diag_rule_sep w0 glibc_os_registry ge G (□ C) T (ho_err o) dom Hdg)
    (getopt_ldiag_rule_sep w0 glibc_os_registry ge G (□ C) T (ho_err o) dom Hld)
    (hello_malloc_rule w0 ge o Hk) (hello_memset_rule w0 ge o Hk Hgms) (hello_free_rule w0 ge o Hk)
    (mkPtr b1 (Ro b1)) (mkPtr b2 (Ro b2)) (mkPtr b3 (Ro b3)) (mkPtr b4 (Ro b4))
    (hello_ro_tcache ge o) (□ C)%I av ar
    (getopt_cutoff_rule_with_loan (glibc_program := program_of w0 glibc_os_registry ge) (G ∗ □ C) DfracDiscarded
      ltac:(reflexivity) Hsf Hss Hcf Hloan) HgC).
Qed.
