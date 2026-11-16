From Glibc Require Import GlibcProgram.
(** Userland glibc asks the processor what it supports before it does
    anything else. In Fil-C the two instructions it needs, CPUID and
    XGETBV, are not available to compiled C code, so glibc calls three
    libpizlo functions instead: `c: zcpuid`, `c: zcpuid_count` and
    `c: zxgetbv`. Those functions sit at the [[external call|contract]]
    boundary between compiled C code and the Fil-C [[runtime]]. This
    module defines their contracts over the shared state [os_world] from
    [OsWorld](OsWorld.v) and derives the [[separation-logic]] rules that
    a proof of `c: init_cpu_features` applies at each call. Their runtime
    behavior is tested against native Fil-C in [zsys-cpuid.c](zsys-cpuid.c).

    ## What libpizlo runs

    The pinned `libpas/src/libpas/filc_runtime.c` executes the instruction
    first and checks the four result pointers afterwards.

    ```c
    static void cpuid_impl(unsigned leaf, unsigned count, filc_ptr eax_ptr,
                           filc_ptr ebx_ptr, filc_ptr ecx_ptr, filc_ptr edx_ptr)
    {
        unsigned eax = leaf, ebx = 0, ecx = count, edx = 0;
        asm volatile("cpuid" : "+a"(eax), "+b"(ebx), "+c"(ecx), "+d"(edx));
        filc_check_write(eax_ptr, sizeof(int32_t));
        filc_check_write(ebx_ptr, sizeof(int32_t));
        filc_check_write(ecx_ptr, sizeof(int32_t));
        filc_check_write(edx_ptr, sizeof(int32_t));
        // Four plain 32-bit stores follow, of eax, ebx, ecx and edx,
        // each through filc_ptr_ptr of its pointer, in that order.
    }
    unsigned long filc_native_zxgetbv(filc_thread *my_thread)
    {
        unsigned low, high;
        asm volatile("xgetbv" : "=a"(low), "=d"(high) : "c"(0));
        return (unsigned long)low | ((unsigned long)high << 32);
    }
    ```

    `c: zcpuid` passes a count of zero. Each call writes four 32-bit
    integers through plain stores, so it changes twelve to sixteen data
    bytes and no [[capability]]. A pointer that does not cover four
    writable bytes makes `c: filc_check_write` panic.

    ## What the processor and the kernel decide

    The contracts say nothing about the four numbers, because the
    processor chooses them and a hypervisor may choose them for it. A
    proof that calls `c: zcpuid` must therefore be safe for every answer.

    There are two exceptions. The first is the one that `c: zxgetbv`
    needs. The XGETBV instruction raises an invalid-opcode fault, which kills the process,
    unless the operating system has set the OSXSAVE bit of control
    register CR4. The processor reports that bit to user code as bit 27
    of the ECX register that CPUID leaf 1 returns, and glibc reads XCR0
    only after it has seen that bit. The assumption [ow_osxsave] about [os_world]
    records whether the kernel enabled XSAVE. The contracts connect the
    two calls through it: `c: zxgetbv` requires [ow_osxsave], and a
    leaf 1 answer has ECX bit 27 equal to [ow_osxsave].

    The second exception is an assumption about the processor that a
    proof may choose to make. Leaf 4 describes one cache in each
    subleaf, and a processor ends the list with an answer whose cache
    type is zero. The cache type is the low five bits of EAX. The
    function `c: get_common_cache_info` in glibc relies on that end
    mark, because it counts the subleaves in a signed 32-bit integer
    and uses the count as an index into a table of sixteen rows. A list
    that never ended would let the count wrap to a negative number, and
    the index would then fail its bounds check. The assumption
    [ow_leaf4_ends] about [os_world] records that the list has ended by
    subleaf 0x7fffffff, which is the last subleaf the count reaches
    before it wraps. When the assumption holds, a leaf 4 answer for that
    subleaf has cache type zero. A proof that needs the loop to stop
    takes [ow_leaf4_ends] as a hypothesis, and no other proof depends
    on it.

    The contracts also assume that CPUID itself does not fault, which
    Linux guarantees after `c: execve` resets `c: ARCH_SET_CPUID`. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld.
From Glibc Require OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** ## The two assumptions

    The record [os_world] holds named assumptions in [ow_facts]. The two
    readers below name the assumptions that this file's contracts use. *)

(** The kernel enabled XSAVE by setting CR4.OSXSAVE, which `c: zxgetbv`
    needs. *)
Definition ow_osxsave (w : os_world) : bool := ow_facts w "osxsave"%string.

(** CPUID leaf 4 reports no cache at its last subleaf, 0x7fffffff. *)
Definition ow_leaf4_ends (w : os_world) : bool := ow_facts w "leaf4_ends"%string.

(** ## The CPUID contracts

    The two CPUID entry points differ only in whether the caller passes
    a subleaf. One contract, indexed by a boolean that is true for
    `c: zcpuid_count`, describes both. The definitions below name the
    arguments, the four output spans, and the single fact a caller
    learns about the answer. *)

(** A call passes the leaf, then the subleaf when sub is true, then the
    four result pointers. [cpuid_args] returns the leaf and the pointers
    for a well-shaped argument list. *)
Definition cpuid_args (sub : bool) (xs : list word) : option (Z * (ptr * ptr * ptr * ptr)) :=
  match sub, xs with
  | false, [WInt leaf; WPtr pa; WPtr pb; WPtr pc; WPtr pd] => Some (leaf, (pa, pb, pc, pd))
  | true, [WInt leaf; WInt _; WPtr pa; WPtr pb; WPtr pc; WPtr pd] => Some (leaf, (pa, pb, pc, pd))
  | _, _ => None
  end.

(** The runtime stores one 32-bit register through each pointer, so the
    call may write the four 4-byte spans of [cpuid_spans]. *)
Definition cpuid_spans (ps : ptr * ptr * ptr * ptr) : list span :=
  let '(pa, pb, pc, pd) := ps in [mkSpan pa 4; mkSpan pb 4; mkSpan pc 4; mkSpan pd 4].

(** A call site satisfies [os_cpuid_abi] when it discards the result and
    passes 32-bit integers followed by four pointers. *)
Definition os_cpuid_abi (sub : bool) (r : call_result) (args : list arg) : Prop :=
  r = CVoid /\ exists l s a b c d,
    args = (if sub then [Arg W l; Arg W s] else [Arg W l]) ++ [Arg P a; Arg P b; Arg P c; Arg P d].

(** At entry, [os_cpuid_pre] requires each result pointer to cover four
    writable bytes of a live object. *)
Definition os_cpuid_pre (sub : bool) (xs : list word) (m : mem) (w : os_world) : Prop :=
  exists leaf ps, cpuid_args sub xs = Some (leaf, ps) /\ Forall (writable_span m) (cpuid_spans ps).

(** The writable spans of a call are the four result spans. *)
Definition os_cpuid_writes (sub : bool) (xs : list word) (m : mem) (w : os_world) : list span :=
  match cpuid_args sub xs with Some (_, ps) => cpuid_spans ps | None => [] end.

(** The runtime stores EDX last. When the EDX span does not overlap the
    ECX span, a leaf 1 call leaves the processor's ECX in memory, and
    [cpuid_osxsave] states that its bit 27 equals [ow_osxsave]. *)
Definition cpuid_osxsave (sub : bool) (xs : list word) (m' : mem) (w : os_world) : Prop :=
  forall pa pb pc pd, cpuid_args sub xs = Some (1, (pa, pb, pc, pd)) ->
    ptr_addr pd + 4 <= ptr_addr pc \/ ptr_addr pc + 4 <= ptr_addr pd ->
    Z.testbit (load_bytes m' (ptr_addr pc) 4) 27 = ow_osxsave w.

(** A call of `c: zcpuid` asks for subleaf zero, and a call of
    `c: zcpuid_count` passes its subleaf as the second argument. *)
Definition cpuid_subleaf (sub : bool) (xs : list word) : Z :=
  match sub, xs with
  | true, _ :: WInt s :: _ => s
  | _, _ => 0
  end.

(** Two result pointers satisfy [spans_apart] when their four-byte
    spans do not overlap. *)
Definition spans_apart (p q : ptr) : Prop :=
  ptr_addr q + 4 <= ptr_addr p \/ ptr_addr p + 4 <= ptr_addr q.

(** A caller that walks the leaf 4 list needs to know that the list
    ends. The runtime stores EAX first, so the processor's EAX stays in
    memory when the three later spans do not overlap the EAX span. The
    predicate [cpuid_leaf4_ends] says that the cache type in that EAX
    is zero. It says so for a leaf 4 call with subleaf 0x7fffffff, in a
    world that satisfies [ow_leaf4_ends]. *)
Definition cpuid_leaf4_ends (sub : bool) (xs : list word) (m' : mem) (w : os_world) : Prop :=
  ow_leaf4_ends w = true ->
  forall pa pb pc pd, cpuid_args sub xs = Some (4, (pa, pb, pc, pd)) ->
    cpuid_subleaf sub xs = 2 ^ 31 - 1 ->
    spans_apart pa pb -> spans_apart pa pc -> spans_apart pa pd ->
    load_bytes m' (ptr_addr pa) 4 mod 32 = 0.

(** The runtime stores each register with one 32-bit store, so every
    byte of the four result spans holds a number below 256. A caller
    that reads a result back one byte at a time relies on
    [cpuid_bytes]. *)
Definition cpuid_bytes (sub : bool) (xs : list word) (m' : mem) : Prop :=
  forall leaf pa pb pc pd, cpuid_args sub xs = Some (leaf, (pa, pb, pc, pd)) ->
    forall p i, In p [pa; pb; pc; pd] -> 0 <= i < 4 -> 0 <= m_bytes m' (ptr_addr p + i) < 256.

(** The contract [os_cpuid_contract] packages these predicates for a
    call that returns nothing. It emits no trace events, allocates and
    frees no objects, leaves the world unchanged, and allows capability
    panics when a result pointer is null, read-only, or out of bounds. *)
Definition os_cpuid_contract (sub : bool) : contract os_world :=
  mkContract os_world RVoid (os_cpuid_abi sub) (os_cpuid_pre sub)
    (fun _ _ _ => []) (os_cpuid_writes sub) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun _ _ w born trace _ w' => born = [] /\ w' = w /\ trace = [])
    (fun xs _ w born trace ending m' w' => born = [] /\ w' = w /\ trace = [] /\
       ending = CallReturn [] /\ cpuid_osxsave sub xs m' w /\ cpuid_leaf4_ends sub xs m' w /\
       cpuid_bytes sub xs m')
    (fun _ => False)
    (fun why => In why [NullCapability; OutOfBounds; Readonly; ArgumentSize; ReturnSize]).

(** ## The XGETBV contract

    Reading XCR0 touches no memory and returns one 64-bit number that the
    kernel chose. The only obligation is the one described above: the
    kernel must have enabled XSAVE. *)

(** A call site satisfies [os_xgetbv_abi] when it passes no arguments
    and either discards the result or binds it to a 64-bit destination. *)
Definition os_xgetbv_abi (r : call_result) (args : list arg) : Prop :=
  (r = CVoid \/ exists d, r = CResult d L) /\ args = [].

(** The contract [os_xgetbv_contract] requires [ow_osxsave], changes
    neither memory nor the world, and returns some 64-bit integer. *)
Definition os_xgetbv_contract : contract os_world :=
  mkContract os_world (RClass L) os_xgetbv_abi
    (fun xs _ w => xs = [] /\ ow_osxsave w = true)
    (fun _ _ _ => []) (fun _ _ _ => []) (fun _ _ _ => [])
    (fun _ _ _ _ _ => False)
    (fun _ m w born trace m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w)
    (fun _ m w born trace ending m' w' => born = [] /\ trace = [] /\ m' = m /\ w' = w /\
       exists v, 0 <= v < 2 ^ 64 /\ ending = CallReturn [WInt v])
    (fun _ => False) (fun why => In why [ArgumentSize; ReturnSize]).

(** ## Over a Logic instance

    A proof of a C function that calls `c: zcpuid` owns the four result
    variables and must get them back after the call, with new contents.
    The rules in this section do that. The caller lends the four
    variables, the call overwrites them, and the caller receives them
    again knowing nothing about the new values except the OSXSAVE bit
    of a leaf 1 answer. A call of `c: zxgetbv` lends nothing. *)

Import OsWorld OsWorld.L OsWorld.LG.

(** A four-byte block inside a live object is a writable span. *)
Lemma cpuid_block_writable m b o :
  blk_live m (b, o, 4) -> writable_span m (mkSpan (mkPtr (b + o) (Obj b)) 4).
Proof.
  intros (reg & [E Lv] & Ho & _ & Hend). cbn in Ho, Hend. split; [cbn; lia|]. exists b, reg.
  split; [reflexivity|]. split; [exact E|]. split; [exact Lv|].
  cbn. apply (access_obj _ _ reg _ _ Write); [exact E | lia | lia | apply Z.mod_1_r].
Qed.

(** When an invocation of [os_cpuid_contract] returns, it leaves the
    world unchanged, returns no values, and its final memory satisfies
    [cpuid_osxsave], [cpuid_leaf4_ends] and [cpuid_bytes]. *)
Lemma os_cpuid_returns sub r args xs s m w trace values s' m' w' :
  M.E.invoke (os_cpuid_contract sub) r args xs s m w trace (CallReturn values) s' m' w' ->
  w' = w /\ values = [] /\ cpuid_osxsave sub xs m' w /\ cpuid_leaf4_ends sub xs m' w /\
  cpuid_bytes sub xs m'.
Proof.
  intros Hi. destruct (os_invoke_returned _ _ _ _ _ _ _ _ _ _ _ _ Hi)
    as (_ & born & _ & _ & -> & _ & He & Hx & H4 & Hb). injection He as ->. auto.
Qed.

(** Suppose a caller owns four bytes of a live object and the memory
    holds a number below 256 at each of their addresses. Then each
    owned byte is below 256. *)
Lemma cpuid_block_bytes m b reg o xs :
  live_at m b reg -> all_agree m (byte_ps b o xs) -> length xs = 4%nat ->
  (forall i, 0 <= i < 4 -> 0 <= m_bytes m (b + o + i) < 256) ->
  Forall (fun x => 0 <= x < 256) xs.
Proof.
  intros Hlv Hag Hlen Hm. apply Forall_lookup_2. intros i x Hx.
  destruct (byte_ps_agree _ _ _ _ _ _ _ Hlv Hag Hx) as (<- & _).
  pose proof (lookup_lt_Some _ _ _ Hx) as Hi. rewrite Hlen in Hi.
  replace (b + (o + Z.of_nat i)) with (b + o + Z.of_nat i) by lia. apply Hm. lia.
Qed.

(** When an invocation of [os_xgetbv_contract] returns, it leaves the
    world unchanged and yields one integer below 2^64. *)
Lemma os_xgetbv_returns r args xs s m w trace values s' m' w' :
  M.E.invoke os_xgetbv_contract r args xs s m w trace (CallReturn values) s' m' w' ->
  w' = w /\ exists v, 0 <= v < 2 ^ 64 /\ values = [WInt v].
Proof.
  intros Hi. destruct (os_invoke_returned _ _ _ _ _ _ _ _ _ _ _ _ Hi)
    as (_ & born & _ & _ & _ & _ & -> & v & Hv & He). injection He as ->. eauto.
Qed.

Import ProgramAbbreviations.
Section rule.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The notation [zexpr] abbreviates expressions of the language over the
    OS contract registry. *)
Local Notation zexpr := (language.expr (nanofil_lang registry ge)).

(** A CPUID call returns each result block as four bytes below 256. *)
Definition cpuid_blk (b o : Z) : iProp Σ :=
  ∃ xs cs, ⌜length xs = 4%nat /\ length cs = 4%nat /\ Forall (fun x => 0 <= x < 256) xs⌝ ∗
    pts (byte_ps b o xs ++ aux_ps b o cs).

(** A caller that does not need the byte bounds can forget them. *)
Lemma cpuid_blk_any b o : cpuid_blk b o -∗ blk_any b o 4.
Proof. iIntros "(%xs & %cs & (% & % & _) & Hp)". iExists xs, cs. iFrame. done. Qed.

(** The ECX block that a CPUID call returns holds four bytes below 256
    whose little-endian value has bit 27 equal to [ow_osxsave],
    provided the call asked for leaf 1 and its EDX block lies
    elsewhere. *)
Definition cpuid_ecx (leaf bc oc bd od : Z) : iProp Σ :=
  ∃ xs cs, ⌜length xs = 4%nat /\ length cs = 4%nat /\ Forall (fun x => 0 <= x < 256) xs /\
            (leaf = 1 -> bd + od + 4 <= bc + oc \/ bc + oc + 4 <= bd + od ->
             Z.testbit (of_bytes xs) 27 = ow_osxsave w0)⌝ ∗
    pts (byte_ps bc oc xs ++ aux_ps bc oc cs).

(** A CPUID call returns its EAX block as four bytes below 256. Their
    little-endian value has cache type zero when three conditions hold.
    The world satisfies [ow_leaf4_ends], the call asked for leaf 4 at
    subleaf 0x7fffffff, and the three other blocks lie elsewhere. *)
Definition cpuid_eax (leaf subleaf ba oa bb ob bc oc bd od : Z) : iProp Σ :=
  ∃ xs cs, ⌜length xs = 4%nat /\ length cs = 4%nat /\ Forall (fun x => 0 <= x < 256) xs /\
            (ow_leaf4_ends w0 = true -> leaf = 4 -> subleaf = 2 ^ 31 - 1 ->
             bb + ob + 4 <= ba + oa \/ ba + oa + 4 <= bb + ob ->
             bc + oc + 4 <= ba + oa \/ ba + oa + 4 <= bc + oc ->
             bd + od + 4 <= ba + oa \/ ba + oa + 4 <= bd + od ->
             of_bytes xs mod 32 = 0)⌝ ∗
    pts (byte_ps ba oa xs ++ aux_ps ba oa cs).

(** A caller that does not need the cache type can forget it. *)
Lemma cpuid_eax_any leaf subleaf ba oa bb ob bc oc bd od :
  cpuid_eax leaf subleaf ba oa bb ob bc oc bd od -∗ blk_any ba oa 4.
Proof. iIntros "(%xs & %cs & (% & % & _) & Hp)". iExists xs, cs. iFrame. done. Qed.

(** A caller that does not need the bit can forget it. *)
Lemma cpuid_ecx_any leaf bc oc bd od : cpuid_ecx leaf bc oc bd od -∗ blk_any bc oc 4.
Proof. iIntros "(%xs & %cs & (% & % & _) & Hp)". iExists xs, cs. iFrame. done. Qed.

(** A call of `c: zcpuid` or `c: zcpuid_count` lends four 4-byte result
    blocks. The assertion Q stands for whatever the caller owns that
    shows the four blocks lie in live objects, usually the lifetimes of
    those objects, and the call returns it unchanged. The call returns
    the four blocks with unknown bytes below 256. In addition, the EAX
    block carries the fact of [cpuid_eax] and the ECX block carries
    the fact of [cpuid_ecx]. *)
Lemma wp_cpuid (sub : bool) f e ls lab args rest j xs leaf ba oa bb ob bc oc bd od (Q : iProp Σ) Φ :
  let g := TAtom (if sub then "zcpuid_count" else "zcpuid")%string in
  registry g = Some (os_cpuid_contract sub) -> find_fn ge g = None -> lookup g (ge_globals ge) = None ->
  map_option (arg_x ge e) args = Some xs -> os_cpuid_abi sub CVoid args ->
  cpuid_args sub xs = Some (leaf, (mkPtr (ba + oa) (Obj ba), mkPtr (bb + ob) (Obj bb),
                                   mkPtr (bc + oc) (Obj bc), mkPtr (bd + od) (Obj bd))) ->
  (forall σ, heap_interp (os_wi w0) σ -∗ Q -∗
     ⌜Forall (blk_live (ls_mem σ)) [(bc, oc, 4); (ba, oa, 4); (bb, ob, 4); (bd, od, 4)]⌝) ->
  Q -∗ blk_any ba oa 4 -∗ blk_any bb ob 4 -∗ blk_any bc oc 4 -∗ blk_any bd od 4 -∗
  ▷ (Q -∗ cpuid_eax leaf (cpuid_subleaf sub xs) ba oa bb ob bc oc bd od -∗ cpuid_blk bb ob -∗
     cpuid_ecx leaf bc oc bd od -∗ cpuid_blk bd od -∗
     WP (ERun (mkFrame f e ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call CVoid (Global g) args :: rest) j)) : zexpr) {{ Φ }}.
Proof.
  intros g Hreg Hfn Hdata Hx Habi Hargs Hlive. iIntros "HQ Ha Hb Hc Hd HK".
  set (bl := [(bc, oc, 4); (ba, oa, 4); (bb, ob, 4); (bd, od, 4)]).
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (os_cpuid_contract sub) xs (Q ∗ blks bl)
            with "[$HQ Ha Hb Hc Hd] [HK]"); [done | done | by destruct sub | exact Hreg | exact Hx | exact Habi | | |].
  - iIntros (σ) "Hσ (HQ & _)". iDestruct (Hlive with "Hσ HQ") as %Hl. iPureIntro.
    eexists _, _. split; [exact Hargs|]. cbn [cpuid_spans].
    inversion_clear Hl as [|? ? Hc Hl']. inversion_clear Hl' as [|? ? Ha Hl]. inversion_clear Hl as [|? ? Hb Hl'].
    inversion_clear Hl' as [|? ? Hd _]. repeat (apply Forall_cons; [apply cpuid_block_writable; assumption|]). apply Forall_nil.
  - rewrite /bl /blks !big_sepL_cons big_sepL_nil. iFrame.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "Hσ (HQ & Hbl)".
    iDestruct (Hlive with "Hσ HQ") as %Hl. iDestruct (os_heap_world with "Hσ") as %[Hw _].
    pose proof Hinv as Hinv0. rewrite Hw in Hinv0.
    destruct (os_cpuid_returns _ _ _ _ _ _ _ _ _ _ _ _ Hinv0) as (-> & -> & Hbit & Hend & Hbytes).
    pose proof (fun p Hp i Hi => Hbytes _ _ _ _ _ Hargs p i Hp Hi) as Hlt.
    iMod (os_call_return w0 _ _ _ _ _ _ _ _ _ _ bl Hinv (eq_sym Hw) eq_refl with "Hσ Hbl") as "(Hσ & Hbl)";
      [|exact Hl|].
    { cbn [contract_writes os_cpuid_contract]. unfold os_cpuid_writes. rewrite Hargs. cbn [cpuid_spans].
      intros sp a Hin Hs. unfold span_contains in Hs.
      destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn in Hs;
        [exists ba, oa, 4 | exists bb, ob, 4 | exists bc, oc, 4 | exists bd, od, 4];
        (split; [cbn; tauto | lia]). }
    iDestruct (Hlive with "Hσ HQ") as %Hl'. inversion_clear Hl' as [|? ? (reg & Hlv & _) Hl''].
    inversion_clear Hl'' as [|? ? (rega & Hlva & _) Hl3].
    inversion_clear Hl3 as [|? ? (regb & Hlvb & _) Hl4]. inversion_clear Hl4 as [|? ? (regd & Hlvd & _) _].
    rewrite /bl /blks !big_sepL_cons big_sepL_nil. cbn [fst snd].
    iDestruct "Hbl" as "(Hc & Ha & Hb & Hd & _)".
    iDestruct "Hc" as (ys cs) "[%Hlen Hc]". destruct Hlen as [Hy Hcs].
    iDestruct (pts_facts with "Hσ Hc") as %(Hag & _). apply all_agree_app in Hag as [Hag _].
    pose proof (bytes_load _ _ _ _ _ Hlv Hag) as Hld. rewrite Hy in Hld. change (Z.of_nat (Z.to_nat 4)) with 4 in Hld.
    iDestruct "Ha" as (ya ca) "[%Hlen Ha]". destruct Hlen as [Hya Hca].
    iDestruct (pts_facts with "Hσ Ha") as %(Haga & _). apply all_agree_app in Haga as [Haga _].
    pose proof (bytes_load _ _ _ _ _ Hlva Haga) as Hlda. rewrite Hya in Hlda.
    change (Z.of_nat (Z.to_nat 4)) with 4 in Hlda.
    iDestruct "Hb" as (yb cb) "[%Hlen Hb]". destruct Hlen as [Hyb Hcb].
    iDestruct (pts_facts with "Hσ Hb") as %(Hagb & _). apply all_agree_app in Hagb as [Hagb _].
    iDestruct "Hd" as (yd cd) "[%Hlen Hd]". destruct Hlen as [Hyd Hcd].
    iDestruct (pts_facts with "Hσ Hd") as %(Hagd & _). apply all_agree_app in Hagd as [Hagd _].
    iModIntro. iExists e. iSplit; [done|]. iFrame "Hσ".
    iApply ("HK" with "HQ [Ha] [Hb] [Hc] [Hd]").
    + iExists ya, ca. iFrame "Ha". iPureIntro. split; [exact Hya|]. split; [exact Hca|].
      split; [apply (cpuid_block_bytes _ _ _ _ _ Hlva Haga Hya); intros i Hi; exact (Hlt (mkPtr (ba + oa) (Obj ba)) ltac:(cbn; tauto) i Hi)|].
      intros Hw4 -> Hs Hb Hc Hd. rewrite <- Hlda. exact (Hend Hw4 _ _ _ _ Hargs Hs Hb Hc Hd).
    + iExists yb, cb. iFrame "Hb". iPureIntro. split; [exact Hyb|]. split; [exact Hcb|].
      apply (cpuid_block_bytes _ _ _ _ _ Hlvb Hagb Hyb); intros i Hi; exact (Hlt (mkPtr (bb + ob) (Obj bb)) ltac:(cbn; tauto) i Hi).
    + iExists ys, cs. iFrame "Hc". iPureIntro.
      split; [exact Hy|]. split; [exact Hcs|].
      split; [apply (cpuid_block_bytes _ _ _ _ _ Hlv Hag Hy); intros i Hi; exact (Hlt (mkPtr (bc + oc) (Obj bc)) ltac:(cbn; tauto) i Hi)|].
      intros -> Hdis. rewrite <- Hld. exact (Hbit _ _ _ _ Hargs Hdis).
    + iExists yd, cd. iFrame "Hd". iPureIntro. split; [exact Hyd|]. split; [exact Hcd|].
      apply (cpuid_block_bytes _ _ _ _ _ Hlvd Hagd Hyd); intros i Hi; exact (Hlt (mkPtr (bd + od) (Obj bd)) ltac:(cbn; tauto) i Hi).
Qed.

(** When a C function calls `c: zxgetbv()` in an OS world whose kernel
    enabled XSAVE, [wp_zxgetbv] binds the destination register to some
    64-bit integer without requiring or modifying any caller-owned
    memory. *)
Lemma wp_zxgetbv f e ls lab d rest j Φ :
  registry (TAtom "zxgetbv") = Some os_xgetbv_contract ->
  find_fn ge (TAtom "zxgetbv") = None -> lookup (TAtom "zxgetbv") (ge_globals ge) = None ->
  ow_osxsave w0 = true ->
  ▷ (∀ v, ⌜0 <= v < 2 ^ 64⌝ -∗
     WP (ERun (mkFrame f (put d (WInt v) e) ls None (Exec lab rest j)) : zexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d L) (Global (TAtom "zxgetbv")) [] :: rest) j)) : zexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hosx. iIntros "HK".
  iApply (wp_os_call w0 _ _ _ _ _ _ _ _ _ _ _ _ [] [] True%I (fun vs => exists v, 0 <= v < 2 ^ 64 /\ vs = [WInt v])
            with "[//] [] [HK]"); [done | done | done | exact Hreg | done | | | done | | |].
  - split; [right; eexists; reflexivity | reflexivity].
  - iIntros (σ) "Hσ _". iDestruct (os_heap_world with "Hσ") as %[-> _]. iPureIntro.
    split; [split; [reflexivity | exact Hosx]|]. split; [constructor | intros ? ? []].
  - intros σ trace vs s' m' w' Hi. iIntros "_ _". iPureIntro. exact (os_xgetbv_returns _ _ _ _ _ _ _ _ _ _ _ Hi).
  - iApply blks_nil.
  - iNext. iIntros (vs (v & Hv & ->)) "_ _". iExists _. iSplit; [|iApply ("HK" with "[%]"); exact Hv].
    iPureIntro. cbn. destruct Hv as [H0 H1]. unfold external_env. cbn.
    rewrite Z.mod_small; [reflexivity | lia].
Qed.

End rule.
