From Glibc Require Import GlibcProgram.
(** DcigettextRoute.v proves glibc's `c: __dcigettext` in the C locale
    when the privilege flag `__libc_enable_secure` reads 0. The flag in
    the linked image of GNU Hello starts as 1, so that statement does not
    cover the initial state. This module proves the same route for every
    32-bit value of the flag. When the flag is nonzero the function also
    calls strchr on the copied locale name, so the caller must then show
    that the program links strchr and strchrnul to the captured bodies.
    The caller gets back the flag cell with the value it lent, and every
    other premise is the same as before. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks OsRegistry FileInv LibioLogic LibioSetb WordString StrlenLogic StrlenWord.
From Glibc Require Import MemFwdCode GetoptLongPfxAlloc DcigettextCode DcigettextFree DcigettextExit DcigettextPreRules.
From Glibc Require Import DcigettextPre DcigettextDom DcigettextJoin DcigettextCopy DcigettextSecure DcigettextRoute StrchrnulLogic.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Import FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance dci_route_v_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).

(** The route reads the same memory as before, except that the flag
    cell may hold any value v. *)
Definition dci_reads_v (dom : ptr) (ds : list Z) (dqd : dfrac) (nb : Z) (nc : cap) (k : Z) (cat : list Z) (dqc : dfrac)
    (cv p276 p277 : ptr) (db : Z) (dqb : dfrac) (dbreg : region) (ib : Z) (dqi : dfrac) (ireg : region)
    (sec : Z) (dqs : dfrac) (secreg : region) (v : Z) : iProp Σ :=
  word_string dqd dom ds ∗ word_string dqc (mkPtr (nb + k) nc) cat ∗
  word_string DfracDiscarded cv [67] ∗ word_string DfracDiscarded p276 [47] ∗
  word_string DfracDiscarded p277 [46; 109; 111] ∗
  liveq dqb db dbreg ∗ pcellq dqb db 0 null ∗ liveq dqi ib ireg ∗ bytesq dqi ib 5 [k] ∗
  liveq dqs sec secreg ∗ int_cellq dqs sec 0 v.

(** With the value 0 the new predicate is the old one. *)
Lemma dci_reads_v_0 dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg :
  dci_reads_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg 0 =
  dci_reads dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg.
Proof using Type. reflexivity. Qed.

(** The route returns the message id for every value of the flag. *)
Lemma wp_dci_route_v e dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg v
    msgid lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy} :
  dci_callees_f lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals eb lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  0 <= v < 2 ^ 32 -> (v = 0 \/ dci_strchr_links) ->
  lookup (TAtom "v0") e = Some (WPtr dom) -> lookup (TAtom "v2") e = Some (WPtr msgid) ->
  lookup (TAtom "v6") e = Some (WInt 0) -> lookup (TAtom "v10") e = Some (WInt 5) -> 0 < ptr_addr msgid < 2 ^ 64 ->
  dci_reads_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v -∗
  L1 -∗ L2 -∗ T -∗ K -∗ C -∗ M -∗ errno_own eb bs -∗
  ▷ (dci_reads_v dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg v -∗
     L1'' -∗ L2'' -∗ T'' -∗ K -∗ C -∗ M -∗ errno_own eb (le_bytes (dci_w bs) 4) -∗ Φ (Ret (WPtr msgid))) -∗
  WP (ERun (mkFrame glibc_dcigettext e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros (Hcpy & Hmv & Hmvf & Hmvs & Hheap & Hmal & Hloc & Hrt1 & Hut & Htf & Hr1 & Hr2 & Hu1 & Hu2)
    (Hlkt & Hrt & Htc & Hge & Hlk1 & Hlk2 & Hdb & Hdd & Hcn & Hci & H276 & H277 & Hsec)
    ((Hdb0 & Hdb8 & Hdbend & Hdbr) & Hic & (Hib0 & Hibend & Hibr) & (Hk & Hnb & Hnbk) & (Hsec0 & Hsec4 & Hsecend & Hsecr))
    Hv Hlinks Hv0 Hv2 Hv6 Hv10 Hm.
  iIntros "(Hdom & Hcat & #Hcv & #H276 & #H277 & Hnl & Hnc & Hil & Hib & Hsecl & Hsecb) HL1 HL2 HT HK HC HM Herr HΦ".
  iDestruct (dci_ws_bounds with "Hdom") as "[%Hdomb Hdom]".
  iApply (wp_dci_pre eb Herr e dom msgid lk1 lk2 L1 L1' L2 L2' bs C cv lkt T T' T'' rt tc K
    with "HL1 HL2 Herr HC HT HK"); try first [assumption | lia].
  iNext. iIntros (e1 xs xreg rl sb sreg (Henv1 & (Hxs0 & Hxs16 & Hxre & Hxsb) & Hxk & Hsb))
    "Hxl Hxc _ _ _ _ _ _ _ Herr HL1 HL2 HC HT HK".
  assert (Hxs8 : xs mod 8 = 0) by (Z.div_mod_to_equations; lia).
  pose proof (dci_w_range bs) as Hs.
  iApply (wp_dci_dom with "Hnl Hnc Hil Hib Hcv HC"); try first [eassumption | lia].
  iNext. iIntros (e2 (Henv2 & Hv7 & Hv9)) "Hnl Hnc Hil Hib HC".
  iApply (wp_dci_join_fr eb Herr _ xs xreg _ _ _ _ _ _ _ _ _ _ _ _ _ L1' L1'' L2' L2'' with "Hcat Hdom HM Hxl Hxc HL1 HL2 Herr");
    try first [eassumption | lia].
  iNext. iSplit.
  { iIntros "_ _ HL1 HL2 Herr Hcat Hdom HM".
    iApply ("HΦ" with "[$Hdom $Hcat $Hcv $H276 $H277 $Hnl $Hnc $Hil $Hib $Hsecl $Hsecb] HL1 HL2 HT HK HC HM Herr"). }
  iIntros (e3 xd (Henv3 & Hv224 & Hv9' & Hv226 & Hv232 & Hxd0 & Hxd16 & Hxdend)) "Ho Hcat Hdom HM Hxl Hxc HL1 HL2 Herr".
  iApply (wp_dci_copy_w_fr eb Herr _ xs xreg _ _ _ _ _ _ _ _ _ _ _ xd p276 p277 _ _ L1' L1'' L2' L2''
    with "Ho Hcat Hdom Hcv H276 H277 HM Hxl Hxc HL1 HL2 Herr"); try first [eassumption | lia].
  iNext. iSplit.
  { iIntros "_ _ HL1 HL2 Herr Hcat Hdom HM".
    iApply ("HΦ" with "[$Hdom $Hcat $Hcv $H276 $H277 $Hnl $Hnc $Hil $Hib $Hsecl $Hsecb] HL1 HL2 HT HK HC HM Herr"). }
  iIntros (e4 sl (Henv4 & Hv224' & Hv232' & Hv254 & Hsl0 & Hslend & Hsl16))
    "Hdl Hsl Hb0 Hb1 Hbs Hcat Hdom HM Hxl Hxc HL1 HL2 Herr".
  assert (0 <= req_extent (heap_req 16 (Z.of_nat (length cat + length ds) + 5))) by (cbn; Z.div_mod_to_equations; lia).
  assert (Hsl8 : sl mod 8 = 0) by (Z.div_mod_to_equations; lia).
  pose proof Henv4 as (Hv17 & Hc0 & _ & _ & _ & Hv2' & Hv6' & _ & Hv32 & Hv69 & _).
  rewrite (_ : replicate 14 0 = (replicate 6 0 ++ replicate 8 0)%list); [|reflexivity]. rewrite bytes_app.
  iDestruct "Hbs" as "[Hbs _]".
  iApply (wp_dci_c_locale_v_fr eb Herr e4 cv sl _ 0 0 sec secreg dqs v xs xreg xd _ (dci_w bs) msgid lk1 lk2 L1' L1'' L2' L2''
    with "Hcv Hsecl Hsecb Hsl Hb0 Hb1 Hbs Hxl Hxc Hdl HL1 HL2 Herr");
    try first [eassumption | reflexivity | cbn [r_end]; lia].
  iNext. iIntros "_ _ Hsecl Hsecb HL1 HL2 Herr".
  iApply ("HΦ" with "[$Hdom $Hcat $Hcv $H276 $H277 $Hnl $Hnc $Hil $Hib $Hsecl $Hsecb] HL1 HL2 HT HK HC HM Herr").
Qed.

(** ## Controls

    When the flag reads 0 the function never calls strchr, so a caller
    should not have to link it. The new route with the value 0 gives the
    old statement, and it needs no strchr link. *)
Lemma wp_dci_route_f_v0 e dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib ic dqi ireg sec dqs secreg
    msgid lk1 lk2 lkt rt tc dd L1 L1' L1'' L2 L2' L2'' T T' T'' K C M bs Φ
    `{!Defines ge "__GI_strlen" glibc_strlen, !Defines ge "__GI_mempcpy" glibc_mempcpy,
      !Defines ge "__GI_memcpy" glibc_memcpy} :
  dci_callees_f lk1 lk2 lkt rt tc L1 L1' L1'' L2 L2' L2'' T T' T'' K C M cv ->
  dci_globals eb lk1 lk2 lkt rt tc dd db nb nc ib ic p276 p277 sec ->
  dci_bounds db dbreg nb ib ic ireg k sec secreg ->
  lookup (TAtom "v0") e = Some (WPtr dom) -> lookup (TAtom "v2") e = Some (WPtr msgid) ->
  lookup (TAtom "v6") e = Some (WInt 0) -> lookup (TAtom "v10") e = Some (WInt 5) -> 0 < ptr_addr msgid < 2 ^ 64 ->
  dci_reads dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg -∗
  L1 -∗ L2 -∗ T -∗ K -∗ C -∗ M -∗ errno_own eb bs -∗
  ▷ (dci_reads dom ds dqd nb nc k cat dqc cv p276 p277 db dqb dbreg ib dqi ireg sec dqs secreg -∗
     L1'' -∗ L2'' -∗ T'' -∗ K -∗ C -∗ M -∗ errno_own eb (le_bytes (dci_w bs) 4) -∗ Φ (Ret (WPtr msgid))) -∗
  WP (ERun (mkFrame glibc_dcigettext e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof using Type*. intros. iApply wp_dci_route_v; try eassumption; [lia | left; reflexivity]. Qed.

(** The block at L298 takes the privileged branch exactly when the flag
    is nonzero modulo 2^32. The values 1 and 0xdeadbeef take it, and 0
    does not. The value 2^32 would pass as 0, which is why the route asks
    for a representable value. *)
Example dci_secure_branch_controls :
  (0 mod 2 ^ 32 =? 0) = true /\ (1 mod 2 ^ 32 =? 0) = false /\
  (3735928559 mod 2 ^ 32 =? 0) = false /\ (2 ^ 32 mod 2 ^ 32 =? 0) = true.
Proof using Type*. vm_compute. auto. Qed.

(** In the privileged branch strchr searches the copied "C" for '/'
    and returns null, while a search for 'C' would return the buffer
    itself. So the branch falls through only because the name has no
    slash. *)
Example dci_secure_strchr_controls :
  strchr_ptr (mkPtr 4096 (Obj 4096)) 47 [67] = mkPtr 0 CNone /\
  strchr_ptr (mkPtr 4096 (Obj 4096)) 67 [67] = mkPtr 4096 (Obj 4096).
Proof using Type*. vm_compute. auto. Qed.
End rules.
