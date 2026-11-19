(** Glibc looks up the C locale's converter and gives it room for a
    single wide character. When the converter rejects a high byte,
    glibc leaves the input and output in place and sets errno. A NUL
    yields zero, and every other ASCII byte consumes one input byte. *)

From Glibc Require Import Unit_wcsmbs_mbrtowc_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic VariadicLogic.
From Glibc Require Import IRFrames.
From Glibc Require Import CodePrelude HelloImageModule HelloImageLoad OsWorld OsBlocks FileInv LibioLogic
  AsciiConvert StartInitMisc DcigettextExit Fix.
From Glibc Require Export CLocaleCells.
Module MbVL := VariadicLogicOn R LG0.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic MbVL.
Open Scope Z_scope.

(** The public name mbrtowc is an alias for this body in Hello. *)
Definition glibc_mbrtowc := Unit_wcsmbs_mbrtowc_os.fn___GI___mbrtowc.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation heap b n := (mkRegion b (b + n) Heap Live).
Local Abbreviation objp b := (mkPtr b (Obj b)).
Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation ts := (img_a "__libc_tsd_LOCALE").
Local Abbreviation gl := (img_a "_nl_global_locale").
Local Abbreviation cc := (img_a "_nl_C_LC_CTYPE").
Local Abbreviation cd := (img_a "glibc_C_ctype#lc_ctype_data").
Local Abbreviation ft := (img_a "__wcsmbs_gconv_fcts_c").
Local Abbreviation st := (img_a "glibc_wcsmbsload#to_wc").
Local Abbreviation fp := (mkPtr (img_a "__gconv_transform_ascii_internal") (Fn (TAtom "__gconv_transform_ascii_internal"))).

Section objects.
Context `{!gen_heapGS piece pval Σ}.

(** The four pointer loads that follow the character category find
    the last conversion step. Its library handle is null and its
    function pointer names the built-in ASCII converter. *)
Definition mbr_tables : iProp Σ :=
  liveq DfracDiscarded cc (img_gd "_nl_C_LC_CTYPE") ∗ pcellq DfracDiscarded cc 32 (rop cd) ∗
  liveq DfracDiscarded cd (img_gd "glibc_C_ctype#lc_ctype_data") ∗ pcellq DfracDiscarded cd 0 (rop ft) ∗
  liveq DfracDiscarded ft (img_gd "__wcsmbs_gconv_fcts_c") ∗ pcellq DfracDiscarded ft 0 (rop st) ∗
  liveq DfracDiscarded st (img_gd "glibc_wcsmbsload#to_wc") ∗ pcellq DfracDiscarded st 0 null ∗ pcellq DfracDiscarded st 40 fp.
End objects.

Section conversion.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (objp eb))
  (Herrno : lookup (TAtom "__libc_errno") (ge_globals ge) = Some (objp eb))
  (Hts : lookup (TAtom "__libc_tsd_LOCALE") (ge_globals ge) = Some (objp ts))
  (Hfp : function_check_res ge fp = Some ok)
  (Hascii : find_fn ge (TAtom "__gconv_transform_ascii_internal") = Some (Defined glibc_ascii_internal)).

(** The result records the number of consumed bytes, except that
    glibc returns zero for NUL and minus one for an illegal byte. The
    shift state stays zero and only an illegal byte changes errno. *)
Lemma wp_mbrtowc_c dq sb sr sa sc ob oreg oa state n x xs es Φ :
  sc = Obj sb \/ sc = Ro sb -> 0 < sb -> sb <= sa -> 1 <= n -> sa + n <= r_end sr -> r_end sr <= 2 ^ 48 ->
  0 < ob -> ob <= oa -> oa + 4 <= r_end oreg -> r_end oreg <= 2 ^ 48 ->
  0 < state -> state + 16 <= 2 ^ 48 -> 0 <= x < 256 -> length xs = 4%nat -> length es = 4%nat ->
  mbr_locale dq -∗ mbr_tables -∗ liveq DfracDiscarded sb sr -∗ bytesq DfracDiscarded sb (sa - sb) [x] -∗
  live state (heap state 16) -∗ bytes state 0 (le_bytes 0 4) -∗ live ob oreg -∗ bytes ob (oa - ob) xs -∗ bytes eb 0 es -∗
  ▷ (mbr_locale dq -∗ live state (heap state 16) -∗ bytes state 0 (le_bytes 0 4) -∗ live ob oreg -∗
     bytes ob (oa - ob) (if x <? 128 then le_bytes x 4 else xs) -∗ bytes eb 0 (if x <? 128 then es else le_bytes 84 4) -∗
     Φ (Ret (WInt (if x <? 128 then if x =? 0 then 0 else 1 else 2^64-1)))) -∗
  WP (ERun (invocation glibc_mbrtowc [WPtr (mkPtr oa (Obj ob)); WPtr (mkPtr sa sc); WInt n; WPtr (objp state)]) : sexpr) {{ Φ }}.
Proof using Type*.
  intros Hsc Hsb Hsa Hn Hse Hsr Hob Hoa Hoe Hor Hstate Hste Hx Hxs Hes.
  iIntros "(Hts & Hts0 & Hgl & Hgl0) (#Hcc & #Hcc32 & #Hcd & #Hcd0 & #Hft & #Hft0 & #Hst & #Hst0 & #Hfn)
    #Hsl #Hbyte Hpsl Hps Hol Hbytes He HK".
  iAssert (live_capq DfracDiscarded sc sr) as "Hsk". { destruct Hsc as [->| ->]; iExact "Hsl". }
  lazymatch goal with |- context [invocation ?f ?xs] => change (invocation f xs) with
    (mkFrame f [(TAtom "v6", WPtr (objp state)); (TAtom "v4", WInt n); (TAtom "v2", WPtr (mkPtr sa sc));
     (TAtom "v0", WPtr (mkPtr oa (Obj ob)))] [] None (Enter (TAtom "start") None)) end.
  step.
  Local Ltac mb_alloc := iApply wp_alloc; [reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |]; iNext.
  mb_alloc. iIntros (? _) "_". mb_alloc. iIntros (d Hd) "Hd".
  change (0 < d /\ d mod 16 = 0 /\ d + 48 <= 2^48) in Hd. destruct Hd as (Hd & Hd16 & Hde).
  iDestruct (obj_zero_block with "Hd") as "(Hdl & Hb & Ha)"; [vm_compute; congruence|].
  iAssert (live d (heap d 48)) with "Hdl" as "Hdl".
  iDestruct (zero_cell_prefix d 0 40 with "Hb Ha") as "(Hout & Hb & Ha)".
  iDestruct (zero_cell_prefix d 8 32 with "Hb Ha") as "(Hend & Hb & Ha)".
  iDestruct (bytes_take_drop _ _ _ 16 with "Hb") as "[Hwords Hb]"; [vm_compute; lia|].
  iDestruct (auxes_take_drop _ _ _ 16 with "Ha") as "[_ Ha]"; [vm_compute; lia|].
  iDestruct (zero_cell_prefix d 32 8 with "Hb Ha") as "(Hstate & _ & _)".
  iDestruct (bytes_take_drop _ _ _ 4 with "Hwords") as "[Hflags Hwords]"; [vm_compute; lia|].
  iDestruct (bytes_take_drop _ _ _ 4 with "Hwords") as "[Hcalls Hwords]"; [vm_compute; lia|].
  iDestruct (bytes_take_drop _ _ _ 4 with "Hwords") as "[Hint _]"; [vm_compute; lia|].
  mb_alloc. iIntros (count Hcount) "Hc". change (0 < count /\ count mod 16 = 0 /\ count + 16 <= 2^48) in Hcount.
  destruct Hcount as (Hcount & Hc16 & Hce). iDestruct (obj_zero_block with "Hc") as "(Hcl & Hb & _)"; [vm_compute; congruence|].
  iDestruct (bytes_take_drop _ _ _ 8 with "Hb") as "[Hb _]"; [vm_compute; lia|]. iAssert (icell count 0 0) with "Hb" as "Hcounter".
  mb_alloc. iIntros (i Hi) "Hi". change (0 < i /\ i mod 16 = 0 /\ i + 16 <= 2^48) in Hi. destruct Hi as (Hi & Hi16 & Hie).
  iDestruct (obj_zero_block with "Hi") as "(Hil & Hb & Ha)"; [vm_compute; congruence|].
  iAssert (live i (heap i 16)) with "Hil" as "Hil". iDestruct (zero_cell_prefix i 0 8 with "Hb Ha") as "(Hin & _ & _)".
  step. step. branch_as false. step. step. check "Hdl". store_int "Hdl" "Hcalls".
  step. check "Hdl". store_int "Hdl" "Hint". step. check "Hdl". store_int "Hdl" "Hflags".
  do 3 step. branch_as false. step. check "Hdl". store "Hdl" "Hstate". do 3 step. branch_as true.
  step. step. branch_as true. step. check "Hdl". store "Hdl" "Hout". step. step. check "Hdl". store "Hdl" "Hend".
  step_global Hts. check "Hts". load_pointer_dq "Hts Hts0 Hgl" by a2. iNext. iIntros "Hts Hts0 Hgl".
  check "Hgl". load_pointer_dq "Hgl Hgl0 Hcc" by a2. iNext. iIntros "Hgl Hgl0 _".
  Local Ltac mb_check H := check_read_dq H by a2; iNext; iIntros "_".
  step. mb_check "Hcc". load_pointer_dq "Hcc Hcc32 Hcd" by a2. iNext. iIntros "_ _ _".
  mb_check "Hcd". load_pointer_dq "Hcd Hcd0 Hft" by a2. iNext. iIntros "_ _ _".
  step. step. branch. step. iApply (StartInitMisc.wp_renew_read_dq with "Hcd");
    [reflexivity | vx | reflexivity | right; reflexivity | a2 | a2 | a2 |]. iNext. iIntros "_".
  load_pointer_dq "Hcd Hcd0 Hft" by a2. iNext. iIntros "_ _ _".
  check "Hil". store "Hil" "Hin". check "Hil". load_pointer_dq "Hil Hin Hsk" by a2. iNext. iIntros "Hil Hin _".
  step. load_pointer_dq "Hil Hin Hsk" by a2. iNext. iIntros "Hil Hin _". do 3 step. branch_as true. step.
  mb_check "Hft". load_pointer_dq "Hft Hft0 Hst" by a2. iNext. iIntros "_ _ _". step. mb_check "Hst".
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 40 fp sr DfracDiscarded DfracDiscarded DfracDiscarded
    with "Hst Hfn []"); [reflexivity | vx | right; reflexivity | a2 | a2 | a2 | done |]. iNext. iIntros "_ _ _".
  load_pointer_dq "Hft Hft0 Hst" by a2. iNext. iIntros "_ _ _". mb_check "Hst".
  iApply (wp_raw_load_pointer_dq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 null sr DfracDiscarded DfracDiscarded DfracDiscarded
    with "Hst Hst0 []"); [reflexivity | vx | right; reflexivity | a2 | a2 | change (0 <= 0 < 2^64); lia | done |].
  iNext. iIntros "_ _ _". step. step. branch. do 3 step. load_pointer_dq "Hft Hft0 Hst" by a2. iNext. iIntros "_ _ _".
  iApply wp_check_function; [vx | exact Hfp |]. iNext.
  iApply wp_raw_call_bind; [vx | reflexivity | exact Hfp | vx | exact Hascii | reflexivity | reflexivity |]. iNext.
  cbn [ptr_addr ptr_cap]. rewrite (Z.mod_small sa (2^64)) ?(Z.mod_small n (2^64)) ?(Z.mod_small (sa+n) (2^64))
    ?(Z.mod_small oa (2^64)) ?(Z.mod_small 4 (2^64)) ?(Z.mod_small (oa+4) (2^64)); try lia.
  iApply (wp_ascii_internal (rop st) d i count sb sr sa sc ob oreg oa n x xs
    with "Hdl Hout Hend Hflags Hcalls Hil Hin Hcl Hcounter Hsl Hbyte Hol Hbytes"); try eassumption.
  iNext. iIntros "Hdl Hout Hil Hin Hol Hbytes". destruct (Z.ltb_spec x 128) as [Hlo|Hhi].
  1: destruct (Z.eqb_spec n 1) as [En|En]. all: iExists _; iSplit; [iPureIntro; reflexivity|]; iNext.
  all: repeat first [step | branch].
  3: (iApply (wp_dci_errno_check eb Herr); [vx |]; iNext; iApply (wp_dci_errno_store eb Herr with "He");
    [vx | vx | exact Hes |]; iNext; iIntros "He"; step; step; iApply wp_ret; [reflexivity | vx |]; iNext;
    iApply ("HK" with "[$Hts $Hts0 $Hgl $Hgl0] Hpsl Hps Hol Hbytes He")).
  all: check "Hdl"; load_pointer_dq "Hdl Hout Hol" by a2; iNext; iIntros "Hdl Hout Hol"; do 3 step; branch_as false;
    step; check "Hol"; load_bytes_dq "Hol Hbytes" decode (apply load_sw_int; lia) by a2; iNext; iIntros "Hol Hbytes";
    step; step; step; destruct (Z.eqb_spec x 0) as [Ez|Ez].
  1,3: (branch_as false; step; step; check "Hdl"; load_pointer_dq "Hdl Hstate Hpsl" by a2; iNext; iIntros "Hdl Hstate Hpsl";
    check "Hpsl"; load_bytes_dq "Hpsl Hps" decode reflexivity by a2; iNext; iIntros "Hpsl Hps"; step; branch; step;
    iApply wp_ret; [reflexivity | vx |]; iNext; iApply ("HK" with "[$Hts $Hts0 $Hgl $Hgl0] Hpsl Hps Hol Hbytes He")).
  all: branch_as true; step; check "Hil"; load_pointer_dq "Hil Hin Hsk" by a2; iNext; iIntros "Hil Hin _";
    do 5 step; iApply wp_ret; [reflexivity | vx |]; iNext.
  all: cbn [ptr_addr]; rewrite ?(Z.mod_small sa (2^64)) ?(Z.mod_small (sa+1) (2^64)); try lia;
    replace (sa+1-sa) with 1 by lia; iApply ("HK" with "[$Hts $Hts0 $Hgl $Hgl0] Hpsl Hps Hol Hbytes He").
Qed.
End conversion.

(** The linker resolves the public alias and the converter's function
    pointer to the two bodies used above. The two data symbols name
    the objects that startup supplies. *)
Lemma mbrtowc_image_link fr : let ge := mkGenv hello_image_module img_globals fr in
  find_fn ge (TAtom "mbrtowc") = Some (Defined glibc_mbrtowc) /\
  find_fn ge (TAtom "__gconv_transform_ascii_internal") = Some (Defined glibc_ascii_internal) /\
  function_check_res ge fp = Some ok /\ lookup (TAtom "__libc_tsd_LOCALE") (ge_globals ge) = Some (objp ts) /\
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (objp (img_a "errno")).
Proof. vm_compute. repeat split. Qed.
