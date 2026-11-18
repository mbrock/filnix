(** The wide flush `c: _IO_wdo_write` turns a stream's wide characters
    into bytes by calling `c: __libio_codecvt_out`:

    ```
    enum __codecvt_result
    __libio_codecvt_out (struct _IO_codecvt *codecvt, __mbstate_t *statep,
                         const wchar_t *from_start, const wchar_t *from_end,
                         const wchar_t **from_stop, char *to_start, char *to_end,
                         char **to_stop)
    {
      struct __gconv_step *gs = codecvt->__cd_out.step;
      size_t dummy;
      const unsigned char *from_start_copy = from_start;
      codecvt->__cd_out.step_data.__outbuf = to_start;
      codecvt->__cd_out.step_data.__outbufend = to_end;
      codecvt->__cd_out.step_data.__statep = statep;
      __gconv_fct fct = gs->__fct;
      if (gs->__shlib_handle != NULL)
        PTR_DEMANGLE (fct);
      status = DL_CALL_FCT (fct, (gs, &codecvt->__cd_out.step_data, &from_start_copy,
                                  from_end, NULL, &dummy, 0, 0));
      *from_stop = from_start_copy;
      *to_stop = codecvt->__cd_out.step_data.__outbuf;
      ...
    }
    ```

    The function points the output descriptor at the destination,
    calls the descriptor's conversion step, and reports where the step
    stopped in the source and in the destination. It maps the step's
    status to the three results that the flush distinguishes. In the C
    locale the step is the ASCII converter, and a null output start
    makes it run as the last step of its chain. This file proves the
    function against a rule for that run of the step. *)

From Glibc Require Import HelloImageTypedLI.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic AbsInfer.
From Glibc Require Import CodePrelude HelloImageLoad HelloImageWConvObjs OsWorld FileInv
  LibioLogic LibioCloseSteps LibioWIdle Mbrtowc CBlocks Fix LibioWConvAscii LibioWConvConsts.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation objp b := (mkPtr b (Obj b)).
Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation tmb := (img_a "glibc_wcsmbsload#to_mb").
Local Abbreviation fct := (mkPtr (img_a "__gconv_transform_internal_ascii") (Fn (TAtom "__gconv_transform_internal_ascii"))).

(** This definition is the conversion function as Hello's image holds it. *)
Definition glibc_codecvt_out := hello_image_fn___libio_codecvt_out.

Section out.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** ## The rule of the ASCII step

    The conversion function hands all of its work to the ASCII step.
    The proof of that step belongs to another file, so this section
    takes its rule as a hypothesis. *)

(** The rule [ia_last_rule] dl describes one call of the ASCII step
    with a null output start. The step reads the characters ws through
    the source cursor in the cell pi and writes bytes into the window
    that the output descriptor names. It moves the cursor past the k
    characters it consumed and the window's start past the j bytes it
    produced, and it may set the illegal-input flag. *)
Definition ia_last_rule (dl : dfrac) : Prop :=
  forall fr wd wreg sb sreg dq sc so ws tb treg to xs fl cnt pi pireg lb lbreg c0 Φ,
  let n := Z.of_nat (length ws) in let m := Z.of_nat (length xs) in
  call_frame glibc_internal_ascii [WPtr (rop tmb); WPtr (mkPtr (wd + 168) (Obj wd)); WPtr (objp pi);
    WPtr (mkPtr (sb + so + 4 * n) sc); WPtr null; WPtr (objp lb); WInt 0; WInt 0] = Some fr ->
  wflags_ok fl ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 ->
  (sc = Obj sb \/ sc = Ro sb) -> 0 < sb -> 0 <= so -> sb + so + 4 * n <= r_end sreg -> r_end sreg <= 2 ^ 63 ->
  (sb = wd -> sreg = wreg) -> Forall (fun c => 0 <= c < 2 ^ 32) ws ->
  0 < tb -> 0 <= to -> tb + to + m <= r_end treg -> r_end treg <= 2 ^ 63 -> Forall (fun x => 0 <= x < 256) xs ->
  0 < pi -> pi mod 8 = 0 -> pi + 8 <= r_end pireg -> r_end pireg <= 2 ^ 63 ->
  0 < lb -> lb mod 8 = 0 -> lb + 8 <= r_end lbreg -> r_end lbreg <= 2 ^ 63 ->
  ⊢ wconv_ro -∗ wlocale dl -∗ live wd wreg -∗
    pcell wd 168 (mkPtr (tb + to) (Obj tb)) -∗ pcell wd 176 (mkPtr (tb + to + m) (Obj tb)) -∗
    int_cell wd 184 fl -∗ int_cell wd 188 cnt -∗
    (if decide (sb = wd) then True else liveq dq sb sreg) -∗ bytesq dq sb so (le_words ws) -∗
    live tb treg -∗ bytes tb to xs -∗ live pi pireg -∗ pcell pi 0 (mkPtr (sb + so) sc) -∗
    live lb lbreg -∗ icell lb 0 c0 -∗
    ▷ (∀ st k j zs fl' cnt' c', ⌜0 <= k <= n /\ 0 <= j <= m /\ length zs = length xs /\
         Forall (fun z => 0 <= z < 256) zs /\ (fl' = fl \/ fl' = Z.lor fl (2 ^ 30))⌝ -∗
       wlocale dl -∗ live wd wreg -∗
       pcell wd 168 (mkPtr (tb + to + j) (Obj tb)) -∗ pcell wd 176 (mkPtr (tb + to + m) (Obj tb)) -∗
       int_cell wd 184 fl' -∗ int_cell wd 188 cnt' -∗
       (if decide (sb = wd) then True else liveq dq sb sreg) -∗ bytesq dq sb so (le_words ws) -∗
       live tb treg -∗ bytes tb to zs -∗ live pi pireg -∗ pcell pi 0 (mkPtr (sb + so + 4 * k) sc) -∗
       live lb lbreg -∗ icell lb 0 c' -∗ Φ (Ret (WInt st))) -∗
    WP (ERun fr : sexpr) {{ Φ }}.

Context (dl : dfrac) (Hlast : ia_last_rule dl).
Context `{Hia : !Defines ge "__gconv_transform_internal_ascii" glibc_internal_ascii}
  (Hfct : function_check_res ge fct = Some ok)
  (Htmb : lookup (TAtom "glibc_wcsmbsload#to_mb") (ge_globals ge) = Some (rop tmb)).

(** ## The conversion

    The conversion function only moves pointers between its caller and
    the step. It reads the step through the output descriptor, which
    the stream owns, and through read-only tables of the C locale. The
    collector reclaims the two eight-byte locals that it allocates. *)

(** The conversion reads the step's fields through a read-only
    pointer, so its half check needs only a share of the step's life. *)
Local Lemma wp_half_check_read_dq f e ls l d bd lo hi al args rest j classes p1 p b reg dq' Φ :
  op_arg_classes (HalfCheck bd lo hi Read al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p1; WPtr p] ->
  ptr_cap p1 = ptr_cap p -> ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  b <= raw_address (ptr_addr p) lo -> raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg ->
  lo < hi -> r_end reg <= 2 ^ 63 -> raw_address (ptr_addr p) lo mod al = 0 ->
  liveq dq' b reg -∗
  ▷ (liveq dq' b reg -∗ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (HalfCheck bd lo hi Read al) args :: rest) j)) : sexpr) {{ Φ }}.
Proof using Type.
  intros Hc Hx Hp1 Hp H1 H2 H3 H4 H5. apply (wp_read_dq registry (os_wi w0) ge dq' _ _ _ []).
  intros m fuel (Hf & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E Lv] _].
  apply rule_let with (classes := classes) (xs := [WPtr p1; WPtr p]); [reflexivity | exact Hc | exact Hx |].
  exact (op_half_check_read _ _ _ _ _ _ _ _ _ Hp1 Hp E Lv H1 H2 H3 H4 H5).
Qed.

(** The tactic [co_alloc] allocates one eight-byte local, which starts zeroed. *)
Local Ltac co_alloc b H L C :=
  iApply wp_alloc; [reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |]; iNext; iIntros (b H) "Hob";
  change (0 < b /\ b mod 16 = 0 /\ b + 16 <= 2^48) in H;
  iDestruct (obj_zero_block with "Hob") as "(Hobl & Hobb & Hoba)"; [vm_compute; congruence|];
  iDestruct (Mbrtowc.MbVL.zero_cell_prefix b 0 8 with "Hobb Hoba") as "(Hobc & _ & _)";
  iAssert (live b (mkRegion b (b + 16) Heap Live)) with "Hobl" as L; iRename "Hobc" into C.

(** The flush calls the conversion with a source of n wide characters
    and a destination of m bytes. The conversion reports how many
    characters the step consumed and how many bytes it produced, and it
    returns the descriptor with its new output bounds and flags. *)
Lemma wp_codecvt_out fr tm wd wreg ob oe fl cnt sb sreg dq sc so ws tb treg to xs nb nreg n0 tpb tpreg t0 Φ :
  let n := Z.of_nat (length ws) in let m := Z.of_nat (length xs) in
  call_frame glibc_codecvt_out [WPtr (mkPtr (wd + woff_cd_in) (Obj wd)); WPtr (mkPtr (wd + woff_state) (Obj wd));
    WPtr (mkPtr (sb + so) sc); WPtr (mkPtr (sb + so + 4 * n) sc); WPtr (mkPtr nb (Obj nb));
    WPtr (mkPtr (tb + to) (Obj tb)); WPtr (mkPtr (tb + to + m) (Obj tb)); WPtr (mkPtr tpb (Obj tpb))] = Some fr ->
  lookup (TAtom "glibc_wcsmbsload#to_mb") (ge_globals ge) = Some tm ->
  fl = 9 \/ fl = Z.lor 9 (2 ^ 30) ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 ->
  (sc = Obj sb \/ sc = Ro sb) -> 0 < sb -> 0 <= so -> sb + so + 4 * n <= r_end sreg -> r_end sreg <= 2 ^ 63 ->
  (sb = wd -> sreg = wreg) -> Forall (fun c => 0 <= c < 2 ^ 32) ws ->
  0 < tb -> 0 <= to -> tb + to + m <= r_end treg -> r_end treg <= 2 ^ 63 -> Forall (fun x => 0 <= x < 256) xs ->
  0 < nb -> nb mod 8 = 0 -> nb + 8 <= r_end nreg -> r_end nreg <= 2 ^ 63 ->
  0 < tpb -> tpb mod 8 = 0 -> tpb + 8 <= r_end tpreg -> r_end tpreg <= 2 ^ 63 ->
  wconv_ro -∗ wlocale dl -∗ live wd wreg -∗ iconv_cell wd woff_cd_out tm ob oe fl cnt -∗
  bytes wd woff_state (replicate 16 0) -∗ (if decide (sb = wd) then True else liveq dq sb sreg) -∗
  bytesq dq sb so (flat_map (fun c => le_bytes c 4) ws) -∗ live tb treg -∗ bytes tb to xs -∗
  live nb nreg -∗ pcell nb 0 n0 -∗ live tpb tpreg -∗ pcell tpb 0 t0 -∗
  ▷ (∀ k j zs res ob' oe' fl' cnt',
       ⌜0 <= k <= n /\ length zs = length xs /\ 0 <= j <= m /\ Forall (fun z => 0 <= z < 256) zs /\
        (res = 0 \/ res = 1 \/ res = 2) /\ (fl' = fl \/ fl' = Z.lor fl (2 ^ 30))⌝ -∗
     wlocale dl -∗ live wd wreg -∗ iconv_cell wd woff_cd_out tm ob' oe' fl' cnt' -∗
     bytes wd woff_state (replicate 16 0) -∗ (if decide (sb = wd) then True else liveq dq sb sreg) -∗
     bytesq dq sb so (flat_map (fun c => le_bytes c 4) ws) -∗ live tb treg -∗ bytes tb to zs -∗
     live nb nreg -∗ pcell nb 0 (mkPtr (sb + so + 4 * k) sc) -∗
     live tpb tpreg -∗ pcell tpb 0 (mkPtr (tb + to + j) (Obj tb)) -∗ Φ (Ret (WInt res))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros n m Hfr Htm Hfl Hwd Hwa Hwe Hwr Hsc Hsb Hso Hse Hsr Hsw Hws Htb Hto Hte Htr Hxs Hnb Hna Hne Hnr Htp Hta Htpe Htpr.
  rewrite Htmb in Htm. injection Htm as <-. injection Hfr as <-.
  iIntros "#Hro Hloc Hwl Hcd Hst Hsl Hsrc Htl Htx Hnl Hnc Htpl Htpc HK".
  iPoseProof (wconv_ro_consts with "Hro") as "(#Html & #Htm0 & #Htm40 & _)".
  iDestruct "Hcd" as (sd Hsd) "(C160 & C168 & C176 & C184 & C188 & C192 & C196 & C200 & C208)".
  unfold woff_cd_out, woff_state, woff_cd_in in *.
  step. co_alloc lb Hlb "Hlbl" "Hlbc". co_alloc pi Hpi "Hpil" "Hpic". step. check "Hwl".
  load_pointer_dq "Hwl C160 Html" by a2. iNext. iIntros "Hwl C160 _".
  check "Hpil". store "Hpil" "Hpic". step. check "Hwl". store "Hwl" "C168". step. check "Hwl". store "Hwl" "C176".
  step. check "Hwl". store "Hwl" "C200". step.
  check_read_dq "Html" by a2. iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Html Htm40 []"); [reflexivity | vx | right; reflexivity | a2 | a2 | a2 | done |].
  iNext. iIntros "_ _ _".
  iApply (wp_half_check_read_dq with "Html"); [reflexivity | vx | reflexivity | right; reflexivity | a2 | a2 | lia | a2 | a2 |].
  iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Html Htm0 []"); [reflexivity | vx | right; reflexivity | a2 | a2 | cbn; lia | done |].
  iNext. iIntros "_ _ _". do 3 step. branch. do 5 step.
  iApply wp_check_function; [vx | exact Hfct |]. iNext.
  iApply wp_raw_call_bind; [vx | reflexivity | exact Hfct | vx | exact Hia | reflexivity | reflexivity |]. iNext.
  cbn [ptr_addr ptr_cap].
  rewrite (Z.mod_small (wd + 104) (2^64)); [|lia]. rewrite (Z.mod_small 56 (2^64)); [|lia].
  rewrite (Z.mod_small (wd + 104 + 56) (2^64)); [|lia]. rewrite (Z.mod_small (wd + 104 + 56) (2^64)); [|lia].
  rewrite (Z.mod_small 8 (2^64)); [|lia]. rewrite (Z.mod_small (wd + 104 + 56 + 8) (2^64)); [|lia].
  rewrite (Z.mod_small 0 (2^64)); [|lia]. replace (wd + 104 + 56 + 8) with (wd + 168) by lia.
  iAssert (icell lb 0 0) with "[Hlbc]" as "Hlbc".
  { rewrite /pcell /icell /pts big_sepL_cons. iDestruct "Hlbc" as "[_ $]". }
  destruct Hpi as (? & ? & ?), Hlb as (? & ? & ?).
  iApply (Hlast _ wd wreg sb sreg dq sc so ws tb treg to xs fl cnt pi _ lb _ 0
    with "Hro Hloc Hwl C168 C176 C184 C188 Hsl [Hsrc] Htl Htx Hpil Hpic Hlbl Hlbc");
    try first [reflexivity | assumption | lia | (apply mod16_mod8; assumption) | (cbn; lia)].
  { done. }
  iNext. iIntros (st k j zs fl2 cnt2 c2 (Hk & Hj & Hzs & Hzv & Hfl2))
    "Hloc Hwl C168 C176 C184 C188 Hsl Hsrc Htl Htx Hpil Hpic Hlbl Hlbc".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  check "Hpil".
  iAssert (∃ dq3 reg3, live_capq dq3 sc reg3 ∗
    (live_capq dq3 sc reg3 -∗ live wd wreg ∗ (if decide (sb = wd) then True else liveq dq sb sreg)))%I
    with "[Hwl Hsl]" as (dq3 reg3) "[Hcap Hcapb]".
  { destruct (decide (sb = wd)) as [<-|Nw].
    - iExists (DfracOwn 1), wreg. destruct Hsc as [-> | ->]; cbn [live_capq]; iSplitL "Hwl";
        [iExact "Hwl" | iIntros "H"; iFrame "H"; done | iExact "Hwl" | iIntros "H"; iFrame "H"; done].
    - iExists dq, sreg. destruct Hsc as [-> | ->]; cbn [live_capq]; iFrame "Hwl"; iSplitL "Hsl";
        [iExact "Hsl" | iIntros "H"; iExact "H" | iExact "Hsl" | iIntros "H"; iExact "H"]. }
  load_pointer_dq "Hpil Hpic Hcap" by a2. iNext. iIntros "Hpil Hpic Hcap".
  iDestruct ("Hcapb" with "Hcap") as "[Hwl Hsl]". check "Hnl". store "Hnl" "Hnc".
  check "Hwl". load "Hwl" "C168" "Htl". check "Htpl". store "Htpl" "Htpc". step.
  all: repeat first [step | branch_cases].
  all: iApply wp_ret; [reflexivity | vx |]; iNext.
  all: iApply ("HK" $! k j zs _ (mkPtr (tb + to + j) (Obj tb)) (mkPtr (tb + to + m) (Obj tb)) fl2 cnt2
    with "[%] Hloc Hwl [C160 C168 C176 C184 C188 C192 C196 C200 C208] Hst Hsl [Hsrc] Htl Htx Hnl Hnc Htpl Htpc");
    [split_and!; try lia; try assumption; try tauto | iExists sd; iFrame; done | done].
  Unshelve. all: first [exact DfracDiscarded | exact wreg].
Qed.
End out.
