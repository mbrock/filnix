(** The formatter walks its format in the function
    `c: __printf_buffer`. The function copies the plain text of the
    format into a buffer, and for each conversion it takes one argument
    and appends its text. This module proves that the compiled function
    is safe for the formats that print only strings, and that it meets
    [printf_buffer_spec] of [PrintfSpec](PrintfSpec.v) for them. Such a
    format has plain text and the conversion `%s`.

    The function is a loop over the conversions of the format. A proof
    about a loop needs a statement that is true whenever a round
    starts, and here the statement has three parts. First, the buffer
    is usable. Second, the variable `c: f` points to a percent sign in
    the format, and the format from that sign on still parses. Third,
    the arguments that are left fit the conversions that are left.

    The compiled function has 376 basic blocks, because it handles
    every conversion that glibc knows. A format of plain text and `%s`
    reaches about 40 of them. The proof states what is true at four
    places in the function, and it follows the code between them. The
    four places are the function's entry, the start of a round, the
    code that prints the string of a `%s`, and the code that ends a
    conversion and copies the plain text after it. A lemma of the
    module [CBlocks](../CBlocks.v) turns the four statements, each with
    a proof of the code that follows it, into a proof about the whole
    function.

    The loop calls five other functions. Two of them append to the
    buffer. One tests whether the buffer has failed, one finds the
    next percent sign, and one is `c: strlen`. The proof assumes a
    contract for each of the five, which says what the function needs
    and what it gives back. *)

From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  VariadicLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv LibioLogic LibioDefaultXsputnBuf WordString StrchrnulLogic
  StrlenWord FxprintfStream NarrowFormat NarrowArgs DcigettextExit DcigettextPreRules
  FormatterCode FormatterSrc FormatterStringTable FormatterStringArg FormatterStringDispatch FormatterStringRead
  CFrame CStruct CBlocks PrintfLayout PrintfOut PrintfSpec PrintfCopy FormatterNames.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic StringVL.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Module S := FormatterSrc.fn___printf_buffer.

(** ## The temporaries at the four places *)

(** The compiler keeps the function's C variables in temporaries,
    which are the registers of the compiled code. About twenty
    variables are in use at each of the four places. Most of them
    belong to conversions that a format of plain text and `%s` never
    reaches, and the proof does not follow them. The list [loop_keys]
    names the variables that the proof does follow. The function
    [keep] takes a list of temporaries and drops every variable that
    is not in [loop_keys]. *)
Definition loop_keys : list string :=
  ["&f"; "buf"; "&work_buffer"; "ap"; "v55"; "grouping"; "thousands_sep"; "readonly_format"; "nspecs_done";
   "left"; "width"; "len"; "string"; "&null"].
Definition keep (sig : cut_sig) : cut_sig :=
  filter (fun '(_, (key, _)) => existsb (String.eqb key) loop_keys) sig.

(** At the entry the temporaries hold the function's four parameters. *)
Definition entry_sig : cut_sig := Eval vm_compute in cut_at S.temp_keys S.live_in "start".

(** Each round of the loop handles one conversion, and the compiled
    code starts a round at the block `L79`. The function comes to this
    block from the block `L67` before the first round, and from the
    block `L2128` after every round. The count of conversions and
    three other variables get their values on the way in. So the proof
    has one list of temporaries for each way in and one list for the
    rest of the block. *)
Definition head_from_entry : cut_sig :=
  Eval vm_compute in keep (cut_edge S.temp_keys S.live_in glibc_printf_buffer "L79" "L67").
Definition head_from_round : cut_sig :=
  Eval vm_compute in keep (cut_edge S.temp_keys S.live_in glibc_printf_buffer "L79" "L2128").
Definition head_body : cut_sig :=
  Eval vm_compute in keep (cut_body S.temp_keys S.live_in glibc_printf_buffer "L79" "L2128").

(** The block `L1831` prints the string of a `%s`. The function comes
    from the block `L1871` with the argument's string and its length,
    and from the block `L1836` with the constant `(null)`. *)
Definition print_from_len : cut_sig :=
  Eval vm_compute in keep (cut_edge S.temp_keys S.live_in glibc_printf_buffer "L1831" "L1871").
Definition print_from_null : cut_sig :=
  Eval vm_compute in keep (cut_edge S.temp_keys S.live_in glibc_printf_buffer "L1831" "L1836").
Definition print_body : cut_sig :=
  Eval vm_compute in keep (cut_body S.temp_keys S.live_in glibc_printf_buffer "L1831" "L1871").

(** The block `L1150` ends a conversion. The function comes from the
    block `L1887` when the string needed no padding, and from the block
    `L1901` otherwise. *)
Definition next_from_write : cut_sig :=
  Eval vm_compute in keep (cut_edge S.temp_keys S.live_in glibc_printf_buffer "L1150" "L1887").
Definition next_from_pad : cut_sig :=
  Eval vm_compute in keep (cut_edge S.temp_keys S.live_in glibc_printf_buffer "L1150" "L1901").
Definition next_body : cut_sig :=
  Eval vm_compute in keep (cut_body S.temp_keys S.live_in glibc_printf_buffer "L1150" "L1887").

(** ## Formats of plain text and `%s` *)

(** The proof follows the format one piece at a time, and it needs
    three facts about a format that parses. Each fact says what the
    bytes at the pointer `c: f` are and what is left to do after the
    function has passed them. *)

(** The function finds the next percent sign with a search, and it
    copies the bytes before that sign as plain text. Those bytes are
    the first directives of the format, and none of them takes an
    argument. So the format splits into that plain text a and a rest b.
    The rest is empty or starts with a percent sign. It parses to
    directives that the proof still covers, and the arguments that fit
    the whole format fit the rest. *)
Lemma lit_run (cover : narrow_directive -> Prop) tl ds :
  parse_narrow tl = Some ds -> Forall cover ds ->
  exists a b ds', tl = a ++ b /\ length a = chr_idx 37 tl /\ (b = [] \/ exists b', b = 37 :: b') /\
    parse_narrow b = Some ds' /\ Forall cover ds' /\
    (forall xs rest, narrow_fits ds xs rest -> narrow_fits ds' xs rest).
Proof.
  revert ds. induction tl as [|c r IH]; intros ds Hp Hc.
  { exists [], [], ds. cbn in *. split_and!; auto. }
  cbn [parse_narrow chr_idx] in *. destruct (c =? 37) eqn:E.
  { apply Z.eqb_eq in E as ->. exists [], (37 :: r), ds. split_and!; eauto. }
  destruct (literal_byte c) eqn:Hl; [|discriminate]. destruct (parse_narrow r) as [ds0|] eqn:Hr; [|discriminate].
  cbn in Hp. injection Hp as <-. apply List.Forall_cons_iff in Hc as [_ Hc].
  destruct (IH ds0 eq_refl Hc) as (a & b & ds' & -> & Hlen & Hb & Hpb & Hcb & Hfit).
  exists (c :: a), b, ds'. split_and!; auto; [cbn [length]; congruence|].
  intros xs rest (used & -> & Hargs). apply Hfit. exists used. split; [reflexivity|].
  inversion Hargs as [|? ? ? ? Hrest | |? ? ? ? Hd]; subst; [exact Hrest | inversion Hd].
Qed.

(** A format that starts with a percent sign and prints only strings
    starts with `%s`, and what follows the two bytes parses to the
    directives after that conversion. *)
Lemma str_conversion tl ds :
  parse_narrow (37 :: tl) = Some ds -> Forall lit_or_str ds ->
  exists tail ds0, tl = 115 :: tail /\ ds = FmtStr :: ds0 /\ parse_narrow tail = Some ds0 /\ Forall lit_or_str ds0.
Proof.
  cbn [parse_narrow]. change (37 =? 37) with true. cbv iota. destruct tl as [|letter tail]; [discriminate|].
  destruct (conversion letter) as [d|] eqn:Hd; [|discriminate].
  destruct (parse_narrow tail) as [ds0|] eqn:Ht; [|discriminate]. intros [= <-] Hc.
  apply List.Forall_cons_iff in Hc as [Hc Hc0]. exists tail, ds0. unfold conversion in Hd.
  destruct (Z.eqb_spec letter 115) as [->|_]; [injection Hd as <-; auto|].
  destruct (letter =? 99); [injection Hd as <-; destruct Hc|].
  destruct (letter =? 100); [injection Hd as <-; destruct Hc|].
  destruct (letter =? 37); [injection Hd as <-; destruct Hc | discriminate].
Qed.

(** The arguments that fit a format which starts with `%s` start with
    a pointer, and the arguments after it fit the rest of the
    format. *)
Lemma str_fits ds xs rest :
  narrow_fits (FmtStr :: ds) xs rest -> exists q xs', xs = WPtr q :: xs' /\ narrow_fits ds xs' rest.
Proof.
  intros (used & -> & Hargs). inversion Hargs as [| | |? ? ? used' Hd Hrest]; subst.
  inversion Hd; subst. eexists _, _. split; [reflexivity|]. exists used'. auto.
Qed.

(** The byte at an index of a list that is written as two parts is the
    first byte of the second part. *)
Lemma byte_after (pre tl : list Z) x :
  head (tl ++ [0]) = Some x -> ((pre ++ tl) ++ [0]) !! length pre = Some x.
Proof.
  intros H. rewrite -app_assoc lookup_app_r; [|lia]. rewrite Nat.sub_diag. destruct (tl ++ [0]); [discriminate|exact H].
Qed.

(** The arguments from an index on start with the argument at that
    index, and the arguments from the next index on follow it. *)
Lemma skipn_cons {A : Type} (i : nat) (xs : list A) x xs' :
  skipn i xs = x :: xs' -> xs !! i = Some x /\ skipn (S i) xs = xs' /\ (i < length xs)%nat.
Proof.
  revert xs. induction i as [|i IH]; intros [|y xs]; cbn [skipn]; try discriminate.
  - intros [= -> ->]. cbn. split_and!; [reflexivity..|lia].
  - intros H. destruct (IH xs H) as (H1 & H2 & H3). cbn [length]. split_and!; [exact H1 | exact H2 | lia].
Qed.

Section loop.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** ## Reading an argument *)

(** A variadic call copies its arguments into an object of their own,
    and a cursor points to the next argument in that copy. The
    predicate [va_at] owns the copy and the cursor. The conversion `%s`
    reads one pointer from the copy and moves the cursor to the
    argument after it. The rule for that step asks for three things:
    the cursor, the lifetime of the copy, and the cell that holds the
    pointer. The lemmas below take these three out of [va_at] and put
    them back. *)

(** Ownership of a list of pieces gives ownership of some of them, and
    it comes back when those are returned. The pieces taken must be
    distinct and must all occur in the list. *)
Lemma pts_take ps qs :
  base.NoDup qs -> (forall x, x ∈ qs -> x ∈ ps) -> pts ps ⊢ pts qs ∗ (pts qs -∗ pts ps).
Proof using Type.
  intros Hnd Hin. destruct (submseteq_Permutation qs ps (NoDup_submseteq _ _ Hnd Hin)) as [rest Hp].
  rewrite /pts Hp big_sepL_app. iIntros "[$ Hr] Hq". iFrame.
Qed.

(** The cell of an argument and the lifetime of the copy are distinct
    pieces. *)
Lemma arg_pieces_nodup sb sr o q :
  base.NoDup ((PLive sb, VLive sr) :: (PAux sb o, VAux (ptr_cap q)) :: cell sb o (ptr_addr q)).
Proof using Type.
  unfold cell. cbn [List.map]. repeat (apply list.NoDup_cons; split; [rewrite ?elem_of_cons elem_of_nil; intros H;
    repeat destruct H as [H|H]; try discriminate H; try (injection H; lia); exact H|]). apply base.NoDup_nil_2.
Qed.

(** These two notations name the region of the copy of the arguments
    xs at the address sb, and the region of the cursor at the address
    cb. *)
Local Notation snap_region xs sb := (mkRegion sb (sb + req_extent (fx_req xs)) (req_kind (fx_req xs)) Live).
Local Notation cursor_region cb := (mkRegion cb (cb + 32) Heap Live).

(** The lifetime of the copy is the first piece of the copy. *)
Lemma snap_live_in xs sb : (PLive sb, VLive (snap_region xs sb)) ∈ snapshot_ps xs sb (fx_req xs).
Proof using Type. unfold snapshot_ps, obj_ps. rewrite fmap_cons. apply elem_of_cons. left. reflexivity. Qed.

(** The cursor is an object with a lifetime and one cell, and the
    cell holds the pointer to the next argument. *)
Lemma va_cursor_own cb reg c : pts (va_cursor_ps cb reg c) ⊣⊢ live cb reg ∗ pcell cb 0 c.
Proof using Type. rewrite /live /pcell -pts_app. reflexivity. Qed.

(** The function's entry loads the pointer that the cursor holds. This
    lemma takes out of [va_at] what that load needs. The load needs
    the cursor's cell, which holds a pointer into the copy, and the
    lifetimes of the cursor and of the copy. The lemma also gives a way
    to put the three back. *)
Lemma va_at_cursor ap skip xs :
  va_at ap skip xs ⊢ ∃ cb sb,
    ⌜ap = mkPtr cb (Obj cb) /\ 0 < cb /\ cb mod 8 = 0 /\ cb + 32 <= 2 ^ 48 /\ 0 < sb /\ sb + skip <= 2 ^ 48 /\
     0 <= skip⌝ ∗
    live cb (cursor_region cb) ∗ pcell cb 0 (mkPtr (sb + skip) (Ro sb)) ∗ live sb (snap_region xs sb) ∗
    (live cb (cursor_region cb) -∗ pcell cb 0 (mkPtr (sb + skip) (Ro sb)) -∗ live sb (snap_region xs sb) -∗
     va_at ap skip xs).
Proof using Type.
  iIntros "(%cb & %sb & (-> & %Hcb & %Hc8 & %Hce & %Hsb & %Hs16 & %Hend & %Hskip) & Hcur & Hsnap)".
  pose proof (heap_req_extent 16 (8 * Z.of_nat (length xs))) as Hext. unfold fx_req in Hend.
  iDestruct (pts_take _ [(PLive sb, VLive (snap_region xs sb))] with "Hsnap") as "[Hsl Hback]";
    [apply list.NoDup_singleton | intros x ->%list_elem_of_singleton; apply snap_live_in|].
  iExists cb, sb. iSplit; [iPureIntro; split_and!; [reflexivity | first [assumption | lia]..]|].
  rewrite va_cursor_own. iDestruct "Hcur" as "[Hcl Hcc]". iFrame "Hcl Hcc Hsl".
  iIntros "Hcl Hcc Hsl". iExists cb, sb. iSplit; [iPureIntro; split_and!; [reflexivity | first [assumption | lia]..]|].
  rewrite va_cursor_own. iFrame "Hcl Hcc". iApply ("Hback" with "Hsl").
Qed.

(** The predicate [va_at] gives the parts that the rule for reading a
    pointer argument asks for. The cursor stands at the argument with
    the index i, which is the pointer q. The parts come back with the
    cursor at the next argument. *)
Lemma va_at_arg ap (i : nat) xs q :
  xs !! i = Some (WPtr q) ->
  va_at ap (8 * Z.of_nat i) xs ⊢ ∃ cb sb,
    ⌜ap = mkPtr cb (Obj cb) /\ 0 < cb /\ cb mod 8 = 0 /\ cb + 32 <= 2 ^ 48 /\ 0 < sb /\ sb mod 8 = 0 /\
     sb + 8 * Z.of_nat i + 8 <= sb + req_extent (fx_req xs) /\ sb + req_extent (fx_req xs) <= 2 ^ 48⌝ ∗
    pts (va_cursor_ps cb (cursor_region cb) (mkPtr (sb + 8 * Z.of_nat i) (Ro sb))) ∗
    live sb (snap_region xs sb) ∗ pcell sb (8 * Z.of_nat i) q ∗
    (pts (va_cursor_ps cb (cursor_region cb) (mkPtr (sb + 8 * Z.of_nat i + 8) (Ro sb))) -∗
     live sb (snap_region xs sb) -∗ pcell sb (8 * Z.of_nat i) q -∗ va_at ap (8 * Z.of_nat (S i)) xs).
Proof using Type.
  intros Hi. pose proof (lookup_lt_Some _ _ _ Hi) as Hlt.
  iIntros "(%cb & %sb & (-> & %Hcb & %Hc8 & %Hce & %Hsb & %Hs16 & %Hend & %Hskip) & Hcur & Hsnap)".
  pose proof (heap_req_extent 16 (8 * Z.of_nat (length xs))) as Hext. fold (fx_req xs) in Hext.
  iDestruct (pts_take _ ((PLive sb, VLive (snap_region xs sb)) :: (PAux sb (8 * Z.of_nat i), VAux (ptr_cap q)) ::
      cell sb (8 * Z.of_nat i) (ptr_addr q)) with "Hsnap") as "[Hq Hback]"; [apply arg_pieces_nodup| |].
  { intros [l v] [[= -> ->]|Hin]%elem_of_cons; [apply snap_live_in|].
    apply (snapshot_ps_pointer xs i q sb (fx_req xs) Hi); [lia | exact Hin]. }
  iExists cb, sb. iSplit; [iPureIntro; split_and!; [reflexivity | first [assumption | lia | Z.div_mod_to_equations; lia]..]|].
  iFrame "Hcur". rewrite /live /pcell (pts_app [_]). iDestruct "Hq" as "[$ $]".
  iIntros "Hcur Hsl Hc". iExists cb, sb. iSplit; [iPureIntro; split_and!; [reflexivity | first [assumption | lia]..]|].
  replace (8 * Z.of_nat (S i)) with (8 * Z.of_nat i + 8) by lia. rewrite Z.add_assoc. iFrame "Hcur".
  iApply "Hback". rewrite (pts_app [_]). iFrame "Hsl Hc".
Qed.

(** The loop keeps what it knows about the arguments across its
    rounds, because that knowledge is only read-only strings. *)
#[global] Instance str_arg_persistent x : Persistent (str_arg x).
Proof using Type. destruct x; rewrite /str_arg; apply _. Qed.

(** A string argument is the null pointer or the start of a string
    that anyone may read. *)
Lemma str_arg_string q :
  str_arg (WPtr q) ⊢ ⌜q = null⌝ ∨ ∃ s, word_string DfracDiscarded q s.
Proof using Type.
  iIntros "[%Hq | (%p & %s & %j & [-> %Hj] & Hs)]"; [iLeft; done|]. iRight. iExists (drop j s).
  rewrite -{1}(take_drop j s). iDestruct (word_string_suffix with "Hs") as "Hs". rewrite length_take_le; [|exact Hj].
  iExact "Hs".
Qed.

(** ## Reading the format *)

(** The variable `c: f` is a pointer into the format, and the function
    keeps it in a cell on the heap. The function loads it from the
    cell and reads the byte that it points to. Both steps need the
    lifetime of the format's object, which the string owns. The lemmas
    below take what a step needs out of the string and put it back. *)

(** A string starts above the address 0 and ends below the end of the
    address space of a Fil-C program. *)
Lemma word_string_range dq p s :
  word_string dq p s ⊢ ⌜0 < ptr_addr p /\ ptr_addr p + Z.of_nat (length s) < 2 ^ 48⌝.
Proof using Type.
  iIntros "(%b & %reg & %ws & %Hs & _)". iPureIntro.
  destruct Hs as [Hc Hb0 Hb8 Hst Hf Hsp Hlen Hws Hby Hch]. unfold wstart in Hf.
  pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)). lia.
Qed.

(** A cell holds a pointer into a string, at the index i. Loading the
    pointer from the cell keeps the cell and the string. *)
Lemma wp_load_fmt f e ls l d off args rest j classes p fb freg o dq q s i Φ :
  op_arg_classes (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) P = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj fb -> raw_address (ptr_addr p) off = fb + o -> (fb + o) mod 8 = 0 ->
  0 <= i <= Z.of_nat (length s) ->
  live fb freg -∗ pcell fb o (ptr_add q i) -∗ word_string dq q s -∗
  ▷ (live fb freg -∗ pcell fb o (ptr_add q i) -∗ word_string dq q s -∗
     WP (ERun (mkFrame f (put d (WPtr (ptr_add q i)) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
        (Exec l (Let d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) args :: rest) j)) : sexpr) {{ Φ }}.
Proof using Type.
  intros Hc Hx Hp Ha Hal Hi. iIntros "Hl Hc Hs HK". iDestruct (word_string_range with "Hs") as %Hr.
  iDestruct "Hs" as (b reg ws) "(%Hs & Hsl & Hw)". pose proof (ss_cap _ _ _ _ _ Hs) as Hcap.
  iAssert (live_capq dq (ptr_cap (ptr_add q i)) reg) with "[Hsl]" as "Hsl".
  { cbn [ptr_add ptr_cap]. destruct Hcap as [-> | ->]; iExact "Hsl". }
  iApply (wp_raw_load_pointer_dq with "Hl Hc Hsl"); [exact Hc | exact Hx | left; exact Hp | exact Ha | exact Hal | cbn; lia |].
  iNext. iIntros "Hl Hc Hsl". iApply ("HK" with "Hl Hc"). iExists b, reg, ws. iSplit; [done|]. iFrame "Hw".
  cbn [ptr_add ptr_cap]. destruct Hcap as [-> | ->]; iExact "Hsl".
Qed.

End loop.

(** The tactic [load_fmt] loads the pointer `c: f` from its cell. Hl
    names the cell's lifetime, Hc the cell and Hs the string that the
    pointer points into. *)
Ltac load_fmt Hl Hc Hs :=
  iRevert Hs; iRevert Hc; iRevert Hl;
  eapply step_res3; [eapply wp_load_fmt; inst; [reflexivity | vx | reflexivity | a2 | a2 | lia] |];
  iIntros Hl; iIntros Hc; iIntros Hs.

(** The tactic [read_byte] runs the check and the load that read one
    byte of the string in the hypothesis Hs. The byte is at the index
    i and has the value x, and H proves that. *)
Ltac read_byte Hs i x H :=
  let b := fresh "rb" in let r := fresh "rr" in let Fc := fresh "Hrc" in let Fr := fresh "Hrr" in
  iDestruct (word_string_at _ _ _ i x H with Hs) as (b r) "(HF & Hsl & Hsx & Hback)";
  iDestruct "HF" as %[Fc Fr];
  check_read_dq "Hsl" by (cbn [ptr_add ptr_addr ptr_cap] in *; unfold raw_address; rewrite ?Z.add_0_r; unwrap2; lia);
  iNext; iIntros "Hsl";
  load_bytes_dq "Hsl Hsx" decode (reflexivity)
    by (cbn [ptr_add ptr_addr ptr_cap] in *; unfold raw_address; rewrite ?Z.add_0_r; unwrap2; lia);
  iNext; iIntros "Hsl Hsx"; iDestruct ("Hback" with "Hsl Hsx") as Hs; clear Fc Fr.

Section table.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (k : Z) (R : Z * region * Z * Z -> iProp Σ).
Context `{!Callees [(TAtom "__printf_buffer_write", write_spec k R);
                    (TAtom "glibc_vfprintf_internal#__printf_buffer_has_failed", has_failed_spec k R);
                    (TAtom "glibc_vfprintf_internal#__find_specmb.gnu_inline", find_spec_spec);
                    (TAtom "__GI_strlen", strlen_spec);
                    (TAtom "glibc_vfprintf_internal#__printf_buffer_pad", pad_spec k R)] }.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** ## The block table *)

(** The record [pl_in] is the logical input of a place inside the
    loop. It names the input of the call, the cell of the variable
    `c: f` and the work buffer. It splits the format's bytes into the
    bytes before the pointer `c: f` and the bytes from it on. It names
    the directives that are still to run, the number of arguments
    already read and the count of conversions done. *)
Record pl_in : Type := PlIn {
  pl_x : pb_in;
  pl_fb : Z; pl_wb : Z;
  pl_pre : list Z; pl_tl : list Z;
  pl_ds : list narrow_directive;
  pl_i : nat;
  pl_n : Z
}.

(** The function [pl_vals] lists the variables that the loop keeps in
    temporaries, each with its value. Three of them never change on
    the path that the proof follows: no thousands separator is in use,
    and the format is not known to be read-only. *)
Definition pl_vals (y : pl_in) : list (string * word) :=
  [("&f", WPtr (mkPtr (pl_fb y) (Obj (pl_fb y))));
   ("buf", WPtr (mkPtr (pb_buf (pl_x y)) (Obj (pb_buf (pl_x y)))));
   ("&work_buffer", WPtr (mkPtr (pl_wb y) (Obj (pl_wb y))));
   ("ap", WPtr (pb_ap (pl_x y)));
   ("v55", WInt 0);
   ("grouping", WPtr (mkPtr (2 ^ 64 - 1) CNone));
   ("thousands_sep", WPtr null);
   ("readonly_format", WInt 0);
   ("nspecs_done", WInt (pl_n y))].

(** The two parts make up the format. The directives left to run
    print only strings, and the arguments that are left fit them. The
    cell of `c: f` is an 8-aligned heap object. *)
Definition pl_ok (y : pl_in) : Prop :=
  pb_bytes (pl_x y) = pl_pre y ++ pl_tl y /\ Forall lit_or_str (pl_ds y) /\
  narrow_fits (pl_ds y) (skipn (pl_i y) (pb_xs (pl_x y))) (pb_rest (pl_x y)) /\
  0 < pl_fb y /\ pl_fb y mod 8 = 0 /\ pl_fb y + 16 <= 2 ^ 48 /\ 0 <= pl_n y < 2 ^ 32.

(** Inside the loop the function owns everything that its caller
    lent. It also owns the cell of the variable `c: f`, and that cell
    holds a pointer to the second part of the format. The argument
    cursor points to the next argument that a conversion will read. *)
Definition pl_own (y : pl_in) : iProp Σ :=
  printf_out k R (pb_buf (pl_x y)) ∗
  word_string (pb_dq (pl_x y)) (pb_fmt (pl_x y)) (pb_bytes (pl_x y)) ∗
  live (pl_fb y) (mkRegion (pl_fb y) (pl_fb y + 16) Heap Live) ∗
  pcell (pl_fb y) 0 (ptr_add (pb_fmt (pl_x y)) (Z.of_nat (length (pl_pre y)))) ∗
  va_at (pb_ap (pl_x y)) (8 * Z.of_nat (pl_i y)) (pb_xs (pl_x y)) ∗
  ([∗ list] a ∈ skipn (pl_i y) (pb_xs (pl_x y)), str_arg a) ∗
  errno_any (pb_eb (pl_x y)) ∗ printf_ro.

(** A round starts with `c: f` at a percent sign, and the format from
    there on parses to the directives left to run. *)
Definition head_pre (y : pl_in) : iProp Σ :=
  (⌜pl_ok y /\ head (pl_tl y) = Some 37 /\ parse_narrow (pl_tl y) = Some (pl_ds y)⌝ ∗ pl_own y)%I.

(** The function has done no conversion before the first round. The
    compiled code sets the count of conversions to zero on that way
    into the block `L79`, so the row for that way in asks that the
    count is zero. *)
Definition head_entry_pre (y : pl_in) : iProp Σ := (⌜pl_n y = 0⌝ ∗ head_pre y)%I.

(** A conversion ends with `c: f` at its last byte, and the format
    after that byte parses to the directives left to run. *)
Definition next_pre (y : pl_in) : iProp Σ :=
  (⌜pl_ok y /\ pl_tl y <> [] /\ parse_narrow (tail (pl_tl y)) = Some (pl_ds y)⌝ ∗ pl_own y)%I.

(** The record [pp_in] adds the string that a `%s` prints to the
    input of a place. *)
Record pp_in : Type := PpIn { pp_in_ : pl_in; pp_str : ptr; pp_text : list Z }.

(** The block that prints has the string and its length in
    temporaries. The conversion has no width and no flag. *)
Definition pp_vals (z : pp_in) : list (string * word) :=
  pl_vals (pp_in_ z) ++
  [("left", WInt 0); ("width", WInt 0); ("len", WInt (Z.of_nat (length (pp_text z)))); ("string", WPtr (pp_str z));
   ("&null", WPtr (pp_str z))].

(** The string is one that anyone may read. *)
Definition print_pre (z : pp_in) : iProp Σ :=
  (next_pre (pp_in_ z) ∗ word_string DfracDiscarded (pp_str z) (pp_text z))%I.

(** A null argument prints the constant `(null)`. The compiled code
    sets the length to six on the way in from the block `L1836`, so
    the row for that way in asks that the text is this constant. *)
Definition print_null_pre (z : pp_in) : iProp Σ := (⌜pp_text z = null_text_bytes⌝ ∗ print_pre z)%I.

(** The function returns nothing and gives back what its caller
    lent. *)
Definition pl_post (y : pl_in) : outcome -> iProp Σ := fs_post (printf_buffer_spec lit_or_str k R) (pl_x y).

(** At the entry the temporaries hold the parameters. *)
Definition entry_vals (x : pb_in) : list (string * word) :=
  [("buf", WPtr (mkPtr (pb_buf x) (Obj (pb_buf x)))); ("format", WPtr (pb_fmt x)); ("ap", WPtr (pb_ap x));
   ("mode_flags", WInt 0)].

(** The table has a row for the entry and two rows for each of the
    three places inside the loop, one for each way in. *)
Definition loop_blocks : list bspec :=
  [BSpec "start" None entry_sig pb_in entry_vals (fs_pre (printf_buffer_spec lit_or_str k R))
     (fs_post (printf_buffer_spec lit_or_str k R));
   BSpec "L79" (Some "L67") head_from_entry pl_in pl_vals head_entry_pre pl_post;
   BSpec "L79" (Some "L2128") head_from_round pl_in pl_vals head_pre pl_post;
   BSpec "L1831" (Some "L1871") print_from_len pp_in pp_vals print_pre (fun z => pl_post (pp_in_ z));
   BSpec "L1831" (Some "L1836") print_from_null pp_in pp_vals print_null_pre (fun z => pl_post (pp_in_ z));
   BSpec "L1150" (Some "L1887") next_from_write pl_in pl_vals next_pre pl_post;
   BSpec "L1150" (Some "L1901") next_from_pad pl_in pl_vals next_pre pl_post].

(** ## The blocks *)

(** The function allocates its local variables on the heap when it
    starts. The tactic [alloc_keep] runs one allocation and names the
    new object, and the tactic [alloc_drop] runs one whose object the
    proof never uses. *)
Local Ltac alloc_keep b H :=
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |];
  iNext; iIntros (b H) "Hobj".
Local Ltac alloc_drop :=
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |];
  iNext; iIntros (? _) "_".

(** The tactic [row_simpl] unfolds a row's statement into the facts
    and the ownership that it stands for. *)
Local Ltac row_simpl :=
  cbn [bs_sig bs_vals bs_pre bs_post bs_label] in *;
  unfold head_entry_pre, print_null_pre, print_pre, head_pre, next_pre, pl_post, pl_own, pl_ok, pl_vals, pp_vals,
    entry_vals in *;
  cbn [app fs_pre fs_post printf_buffer_spec pp_in_ pp_str pp_text pl_x pl_fb pl_wb pl_pre pl_tl pl_ds pl_i pl_n
       pb_buf pb_fmt pb_dq pb_bytes pb_ds pb_ap pb_skip pb_xs pb_rest pb_eb ptr_addr ptr_cap] in *.

(** Every block of the function meets its row. *)
Lemma loop_table : ⊢ blocks_hold glibc_printf_buffer loop_blocks.
Proof using Type*.
  apply blocks_close. iIntros "#IH".
  iAssert (body_triple glibc_printf_buffer "L79" head_body pl_in pl_vals head_pre pl_post) as "#Hhead".
  { iModIntro. iIntros ([[bb [fa fc] dq bytes ds0 ap skip xs rest eb] fb wb pre tl ds i n] e Φ) "%He H HK".
    row_simpl. c_env_open He.
    iDestruct "H" as "(((%Hbytes & %Hcov & %Hfit & %Hfb & %Hf8 & %Hfe & %Hn) & %Hhd & %Hp) & Hout & Hs & Hfl & Hfc & Hva & #Hargs & Herrno & #Hro)".
    destruct tl as [|c tl]; [discriminate|]. injection Hhd as ->.
    destruct (str_conversion tl ds Hp Hcov) as (tail & ds1 & -> & -> & Hptail & Hcov1).
    destruct (str_fits _ _ _ Hfit) as (q & args & Hargs_eq & Hfit1).
    destruct (skipn_cons _ _ _ _ Hargs_eq) as (Hxi & Hskip1 & Hilt).
    iDestruct (word_string_range with "Hs") as %Hfr. cbn [ptr_addr] in Hfr.
    assert (Hlen : length bytes = (length pre + S (S (length tail)))%nat) by (rewrite Hbytes length_app; reflexivity).
    body_start glibc_printf_buffer "L79". step. check "Hfl". load_fmt "Hfl" "Hfc" "Hs". step. check "Hfl". store "Hfl" "Hfc".
    assert (Hx : (bytes ++ [0]) !! S (length pre) = Some 115).
    { rewrite Hbytes -app_assoc lookup_app_r; [|lia]. replace (S (length pre) - length pre)%nat with 1%nat by lia. reflexivity. }
    cbn [ptr_add ptr_addr ptr_cap]. unwrap2. read_byte "Hs" (S (length pre)) 115 Hx. step. step. branch.
    step. step. step. step. branch.
    (* The byte `s` selects its handler through the two dispatch tables. *)
    iPoseProof "Hro" as "(Hjt & Hst & _ & Hnt & _)".
    iDestruct "Hjt" as (jb jr) "((%Hjg & %Hjb & %Hje & %Hjr) & Hjl & Hjbs)".
    iDestruct "Hst" as (tb tr) "((%Htg & %Htb & %Hte & %Htr) & Htl & Htbs)".
    change (Z.of_nat (length (table_bytes jump_table))) with 91 in Hje.
    change (Z.of_nat (length (table_bytes step0_jumps))) with 128 in Hte.
    iDestruct (bytesq_sub _ _ _ _ 83 1 with "Hjbs") as "[Hj83 _]"; [vm_compute; lia|].
    iDestruct (bytesq_sub _ _ _ _ 84 4 with "Htbs") as "[Ht84 _]"; [vm_compute; lia|].
    change (take 1 (drop 83 (table_bytes jump_table))) with [21]. change (take 4 (drop 84 (table_bytes step0_jumps))) with ([21; 0; 0; 0]).
    change (0 + Z.of_nat 83) with 83. change (0 + Z.of_nat 84) with 84.
    iApply (wp_formatter_string_table with "Hjl Hj83 Htl Ht84"); [lk_prove | exact Hjg | exact Htg | lia..|].
    iNext. iIntros "_ _ _ _".
    iApply (wp_formatter_string_dispatch _ _ (mkPtr (2 ^ 64 - 1) CNone) null);
      [unfold string_table_env; cbn [fold_left fst snd]; lk_prove..|]. iNext.
    (* The conversion reads its argument, which is the null pointer or a string. *)
    iEval (rewrite Hargs_eq big_sepL_cons) in "Hargs". iDestruct "Hargs" as "[Hq Hargs1]". rewrite -Hskip1.
    iDestruct (va_at_arg _ i xs q Hxi with "Hva")
      as (cb sb) "((-> & %Hcb & %Hc8 & %Hce & %Hsb & %Hs8 & %Hse & %Hsr) & Hcur & Hsl & Hqc & Hvback)".
    iDestruct (str_arg_string with "Hq") as "[-> | (%s & #Hqs)]".
    { iApply (wp_formatter_string_arg _ _ _ cb _ sb _ (8 * Z.of_nat i) null [] with "Hcur Hsl Hqc []");
        [unfold string_dispatch_env, string_table_env; cbn [fold_left fst snd]; lk_prove | assumption | assumption | lia |
         cbn [r_end]; lia | cbn [r_end]; lia | Z.div_mod_to_equations; lia | cbn; lia | left; reflexivity |
         by rewrite /pts big_sepL_nil |].
      iNext. iIntros "Hcur Hsl Hqc _". iDestruct ("Hvback" with "Hcur Hsl Hqc") as "Hva".
      unfold string_dispatch_env, string_table_env; cbn [fold_left fst snd]. step. step. step. branch.
      (* A null argument prints the constant `(null)`. *)
      step. step. branch. step. branch. iDestruct "Hnt" as (nb) "[%Hng Hns]". unfold null_text in Hng.
      step. step_global Hng.
      step.
      goto_block "IH" "HK" 4%nat
        with (PpIn (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 (mkPtr cb (Obj cb)) skip xs rest eb) fb wb (pre ++ [37])
                      (115 :: tail) ds1 (S i) n) (mkPtr nb (Ro nb)) null_text_bytes).
      row_simpl.
      rewrite length_app Nat2Z.inj_add Hskip1. cbn [length Z.of_nat Pos.of_succ_nat].
      iFrame "Hout Hs Hfl Hva Hargs1 Herrno Hro Hns". iSplit; [done|]. iSplit; [iPureIntro|].
      { split_and!; [by rewrite Hbytes -app_assoc | exact Hcov1 | exact Hfit1 | lia..| discriminate | exact Hptail]. }
      unfold ptr_add; cbn [ptr_addr ptr_cap].
      replace (fa + (Z.of_nat (length pre) + Z.of_nat 1)) with (fa + Z.of_nat (length pre) + 1) by lia. iFrame "Hfc". }
    (* Any other argument is a string, and the function measures it. *)
    iDestruct (word_string_range with "Hqs") as %Hqr.
    iApply (wp_formatter_string_arg_word _ _ _ cb _ sb _ (8 * Z.of_nat i) q DfracDiscarded s with "Hcur Hsl Hqc Hqs");
      [unfold string_dispatch_env, string_table_env; cbn [fold_left fst snd]; lk_prove | assumption | assumption | lia |
       cbn [r_end]; lia | cbn [r_end]; lia | Z.div_mod_to_equations; lia | lia |].
    iNext. iIntros "Hcur Hsl Hqc _". iDestruct ("Hvback" with "Hcur Hsl Hqc") as "Hva".
    unfold string_dispatch_env, string_table_env; cbn [fold_left fst snd]. step. step. step.
    replace (ptr_addr q mod 2 ^ 64 =? 0 mod 2 ^ 64) with false
      by (symmetry; apply Z.eqb_neq; change (0 mod 2 ^ 64) with 0; rewrite Z.mod_small; lia).
    branch. step. step. branch. step. step. step. step. step. branch. step. step. branch. step.
    call_callee with (DfracDiscarded, q, s) giving ""; [iExact "Hqs"|]. iDestruct "Hpost" as "[-> _]". block_resume.
    step. step. step. rewrite !(Z.mod_small (Z.of_nat (length s))); [|lia..]. cbn [edge_label].
    goto_block "IH" "HK" 3%nat
      with (PpIn (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 (mkPtr cb (Obj cb)) skip xs rest eb) fb wb (pre ++ [37])
                    (115 :: tail) ds1 (S i) n) q s).
    row_simpl. rewrite length_app Nat2Z.inj_add Hskip1. cbn [length Z.of_nat Pos.of_succ_nat].
    iFrame "Hout Hs Hfl Hva Hargs1 Herrno Hro Hqs". iSplit; [iPureIntro|].
    { split_and!; [by rewrite Hbytes -app_assoc | exact Hcov1 | exact Hfit1 | lia..| discriminate | exact Hptail]. }
    unfold ptr_add; cbn [ptr_addr ptr_cap].
    replace (fa + (Z.of_nat (length pre) + Z.of_nat 1)) with (fa + Z.of_nat (length pre) + 1) by lia. iFrame "Hfc". }
  (* L1831: the block prints the string, after padding that a conversion with no width never needs. *)
  iAssert (body_triple glibc_printf_buffer "L1831" print_body pp_in pp_vals print_pre (fun z => pl_post (pp_in_ z)))
    as "#Hprint".
  { iModIntro.
    iIntros ([[[bb [fa fc] dq bytes ds0 ap skip xs rest eb] fb wb pre tl ds i n] str text] e Φ) "%He H HK".
    row_simpl. c_env_open He. iDestruct "H" as "((%Hok & Hout & Hown) & #Hstr)".
    iDestruct (word_string_range with "Hstr") as %Htr.
    body_start glibc_printf_buffer "L1831". step. step. step. branch_eqn E.
    - (* The string is empty or huge: the function pads with the difference, then writes the string. *)
      clear E. step. step. branch. step. step. step.
      call_callee with (bb, 32, _) giving "Hout"; [iFrame "Hout"; iPureIntro; split; [lia | apply Z.mod_pos_bound; lia]|].
      iDestruct "Hpost" as "(-> & Hout)". block_resume. step. step.
      call_callee with (bb, DfracDiscarded, str, text, _) giving "Hout"; [iFrame "Hout Hstr"; iPureIntro; unwrap2; lia|].
      iDestruct "Hpost" as "(-> & Hout & _)". block_resume. branch.
      goto_block "IH" "HK" 6%nat
        with (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 ap skip xs rest eb) fb wb pre tl ds i n).
      row_simpl. iFrame "Hout Hown". done.
    - (* Otherwise the function writes the string at once. *)
      clear E. step.
      call_callee with (bb, DfracDiscarded, str, text, _) giving "Hout"; [iFrame "Hout Hstr"; iPureIntro; unwrap2; lia|].
      iDestruct "Hpost" as "(-> & Hout & _)". block_resume. step.
      goto_block "IH" "HK" 5%nat
        with (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 ap skip xs rest eb) fb wb pre tl ds i n).
      row_simpl. iFrame "Hout Hown". done. }
  (* L1150: the block ends a conversion. It counts the conversion, steps over its last byte, writes the plain
     text up to the next percent sign, and then starts another round or returns at the end of the format. *)
  iAssert (body_triple glibc_printf_buffer "L1150" next_body pl_in pl_vals next_pre pl_post) as "#Hnext".
  { iModIntro. iIntros ([[bb [fa fc] dq bytes ds0 ap skip xs rest eb] fb wb pre tl ds i n] e Φ) "%He H HK".
    row_simpl. c_env_open He.
    iDestruct "H" as "(((%Hbytes & %Hcov & %Hfit & %Hfb & %Hf8 & %Hfe & %Hn) & %Hne & %Hp) & Hout & Hs & Hfl & Hfc & Hva & #Hargs & Herrno & #Hro)".
    destruct tl as [|c tl]; [done|]. cbn [tail] in Hp. clear Hne.
    iDestruct (word_string_range with "Hs") as %Hfr. cbn [ptr_addr] in Hfr.
    assert (Hlen : length bytes = (length pre + S (length tl))%nat) by (rewrite Hbytes length_app; reflexivity).
    body_start glibc_printf_buffer "L1150". step. check "Hfl". load_fmt "Hfl" "Hfc" "Hs". step. check "Hfl". store "Hfl" "Hfc".
    cbn [ptr_add ptr_addr ptr_cap]. unwrap2.
    (* The rest of the format, after the conversion's last byte, is a string of its own for the search. *)
    assert (Hsplit : bytes = (pre ++ [c]) ++ tl) by (rewrite Hbytes -app_assoc; reflexivity).
    iEval (rewrite Hsplit) in "Hs". iDestruct (word_string_borrow_any with "Hs") as (dq') "[Hsuf Hsback]".
    rewrite length_app Nat2Z.inj_add. unfold ptr_add; cbn [ptr_addr ptr_cap length].
    replace (fa + (Z.of_nat (length pre) + Z.of_nat 1)) with (fa + Z.of_nat (length pre) + 1) by lia.
    pose proof (chr_idx_le 37 tl) as Hidx.
    iDestruct (word_string_range with "Hsuf") as %Hsr. cbn [ptr_addr] in Hsr.
    call_callee with (dq', mkPtr (fa + Z.of_nat (length pre) + 1) fc, tl) giving "Hsuf"; [iExact "Hsuf"|].
    iDestruct "Hpost" as "[-> Hsuf]". block_resume.
    check "Hfl". store "Hfl" "Hfc". check "Hfl". load_fmt "Hfl" "Hfc" "Hsuf". step. step. step.
    call_callee with (bb, dq', mkPtr (fa + Z.of_nat (length pre) + 1) fc, tl, _) giving "Hout Hsuf";
      [iFrame "Hout Hsuf"; iPureIntro; unwrap2; lia|].
    iDestruct "Hpost" as "(-> & Hout & Hsuf)". block_resume.
    check "Hfl". load_fmt "Hfl" "Hfc" "Hsuf".
    destruct (lit_run lit_or_str tl ds Hp Hcov) as (lit & tl2 & ds' & Htl & Hlit & Htl2 & Hptl & Hcov' & Hfit').
    destruct Htl2 as [-> | [tl' ->]].
    { (* The format ends here, and the function returns. *)
      assert (Hx : (tl ++ [0]) !! chr_idx 37 tl = Some 0) by (rewrite -Hlit Htl; apply byte_after; reflexivity).
      read_byte "Hsuf" (chr_idx 37 tl) 0 Hx. iDestruct ("Hsback" with "Hsuf") as "Hs". rewrite -Hsplit.
      step. branch. step. branch. step. iApply wp_ret_void. iNext. iApply "HK". iFrame "Hout Hs Herrno". done. }
    assert (Hx : (tl ++ [0]) !! chr_idx 37 tl = Some 37) by (rewrite -Hlit Htl; apply byte_after; reflexivity).
    read_byte "Hsuf" (chr_idx 37 tl) 37 Hx. iDestruct ("Hsback" with "Hsuf") as "Hs". rewrite -Hsplit.
    step. branch. step.
    call_callee with bb giving "Hout"; [iExact "Hout"|]. iDestruct "Hpost" as (b) "((-> & %Hb) & Hout)". block_resume.
    step. step. step. step. branch_eqn E.
    { clear E. step. iApply wp_ret_void. iNext. iApply "HK". iFrame "Hout Hs Herrno". done. }
    clear E.
    goto_block "IH" "HK" 2%nat
      with (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds0 ap skip xs rest eb) fb wb (pre ++ c :: lit) (37 :: tl') ds' i
              ((n + 1) mod 2 ^ 32)).
    row_simpl. iFrame "Hout Hs Hfl Hva Hargs Herrno Hro". iSplit; [iPureIntro|].
    { pose proof (Z.mod_pos_bound (n + 1) (2 ^ 32) ltac:(lia)).
      split_and!; [rewrite Hbytes Htl -app_assoc; reflexivity | exact Hcov' | exact (Hfit' _ _ Hfit) | lia..|
                   reflexivity | exact Hptl]. }
    rewrite length_app. cbn [length]. unfold ptr_add; cbn [ptr_addr ptr_cap].
    replace (fa + Z.of_nat (length pre + S (length lit))) with (fa + Z.of_nat (length pre) + 1 + Z.of_nat (chr_idx 37 tl))
      by lia.
    iFrame "Hfc". }
  repeat iSplit; [| | | | | | | done]; iModIntro.
  - (* start *)
    iIntros ([bb [fa fc] dq bytes ds ap skip xs rest eb] e from Φ) "_ %He H HK". row_simpl. c_env_open He.
    iDestruct "H" as "((%Hp & %Hcov & %Hfit & %Hs0 & %Hs8 & %Herr & %Hge) & Hout & Hs & Hva & #Hargs & Herrno & #Hro)".
    block_enter.
    alloc_keep fb Hfb. change (0 < fb /\ fb mod 16 = 0 /\ fb + 16 <= 2 ^ 48) in Hfb. destruct Hfb as (Hfb & Hf16 & Hfe).
    iDestruct (obj_zero_block with "Hobj") as "(Hfl & Hfx & Hfc)"; [compute; discriminate|].
    iAssert (live fb (mkRegion fb (fb + 16) Heap Live)) with "Hfl" as "Hfl".
    iDestruct (zero_cell_prefix fb 0 8 with "Hfx Hfc") as "(Hfc & _ & _)".
    alloc_keep wb Hwb. iClear "Hobj".
    alloc_keep vb Hvb. change (0 < vb /\ vb mod 16 = 0 /\ vb + 32 <= 2 ^ 48) in Hvb. destruct Hvb as (Hvb & Hv16 & Hve).
    iDestruct (obj_zero_block with "Hobj") as "(Hvl & Hvx & Hvc)"; [compute; discriminate|].
    iAssert (live vb (mkRegion vb (vb + 32) Heap Live)) with "Hvl" as "Hvl".
    iDestruct (zero_cell_prefix vb 0 24 with "Hvx Hvc") as "(Hvc & _ & _)". do 8 alloc_drop.
    step_global Hge. iApply (wp_dci_errno_check eb Herr); [vx|]. iNext.
    iDestruct "Herrno" as (bs cs [Hbs Hcs]) "Hp". iEval (rewrite pts_app) in "Hp". iDestruct "Hp" as "[Heb Hea]".
    iApply (wp_dci_errno_load eb Herr with "Heb"); [vx | exact Hbs|]. iNext. iIntros "Heb".
    iAssert (errno_any eb) with "[Heb Hea]" as "Herrno". { iExists bs, cs. iSplit; [done|]. rewrite pts_app. iFrame. }
    step.
    iDestruct (va_at_cursor with "Hva") as (cb sb) "((-> & %Hcb & %Hc8 & %Hce & %Hsb & %Hsk & _) & Hcl & Hcc & Hsl & Hvback)".
    check "Hcl". iApply (wp_raw_load_pointer_dq with "Hcl Hcc Hsl"); [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; lia |].
    iNext. iIntros "Hcl Hcc Hsl". iDestruct ("Hvback" with "Hcl Hcc Hsl") as "Hva".
    check "Hvl". store "Hvl" "Hvc". iClear "Hvl Hvc".
    iDestruct (word_string_short with "Hs") as %Hshort.
    call_callee with (dq, mkPtr fa fc, bytes) giving "Hs"; [iExact "Hs"|]. iDestruct "Hpost" as "[-> Hs]". block_resume.
    check "Hfl". store "Hfl" "Hfc". step. step. step.
    iDestruct (word_string_range with "Hs") as %Hfr. cbn [ptr_addr] in Hfr. pose proof (chr_idx_le 37 bytes) as Hidx.
    call_callee with (bb, dq, mkPtr fa fc, bytes, _) giving "Hout Hs"; [iFrame "Hout Hs"; iPureIntro; unwrap2; lia|].
    iDestruct "Hpost" as "(-> & Hout & Hs)". block_resume.
    call_callee with bb giving "Hout"; [iExact "Hout"|]. iDestruct "Hpost" as (b) "((-> & %Hb) & Hout)". block_resume.
    step. branch_eqn E.
    2: { step. iApply wp_ret_void. iNext. iApply "HK". iFrame "Hout Hs Herrno". done. }
    clear E. step. check "Hfl". load_fmt "Hfl" "Hfc" "Hs".
    destruct (lit_run lit_or_str bytes ds Hp Hcov) as (lit & tl & ds' & Hbytes & Hlit & Htl & Hptl & Hcov' & Hfit').
    destruct Htl as [-> | [tl' ->]].
    { (* The format has no conversion, and the function returns. *)
      assert (Hx : (bytes ++ [0]) !! chr_idx 37 bytes = Some 0) by (rewrite -Hlit Hbytes; apply byte_after; reflexivity).
      read_byte "Hs" (chr_idx 37 bytes) 0 Hx. step. branch. step. iApply wp_ret_void. iNext. iApply "HK".
      iFrame "Hout Hs Herrno". done. }
    assert (Hx : (bytes ++ [0]) !! chr_idx 37 bytes = Some 37) by (rewrite -Hlit Hbytes; apply byte_after; reflexivity).
    read_byte "Hs" (chr_idx 37 bytes) 37 Hx. step. branch.
    (* No conversion is registered, so the function takes the loop without positional arguments. *)
    iPoseProof "Hro" as "(_ & _ & _ & _ & Hn1 & Hn2 & Hn3)".
    iDestruct "Hn1" as (n1 r1) "((%Hg1 & %Hb1 & %Ha1 & %He1 & %Hr1) & Hl1 & Hc1)".
    iDestruct "Hn2" as (n2 r2) "((%Hg2 & %Hb2 & %Ha2 & %He2 & %Hr2) & Hl2 & Hc2)".
    iDestruct "Hn3" as (n3 r3) "((%Hg3 & %Hb3 & %Ha3 & %He3 & %Hr3) & Hl3 & Hc3)".
    step. step_global Hg1. check_read_dq "Hl1" by a2. iNext. iIntros "_".
    iApply (wp_raw_load_pointer_dq with "Hl1 Hc1 []"); [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; lia | done |].
    iNext. iIntros "_ _ _". step. step. step. branch.
    step. step_global Hg2. check_read_dq "Hl2" by a2. iNext. iIntros "_".
    iApply (wp_raw_load_pointer_dq with "Hl2 Hc2 []"); [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; lia | done |].
    iNext. iIntros "_ _ _". step. step. step. step. branch.
    step. step_global Hg3. check_read_dq "Hl3" by a2. iNext. iIntros "_".
    iApply (wp_raw_load_pointer_dq with "Hl3 Hc3 []"); [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; lia | done |].
    iNext. iIntros "_ _ _". step. step. step. step. branch.
    assert (Hi0 : 8 * Z.of_nat (Z.to_nat (skip / 8)) = skip) by (Z.div_mod_to_equations; lia).
    goto_block "IH" "HK" 1%nat
      with (PlIn (PbIn bb (mkPtr fa fc) dq bytes ds (mkPtr cb (Obj cb)) skip xs rest eb) fb wb lit (37 :: tl') ds'
              (Z.to_nat (skip / 8)) 0).
    row_simpl. rewrite Hi0 Hlit. iFrame "Hout Hs Hfl Hfc Hva Hargs Herrno Hro". iPureIntro.
    split_and!; [reflexivity | exact Hbytes | exact Hcov' | exact (Hfit' _ _ Hfit) | lia | Z.div_mod_to_equations; lia |
                 lia | lia | lia | reflexivity | exact Hptl].
  (* The two rows for L79 take the step into the block and use its body. *)
  - iIntros (y e from Φ) "%Hfrom %He H HK". row_simpl. iDestruct "H" as "[%Hn0 H]". c_env_open He.
    block_enter_from Hfrom.
    iApply ("Hhead" $! y with "[] [H] HK"); [iPureIntro; row_simpl; rewrite Hn0; c_env_close | row_simpl; iExact "H"].
  - iIntros (y e from Φ) "%Hfrom %He H HK". row_simpl. iDestruct "H" as "[%Hok H]". c_env_open He.
    block_enter_from Hfrom.
    iApply ("Hhead" $! y with "[] [H] HK");
      [iPureIntro; row_simpl; rewrite (Z.mod_small (pl_n y)); [c_env_close | lia] | row_simpl; iFrame "H"; done].
  (* The two rows for L1831 do the same. The phi nodes copy the string and its length. *)
  - iIntros (z e from Φ) "%Hfrom %He H HK". row_simpl. iDestruct "H" as "[H #Hstr]". c_env_open He.
    iDestruct (word_string_range with "Hstr") as %Htr. block_enter_from Hfrom.
    iApply ("Hprint" $! z with "[] [H] HK");
      [iPureIntro; row_simpl; rewrite Z.mod_small; [c_env_close | lia] | row_simpl; iFrame "H Hstr"].
  - iIntros (z e from Φ) "%Hfrom %He H HK". row_simpl. iDestruct "H" as "(%Htext & H & #Hstr)". c_env_open He.
    block_enter_from Hfrom.
    iApply ("Hprint" $! z with "[] [H] HK"); [iPureIntro; row_simpl; rewrite Htext; c_env_close | row_simpl; iFrame "H Hstr"].
  (* The two rows for L1150 do the same. *)
  - iIntros (y e from Φ) "%Hfrom %He H HK". row_simpl. c_env_open He. block_enter_from Hfrom.
    iApply ("Hnext" $! y with "[] [H] HK"); [iPureIntro; row_simpl; c_env_close | row_simpl; iExact "H"].
  - iIntros (y e from Φ) "%Hfrom %He H HK". row_simpl. c_env_open He. block_enter_from Hfrom.
    iApply ("Hnext" $! y with "[] [H] HK"); [iPureIntro; row_simpl; c_env_close | row_simpl; iExact "H"].
  (* The start row loads three cells that hold null pointers, and a null pointer names no object. *)
  Unshelve. all: first [exact DfracDiscarded | exact (mkRegion 0 0 Heap Live)].
Qed.

(** ## The contract *)

(** A caller of `c: __printf_buffer` uses this lemma. It says that the
    compiled function meets [printf_buffer_spec] for the formats of
    plain text and `%s`, in every program that defines the function. *)
Lemma printf_buffer_has_spec `{!Defines ge "__printf_buffer" glibc_printf_buffer} :
  HasSpec registry (os_wi w0) ge (TAtom "__printf_buffer") (printf_buffer_spec lit_or_str k R).
Proof using Type*.
  eapply (blocks_has_spec _ _ _ loop_blocks); [exact defines | reflexivity | reflexivity | | exact loop_table].
  intros x. eexists _, x. split; [reflexivity|]. split.
  { destruct x as [bb [fa fc] dq bytes ds [ca cc] skip xs rest eb]. c_env_close. }
  cbn [bs_pre bs_post]. iIntros "$". iIntros (r) "$".
Qed.

End table.
