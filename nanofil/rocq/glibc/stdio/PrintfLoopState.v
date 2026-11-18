(** The formatter walks its format in the function
    `c: __printf_buffer`. The function copies the plain text of the
    format into a buffer, and for each conversion it takes one argument
    and appends its text. The module [PrintfLoop](PrintfLoop.v) proves
    that the compiled function is safe and that it meets
    [printf_buffer_spec] of [PrintfSpec](PrintfSpec.v). This module
    states what that proof shows at each place of the function where
    it stops, and it proves the facts that every part of the proof
    uses.

    The function is a loop over the conversions of the format. A proof
    about a loop needs a statement that is true whenever a round
    starts, and here the statement has three parts. First, the buffer
    is usable. Second, the variable `c: f` points to a percent sign in
    the format, and the format from that sign on still parses. Third,
    the arguments that are left fit the conversions that are left.

    The compiled function has 376 basic blocks, because it handles
    every conversion that glibc knows. The proof states what is true
    at a few places in the function, and it follows the code between
    them. The places are the function's entry, the start of a round,
    the first block of each conversion that the proof covers, the code
    that prints the string of a `%s`, and the code that ends a
    conversion and copies the plain text after it. The table
    [loop_blocks] has one row for each way into each place. A lemma of
    the module [CBlocks](../CBlocks.v) turns the rows, each with a
    proof of the code that follows it, into a proof about the whole
    function.

    Each place has a module of its own for its proof, so that a
    change to one conversion checks quickly. The module
    [PrintfLoopHead](PrintfLoopHead.v) reads the letter of a conversion
    and jumps to the conversion's code. The module
    [PrintfLoopNext](PrintfLoopNext.v) follows the code after a
    conversion.

    Three modules follow the conversions. The first one,
    [PrintfLoopStr](PrintfLoopStr.v), follows a `%s`. The second one,
    [PrintfLoopChar](PrintfLoopChar.v), follows a `%c` and a `%%`. The
    third one, [PrintfLoopInt](PrintfLoopInt.v), follows a `%d`.

    The loop calls seven other functions. Three of them append to the
    buffer. One tests whether the buffer has failed, and one finds the
    next percent sign. One measures a string, and one turns a number
    into digits. The proof assumes a contract for each of the seven,
    which says what the function needs and what it gives back. *)

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
  CFrame CStruct CBlocks PrintfLayout PrintfOut PrintfSpec ItoaWordSpec PrintfCopy FormatterNames VaArgRound.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic StringVL.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.


Module S := FormatterSrc.fn___printf_buffer.

(** ## The temporaries at the places *)

(** The compiler keeps the function's C variables in temporaries,
    which are the registers of the compiled code. About twenty
    variables are in use at each place. Most of them belong to
    conversions that the proof does not cover, and the proof does not
    follow them. The list [loop_keys] names the variables that the
    proof follows in every round. The first block of a conversion also
    reads the flags, the width and the precision of the conversion,
    and the list [conv_keys] adds those. The function [keep_keys]
    takes a list of temporaries and drops every variable that is not
    in a list of names. *)
Definition loop_keys : list string :=
  ["&f"; "buf"; "&work_buffer"; "ap"; "v55"; "grouping"; "thousands_sep"; "readonly_format"; "nspecs_done";
   "left"; "width"; "len"; "string"; "&null"].
Definition conv_keys : list string := loop_keys ++ ["is_long"; "prec"; "spec"].
Definition int_keys : list string :=
  conv_keys ++ ["alt"; "space"; "showsign"; "group"; "is_short"; "is_char"; "use_outdigits"; "pad"; "workend"; "base";
                "is_negative"; "pr.21"; "signed_number"; "number_length"; "v1332"; "v1418"; "v1429"; "prec_inc"; "v1456"].
Definition keep_keys (keys : list string) (sig : cut_sig) : cut_sig :=
  filter (fun '(_, (key, _)) => existsb (String.eqb key) keys) sig.
Notation keep := (keep_keys loop_keys).

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

(** The code of a conversion starts at a block of its own. The block
    `L1825` starts a `%s`, the block `L1796` starts a `%c`, and the
    block `L1151` handles `%%`. *)
Definition str_sig : cut_sig := Eval vm_compute in keep_keys conv_keys (cut_at S.temp_keys S.live_in "L1825").
Definition char_sig : cut_sig := Eval vm_compute in keep_keys conv_keys (cut_at S.temp_keys S.live_in "L1796").
Definition percent_sig : cut_sig := Eval vm_compute in keep (cut_at S.temp_keys S.live_in "L1151").

(** A `%d` runs more code than the other conversions, so the proof
    stops at five blocks of it. The first block reads the number, and
    the second block turns the number into digits. The third block
    works out the padding. The fourth block pads and prints the sign,
    and the fifth block writes the digits. The labels of the five
    blocks are `L1155`, `L1290`, `L1442`, `L1498` and `L1508`, and the
    function reaches each of them in one way. *)
Definition int_sig : cut_sig := Eval vm_compute in keep_keys int_keys (cut_at S.temp_keys S.live_in "L1155").
Definition number_sig : cut_sig := Eval vm_compute in keep_keys int_keys (cut_at S.temp_keys S.live_in "L1290").
Definition digits_sig : cut_sig := Eval vm_compute in keep_keys int_keys (cut_at S.temp_keys S.live_in "L1442").
Definition pad_sig : cut_sig := Eval vm_compute in keep_keys int_keys (cut_at S.temp_keys S.live_in "L1498").
Definition sign_sig : cut_sig := Eval vm_compute in keep_keys int_keys (cut_at S.temp_keys S.live_in "L1508").

(** The block `L1831` prints the string of a `%s`. The function comes
    from the block `L1871` with the argument's string and its length,
    and from the block `L1836` with the constant `(null)`. *)
Definition print_from_len : cut_sig :=
  Eval vm_compute in keep (cut_edge S.temp_keys S.live_in glibc_printf_buffer "L1831" "L1871").
Definition print_from_null : cut_sig :=
  Eval vm_compute in keep (cut_edge S.temp_keys S.live_in glibc_printf_buffer "L1831" "L1836").
Definition print_body : cut_sig :=
  Eval vm_compute in keep (cut_body S.temp_keys S.live_in glibc_printf_buffer "L1831" "L1871").

(** Every conversion ends at the block `L1150`, which counts the
    conversion and copies the plain text after it. The function
    reaches this block in five ways. Two of them come from a `%s`: the
    block `L1887` when the string needed no padding, and the block
    `L1901` when it did. The block `L1807` comes from a `%c`, the
    block `L1151` comes from a `%%`, and the block `L1558` comes from
    a `%d`. *)
Definition next_from_write : cut_sig :=
  Eval vm_compute in keep (cut_edge S.temp_keys S.live_in glibc_printf_buffer "L1150" "L1887").
Definition next_from_pad : cut_sig :=
  Eval vm_compute in keep (cut_edge S.temp_keys S.live_in glibc_printf_buffer "L1150" "L1901").
Definition next_from_char : cut_sig :=
  Eval vm_compute in keep (cut_edge S.temp_keys S.live_in glibc_printf_buffer "L1150" "L1807").
Definition next_from_percent : cut_sig :=
  Eval vm_compute in keep (cut_edge S.temp_keys S.live_in glibc_printf_buffer "L1150" "L1151").
Definition next_from_digits : cut_sig :=
  Eval vm_compute in keep (cut_edge S.temp_keys S.live_in glibc_printf_buffer "L1150" "L1558").
Definition next_body : cut_sig :=
  Eval vm_compute in keep (cut_body S.temp_keys S.live_in glibc_printf_buffer "L1150" "L1887").

(** ## Formats and their arguments *)

(** The function reads its format one piece at a time: some plain
    text, then a conversion, then more plain text. The proof follows
    it. At each piece the proof needs to know what the bytes at the
    pointer `c: f` are and what is left of the format after them. The
    lemmas below say this for a format that parses. *)

(** The function finds the next percent sign with a search, and it
    copies the bytes before that sign as plain text. Those bytes are
    the first directives of the format, and none of them takes an
    argument. So the format splits into that plain text a and a rest b.
    The rest is empty or starts with a percent sign. It parses, and
    the arguments that fit the whole format fit the rest. *)
Lemma lit_run tl ds :
  parse_narrow tl = Some ds ->
  exists a b ds', tl = a ++ b /\ length a = chr_idx 37 tl /\ (b = [] \/ exists b', b = 37 :: b') /\
    parse_narrow b = Some ds' /\
    (forall xs rest, narrow_fits ds xs rest -> narrow_fits ds' xs rest).
Proof.
  revert ds. induction tl as [|c r IH]; intros ds Hp.
  { exists [], [], ds. cbn in *. split_and!; auto. }
  cbn [parse_narrow chr_idx] in *. destruct (c =? 37) eqn:E.
  { apply Z.eqb_eq in E as ->. exists [], (37 :: r), ds. split_and!; eauto. }
  destruct (literal_byte c) eqn:Hl; [|discriminate]. destruct (parse_narrow r) as [ds0|] eqn:Hr; [|discriminate].
  cbn in Hp. injection Hp as <-.
  destruct (IH ds0 eq_refl) as (a & b & ds' & -> & Hlen & Hb & Hpb & Hfit).
  exists (c :: a), b, ds'. split_and!; auto; [cbn [length]; congruence|].
  intros xs rest (used & -> & Hargs). apply Hfit. exists used. split; [reflexivity|].
  inversion Hargs as [|? ? ? ? Hrest | |? ? ? ? Hd]; subst; [exact Hrest | inversion Hd].
Qed.

(** A format that starts with a percent sign continues with the letter
    x of a conversion, and what follows the two bytes parses to the
    directives after that conversion. *)
Lemma conv_start tl ds :
  parse_narrow (37 :: tl) = Some ds ->
  exists x tail d ds0, tl = x :: tail /\ conversion x = Some d /\ ds = d :: ds0 /\ parse_narrow tail = Some ds0.
Proof.
  cbn [parse_narrow]. change (37 =? 37) with true. cbv iota. destruct tl as [|x tail]; [discriminate|].
  destruct (conversion x) as [d|] eqn:Hd; [|discriminate].
  destruct (parse_narrow tail) as [ds0|] eqn:Ht; [|discriminate]. intros [= <-]. exists x, tail, d, ds0. auto.
Qed.

(** The parser knows four letters, and each letter stands for one
    conversion. *)
Lemma conv_letter x d :
  conversion x = Some d ->
  (x = 115 /\ d = FmtStr) \/ (x = 99 /\ d = FmtChar) \/ (x = 100 /\ d = FmtInt) \/ (x = 37 /\ d = FmtPercent).
Proof.
  unfold conversion. destruct (Z.eqb_spec x 115) as [->|_]; [intros [= <-]; auto|].
  destruct (Z.eqb_spec x 99) as [->|_]; [intros [= <-]; auto|].
  destruct (Z.eqb_spec x 100) as [->|_]; [intros [= <-]; auto|].
  destruct (Z.eqb_spec x 37) as [->|_]; [intros [= <-]; auto 6 | discriminate].
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

(** The arguments that fit a format which starts with `%c` start with
    an integer of 32 bits, and the arguments after it fit the rest of
    the format. *)
Lemma char_fits ds xs rest :
  narrow_fits (FmtChar :: ds) xs rest ->
  exists n xs', xs = WInt n :: xs' /\ 0 <= n < 2 ^ 32 /\ narrow_fits ds xs' rest.
Proof.
  intros (used & -> & Hargs). inversion Hargs as [| | |? ? ? used' Hd Hrest]; subst.
  inversion Hd as [|? Hn|]; subst. eexists _, _. split; [reflexivity|]. split; [exact Hn|]. exists used'. auto.
Qed.

(** The arguments that fit a format which starts with `%d` start with
    an integer of 32 bits as well. *)
Lemma int_fits ds xs rest :
  narrow_fits (FmtInt :: ds) xs rest ->
  exists n xs', xs = WInt n :: xs' /\ 0 <= n < 2 ^ 32 /\ narrow_fits ds xs' rest.
Proof.
  intros (used & -> & Hargs). inversion Hargs as [| | |? ? ? used' Hd Hrest]; subst.
  inversion Hd as [| |? Hn]; subst. eexists _, _. split; [reflexivity|]. split; [exact Hn|]. exists used'. auto.
Qed.

(** The conversion `%%` takes no argument, so the arguments that fit a
    format which starts with it fit the rest of the format. *)
Lemma percent_fits ds xs rest : narrow_fits (FmtPercent :: ds) xs rest -> narrow_fits ds xs rest.
Proof.
  intros (used & -> & Hargs). exists used. split; [reflexivity|].
  inversion Hargs as [| |? ? Hrest|? ? ? ? Hd]; subst; [exact Hrest | inversion Hd].
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

(** These two notations name the region of the copy of the arguments
    xs at the address sb, and the region of the cursor at the address
    cb. *)
Notation snap_region xs sb := (mkRegion sb (sb + req_extent (fx_req xs)) (req_kind (fx_req xs)) Live).
Notation cursor_region cb := (mkRegion cb (cb + 32) Heap Live).

Section loop.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** ## Reading an argument *)

(** A variadic call copies its arguments into an object of their own,
    and a cursor points to the next argument in that copy. The
    predicate [va_at] owns the copy and the cursor. A conversion
    reads one argument from the copy and moves the cursor past it. The
    rule for that step asks for three things: the cursor, the lifetime
    of the copy, and the cell that holds the argument. The lemmas
    below take these three out of the ownership of the copy and put
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

(** A conversion that takes a 32-bit integer moves the cursor only 4
    bytes, so the cursor then stands in the middle of a slot. The next
    read rounds the cursor up to the next slot before it reads. So
    inside the loop the cursor stands at the next argument or up to 7
    bytes before it. The predicate [va_cur] owns the copy of the
    arguments and such a cursor, and i is the index of the next
    argument. *)
Definition va_cur (ap : ptr) (i : nat) (xs : list word) : iProp Σ :=
  ∃ cb sb cur, ⌜ap = mkPtr cb (Obj cb) /\ 0 < cb /\ cb mod 8 = 0 /\ cb + 32 <= 2 ^ 48 /\ 0 < sb /\ sb mod 16 = 0 /\
                sb + req_extent (fx_req xs) <= 2 ^ 48 /\ (i <= length xs)%nat /\ 0 <= cur /\
                ((cur + 8 - 1) / 8 * 8)%Z = (sb + 8 * Z.of_nat i)%Z⌝ ∗
    pts (va_cursor_ps cb (cursor_region cb) (mkPtr cur (Ro sb))) ∗ pts (snapshot_ps xs sb (fx_req xs)).

(** The function's caller gives a cursor that stands at an argument. *)
Lemma va_at_cur ap (i : nat) xs : va_at ap (8 * Z.of_nat i) xs ⊢ va_cur ap i xs.
Proof using Type.
  iIntros "(%cb & %sb & (-> & %Hcb & %Hc8 & %Hce & %Hsb & %Hs16 & %Hend & %Hskip) & Hcur & Hsnap)".
  iExists cb, sb, (sb + 8 * Z.of_nat i). iFrame "Hcur Hsnap". iPureIntro.
  split_and!; [reflexivity | first [assumption | lia | Z.div_mod_to_equations; lia]..].
Qed.

(** The cell of an integer argument and the lifetime of the copy are
    distinct pieces. *)
Lemma int_pieces_nodup sb sr o n : base.NoDup ((PLive sb, VLive sr) :: cell sb o n).
Proof using Type.
  unfold cell. cbn [List.map]. repeat (apply list.NoDup_cons; split; [rewrite ?elem_of_cons elem_of_nil; intros H;
    repeat destruct H as [H|H]; try discriminate H; try (injection H; lia); exact H|]). apply base.NoDup_nil_2.
Qed.

(** The rule for reading a pointer argument asks for a few parts of
    memory. The predicate [va_cur] gives those parts when the next
    argument has the index i and is the pointer q. The parts come back
    with the cursor at the argument after it. *)
Lemma va_cur_ptr ap (i : nat) xs q :
  xs !! i = Some (WPtr q) ->
  va_cur ap i xs ⊢ ∃ cb sb cur,
    ⌜ap = mkPtr cb (Obj cb) /\ cb mod 8 = 0 /\ 0 < sb /\
     sb + 8 * Z.of_nat i + 8 <= sb + req_extent (fx_req xs) /\ sb + req_extent (fx_req xs) <= 2 ^ 48 /\
     0 <= cur /\ ((cur + 8 - 1) / 8 * 8)%Z = (sb + 8 * Z.of_nat i)%Z⌝ ∗
    pts (va_cursor_ps cb (cursor_region cb) (mkPtr cur (Ro sb))) ∗
    live sb (snap_region xs sb) ∗ pcell sb (8 * Z.of_nat i) q ∗
    (pts (va_cursor_ps cb (cursor_region cb) (mkPtr (sb + 8 * Z.of_nat i + 8) (Ro sb))) -∗
     live sb (snap_region xs sb) -∗ pcell sb (8 * Z.of_nat i) q -∗ va_cur ap (S i) xs).
Proof using Type.
  intros Hi. pose proof (lookup_lt_Some _ _ _ Hi) as Hlt.
  iIntros "(%cb & %sb & %cur & (-> & %Hcb & %Hc8 & %Hce & %Hsb & %Hs16 & %Hend & %Hlen & %Hcur0 & %Hround) & Hcur & Hsnap)".
  pose proof (heap_req_extent 16 (8 * Z.of_nat (length xs))) as Hext. fold (fx_req xs) in Hext.
  iDestruct (pts_take _ ((PLive sb, VLive (snap_region xs sb)) :: (PAux sb (8 * Z.of_nat i), VAux (ptr_cap q)) ::
      cell sb (8 * Z.of_nat i) (ptr_addr q)) with "Hsnap") as "[Hq Hback]"; [apply arg_pieces_nodup| |].
  { intros [l v] [[= -> ->]|Hin]%elem_of_cons; [apply snap_live_in|].
    apply (snapshot_ps_pointer xs i q sb (fx_req xs) Hi); [lia | exact Hin]. }
  iExists cb, sb, cur. iSplit; [iPureIntro; split_and!; [reflexivity | first [assumption | lia]..]|].
  iFrame "Hcur". rewrite /live /pcell (pts_app [_]). iDestruct "Hq" as "[$ $]".
  iIntros "Hcur Hsl Hc". iExists cb, sb, (sb + 8 * Z.of_nat i + 8).
  iSplit; [iPureIntro; split_and!; [reflexivity | first [assumption | lia | Z.div_mod_to_equations; lia]..]|].
  iFrame "Hcur". iApply "Hback". rewrite (pts_app [_]). iFrame "Hsl Hc".
Qed.

(** A conversion that takes a 32-bit integer reads it with the rule
    for a 32-bit argument. This lemma takes out of [va_cur] what that
    rule asks for, when the next argument has the index i and is the
    integer n. The rule moves the cursor only 4 bytes, so the cursor
    then stands inside the slot of the argument that was read. That
    position is less than 8 bytes before the next argument, and the
    lemma gives back [va_cur] for the index after i. *)
Lemma va_cur_int ap (i : nat) xs n :
  xs !! i = Some (WInt n) ->
  va_cur ap i xs ⊢ ∃ cb sb cur,
    ⌜ap = mkPtr cb (Obj cb) /\ cb mod 8 = 0 /\ 0 < sb /\
     sb + 8 * Z.of_nat i + 8 <= sb + req_extent (fx_req xs) /\ sb + req_extent (fx_req xs) <= 2 ^ 48 /\
     0 <= cur /\ ((cur + 8 - 1) / 8 * 8)%Z = (sb + 8 * Z.of_nat i)%Z⌝ ∗
    pts (va_cursor_ps cb (cursor_region cb) (mkPtr cur (Ro sb))) ∗
    live sb (snap_region xs sb) ∗ icell sb (8 * Z.of_nat i) n ∗
    (pts (va_cursor_ps cb (cursor_region cb) (mkPtr (sb + 8 * Z.of_nat i + 4) (Ro sb))) -∗
     live sb (snap_region xs sb) -∗ icell sb (8 * Z.of_nat i) n -∗ va_cur ap (S i) xs).
Proof using Type.
  intros Hi. pose proof (lookup_lt_Some _ _ _ Hi) as Hlt.
  iIntros "(%cb & %sb & %cur & (-> & %Hcb & %Hc8 & %Hce & %Hsb & %Hs16 & %Hend & %Hlen & %Hcur0 & %Hround) & Hcur & Hsnap)".
  pose proof (heap_req_extent 16 (8 * Z.of_nat (length xs))) as Hext. fold (fx_req xs) in Hext.
  iDestruct (pts_take _ ((PLive sb, VLive (snap_region xs sb)) :: cell sb (8 * Z.of_nat i) n) with "Hsnap")
    as "[Hq Hback]"; [apply int_pieces_nodup| |].
  { intros [l v] [[= -> ->]|Hin]%elem_of_cons; [apply snap_live_in|].
    apply (snapshot_ps_cell xs i (WInt n) n sb (fx_req xs) Hi eq_refl); [lia | exact Hin]. }
  iExists cb, sb, cur. iSplit; [iPureIntro; split_and!; [reflexivity | first [assumption | lia]..]|].
  iFrame "Hcur". rewrite /live /icell (pts_app [_]). iDestruct "Hq" as "[$ $]".
  iIntros "Hcur Hsl Hc". iExists cb, sb, (sb + 8 * Z.of_nat i + 4).
  iSplit; [iPureIntro; split_and!; [reflexivity | first [assumption | lia | Z.div_mod_to_equations; lia]..]|].
  iFrame "Hcur". iApply "Hback". rewrite (pts_app [_]). iFrame "Hsl Hc".
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


(** ## The functions that the loop calls *)

(** The loop appends through three functions of the buffer. It asks
    the buffer whether it has failed, it searches the format for the
    next percent sign, and it measures a string argument. It turns the
    number of a `%d` into digits with `c: _itoa_word`. Every part of
    the proof assumes the same contracts for these seven functions. *)
Notation loop_callees k R :=
  [(TAtom "__printf_buffer_write", write_spec k R);
   (TAtom "glibc_vfprintf_internal#__printf_buffer_has_failed", has_failed_spec k R);
   (TAtom "glibc_vfprintf_internal#__find_specmb.gnu_inline", find_spec_spec);
   (TAtom "__GI_strlen", strlen_spec);
   (TAtom "glibc_vfprintf_internal#__printf_buffer_pad", pad_spec k R);
   (TAtom "glibc_vfprintf_internal#__printf_buffer_putc", putc_spec k R);
   (TAtom "__printf_buffer_write", write_bytes_spec k R);
   (TAtom "_itoa_word", itoa_word_spec)].

(** The loop calls `c: __printf_buffer_write` under two contracts.
    One contract is for the bytes of a string, and the other is for a
    run of bytes. The tactic [call_callee] uses the first contract
    that the list has for a function. The tactic [call_spec] makes the
    same call with a contract s that the proof names. *)
Tactic Notation "call_spec" constr(s) "with" uconstr(x) "giving" constr(Hs) :=
  lazymatch goal with
  | P : @GlibcProgram ?hlc ?Σ |- context [mkFrame _ _ _ None (Exec _ (Call _ (Global ?n) _ :: _) _)] =>
      let H := constr:(ltac:(eapply callee_spec; [typeclasses eauto | callee_member]) :
        HasSpec (@program_registry hlc Σ P) (os_wi (@program_world hlc Σ P)) (@program_ge hlc Σ P) n s) in
      iApply (wp_call_callee n s (HasSpec0 := H) x);
        [vxu
        | iSplitL Hs;
            [cbn [fs_pre]
            | cbn [fs_post]; let v := fresh "v" in iIntros (v) "Hpost"]]
  end.

Section table.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (k : Z) (R : Z * region * Z * Z -> iProp Σ).

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

(** Some facts hold at every place inside the loop. The bytes before
    `c: f` and the bytes from it on make up the format. The arguments
    that are left fit the directives that are left to run. The cell of
    `c: f` is an 8-aligned heap object, and the count of conversions
    fits in 32 bits. The predicate [pl_ok] collects these facts. *)
Definition pl_ok (y : pl_in) : Prop :=
  pb_bytes (pl_x y) = pl_pre y ++ pl_tl y /\
  narrow_fits (pl_ds y) (skipn (pl_i y) (pb_xs (pl_x y))) (pb_rest (pl_x y)) /\
  0 < pl_fb y /\ pl_fb y mod 8 = 0 /\ pl_fb y + 16 <= 2 ^ 48 /\ 0 <= pl_n y < 2 ^ 32.

(** The function keeps a work buffer of 1000 bytes among its local
    variables, and the conversion `%d` writes the digits of its number
    at the end of that buffer. A number has at most 20 digits. So the
    predicate [work_own] owns the last 20 bytes of the buffer at wb
    and the lifetime of its object, which is 1008 bytes long. *)
Definition work_own (wb : Z) : iProp Σ :=
  ∃ old, ⌜0 < wb /\ wb mod 8 = 0 /\ wb + 1008 <= 2 ^ 48 /\ length old = 20%nat⌝ ∗
    live wb (mkRegion wb (wb + 1008) Heap Live) ∗ bytes wb 980 old.

(** The work buffer lies in the address space of a Fil-C program. *)
Lemma work_own_range wb : work_own wb ⊢ ⌜0 < wb /\ wb + 1008 <= 2 ^ 48⌝.
Proof using Type. iIntros "(%old & (%H0 & _ & %He & _) & _)". done. Qed.

(** Inside the loop the function owns everything that its caller
    lent: the buffer, the format, the copy of the arguments and errno.
    It also owns the cell of the variable `c: f`, and that cell holds
    a pointer to the second part of the format. The argument cursor
    stands at the next argument that a conversion will read, or a few
    bytes before it. The parameter W is what the function owns of its
    work buffer, which changes while a `%d` runs. *)
Definition pl_own_with (W : iProp Σ) (y : pl_in) : iProp Σ :=
  printf_out k R (pb_buf (pl_x y)) ∗
  word_string (pb_dq (pl_x y)) (pb_fmt (pl_x y)) (pb_bytes (pl_x y)) ∗
  live (pl_fb y) (mkRegion (pl_fb y) (pl_fb y + 16) Heap Live) ∗
  pcell (pl_fb y) 0 (ptr_add (pb_fmt (pl_x y)) (Z.of_nat (length (pl_pre y)))) ∗
  va_cur (pb_ap (pl_x y)) (pl_i y) (pb_xs (pl_x y)) ∗
  ([∗ list] a ∈ skipn (pl_i y) (pb_xs (pl_x y)), str_arg a) ∗
  W ∗ errno_any (pb_eb (pl_x y)) ∗ printf_ro.

(** Outside a `%d` the function owns the last 20 bytes of the work
    buffer with any contents. *)
Definition pl_own (y : pl_in) : iProp Σ := pl_own_with (work_own (pl_wb y)) y.

(** A round starts with `c: f` at a percent sign, and the format from
    there on parses to the directives left to run. *)
Definition head_pre (y : pl_in) : iProp Σ :=
  (⌜pl_ok y /\ head (pl_tl y) = Some 37 /\ parse_narrow (pl_tl y) = Some (pl_ds y)⌝ ∗ pl_own y)%I.

(** The function has done no conversion before the first round. The
    compiled code sets the count of conversions to zero on that way
    into the block `L79`, so the row for that way in asks that the
    count is zero. *)
Definition head_entry_pre (y : pl_in) : iProp Σ := (⌜pl_n y = 0⌝ ∗ head_pre y)%I.


(** The first block of a conversion runs with `c: f` at the letter of
    the conversion. The conversion d is the first directive left to
    run, and the format after the letter parses to the directives
    after it. The conversion has not read its argument yet. *)
Definition conv_pre (d : narrow_directive) (y : pl_in) : iProp Σ :=
  (⌜pl_ok y /\ pl_tl y <> [] /\ exists ds, pl_ds y = d :: ds /\ parse_narrow (tail (pl_tl y)) = Some ds⌝ ∗ pl_own y)%I.

(** A conversion without a flag, a width or a precision starts with
    fixed values in its variables. The letter x of the conversion is
    in a temporary. The compiled code holds the constant −1 for the
    precision, because the format gives none. The padding character is
    a space. The variable `c: workend` points to the end of the work
    buffer. *)
Definition conv_vals (x : Z) (y : pl_in) : list (string * word) :=
  pl_vals y ++
  [("left", WInt 0); ("width", WInt 0); ("is_long", WInt 0); ("prec", WInt 4294967295); ("spec", WInt x);
   ("alt", WInt 0); ("space", WInt 0); ("showsign", WInt 0); ("group", WInt 0); ("is_short", WInt 0);
   ("is_char", WInt 0); ("use_outdigits", WInt 0); ("pad", WInt 32);
   ("workend", WPtr (mkPtr (pl_wb y + 1000) (Obj (pl_wb y))))].

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

(** The record [pi_in] is the logical input of a place inside the
    code of a `%d`. It adds to the input of the loop the number u that
    the conversion prints, without its sign. The other fields are the
    values of variables that the proof follows without knowing them:
    whether the number is negative, whether it is not zero and the
    width that is left to pad. The last field is the count of digits
    that the code writes. *)
Record pi_in : Type := PiIn {
  pi_y : pl_in; pi_u : Z; pi_neg : Z; pi_nz : Z; pi_w : Z; pi_cnt : Z
}.

(** After the digits are written, the variable `c: string` points to
    the first digit in the work buffer. *)
Definition pi_vals (z : pi_in) : list (string * word) :=
  pl_vals (pi_y z) ++
  [("workend", WPtr (mkPtr (pl_wb (pi_y z) + 1000) (Obj (pl_wb (pi_y z))))); ("spec", WInt 100); ("base", WInt 10);
   ("alt", WInt 0); ("space", WInt 0); ("showsign", WInt 0); ("group", WInt 0); ("use_outdigits", WInt 0);
   ("pad", WInt 32); ("prec", WInt 1); ("left", WInt 0); ("pr.21", WInt (pi_u z)); ("signed_number", WInt (pi_u z));
   ("is_negative", WInt (pi_neg z));
   ("string", WPtr (mkPtr (pl_wb (pi_y z) + 1000 - pi_cnt z) (Obj (pl_wb (pi_y z)))));
   ("number_length", WInt (pi_cnt z)); ("v1429", WInt (pi_cnt z)); ("v1332", WInt 0); ("v1418", WInt 0);
   ("prec_inc", WInt 0); ("v1456", WInt (pi_nz z)); ("width", WInt (pi_w z))].

(** The block `L1290` runs after the conversion has read its argument,
    so the loop is in the state that the end of a conversion needs.
    The number is a 64-bit integer. *)
Definition number_pre (z : pi_in) : iProp Σ := (⌜0 <= pi_u z < 2 ^ 64⌝ ∗ next_pre (pi_y z))%I.

(** After the block `L1290` the last bytes of the work buffer hold the
    digits of the number u, and the bytes before them are as they
    were. *)
Definition work_digits (wb u : Z) : iProp Σ :=
  ∃ old, ⌜0 < wb /\ wb mod 8 = 0 /\ wb + 1008 <= 2 ^ 48 /\ length old = 20%nat⌝ ∗
    live wb (mkRegion wb (wb + 1008) Heap Live) ∗
    bytes wb 980 (take (20 - length (dec_digits u)) old ++ dec_digits u).

(** The later blocks of a `%d` run in the same state of the loop, with
    the digits in the work buffer. The count of bytes that the code
    will write is the number of the digits. *)
Definition digits_pre (z : pi_in) : iProp Σ :=
  (⌜pl_ok (pi_y z) /\ pl_tl (pi_y z) <> [] /\ parse_narrow (tail (pl_tl (pi_y z))) = Some (pl_ds (pi_y z)) /\
    pi_cnt z = Z.of_nat (length (dec_digits (pi_u z)))⌝ ∗
   pl_own_with (work_digits (pl_wb (pi_y z)) (pi_u z)) (pi_y z))%I.

(** The function returns nothing and gives back what its caller
    lent. *)
Definition pl_post (y : pl_in) : outcome -> iProp Σ := fs_post (printf_buffer_spec k R) (pl_x y).

(** At the entry the temporaries hold the parameters. *)
Definition entry_vals (x : pb_in) : list (string * word) :=
  [("buf", WPtr (mkPtr (pb_buf x) (Obj (pb_buf x)))); ("format", WPtr (pb_fmt x)); ("ap", WPtr (pb_ap x));
   ("mode_flags", WInt 0)].

(** The table [loop_blocks] says what is true at each place where the
    proof stops. A place that the function reaches in one way has one
    row. A place that the function reaches in several ways has one row
    for each way, because the compiled code copies different values on
    each way in. The rows are in six groups, and a module of its own
    proves each group. *)
Definition start_rows : list bspec :=
  [BSpec "start" None entry_sig pb_in entry_vals (fs_pre (printf_buffer_spec k R))
     (fs_post (printf_buffer_spec k R))].
Definition head_rows : list bspec :=
  [BSpec "L79" (Some "L67") head_from_entry pl_in pl_vals head_entry_pre pl_post;
   BSpec "L79" (Some "L2128") head_from_round pl_in pl_vals head_pre pl_post].
Definition str_rows : list bspec :=
  [BSpec "L1825" None str_sig pl_in (conv_vals 115) (conv_pre FmtStr) pl_post;
   BSpec "L1831" (Some "L1871") print_from_len pp_in pp_vals print_pre (fun z => pl_post (pp_in_ z));
   BSpec "L1831" (Some "L1836") print_from_null pp_in pp_vals print_null_pre (fun z => pl_post (pp_in_ z))].
Definition char_rows : list bspec :=
  [BSpec "L1796" None char_sig pl_in (conv_vals 99) (conv_pre FmtChar) pl_post;
   BSpec "L1151" None percent_sig pl_in pl_vals (conv_pre FmtPercent) pl_post].
Definition next_rows : list bspec :=
  [BSpec "L1150" (Some "L1887") next_from_write pl_in pl_vals next_pre pl_post;
   BSpec "L1150" (Some "L1901") next_from_pad pl_in pl_vals next_pre pl_post;
   BSpec "L1150" (Some "L1807") next_from_char pl_in pl_vals next_pre pl_post;
   BSpec "L1150" (Some "L1151") next_from_percent pl_in pl_vals next_pre pl_post;
   BSpec "L1150" (Some "L1558") next_from_digits pl_in pl_vals next_pre pl_post].
Definition int_rows : list bspec :=
  [BSpec "L1155" None int_sig pl_in (conv_vals 100) (conv_pre FmtInt) pl_post;
   BSpec "L1290" None number_sig pi_in pi_vals number_pre (fun z => pl_post (pi_y z));
   BSpec "L1442" None digits_sig pi_in pi_vals digits_pre (fun z => pl_post (pi_y z));
   BSpec "L1498" None pad_sig pi_in pi_vals digits_pre (fun z => pl_post (pi_y z));
   BSpec "L1508" None sign_sig pi_in pi_vals digits_pre (fun z => pl_post (pi_y z))].
Definition loop_blocks : list bspec :=
  start_rows ++ head_rows ++ str_rows ++ char_rows ++ next_rows ++ int_rows.

End table.

(** The tactic [row_simpl] unfolds a row's statement into the facts
    and the ownership that it stands for. *)
Ltac row_simpl :=
  cbn [bs_sig bs_vals bs_pre bs_post bs_label] in *;
  unfold number_pre, digits_pre, pi_vals, head_entry_pre, print_null_pre, print_pre, head_pre, next_pre, conv_pre, pl_post,
    pl_own, pl_own_with, pl_ok, pl_vals, pp_vals, conv_vals, entry_vals in *;
  cbn [app fs_pre fs_post printf_buffer_spec pp_in_ pp_str pp_text pi_y pi_u pi_neg pi_nz pi_w pi_cnt pl_x pl_fb pl_wb pl_pre pl_tl pl_ds pl_i pl_n
       pb_buf pb_fmt pb_dq pb_bytes pb_ds pb_ap pb_skip pb_xs pb_rest pb_eb ptr_addr ptr_cap] in *.
