(** # Object code from the backend's lines

    The backend builds its assembly as [line]s (Asm.v) and prints them
    as text for GNU as. This file assembles the same lines itself. A
    program that links the backend, such as libnanofil
    (docs/lambda-anf.md, M4), then gets machine code without running
    an assembler. [encode_lines] gives the bytes of every section, the
    relocations that a linker applies to them and the symbols that it
    sees. Elf.v writes them as a shared object.

    The object is the one GNU as makes of the text. tests/encode.sh
    holds every section's bytes, every relocation and every symbol to
    GNU as 2.46 on each module the backend's gates compile and on the
    regular expressions of experiments/regex-nanofil; 2.43.1 and 2.44
    give the same objects. What the gate compares is [dump_parts]
    against tests/objdump.py's reading of GNU as's file.

    Where GNU as could choose, this file chooses as it does:

    | Choice | GNU as's rule |
    | --- | --- |
    | Register to register | the store form (`01 /r`, `89 /r`) |
    | Immediate | `83 /n ib` when it fits in a signed byte after sign extension from the operation's width, else the accumulator form, else `81 /n` |
    | Shift by 1 | `d1 /n` |
    | `movq $n, %r` | `c7 /0` with 32 bits |
    | `jmp` and `jcc` | 2 bytes when the target is in range, after GNU as's relaxation passes |
    | Alignment in code | the multi-byte NOPs of `alt_patt`, after a `0x90` when the last thing was data |

    GNU as shortens a branch only when its target is a label in the
    same section that the linker cannot replace. Such a label is not
    weak, and the branch names it without `@PLT` unless the label is
    local. GNU as starts every such branch short and lengthens the
    ones whose target is out of range, one pass at a time. An
    alignment between a branch and its target can absorb the growth,
    so [relax] repeats GNU as's passes (relax_segment in write.c)
    instead of computing any fixpoint.

    A call keeps a relocation unless its target is a local symbol of
    its own section. The relocation is PLT32 when the symbol was not
    yet defined at the call, or was weak or global. A relocation
    against a local symbol names the symbol's section instead, except
    a GOT or TLS one.

    When this file has no encoding for a line, [encode_lines] gives the
    line's text instead of an object, and the caller treats the module
    as outside the compiler. *)

From Stdlib Require Import String ZArith List Ascii Bool.
From Nanofil Require Import Maps.
From Backend Require Import Text Asm.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** ## Tables keyed by strings *)

(** A map from strings, hashed as the model's name maps are. *)
Definition smap (A : Type) : Type := ZMap.t (list (string * A)).

Definition sm_empty {A : Type} : smap A := ZMap.empty _.

Fixpoint assoc {A : Type} (s : string) (l : list (string * A)) : option A :=
  match l with
  | [] => None
  | (k, v) :: r => if String.eqb k s then Some v else assoc s r
  end.

Definition sm_find {A : Type} (s : string) (m : smap A) : option A :=
  match ZMap.find (string_hash s 0) m with
  | Some l => assoc s l
  | None => None
  end.

Fixpoint assoc_drop {A : Type} (s : string) (l : list (string * A)) : list (string * A) :=
  match l with
  | [] => []
  | (k, v) :: r => if String.eqb k s then r else (k, v) :: assoc_drop s r
  end.

Definition sm_add {A : Type} (s : string) (v : A) (m : smap A) : smap A :=
  let h := string_hash s 0 in
  let l := match ZMap.find h m with Some l => l | None => [] end in
  ZMap.add h ((s, v) :: assoc_drop s l) m.

Definition sm_of_list {A : Type} (l : list (string * A)) : smap A :=
  fold_left (fun m p => sm_add (fst p) (snd p) m) l sm_empty.

(** ## Bytes *)

Definition byte (n : Z) : Z := Z.land n 255.

(** The [k] bytes of [n], least significant first, in two's complement. *)
Fixpoint le_bytes (k : nat) (n : Z) : list Z :=
  match k with
  | O => []
  | S k' => byte n :: le_bytes k' (Z.shiftr n 8)
  end.

Definition le2 (n : Z) : list Z := le_bytes 2 n.
Definition le4 (n : Z) : list Z := le_bytes 4 n.
Definition le8 (n : Z) : list Z := le_bytes 8 n.

Definition fits8 (n : Z) : bool := (-128 <=? n) && (n <=? 127).
Definition fits32 (n : Z) : bool := (-2147483648 <=? n) && (n <=? 2147483647).

Definition zlen {A : Type} (l : list A) : Z := Z.of_nat (length l).

(** Loops over lists, in constant stack. A section or a shared object
    is a list of tens of thousands of bytes, and libnanofil runs on
    its caller's stack, where a recursion as deep as the list is long
    does not fit. *)
Definition map_tr {A B : Type} (f : A -> B) (l : list A) : list B :=
  rev' (fold_left (fun acc x => f x :: acc) l []).

Definition filter_tr {A : Type} (f : A -> bool) (l : list A) : list A :=
  rev' (fold_left (fun acc x => if f x then x :: acc else acc) l []).

Definition flat_map_tr {A B : Type} (f : A -> list B) (l : list A) : list B :=
  rev' (fold_left (fun acc x => rev_append (f x) acc) l []).

(** [n] zeros in front of [acc]. *)
Fixpoint zeros_onto (n : nat) (acc : list Z) : list Z :=
  match n with
  | O => acc
  | S n' => zeros_onto n' (0 :: acc)
  end.

Definition zeros (n : Z) : list Z := zeros_onto (Z.to_nat n) [].

(** The first [n] elements of [l]. *)
Fixpoint take_rev {A : Type} (n : nat) (l : list A) (acc : list A) : list A :=
  match n, l with
  | S n', x :: r => take_rev n' r (x :: acc)
  | _, _ => acc
  end.

Definition take {A : Type} (n : nat) (l : list A) : list A := rev' (take_rev n l []).

(** The concatenation of [chunks], which are in reverse order. *)
Definition join_rev (chunks : list (list Z)) : list Z :=
  rev' (fold_left (fun acc c => rev_append c acc) (rev' chunks) []).

(** A stable merge sort. [merge_onto] merges [l1] and [l2], [l1]'s
    first among equals, after the reversed [acc]; its fuel is their
    total length. *)
Fixpoint merge_onto {A : Type} (le : A -> A -> bool) (fuel : nat) (l1 l2 acc : list A) : list A :=
  match fuel with
  | O => rev_append acc (l1 ++ l2)
  | S fuel' =>
      match l1, l2 with
      | [], _ => rev_append acc l2
      | _, [] => rev_append acc l1
      | x :: r1, y :: r2 =>
          if le x y then merge_onto le fuel' r1 l2 (x :: acc) else merge_onto le fuel' l1 r2 (y :: acc)
      end
  end.

Definition merge {A : Type} (le : A -> A -> bool) (l1 l2 : list A) : list A :=
  merge_onto le (length l1 + length l2) l1 l2 [].

(** Merges the runs pairwise, in order, in front of the reversed [acc]. *)
Fixpoint merge_pairs_onto {A : Type} (le : A -> A -> bool) (runs acc : list (list A)) : list (list A) :=
  match runs with
  | a :: b :: r => merge_pairs_onto le r (merge le a b :: acc)
  | _ => rev_append acc runs
  end.

(** Merges the runs pairwise until one is left; fuel bounds the
    rounds. *)
Fixpoint merge_all {A : Type} (le : A -> A -> bool) (fuel : nat) (runs : list (list A)) : list A :=
  match fuel with
  | O => concat runs
  | S fuel' =>
      match runs with
      | [] => []
      | [a] => a
      | _ => merge_all le fuel' (merge_pairs_onto le runs [])
      end
  end.

Definition sort {A : Type} (le : A -> A -> bool) (l : list A) : list A :=
  merge_all le (length l) (map_tr (fun x => [x]) l).

Definition str_le (a b : string) : bool :=
  match String.compare a b with Gt => false | _ => true end.

(** The bindings of a map, by name. The order of the buckets is no
    answer to give: the OCaml extraction hashes names with OCaml's own
    hash (theories/core/Extract.v). *)
Definition sm_elements {A : Type} (m : smap A) : list (string * A) :=
  sort (fun a b => str_le (fst a) (fst b))
       (rev' (fold_left (fun acc b => rev_append (snd b) acc) (ZMap.elements m) [])).

(** ## Registers and operands *)

Inductive rclass := C8 | C16 | C32 | C64 | CX | CST.

Definition rclass_eqb (a b : rclass) : bool :=
  match a, b with
  | C8, C8 | C16, C16 | C32, C32 | C64, C64 | CX, CX | CST, CST => true
  | _, _ => false
  end.

Record reg := mkreg { rnum : Z; rcls : rclass }.

(** The general registers by number, each as its 64-, 32-, 16- and
    8-bit name. *)
Definition gpr_names : list (list string) :=
  [["rax"; "eax"; "ax"; "al"]; ["rcx"; "ecx"; "cx"; "cl"]; ["rdx"; "edx"; "dx"; "dl"];
   ["rbx"; "ebx"; "bx"; "bl"]; ["rsp"; "esp"; "sp"; "spl"]; ["rbp"; "ebp"; "bp"; "bpl"];
   ["rsi"; "esi"; "si"; "sil"]; ["rdi"; "edi"; "di"; "dil"]; ["r8"; "r8d"; "r8w"; "r8b"];
   ["r9"; "r9d"; "r9w"; "r9b"]; ["r10"; "r10d"; "r10w"; "r10b"]; ["r11"; "r11d"; "r11w"; "r11b"];
   ["r12"; "r12d"; "r12w"; "r12b"]; ["r13"; "r13d"; "r13w"; "r13b"]; ["r14"; "r14d"; "r14w"; "r14b"];
   ["r15"; "r15d"; "r15w"; "r15b"]].

Definition xmm_names : list string :=
  ["xmm0"; "xmm1"; "xmm2"; "xmm3"; "xmm4"; "xmm5"; "xmm6"; "xmm7";
   "xmm8"; "xmm9"; "xmm10"; "xmm11"; "xmm12"; "xmm13"; "xmm14"; "xmm15"].

Definition st_names : list string :=
  ["st(0)"; "st(1)"; "st(2)"; "st(3)"; "st(4)"; "st(5)"; "st(6)"; "st(7)"].

Fixpoint numbered {A : Type} (n : Z) (l : list A) : list (Z * A) :=
  match l with
  | [] => []
  | x :: r => (n, x) :: numbered (n + 1) r
  end.

Definition gpr_row (p : Z * list string) : list (string * reg) :=
  match snd p with
  | [q; d; w; b] =>
      [(q, mkreg (fst p) C64); (d, mkreg (fst p) C32); (w, mkreg (fst p) C16); (b, mkreg (fst p) C8)]
  | _ => []
  end.

Definition reg_table : smap reg :=
  sm_of_list
    (flat_map gpr_row (numbered 0 gpr_names)
     ++ map (fun p => (snd p, mkreg (fst p) CX)) (numbered 0 xmm_names)
     ++ ("st", mkreg 0 CST) :: map (fun p => (snd p, mkreg (fst p) CST)) (numbered 0 st_names)).

(** What a RIP-relative operand refers to: the place itself, its GOT
    entry (`@GOTPCREL`) or its TLS offset's (`@GOTTPOFF`). *)
Inductive ripk := RPlain | RGot | RTpoff.

(** A memory operand: a displacement, a base and maybe an index, as
    register numbers; or RIP-relative, to a symbol plus an addend or
    to a number alone. *)
Inductive mem :=
| MBase (d b : Z) (i : option Z)
| MRip (k : ripk) (s : option string) (a : Z).

Inductive opnd :=
| PImm (n : Z)
| PReg (r : reg)
| PMem (fs : bool) (m : mem)
| PTarget (s : string) (a : Z) (plt : bool) (* a branch target, `S@PLT` when plt *)
| PInd (o : opnd). (* `*O` *)

(** An expression as a symbol, if any, and a number. *)
Fixpoint flat (e : expr) : option (option string * Z) :=
  match e with
  | ELit (LInt n) => Some (None, n)
  | ELit (LSym s) => Some (Some s, 0)
  | EAdd a b =>
      match flat a, flat b with
      | Some (None, x), Some (t, y) => Some (t, x + y)
      | Some (t, x), Some (None, y) => Some (t, x + y)
      | _, _ => None
      end
  end.

Definition gp64 (r : string) : option Z :=
  match sm_find r reg_table with
  | Some (mkreg n C64) => Some n
  | _ => None
  end.

Fixpoint dec (o : operand) : option opnd :=
  match o with
  | OImm e => match flat e with Some (None, n) => Some (PImm n) | _ => None end
  | OReg r => option_map PReg (sm_find r reg_table)
  | OMem (LInt d) b => option_map (fun n => PMem false (MBase d n None)) (gp64 b)
  | OMemIndex (LInt d) b i =>
      match gp64 b, gp64 i with
      | Some nb, Some ni => if ni =? 4 then None else Some (PMem false (MBase d nb (Some ni)))
      | _, _ => None
      end
  | ORip e => option_map (fun p => PMem false (MRip RPlain (fst p) (snd p))) (flat e)
  | OGotpcrel (LSym s) => Some (PMem false (MRip RGot (Some s) 0))
  | OGottpoff (LSym s) => Some (PMem false (MRip RTpoff (Some s) 0))
  | OFs o' => match dec o' with Some (PMem _ m) => Some (PMem true m) | _ => None end
  | OSym e => match flat e with Some (Some s, a) => Some (PTarget s a false) | _ => None end
  | OPlt (LSym s) => Some (PTarget s 0 true)
  | OInd o' => option_map PInd (dec o')
  | _ => None
  end.

Fixpoint dec_all (os : list operand) : option (list opnd) :=
  match os with
  | [] => Some []
  | o :: r =>
      match dec o, dec_all r with
      | Some p, Some ps => Some (p :: ps)
      | _, _ => None
      end
  end.

(** ## Items *)

(** What a field of a section holds until the symbols are placed: a
    PC-relative 32-bit field (PLT32 when [plt]), a GOT entry's offset
    (GOTPCREL 9, GOTPCRELX 41, REX_GOTPCRELX 42), a TLS one (GOTTPOFF),
    or an absolute address of [size] bytes. *)
Inductive fixk := XPc (plt : bool) | XGot (t : Z) | XTpoff | XAbs (size : Z).

(** A field at [fx_at] in its item, of [fx_size] bytes, for [fx_sym]
    plus [fx_add]; a PC-relative field counts from [fx_end], the end
    of its instruction. *)
Record fixup := mkfix {
  fx_at : Z; fx_size : Z; fx_kind : fixk; fx_sym : string; fx_add : Z; fx_end : Z }.

(** What a section is made of: bytes with their fields, zeros, a
    branch GNU as may relax, an alignment and a label. *)
Inductive item :=
| IBytes (bs : list Z) (fx : list fixup)
| IZero (n : Z)
| IJump (cc : option Z) (s : string) (a : Z) (plt : bool)
| IAlign (p : Z) (nop : bool) (data : bool)
  (* to 2^p, with NOPs in code, after a 0x90 when the last thing was data *)
| ILabel (s : string).

(** ## Instructions *)

Inductive width := W8 | W16 | W32 | W64.

Definition wcls (w : width) : rclass :=
  match w with W8 => C8 | W16 => C16 | W32 => C32 | W64 => C64 end.
Definition wpfx (w : width) : list Z := match w with W16 => [102] | _ => [] end.
Definition wrex (w : width) : bool := match w with W64 => true | _ => false end.
Definition wop (w : width) (o : Z) : Z := match w with W8 => o | _ => o + 1 end.

(** A byte register that needs a REX prefix: spl, bpl, sil and dil. *)
Definition force8 (w : width) (n : Z) : bool :=
  match w with W8 => (4 <=? n) && (n <=? 7) | _ => false end.

Definition gpr (w : width) (o : opnd) : option Z :=
  match o with
  | PReg (mkreg n c) => if rclass_eqb c (wcls w) then Some n else None
  | _ => None
  end.

Definition xmm (o : opnd) : option Z :=
  match o with PReg (mkreg n CX) => Some n | _ => None end.

Inductive rm := RmReg (n : Z) | RmMem (m : mem).

(** A register of width [w] or a memory operand, as a ModRM operand,
    with its segment prefix and whether it needs a REX. *)
Definition rm_of (w : width) (o : opnd) : option (rm * list Z * bool) :=
  match o with
  | PReg (mkreg n c) => if rclass_eqb c (wcls w) then Some (RmReg n, [], force8 w n) else None
  | PMem fs m => Some (RmMem m, if fs then [100] else [], false)
  | _ => None
  end.

Definition xrm_of (o : opnd) : option (rm * list Z) :=
  match o with
  | PReg (mkreg n CX) => Some (RmReg n, [])
  | PMem fs m => Some (RmMem m, if fs then [100] else [])
  | _ => None
  end.

(** The mod field and displacement for [d] off a base whose low bits
    are [bb]: none for 0 unless the base is rbp or r13. *)
Definition disp_mod (d bb : Z) : Z * list Z :=
  if (d =? 0) && negb (bb =? 5) then (0, [])
  else if fits8 d then (1, [byte d]) else (2, le4 d).

(** The ModRM byte for register field [reg] and [r], what follows it,
    REX.X, REX.B, and the place of a symbol's displacement. *)
Record modrm_out := mkmo {
  mo_bytes : list Z; mo_x : bool; mo_b : bool; mo_fix : option (Z * ripk * string * Z) }.

Definition modrm (reg : Z) (r : rm) : modrm_out :=
  let rg := Z.land reg 7 * 8 in
  match r with
  | RmReg n => mkmo [192 + rg + Z.land n 7] false (8 <=? n) None
  | RmMem (MBase d b None) =>
      let bb := Z.land b 7 in
      let (md, ds) := disp_mod d bb in
      if bb =? 4 then mkmo (md * 64 + rg + 4 :: 36 :: ds) false (8 <=? b) None
      else mkmo (md * 64 + rg + bb :: ds) false (8 <=? b) None
  | RmMem (MBase d b (Some i)) =>
      let bb := Z.land b 7 in
      let (md, ds) := disp_mod d bb in
      mkmo (md * 64 + rg + 4 :: Z.land i 7 * 8 + bb :: ds) (8 <=? i) (8 <=? b) None
  | RmMem (MRip _ None a) => mkmo (rg + 5 :: le4 a) false false None
  | RmMem (MRip k (Some s) a) => mkmo [rg + 5; 0; 0; 0; 0] false false (Some (1, k, s, a))
  end.

(** GNU as's GOT relocation for an instruction with opcode [op]: the
    relaxable ones for mov, test and an operation into a register
    (REX_GOTPCRELX with a REX), else GOTPCREL. *)
Definition got_type (op : list Z) (rex : bool) : Z :=
  match op with
  | [o] => if (o =? 139) || (o =? 133) || (Z.lor o 56 =? 59) then (if rex then 42 else 41) else 9
  | _ => 9
  end.

(** An instruction with a ModRM byte: prefixes, REX.W, whether a byte
    register forces a REX, the opcode, the register field, the ModRM
    operand and the immediate. *)
Definition modrm_ins (pfx : list Z) (w force : bool) (op : list Z) (reg : Z) (r : rm) (imm : list Z) : item :=
  let mo := modrm reg r in
  let rr := 8 <=? reg in
  let need := w || rr || mo_x mo || mo_b mo || force in
  let rex :=
    if need then [64 + (if w then 8 else 0) + (if rr then 4 else 0)
                  + (if mo_x mo then 2 else 0) + (if mo_b mo then 1 else 0)]
    else [] in
  let head := pfx ++ rex ++ op in
  let bs := head ++ mo_bytes mo ++ imm in
  match mo_fix mo with
  | None => IBytes bs []
  | Some (off, k, s, a) =>
      let kind := match k with
                  | RPlain => XPc false
                  | RGot => XGot (got_type op need)
                  | RTpoff => XTpoff
                  end in
      IBytes bs [mkfix (zlen head + off) 4 kind s a (zlen bs)]
  end.

(** An instruction with the register in its opcode's low bits. *)
Definition reg_ins (pfx : list Z) (w force : bool) (op n : Z) (imm : list Z) : item :=
  let b := 8 <=? n in
  let rex := if w || b || force then [64 + (if w then 8 else 0) + (if b then 1 else 0)] else [] in
  IBytes (pfx ++ rex ++ [op + Z.land n 7] ++ imm) [].

(** An immediate of an operation of width [w] as GNU as keeps it:
    sign-extended from [w] bits, or [None] out of range. *)
Definition imm_norm (w : width) (n : Z) : option Z :=
  match w with
  | W8 => if (-128 <=? n) && (n <=? 255) then Some (Z.land (n + 128) 255 - 128) else None
  | W16 => if (-32768 <=? n) && (n <=? 65535) then Some (Z.land (n + 32768) 65535 - 32768) else None
  | W32 =>
      if (-2147483648 <=? n) && (n <=? 4294967295)
      then Some (Z.land (n + 2147483648) 4294967295 - 2147483648) else None
  | W64 => if fits32 n then Some n else None
  end.

Definition imm_bytes (w : width) (n : Z) : list Z :=
  match w with W8 => [byte n] | W16 => le2 n | _ => le4 n end.

Definition is_acc (r : rm) (seg : list Z) : bool :=
  match r, seg with RmReg 0, [] => true | _, _ => false end.

(** add or adc sbb and sub xor cmp, by [op] 0 to 7. *)
Definition alu (op : Z) (w : width) (os : list opnd) : option item :=
  match os with
  | [PImm n; d] =>
      match imm_norm w n, rm_of w d with
      | Some v, Some (r, seg, f) =>
          match w with
          | W8 =>
              if is_acc r seg then Some (IBytes [op * 8 + 4; byte v] [])
              else Some (modrm_ins seg false f [128] op r [byte v])
          | _ =>
              if fits8 v then Some (modrm_ins (seg ++ wpfx w) (wrex w) f [131] op r [byte v])
              else if is_acc r seg then
                Some (IBytes (wpfx w ++ (if wrex w then [72] else []) ++ op * 8 + 5 :: imm_bytes w v) [])
              else Some (modrm_ins (seg ++ wpfx w) (wrex w) f [129] op r (imm_bytes w v))
          end
      | _, _ => None
      end
  | [s; d] =>
      match gpr w s, rm_of w d with
      | Some rs, Some (r, seg, f) =>
          Some (modrm_ins (seg ++ wpfx w) (wrex w) (f || force8 w rs) [wop w (op * 8)] rs r [])
      | _, _ =>
          match rm_of w s, gpr w d with
          | Some (RmMem m, seg, _), Some rd =>
              Some (modrm_ins (seg ++ wpfx w) (wrex w) (force8 w rd) [wop w (op * 8 + 2)] rd (RmMem m) [])
          | _, _ => None
          end
      end
  | _ => None
  end.

Definition test (w : width) (os : list opnd) : option item :=
  match os with
  | [PImm n; d] =>
      match imm_norm w n, rm_of w d with
      | Some v, Some (r, seg, f) =>
          if is_acc r seg
          then Some (IBytes (wpfx w ++ (if wrex w then [72] else []) ++ wop w 168 :: imm_bytes w v) [])
          else Some (modrm_ins (seg ++ wpfx w) (wrex w) f [wop w 246] 0 r (imm_bytes w v))
      | _, _ => None
      end
  | [s; d] =>
      match gpr w s, rm_of w d with
      | Some rs, Some (r, seg, f) =>
          Some (modrm_ins (seg ++ wpfx w) (wrex w) (f || force8 w rs) [wop w 132] rs r [])
      | _, _ =>
          match rm_of w s, gpr w d with
          | Some (r, seg, f), Some rd =>
              Some (modrm_ins (seg ++ wpfx w) (wrex w) (f || force8 w rd) [wop w 132] rd r [])
          | _, _ => None
          end
      end
  | _ => None
  end.

(** rol ror rcl rcr shl shr sar, by [op]. *)
Definition shift (op : Z) (w : width) (os : list opnd) : option item :=
  let one d := match rm_of w d with
               | Some (r, seg, f) => Some (modrm_ins (seg ++ wpfx w) (wrex w) f [wop w 208] op r [])
               | None => None
               end in
  match os with
  | [PImm 1; d] => one d
  | [PImm n; d] =>
      match rm_of w d with
      | Some (r, seg, f) =>
          if (0 <=? n) && (n <=? 255)
          then Some (modrm_ins (seg ++ wpfx w) (wrex w) f [wop w 192] op r [n]) else None
      | None => None
      end
  | [PReg (mkreg 1 C8); d] =>
      match rm_of w d with
      | Some (r, seg, f) => Some (modrm_ins (seg ++ wpfx w) (wrex w) f [wop w 210] op r [])
      | None => None
      end
  | [d] => one d
  | _ => None
  end.

(** The SSE moves of movq: between a 64-bit register and an XMM one,
    and from and to XMM registers. *)
Definition movq_xmm (os : list opnd) : option item :=
  match os with
  | [s; d] =>
      match gpr W64 s, xmm d with
      | Some rs, Some xd => Some (modrm_ins [102] true false [15; 110] xd (RmReg rs) [])
      | _, _ =>
          match xmm s, gpr W64 d with
          | Some xs, Some rd => Some (modrm_ins [102] true false [15; 126] xs (RmReg rd) [])
          | _, _ =>
              match xrm_of s, xmm d with
              | Some (r, seg), Some xd => Some (modrm_ins (seg ++ [243]) false false [15; 126] xd r [])
              | _, _ =>
                  match xmm s, xrm_of d with
                  | Some xs, Some (RmMem m, seg) => Some (modrm_ins (seg ++ [102]) false false [15; 214] xs (RmMem m) [])
                  | _, _ => None
                  end
              end
          end
      end
  | _ => None
  end.

Definition has_xmm (os : list opnd) : bool :=
  existsb (fun o => match xmm o with Some _ => true | None => false end) os.

Definition mov (w : width) (os : list opnd) : option item :=
  if has_xmm os then match w with W64 => movq_xmm os | _ => None end else
  match os with
  | [PImm n; d] =>
      match gpr w d with
      | Some rd =>
          match w with
          | W64 =>
              if fits32 n then Some (modrm_ins [] true false [199] 0 (RmReg rd) (le4 n))
              else if (-9223372036854775808 <=? n) && (n <=? 18446744073709551615)
              then Some (reg_ins [] true false 184 rd (le8 n)) else None
          | W8 =>
              match imm_norm W8 n with
              | Some v => Some (reg_ins [] false (force8 W8 rd) 176 rd [byte v])
              | None => None
              end
          | _ =>
              match imm_norm w n with
              | Some v => Some (reg_ins (wpfx w) false false 184 rd (imm_bytes w v))
              | None => None
              end
          end
      | None =>
          match imm_norm w n, rm_of w d with
          | Some v, Some (r, seg, f) =>
              Some (modrm_ins (seg ++ wpfx w) (wrex w) f [wop w 198] 0 r (imm_bytes w v))
          | _, _ => None
          end
      end
  | [s; d] =>
      match gpr w s, rm_of w d with
      | Some rs, Some (r, seg, f) =>
          Some (modrm_ins (seg ++ wpfx w) (wrex w) (f || force8 w rs) [wop w 136] rs r [])
      | _, _ =>
          match rm_of w s, gpr w d with
          | Some (RmMem m, seg, _), Some rd =>
              Some (modrm_ins (seg ++ wpfx w) (wrex w) (force8 w rd) [wop w 138] rd (RmMem m) [])
          | _, _ => None
          end
      end
  | _ => None
  end.

(** A zero or sign extension from [sw] to [dw] by [op]. *)
Definition movx (op : list Z) (sw dw : width) (os : list opnd) : option item :=
  match os with
  | [s; d] =>
      match rm_of sw s, gpr dw d with
      | Some (r, seg, f), Some rd => Some (modrm_ins (seg ++ wpfx dw) (wrex dw) f op rd r [])
      | _, _ => None
      end
  | _ => None
  end.

Definition lea (w : width) (os : list opnd) : option item :=
  match os with
  | [PMem _ m; d] =>
      match gpr w d with
      | Some rd => Some (modrm_ins (wpfx w) (wrex w) false [141] rd (RmMem m) [])
      | None => None
      end
  | _ => None
  end.

Definition imul (w : width) (os : list opnd) : option item :=
  match os with
  | [PImm n; s; d] =>
      match imm_norm w n, rm_of w s, gpr w d with
      | Some v, Some (r, seg, _), Some rd =>
          if fits8 v then Some (modrm_ins (seg ++ wpfx w) (wrex w) false [107] rd r [byte v])
          else Some (modrm_ins (seg ++ wpfx w) (wrex w) false [105] rd r (imm_bytes w v))
      | _, _, _ => None
      end
  | [s; d] =>
      match rm_of w s, gpr w d with
      | Some (r, seg, _), Some rd => Some (modrm_ins (seg ++ wpfx w) (wrex w) false [15; 175] rd r [])
      | _, _ => None
      end
  | [s] =>
      match rm_of w s with
      | Some (r, seg, f) => Some (modrm_ins (seg ++ wpfx w) (wrex w) f [wop w 246] 5 r [])
      | None => None
      end
  | _ => None
  end.

(** not neg mul div idiv, by the ModRM extension [ext]. *)
Definition unary (ext : Z) (w : width) (os : list opnd) : option item :=
  match os with
  | [d] =>
      match rm_of w d with
      | Some (r, seg, f) => Some (modrm_ins (seg ++ wpfx w) (wrex w) f [wop w 246] ext r [])
      | None => None
      end
  | _ => None
  end.

Definition setcc (cc : Z) (os : list opnd) : option item :=
  match os with
  | [d] =>
      match rm_of W8 d with
      | Some (r, seg, f) => Some (modrm_ins seg false f [15; 144 + cc] 0 r [])
      | None => None
      end
  | _ => None
  end.

Definition cmov (cc : Z) (w : width) (os : list opnd) : option item :=
  match os with
  | [s; d] =>
      match rm_of w s, gpr w d with
      | Some (r, seg, _), Some rd => Some (modrm_ins (seg ++ wpfx w) (wrex w) false [15; 64 + cc] rd r [])
      | _, _ => None
      end
  | _ => None
  end.

Definition push (os : list opnd) : option item :=
  match os with
  | [PImm n] =>
      if fits8 n then Some (IBytes [106; byte n] [])
      else if fits32 n then Some (IBytes (104 :: le4 n) []) else None
  | [o] =>
      match gpr W64 o with
      | Some n => Some (reg_ins [] false false 80 n [])
      | None =>
          match o with
          | PMem fs m => Some (modrm_ins (if fs then [100] else []) false false [255] 6 (RmMem m) [])
          | _ => None
          end
      end
  | _ => None
  end.

Definition pop (os : list opnd) : option item :=
  match os with
  | [o] =>
      match gpr W64 o with
      | Some n => Some (reg_ins [] false false 88 n [])
      | None =>
          match o with
          | PMem fs m => Some (modrm_ins (if fs then [100] else []) false false [143] 0 (RmMem m) [])
          | _ => None
          end
      end
  | _ => None
  end.

(** An indirect call (ext 2) or jump (ext 4). *)
Definition indirect (ext : Z) (o : opnd) : option item :=
  match o with
  | PMem fs m => Some (modrm_ins (if fs then [100] else []) false false [255] ext (RmMem m) [])
  | _ => match gpr W64 o with
         | Some n => Some (modrm_ins [] false false [255] ext (RmReg n) [])
         | None => None
         end
  end.

(** A call. [npl] says whether GNU as would give a call to the symbol
    a PLT32 relocation at this point of the text. *)
Definition call (npl : string -> bool) (os : list opnd) : option item :=
  match os with
  | [PTarget s a plt] =>
      Some (IBytes [232; 0; 0; 0; 0] [mkfix 1 4 (XPc (plt || ((a =? 0) && npl s))) s a 5])
  | [PInd o] => indirect 2 o
  | _ => None
  end.

Definition jump (cc : option Z) (os : list opnd) : option item :=
  match os with
  | [PTarget s a plt] => Some (IJump cc s a plt)
  | [PInd o] => match cc with None => indirect 4 o | Some _ => None end
  | _ => None
  end.

(** A scalar SSE operation from an XMM register or memory into an XMM
    register, with its mandatory prefix if any. *)
Definition sse (pfx : list Z) (op : Z) (os : list opnd) : option item :=
  match os with
  | [s; d] =>
      match xrm_of s, xmm d with
      | Some (r, seg), Some xd => Some (modrm_ins (seg ++ pfx) false false [15; op] xd r [])
      | _, _ => None
      end
  | _ => None
  end.

(** A conversion from an integer of width [w] into an XMM register. *)
Definition cvt_i2f (pfx : Z) (w : width) (os : list opnd) : option item :=
  match os with
  | [s; d] =>
      match rm_of w s, xmm d with
      | Some (r, seg, _), Some xd => Some (modrm_ins (seg ++ [pfx]) (wrex w) false [15; 42] xd r [])
      | _, _ => None
      end
  | _ => None
  end.

(** A truncating conversion from an XMM register or memory into an
    integer register of width [w]. *)
Definition cvt_f2i (pfx : Z) (w : width) (os : list opnd) : option item :=
  match os with
  | [s; d] =>
      match xrm_of s, gpr w d with
      | Some (r, seg), Some rd => Some (modrm_ins (seg ++ [pfx]) (wrex w) false [15; 44] rd r [])
      | _, _ => None
      end
  | _ => None
  end.

Definition movd (os : list opnd) : option item :=
  match os with
  | [s; d] =>
      match rm_of W32 s, xmm d with
      | Some (r, seg, _), Some xd => Some (modrm_ins (seg ++ [102]) false false [15; 110] xd r [])
      | _, _ =>
          match xmm s, rm_of W32 d with
          | Some xs, Some (r, seg, _) => Some (modrm_ins (seg ++ [102]) false false [15; 126] xs r [])
          | _, _ => None
          end
      end
  | _ => None
  end.

Definition x87_mem (op ext : Z) (os : list opnd) : option item :=
  match os with
  | [PMem fs m] => Some (modrm_ins (if fs then [100] else []) false false [op] ext (RmMem m) [])
  | _ => None
  end.

Definition x87_st (op base : Z) (os : list opnd) : option item :=
  match os with
  | [PReg (mkreg i CST); PReg (mkreg 0 CST)] => Some (IBytes [op; base + i] [])
  | [PReg (mkreg i CST)] => Some (IBytes [op; base + i] [])
  | _ => None
  end.

(** The forms of the mnemonics, by name with the suffix. *)
Inductive form :=
| FAlu (op : Z) (w : width)
| FShift (op : Z) (w : width)
| FMov (w : width)
| FMovabs
| FMovx (op : list Z) (sw dw : width)
| FLea (w : width)
| FTest (w : width)
| FImul (w : width)
| FUnary (ext : Z) (w : width)
| FSet (cc : Z)
| FCmov (cc : Z) (w : width)
| FJcc (cc : Z)
| FJmp
| FCall
| FPush
| FPop
| FFixed (bs : list Z)
| FSse (pfx : list Z) (op : Z)
| FCvtI2F (pfx : Z) (w : width)
| FCvtF2I (pfx : Z) (w : width)
| FMovd
| FX87Mem (op ext : Z)
| FX87St (op base : Z).

Definition suffixes : list (string * width) := [("b", W8); ("w", W16); ("l", W32); ("q", W64)].

Definition sized (base : string) (f : width -> form) : list (string * form) :=
  map (fun p => ((base ++ fst p)%string, f (snd p))) suffixes.

Definition cc_names : list (string * Z) :=
  [("o", 0); ("no", 1); ("b", 2); ("c", 2); ("nae", 2); ("ae", 3); ("nb", 3); ("nc", 3);
   ("e", 4); ("z", 4); ("ne", 5); ("nz", 5); ("be", 6); ("na", 6); ("a", 7); ("nbe", 7);
   ("s", 8); ("ns", 9); ("p", 10); ("pe", 10); ("np", 11); ("po", 11); ("l", 12); ("nge", 12);
   ("ge", 13); ("nl", 13); ("le", 14); ("ng", 14); ("g", 15); ("nle", 15)].

Definition alu_names : list string := ["add"; "or"; "adc"; "sbb"; "and"; "sub"; "xor"; "cmp"].
Definition shift_names : list (string * Z) :=
  [("rol", 0); ("ror", 1); ("rcl", 2); ("rcr", 3); ("shl", 4); ("sal", 4); ("shr", 5); ("sar", 7)].
Definition unary_names : list (string * Z) :=
  [("not", 2); ("neg", 3); ("mul", 4); ("div", 6); ("idiv", 7)].

Definition movx_forms : list (string * form) :=
  [("movzbw", FMovx [15; 182] W8 W16); ("movzbl", FMovx [15; 182] W8 W32);
   ("movzbq", FMovx [15; 182] W8 W64); ("movzwl", FMovx [15; 183] W16 W32);
   ("movzwq", FMovx [15; 183] W16 W64); ("movsbw", FMovx [15; 190] W8 W16);
   ("movsbl", FMovx [15; 190] W8 W32); ("movsbq", FMovx [15; 190] W8 W64);
   ("movswl", FMovx [15; 191] W16 W32); ("movswq", FMovx [15; 191] W16 W64);
   ("movslq", FMovx [99] W32 W64)].

Definition fixed_forms : list (string * form) :=
  [("ret", FFixed [195]); ("retq", FFixed [195]); ("leave", FFixed [201]);
   ("leaveq", FFixed [201]); ("ud2", FFixed [15; 11]); ("cltd", FFixed [153]);
   ("cqto", FFixed [72; 153]); ("cltq", FFixed [72; 152]); ("cwtl", FFixed [152]);
   ("nop", FFixed [144]); ("hlt", FFixed [244]); ("int3", FFixed [204]);
   ("rep movsb", FFixed [243; 164]); ("rep stosb", FFixed [243; 170]);
   ("rep movsq", FFixed [243; 72; 165]); ("rep stosq", FFixed [243; 72; 171]);
   ("fchs", FFixed [217; 224]); ("fabs", FFixed [217; 225]); ("fldz", FFixed [217; 238]);
   ("fld1", FFixed [217; 232]); ("fxch", FFixed [217; 201])].

Definition sse_forms : list (string * form) :=
  [("addsd", FSse [242] 88); ("mulsd", FSse [242] 89); ("subsd", FSse [242] 92);
   ("divsd", FSse [242] 94); ("sqrtsd", FSse [242] 81); ("minsd", FSse [242] 93);
   ("maxsd", FSse [242] 95); ("addss", FSse [243] 88); ("mulss", FSse [243] 89);
   ("subss", FSse [243] 92); ("divss", FSse [243] 94); ("sqrtss", FSse [243] 81);
   ("minss", FSse [243] 93); ("maxss", FSse [243] 95); ("ucomisd", FSse [102] 46);
   ("ucomiss", FSse [] 46); ("comisd", FSse [102] 47); ("comiss", FSse [] 47);
   ("cvtss2sd", FSse [243] 90); ("cvtsd2ss", FSse [242] 90); ("xorpd", FSse [102] 87);
   ("xorps", FSse [] 87); ("andpd", FSse [102] 84); ("andps", FSse [] 84);
   ("cvtsi2sdl", FCvtI2F 242 W32); ("cvtsi2sdq", FCvtI2F 242 W64);
   ("cvtsi2ssl", FCvtI2F 243 W32); ("cvtsi2ssq", FCvtI2F 243 W64);
   ("cvttsd2sil", FCvtF2I 242 W32); ("cvttsd2siq", FCvtF2I 242 W64);
   ("cvttss2sil", FCvtF2I 243 W32); ("cvttss2siq", FCvtF2I 243 W64);
   ("movd", FMovd)].

Definition x87_forms : list (string * form) :=
  [("fldt", FX87Mem 219 5); ("fstpt", FX87Mem 219 7); ("fldl", FX87Mem 221 0);
   ("fstpl", FX87Mem 221 3); ("fstl", FX87Mem 221 2); ("flds", FX87Mem 217 0);
   ("fstps", FX87Mem 217 3); ("fildll", FX87Mem 223 5); ("fildl", FX87Mem 219 0);
   ("fistpll", FX87Mem 223 7); ("fisttpll", FX87Mem 221 1);
   ("fstp", FX87St 221 216); ("fld", FX87St 217 192); ("fadd", FX87St 216 192);
   ("fmul", FX87St 216 200); ("fsub", FX87St 216 224); ("fdiv", FX87St 216 240)].

Definition form_table : smap form :=
  sm_of_list
    (flat_map (fun p => sized (snd p) (FAlu (fst p))) (numbered 0 alu_names)
     ++ flat_map (fun p => sized (fst p) (FShift (snd p))) shift_names
     ++ flat_map (fun p => sized (fst p) (FUnary (snd p))) unary_names
     ++ sized "mov" FMov ++ sized "lea" FLea ++ sized "test" FTest ++ sized "imul" FImul
     ++ map (fun p => (("j" ++ fst p)%string, FJcc (snd p))) cc_names
     ++ map (fun p => (("set" ++ fst p)%string, FSet (snd p))) cc_names
     ++ flat_map (fun p => (("cmov" ++ fst p)%string, FCmov (snd p) W64) :: sized ("cmov" ++ fst p)%string (FCmov (snd p))) cc_names
     ++ [("movabsq", FMovabs); ("jmp", FJmp); ("jmpq", FJmp); ("call", FCall); ("callq", FCall);
         ("push", FPush); ("pushq", FPush); ("pop", FPop); ("popq", FPop)]
     ++ movx_forms ++ fixed_forms ++ sse_forms ++ x87_forms).

Definition encode_form (npl : string -> bool) (f : form) (os : list opnd) : option item :=
  match f with
  | FAlu op w => alu op w os
  | FShift op w => shift op w os
  | FMov w => mov w os
  | FMovabs =>
      match os with
      | [PImm n; d] => match gpr W64 d with Some rd => Some (reg_ins [] true false 184 rd (le8 n)) | None => None end
      | _ => None
      end
  | FMovx op sw dw => movx op sw dw os
  | FLea w => lea w os
  | FTest w => test w os
  | FImul w => imul w os
  | FUnary ext w => unary ext w os
  | FSet cc => setcc cc os
  | FCmov cc w => cmov cc w os
  | FJcc cc => jump (Some cc) os
  | FJmp => jump None os
  | FCall => call npl os
  | FPush => push os
  | FPop => pop os
  | FFixed bs => match os with [] => Some (IBytes bs []) | _ => None end
  | FSse pfx op => sse pfx op os
  | FCvtI2F pfx w => cvt_i2f pfx w os
  | FCvtF2I pfx w => cvt_f2i pfx w os
  | FMovd => movd os
  | FX87Mem op ext => x87_mem op ext os
  | FX87St op base => x87_st op base os
  end.

Definition fixed_bytes (m : fixed_op) : list Z :=
  match m with
  | Cpuid => [72; 137; 222; 15; 162; 137; 223; 72; 137; 243]
  | Xgetbv => [15; 1; 208]
  | Rdtsc => [15; 49]
  | Rdtscp => [15; 1; 249]
  | Lfence => [15; 174; 232]
  | Sfence => [15; 174; 248]
  | Pause => [243; 144]
  end.

(** ## Sections and symbols *)

(** A section: its name, ELF type and flags, whether it holds code,
    its items (last first), its alignment, and whether the last thing
    in it was a data directive. *)
Record sec := mksec {
  c_name : string; c_type : Z; c_flags : string; c_code : bool;
  c_items : list item; c_align : Z; c_data : bool }.

Definition new_sec (s : section) : sec :=
  match s with
  | SText => mksec ".text" 1 "AX" true [] 1 false
  | SData => mksec ".data" 1 "WA" false [] 1 false
  | SRodata => mksec ".rodata" 1 "A" false [] 1 false
  | SBss => mksec ".bss" 8 "WA" false [] 1 false
  | STbss => mksec ".tbss" 8 "WAT" false [] 1 false
  | SDataRelRo => mksec ".data.rel.ro" 1 "WA" false [] 1 false
  | SNoteGnuStack => mksec ".note.GNU-stack" 1 "-" false [] 1 false
  | SInit ctor prio =>
      let base := if ctor then ".init_array" else ".fini_array" in
      let name := match prio with None => base | Some p => (base ++ "." ++ lit_text p)%string end in
      mksec name (if ctor then 14 else 15) "WA" false [] 1 false
  end.

(** What the text says of a symbol: .globl, .weak, .hidden, .type,
    .size (a number, or `.-S` when [None]), .set to a symbol plus an
    addend; the section of its label; whether a GOTTPOFF names it. *)
Record sym := mksym {
  s_glob : bool; s_weak : bool; s_hidden : bool; s_type : option string;
  s_size : option (option Z); s_set : option (string * Z); s_def : option string; s_tls : bool }.

Definition no_sym : sym := mksym false false false None None None None false.

(** What the text has done so far: the current section and the
    others, the symbols, whether a GOT operand was used. *)
Record pstate := mkps { p_cur : sec; p_others : list sec; p_syms : smap sym; p_got : bool }.

Definition get_sym (st : pstate) (s : string) : sym :=
  match sm_find s (p_syms st) with Some y => y | None => no_sym end.

Definition put_sym (st : pstate) (s : string) (y : sym) : pstate :=
  mkps (p_cur st) (p_others st) (sm_add s y (p_syms st)) (p_got st).

Definition upd_sym (st : pstate) (s : string) (f : sym -> sym) : pstate :=
  put_sym st s (f (get_sym st s)).

(** Adds an item to the current section; [data] says whether it is a
    data directive, which matters in code. *)
Definition add_item (st : pstate) (it : item) (data : bool) : pstate :=
  let c := p_cur st in
  mkps (mksec (c_name c) (c_type c) (c_flags c) (c_code c) (it :: c_items c) (c_align c) data)
       (p_others st) (p_syms st) (p_got st).

Fixpoint take_sec (n : string) (l : list sec) : option sec * list sec :=
  match l with
  | [] => (None, [])
  | c :: r =>
      if String.eqb (c_name c) n then (Some c, r)
      else let (f, r') := take_sec n r in (f, c :: r')
  end.

(** Switches to section [s], made when first named. The others are
    kept in the order they were made. *)
Definition switch (st : pstate) (s : section) : pstate :=
  let fresh := new_sec s in
  let cur := p_cur st in
  if String.eqb (c_name cur) (c_name fresh) then st else
  let others := p_others st ++ [cur] in
  let (found, rest) := take_sec (c_name fresh) others in
  let others' := match found with Some _ => others | None => others ++ [fresh] end in
  let (c, rest') := take_sec (c_name fresh) others' in
  match c with
  | Some c' => mkps c' rest' (p_syms st) (p_got st)
  | None => st
  end.

Definition set_align (st : pstate) (p : Z) : pstate :=
  let c := p_cur st in
  mkps (mksec (c_name c) (c_type c) (c_flags c) (c_code c) (c_items c)
               (Z.max (c_align c) (Z.shiftl 1 p)) (c_data c))
       (p_others st) (p_syms st) (p_got st).

Definition is_local_label (s : string) : bool := String.prefix ".L" s.

(** Whether GNU as would give a call to [s] a PLT32 relocation now:
    when [s] is not yet defined, or is weak or global. *)
Definition need_plt (st : pstate) (s : string) : bool :=
  let y := get_sym st s in
  s_weak y || s_glob y ||
  match s_def y, s_set y with None, None => true | _, _ => false end.

(** The key of the place a `.size S, .-S` measures to: a label no
    text can name. *)
Definition dot_key (s : string) : string := String "001"%char s.

(** The bytes of an .asciz text, with GNU as's escapes. *)
Fixpoint unescape (fuel : nat) (cs : list ascii) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      match cs with
      | [] => []
      | c :: r =>
          if Ascii.eqb c "\"%char then
            match r with
            | [] => [92]
            | d :: r' =>
                let n := Z.of_nat (nat_of_ascii d) in
                if (48 <=? n) && (n <=? 55) then
                  (* up to three octal digits *)
                  let oct (x : ascii) := let v := Z.of_nat (nat_of_ascii x) in (48 <=? v) && (v <=? 55) in
                  match r' with
                  | e :: f :: r'' =>
                      if oct e then
                        if oct f then byte ((n - 48) * 64 + (Z.of_nat (nat_of_ascii e) - 48) * 8 + (Z.of_nat (nat_of_ascii f) - 48)) :: unescape fuel' r''
                        else byte ((n - 48) * 8 + (Z.of_nat (nat_of_ascii e) - 48)) :: unescape fuel' (f :: r'')
                      else (n - 48) :: unescape fuel' r'
                  | [e] =>
                      if oct e then byte ((n - 48) * 8 + (Z.of_nat (nat_of_ascii e) - 48)) :: []
                      else (n - 48) :: unescape fuel' r'
                  | [] => [n - 48]
                  end
                else
                  (if n =? 110 then 10 else if n =? 116 then 9 else if n =? 114 then 13
                   else if n =? 98 then 8 else if n =? 102 then 12 else n) :: unescape fuel' r'
            end
          else Z.of_nat (nat_of_ascii c) :: unescape fuel' r
      end
  end.

Definition text_bytes (s : string) : list Z :=
  let cs := list_ascii_of_string s in unescape (length cs) cs.

Definition lit_int (a : lit) : option Z := match a with LInt n => Some n | LSym _ => None end.

(** A data item of [n] bytes for expression [e]. *)
Definition data_item (n : Z) (e : expr) : option item :=
  match flat e with
  | Some (None, v) => Some (IBytes (le_bytes (Z.to_nat n) v) [])
  | Some (Some s, a) => Some (IBytes (zeros n) [mkfix 0 n (XAbs n) s a n])
  | None => None
  end.

(** The mnemonic of an instruction, with its suffix. *)
Definition mnemonic (op : string) (suffix : option string) : string :=
  match suffix with None => op | Some s => (op ++ s)%string end.

Definition is_got (os : list opnd) : bool :=
  existsb (fun o => match o with
                    | PMem _ (MRip RGot _ _) | PMem _ (MRip RTpoff _ _) => true
                    | _ => false end) os.

Definition tpoff_syms (os : list opnd) : list string :=
  flat_map (fun o => match o with PMem _ (MRip RTpoff (Some s) _) => [s] | _ => [] end) os.

Definition line_text (l : line) : string := String.concat "" (line_parts l []).

(** One line, or the text of the line it cannot take. *)
Definition step (st : pstate) (l : line) : pstate + string :=
  match l with
  | Label (LSym s) =>
      inl (add_item (upd_sym st s (fun y => mksym (s_glob y) (s_weak y) (s_hidden y) (s_type y) (s_size y)
                                                  (s_set y) (Some (c_name (p_cur st))) (s_tls y)))
                    (ILabel s) (c_data (p_cur st)))
  | Label _ => inr (line_text l)
  | Fixed m => inl (add_item st (IBytes (fixed_bytes m) []) false)
  | Ins op suffix os =>
      match sm_find (mnemonic op suffix) form_table, dec_all os with
      | Some f, Some ps =>
          match encode_form (need_plt st) f ps with
          | Some it =>
              let st1 := if is_got ps then mkps (p_cur st) (p_others st) (p_syms st) true else st in
              let st2 := fold_left (fun t s => upd_sym t s (fun y => mksym (s_glob y) (s_weak y) (s_hidden y)
                                                     (s_type y) (s_size y) (s_set y) (s_def y) true))
                                   (tpoff_syms ps) st1 in
              inl (add_item st2 it false)
          | None => inr (line_text l)
          end
      | _, _ => inr (line_text l)
      end
  | Dir d =>
      let data_dir it := inl (add_item st it (c_code (p_cur st))) in
      match d with
      | DSection s => inl (switch st s)
      | DP2align (LInt p) =>
          inl (add_item (set_align st p) (IAlign p (c_code (p_cur st)) (c_data (p_cur st))) (c_data (p_cur st)))
      | DBalign (LInt n) =>
          let p := Z.log2 n in
          inl (add_item (set_align st p) (IAlign p (c_code (p_cur st)) (c_data (p_cur st))) (c_data (p_cur st)))
      | DGlobl (LSym s) => inl (upd_sym st s (fun y => mksym true (s_weak y) (s_hidden y) (s_type y) (s_size y) (s_set y) (s_def y) (s_tls y)))
      | DWeak (LSym s) => inl (upd_sym st s (fun y => mksym (s_glob y) true (s_hidden y) (s_type y) (s_size y) (s_set y) (s_def y) (s_tls y)))
      | DHidden (LSym s) => inl (upd_sym st s (fun y => mksym (s_glob y) (s_weak y) true (s_type y) (s_size y) (s_set y) (s_def y) (s_tls y)))
      | DType (LSym s) t => inl (upd_sym st s (fun y => mksym (s_glob y) (s_weak y) (s_hidden y) (Some (lit_text t)) (s_size y) (s_set y) (s_def y) (s_tls y)))
      | DSize (LSym s) =>
          inl (add_item (upd_sym st s (fun y => mksym (s_glob y) (s_weak y) (s_hidden y) (s_type y) (Some None) (s_set y) (s_def y) (s_tls y)))
                        (ILabel (dot_key s)) (c_data (p_cur st)))
      | DSizeOf (LSym s) (LInt n) =>
          inl (upd_sym st s (fun y => mksym (s_glob y) (s_weak y) (s_hidden y) (s_type y) (Some (Some n)) (s_set y) (s_def y) (s_tls y)))
      | DSet (LSym s) e =>
          match flat e with
          | Some (Some t, a) => inl (upd_sym st s (fun y => mksym (s_glob y) (s_weak y) (s_hidden y) (s_type y) (s_size y) (Some (t, a)) (s_def y) (s_tls y)))
          | _ => inr (line_text l)
          end
      | DQuad e => match data_item 8 e with Some it => data_dir it | None => inr (line_text l) end
      | DLong n | DInt n => match data_item 4 (ELit n) with Some it => data_dir it | None => inr (line_text l) end
      | DShort (LInt n) => data_dir (IBytes (le2 n) [])
      | DByte n ns =>
          match lit_int n, fold_right (fun a acc => match lit_int a, acc with Some v, Some vs => Some (byte v :: vs) | _, _ => None end) (Some []) ns with
          | Some v, Some vs => data_dir (IBytes (byte v :: vs) [])
          | _, _ => inr (line_text l)
          end
      | DZero (LInt n) => data_dir (IZero n)
      | DAscii cs => inl (add_item st (IBytes (map (fun c => Z.of_nat (nat_of_ascii c)) cs) []) (c_data (p_cur st)))
      | DAsciz a => inl (add_item st (IBytes (text_bytes (lit_text a) ++ [0]) []) (c_data (p_cur st)))
      | _ => inr (line_text l)
      end
  end.

(** At most [n] of the lines, and the lines left. *)
Fixpoint steps_n (n : nat) (st : pstate) (ls : list line) : (pstate * list line) + string :=
  match n, ls with
  | S n', l :: r => match step st l with inl st' => steps_n n' st' r | inr w => inr w end
  | _, _ => inl (st, ls)
  end.

(** The lines, in runs of 256. In the λANF build, [step] is inlined in
    the loop over the lines, which then calls itself through its own
    closure, a native frame per line; a run bounds those, and the loop
    over the runs is a loop. The fuel is the number of lines. *)
Fixpoint steps_runs (fuel : nat) (st : pstate) (ls : list line) : pstate + string :=
  match fuel, ls with
  | S fuel', _ :: _ =>
      match steps_n 256 st ls with
      | inl (st', r) => steps_runs fuel' st' r
      | inr w => inr w
      end
  | _, _ => inl st
  end.

Definition steps (st : pstate) (ls : list line) : pstate + string := steps_runs (length ls) st ls.

(** ## Placing the items *)

(** Where a symbol's label is: its section, frag and offset in it. *)
Record place := mkplace { pl_sec : string; pl_frag : Z; pl_off : Z }.

(** What ends a frag: nothing, a branch GNU as relaxes (long when
    [long]), or an alignment. *)
Inductive fend := ENone | EJump (cc : option Z) (s : string) (a : Z) | EAlign (p : Z).

(** A frag: its items, the size of its fixed part (a branch's opcode
    byte included), and what ends it. *)
Record frag := mkfrag { fr_items : list item; fr_fix : Z; fr_end : fend }.

(** The section that a symbol resolves to through its .set, with the
    symbol it ends at and the addend; fuel bounds the chain. *)
Fixpoint resolve (syms : smap sym) (fuel : nat) (s : string) (a : Z) : string * Z :=
  match fuel with
  | O => (s, a)
  | S fuel' =>
      match sm_find s syms with
      | Some y => match s_def y, s_set y with
                  | None, Some (t, b) => resolve syms fuel' t (a + b)
                  | _, _ => (s, a)
                  end
      | None => (s, a)
      end
  end.

Definition chain_fuel : nat := 64.

Definition sym_sec (syms : smap sym) (s : string) : option string :=
  let (t, _) := resolve syms chain_fuel s 0 in
  match sm_find t syms with Some y => s_def y | None => None end.

(** Whether GNU as relaxes a branch to [s] in section [cur]: the label
    is in [cur], and the linker cannot replace it. *)
Definition relaxable (syms : smap sym) (cur : string) (s : string) (plt : bool) : bool :=
  let y := match sm_find s syms with Some y => y | None => no_sym end in
  match sym_sec syms s with
  | Some c =>
      String.eqb c cur &&
      (if s_weak y then false
       else if negb (s_glob y) then true
       else if s_hidden y then true
       else negb plt)
  | None => false
  end.

(** The final rule for a PLT32 relocation of a branch: weak,
    undefined or global. *)
Definition need_plt_final (syms : smap sym) (s : string) : bool :=
  let y := match sm_find s syms with Some y => y | None => no_sym end in
  s_weak y || s_glob y || match sym_sec syms s with None => true | Some _ => false end.

(** The branches GNU as does not relax, as their long form with the
    relocation it gives them. *)
Definition settle (syms : smap sym) (cur : string) (it : item) : item :=
  match it with
  | IJump cc s a plt =>
      if relaxable syms cur s plt then it else
      let k := XPc (plt || ((a =? 0) && need_plt_final syms s)) in
      match cc with
      | None => IBytes [233; 0; 0; 0; 0] [mkfix 1 4 k s a 5]
      | Some c => IBytes [15; 128 + c; 0; 0; 0; 0] [mkfix 2 4 k s a 6]
      end
  | _ => it
  end.

Definition item_size (it : item) : Z :=
  match it with
  | IBytes bs _ => zlen bs
  | IZero n => n
  | _ => 0
  end.

(** The frags of a section's items, first to last, and its labels'
    places. *)
Fixpoint frags (cur : string) (n : Z) (fsz : Z) (acc : list item) (its : list item)
         (labels : smap place) (out : list frag) : list frag * smap place :=
  match its with
  | [] => (rev' (mkfrag (rev' acc) fsz ENone :: out), labels)
  | it :: r =>
      match it with
      | ILabel s => frags cur n fsz (it :: acc) r (sm_add s (mkplace cur n fsz) labels) out
      | IJump cc s a _ =>
          frags cur (n + 1) 0 [] r labels (mkfrag (rev' (it :: acc)) (fsz + 1) (EJump cc s a) :: out)
      | IAlign p _ _ =>
          frags cur (n + 1) 0 [] r labels (mkfrag (rev' (it :: acc)) fsz (EAlign p) :: out)
      | _ => frags cur n (fsz + item_size it) (it :: acc) r labels out
      end
  end.

Definition align_pad (addr p : Z) : Z :=
  let m := Z.shiftl 1 p in (m - addr mod m) mod m.

(** The state of a frag in relaxation: its address, its region (the
    alignments before it) and whether its branch is long. *)
Record frst := mkfrst { f_addr : Z; f_region : Z; f_long : bool }.

Definition var_size (f : frag) (long : bool) (addr : Z) : Z :=
  match fr_end f with
  | ENone => 0
  | EJump None _ _ => if long then 4 else 1
  | EJump (Some _) _ _ => if long then 5 else 1
  | EAlign p => align_pad (addr + fr_fix f) p
  end.

(** The first addresses and regions, every branch short. *)
Fixpoint initial (fs : list frag) (i addr region : Z) (m : ZMap.t frst) : ZMap.t frst :=
  match fs with
  | [] => m
  | f :: r =>
      let m' := ZMap.add i (mkfrst addr region false) m in
      let addr' := addr + fr_fix f + var_size f false addr in
      let region' := match fr_end f with EAlign _ => region + 1 | _ => region end in
      initial r (i + 1) addr' region' m'
  end.

Definition get_fst (m : ZMap.t frst) (i : Z) : frst :=
  match ZMap.find i m with Some s => s | None => mkfrst 0 0 false end.

(** One pass of GNU as's relaxation (write.c's relax_segment): each
    frag moves by the growth of those before it, an alignment takes
    up what it now needs, and a short branch out of range grows.
    [labels] places the targets; a target in a frag not yet reached
    in this pass is assumed to move as this one did, unless an
    alignment lies between them. Gives the new states and whether
    anything grew or shrank. *)
Fixpoint pass (fs : list frag) (labels : smap place) (old : ZMap.t frst) (i stretch : Z)
         (nw : ZMap.t frst) (changed : bool) : ZMap.t frst * bool :=
  match fs with
  | [] => (nw, changed)
  | f :: r =>
      let o := get_fst old i in
      let addr := f_addr o + stretch in
      let growth_long :=
        match fr_end f with
        | ENone => (0, f_long o)
        | EAlign p => (align_pad (addr + fr_fix f) p - align_pad (f_addr o + fr_fix f) p, false)
        | EJump cc s a =>
            if f_long o then (0, true) else
            match sm_find s labels with
            | None => (0, false)
            | Some pl =>
                let j := pl_frag pl in
                let base := if j <=? i then (if j =? i then addr else f_addr (get_fst nw j))
                            else f_addr (get_fst old j) in
                let target := base + pl_off pl + a in
                let here := addr + fr_fix f in
                let reached := j <=? i in
                let skip := negb (stretch =? 0) && negb reached
                            && negb ((stretch <? 0) || (f_region (get_fst old j) =? f_region o))
                            && (target <? here) in
                let target' := if negb (stretch =? 0) && negb reached
                                  && ((stretch <? 0) || (f_region (get_fst old j) =? f_region o))
                               then target + stretch else target in
                let aim := target' - here in
                if skip then (0, false)
                else if (aim <? 0) then (if -127 <=? aim then (0, false) else (match cc with None => 3 | Some _ => 4 end, true))
                else if aim <=? 128 then (0, false)
                else (match cc with None => 3 | Some _ => 4 end, true)
            end
        end in
      let (growth, long) := growth_long in
      pass r labels old (i + 1) (stretch + growth)
           (ZMap.add i (mkfrst addr (f_region o) long) nw) (changed || negb (growth =? 0))
  end.

Fixpoint relax (fuel : nat) (fs : list frag) (labels : smap place) (st : ZMap.t frst) : ZMap.t frst :=
  match fuel with
  | O => st
  | S fuel' =>
      let (st', changed) := pass fs labels st 0 0 (ZMap.empty _) false in
      if changed then relax fuel' fs labels st' else st'
  end.

(** A laid-out section: its frags, their final states, its size. *)
Record laid := mklaid { ly_sec : sec; ly_frags : list frag; ly_st : ZMap.t frst; ly_size : Z }.

Fixpoint count_jumps (fs : list frag) : nat :=
  match fs with
  | [] => O
  | f :: r => match fr_end f with EJump _ _ _ => S (count_jumps r) | _ => count_jumps r end
  end.

Fixpoint last_end (fs : list frag) (st : ZMap.t frst) (i : Z) : Z :=
  match fs with
  | [] => 0
  | [f] => let s := get_fst st i in f_addr s + fr_fix f + var_size f (f_long s) (f_addr s)
  | _ :: r => last_end r st (i + 1)
  end.

Definition lay (syms : smap sym) (c : sec) (labels : smap place) : laid * smap place :=
  let its := map_tr (settle syms (c_name c)) (rev' (c_items c)) in
  let (fs, labels') := frags (c_name c) 0 0 [] its labels [] in
  let st0 := initial fs 0 0 0 (ZMap.empty _) in
  let st := relax (S (S (count_jumps fs))) fs labels' st0 in
  (mklaid c fs st (last_end fs st 0), labels').

(** ## The object *)

Record osec := mkosec {
  os_name : string; os_type : Z; os_flags : string; os_align : Z; os_size : Z; os_bytes : list Z }.

(** A relocation: section, offset, type, the symbol or section it is
    against, whether that is a section, and the addend. *)
Record oreloc := mkoreloc {
  or_sec : string; or_off : Z; or_type : Z; or_sym : string; or_secsym : bool; or_add : Z }.

(** A symbol: name, binding (0 local, 1 global, 2 weak), type (0
    notype, 1 object, 2 function, 6 TLS), visibility (0 or 2 hidden),
    section ([None] undefined), value and size. *)
Record osym := mkosym {
  oy_name : string; oy_bind : Z; oy_type : Z; oy_vis : Z; oy_sec : option string;
  oy_value : Z; oy_size : Z }.

Record obj := mkobj { ob_secs : list osec; ob_relocs : list oreloc; ob_syms : list osym }.

(** The address of a label in its section. *)
Definition label_addr (lays : list laid) (pl : place) : Z :=
  match find (fun l => String.eqb (c_name (ly_sec l)) (pl_sec pl)) lays with
  | Some l =>
      let s := get_fst (ly_st l) (pl_frag pl) in
      f_addr s + pl_off pl
  | None => 0
  end.

(** Where [s] is: its section and address, through any .set. *)
Definition sym_where (syms : smap sym) (labels : smap place) (lays : list laid) (s : string) : option (string * Z) :=
  let (t, a) := resolve syms chain_fuel s 0 in
  match sm_find t labels with
  | Some pl => Some (pl_sec pl, label_addr lays pl + a)
  | None => None
  end.

Definition is_local (syms : smap sym) (s : string) : bool :=
  match sm_find s syms with
  | Some y => negb (s_glob y || s_weak y)
  | None => true
  end.

(** The bytes of a section and its relocations, last first. *)
Record emitted := mkem { em_bytes : list Z; em_relocs : list oreloc }.

(** Writes [v] into [n] bytes at [pos] of [bs]. *)
Definition patch (bs : list Z) (pos n v : Z) : list Z :=
  firstn (Z.to_nat pos) bs ++ le_bytes (Z.to_nat n) v ++ skipn (Z.to_nat (pos + n)) bs.

Definition reloc_type (k : fixk) : Z :=
  match k with
  | XPc true => 4
  | XPc false => 2
  | XGot t => t
  | XTpoff => 22
  | XAbs n => if n =? 8 then 1 else 10
  end.

(** Applies or records the fixups of an item at [addr] of section
    [cur]. *)
Fixpoint fix_item (syms : smap sym) (labels : smap place) (lays : list laid) (cur : string)
         (addr : Z) (bs : list Z) (fx : list fixup) (rs : list oreloc) : list Z * list oreloc :=
  match fx with
  | [] => (bs, rs)
  | x :: r =>
      let pos := addr + fx_at x in
      let pcadj := match fx_kind x with XPc _ | XGot _ | XTpoff => fx_end x - fx_at x | XAbs _ => 0 end in
      let where_ := sym_where syms labels lays (fx_sym x) in
      let local := is_local syms (fx_sym x) in
      match fx_kind x, where_ with
      | XPc _, Some (c, v) =>
          if String.eqb c cur && local then
            fix_item syms labels lays cur addr (patch bs (fx_at x) 4 (v + fx_add x - (addr + fx_end x))) r rs
          else if local then
            fix_item syms labels lays cur addr bs r (mkoreloc cur pos (reloc_type (fx_kind x)) c true (v + fx_add x - pcadj) :: rs)
          else
            fix_item syms labels lays cur addr bs r (mkoreloc cur pos (reloc_type (fx_kind x)) (fx_sym x) false (fx_add x - pcadj) :: rs)
      | XAbs _, Some (c, v) =>
          if local then
            fix_item syms labels lays cur addr bs r (mkoreloc cur pos (reloc_type (fx_kind x)) c true (v + fx_add x) :: rs)
          else
            fix_item syms labels lays cur addr bs r (mkoreloc cur pos (reloc_type (fx_kind x)) (fx_sym x) false (fx_add x) :: rs)
      | _, _ =>
          fix_item syms labels lays cur addr bs r (mkoreloc cur pos (reloc_type (fx_kind x)) (fx_sym x) false (fx_add x - pcadj) :: rs)
      end
  end.

(** The NOPs GNU as pads code with: [alt_patt], one of each size up
    to 11. *)
Definition nop_patterns : list (list Z) :=
  [[144]; [102; 144]; [15; 31; 0]; [15; 31; 64; 0]; [15; 31; 68; 0; 0];
   [102; 15; 31; 68; 0; 0]; [15; 31; 128; 0; 0; 0; 0]; [15; 31; 132; 0; 0; 0; 0; 0];
   [102; 15; 31; 132; 0; 0; 0; 0; 0]; [102; 46; 15; 31; 132; 0; 0; 0; 0; 0];
   [102; 102; 46; 15; 31; 132; 0; 0; 0; 0; 0]].

(** [n] bytes of NOPs: as many 11-byte ones as fit and one for the
    rest, the rest last as GNU as 2.43 and 2.44 put it, or first as
    2.46 does ([rest_first]). GNU as jumps over more than seven
    11-byte NOPs, which no alignment here needs. *)
Definition nops (rest_first : bool) (n : Z) : list Z :=
  let rest := n mod 11 in
  let rest_bytes := if rest =? 0 then [] else nth (Z.to_nat (rest - 1)) nop_patterns [] in
  let elevens := concat (repeat (nth 10 nop_patterns []) (Z.to_nat (n / 11))) in
  if n <=? 11 then (if n <=? 0 then [] else nth (Z.to_nat (n - 1)) nop_patterns [])
  else if rest_first then rest_bytes ++ elevens else elevens ++ rest_bytes.

Definition pad (rest_first nop data : bool) (n : Z) : list Z :=
  if negb nop then zeros n
  else if n <=? 0 then []
  else if data then 144 :: nops rest_first (n - 1)
  else nops rest_first n.

(** The bytes of a frag's items at [addr], with the relocations. *)
Fixpoint emit_items (rf keep : bool) (syms : smap sym) (labels : smap place) (lays : list laid) (cur : string)
         (its : list item) (f : frag) (fs : frst) (addr : Z) (out : list (list Z)) (rs : list oreloc)
  : Z * list (list Z) * list oreloc :=
  match its with
  | [] => (addr, out, rs)
  | it :: r =>
      match it with
      | IBytes bs fx =>
          let (bs', rs') := fix_item syms labels lays cur addr bs fx rs in
          emit_items rf keep syms labels lays cur r f fs (addr + zlen bs) (bs' :: out) rs'
      | IZero n => emit_items rf keep syms labels lays cur r f fs (addr + n) ((if keep then zeros n else []) :: out) rs
      | IJump cc s a _ =>
          let target := match sym_where syms labels lays s with Some (_, v) => v + a | None => 0 end in
          let bs := match cc, f_long fs with
                    | None, false => [235; byte (target - (addr + 2))]
                    | None, true => 233 :: le4 (target - (addr + 5))
                    | Some c, false => [112 + c; byte (target - (addr + 2))]
                    | Some c, true => 15 :: 128 + c :: le4 (target - (addr + 6))
                    end in
          emit_items rf keep syms labels lays cur r f fs (addr + zlen bs) (bs :: out) rs
      | IAlign p nop data =>
          let n := align_pad addr p in
          emit_items rf keep syms labels lays cur r f fs (addr + n) ((if keep then pad rf nop data n else []) :: out) rs
      | ILabel _ => emit_items rf keep syms labels lays cur r f fs addr out rs
      end
  end.

Fixpoint emit_frags (rf keep : bool) (syms : smap sym) (labels : smap place) (lays : list laid) (cur : string)
         (fs : list frag) (st : ZMap.t frst) (i : Z) (out : list (list Z)) (rs : list oreloc)
  : list (list Z) * list oreloc :=
  match fs with
  | [] => (out, rs)
  | f :: r =>
      let s := get_fst st i in
      let '(_, out', rs') := emit_items rf keep syms labels lays cur (fr_items f) f s (f_addr s) out rs in
      emit_frags rf keep syms labels lays cur r st (i + 1) out' rs'
  end.

Definition type_code (t : option string) : Z :=
  match t with
  | Some n =>
      if String.eqb n "function" then 2 else if String.eqb n "object" then 1
      else if String.eqb n "tls_object" then 6 else if String.eqb n "gnu_indirect_function" then 10
      else 0
  | None => 0
  end.

(** The symbol table: every symbol but the `.L` ones, and
    _GLOBAL_OFFSET_TABLE_ when a GOT operand was used. *)
Definition symbols (syms : smap sym) (labels : smap place) (lays : list laid) (got : bool) : list osym :=
  let one (p : string * sym) : list osym :=
    let (s, y) := p in
    if is_local_label s then [] else
    let bind := if s_weak y then 2 else if s_glob y then 1 else 0 in
    let vis := if s_hidden y then 2 else 0 in
    match sym_where syms labels lays s with
    | Some (c, v) =>
        let (t, _) := resolve syms chain_fuel s 0 in
        let ty := match s_type y with
                  | Some _ => type_code (s_type y)
                  | None => if String.eqb c ".tbss" then 6 else 0
                  end in
        let ty' := if String.eqb c ".tbss" then (if (ty =? 1) || (ty =? 0) then 6 else ty) else ty in
        let size_of (z : sym) (who : string) :=
          match s_size z with
          | Some (Some n) => n
          | Some None =>
              match sm_find (dot_key who) labels, sym_where syms labels lays who with
              | Some pl, Some (_, w) => label_addr lays pl - w
              | _, _ => 0
              end
          | None => 0
          end in
        let size := match s_size y with
                    | Some _ => size_of y s
                    | None => match sm_find t syms with Some z => size_of z t | None => 0 end
                    end in
        [mkosym s bind ty' vis (Some c) v size]
    | None =>
        let ty := if s_tls y then 6 else type_code (s_type y) in
        [mkosym s (if s_weak y then 2 else 1) ty vis None 0 0]
    end in
  (if got then [mkosym "_GLOBAL_OFFSET_TABLE_" 1 0 0 None 0 0] else [])
  ++ flat_map_tr one (sm_elements syms).

(** Every symbol a relocation names, so an undefined one is in the
    table even when nothing else mentions it. *)
Definition note_refs (syms : smap sym) (its : list item) : smap sym :=
  fold_left (fun m it =>
               match it with
               | IBytes _ fx => fold_left (fun m' x => match sm_find (fx_sym x) m' with
                                                       | Some _ => m'
                                                       | None => sm_add (fx_sym x) no_sym m' end) fx m
               | IJump _ s _ _ => match sm_find s m with Some _ => m | None => sm_add s no_sym m end
               | _ => m
               end) its syms.

(** The object GNU as makes of [ls], or the text of a line it has no
    encoding for here; [rest_first] pads code as GNU as 2.46 does. *)
Definition encode_lines (rest_first : bool) (ls : list line) : obj + string :=
  let st0 := mkps (new_sec SText) [] sm_empty false in
  match steps st0 ls with
  | inr w => inr w
  | inl st =>
      let secs := p_cur st :: p_others st in
      let secs := fold_left (fun acc c => if existsb (fun d => String.eqb (c_name d) (c_name c)) acc then acc else acc ++ [c]) secs [] in
      let syms := fold_left (fun m c => note_refs m (c_items c)) secs (p_syms st) in
      let '(lays, labels) :=
        fold_left (fun (acc : list laid * smap place) c =>
                     let '(ls', labels) := acc in
                     let (l, labels') := lay syms c labels in (ls' ++ [l], labels'))
                  secs ([], sm_empty) in
      let one (l : laid) : osec * list oreloc :=
        let c := ly_sec l in
        let (out, rs) := emit_frags rest_first (negb (c_type c =? 8)) syms labels lays (c_name c) (ly_frags l) (ly_st l) 0 [] [] in
        (mkosec (c_name c) (c_type c) (c_flags c) (c_align c) (ly_size l)
                (if c_type c =? 8 then [] else join_rev out), rev' rs) in
      let done := map one lays in
      inl (mkobj (map fst done) (flat_map_tr snd done) (symbols syms labels lays (p_got st)))
  end.

(** ## The text the gate compares *)

Definition hex_digits : string := "0123456789abcdef".

Definition hex2 (b : Z) : string :=
  String (match String.get (Z.to_nat (b / 16)) hex_digits with Some c => c | None => "?"%char end)
    (String (match String.get (Z.to_nat (b mod 16)) hex_digits with Some c => c | None => "?"%char end) "").

Fixpoint hex_lines (bs : list Z) (n : nat) (cur : list string) (k : parts) : parts :=
  match bs with
  | [] => match cur with [] => k | _ => "bytes " :: String.concat "" (rev' cur) :: nl :: k end
  | b :: r =>
      match n with
      | O => "bytes " :: String.concat "" (rev' cur) :: nl :: hex_lines r 31 [hex2 b] k
      | S n' => hex_lines r n' (hex2 b :: cur) k
      end
  end.

Definition type_name (t : Z) : string :=
  if t =? 8 then "NOBITS" else if t =? 14 then "INIT_ARRAY" else if t =? 15 then "FINI_ARRAY" else "PROGBITS".

Definition bind_name (b : Z) : string := if b =? 0 then "LOCAL" else if b =? 2 then "WEAK" else "GLOBAL".
Definition stype_name (t : Z) : string :=
  if t =? 1 then "OBJECT" else if t =? 2 then "FUNC" else if t =? 6 then "TLS"
  else if t =? 10 then "IFUNC" else "NOTYPE".
Definition vis_name (v : Z) : string := if v =? 2 then "HIDDEN" else "DEFAULT".

(** The object as tests/objdump.py prints GNU as's: sections by name
    with their bytes, then the relocations by section and offset, then
    the symbols by name. *)
Definition dump_parts (o : obj) : parts :=
  let secs := sort (fun a b => str_le (os_name a) (os_name b))
                   (filter (fun s => negb (os_size s =? 0) || String.eqb (os_name s) ".note.GNU-stack") (ob_secs o)) in
  let sec_parts (s : osec) (k : parts) : parts :=
    "section " :: os_name s :: " " :: type_name (os_type s) :: " " :: os_flags s :: " "
      :: decimal (os_align s) :: " " :: decimal (os_size s) :: nl :: hex_lines (os_bytes s) 32 [] k in
  let reloc_parts (r : oreloc) (k : parts) : parts :=
    "reloc " :: or_sec r :: " " :: decimal (or_off r) :: " " :: decimal (or_type r) :: " "
      :: or_sym r :: " " :: decimal (or_add r) :: nl :: k in
  let sym_parts (y : osym) (k : parts) : parts :=
    "symbol " :: oy_name y :: " " :: bind_name (oy_bind y) :: " " :: stype_name (oy_type y) :: " "
      :: vis_name (oy_vis y) :: " " :: match oy_sec y with Some c => c | None => "UND" end :: " "
      :: decimal (oy_value y) :: " " :: decimal (oy_size y) :: nl :: k in
  let relocs := flat_map (fun s => filter (fun r => String.eqb (or_sec r) (os_name s)) (ob_relocs o)) secs in
  let syms := sort (fun a b => str_le (oy_name a) (oy_name b)) (ob_syms o) in
  fold_right sec_parts (fold_right reloc_parts (fold_right sym_parts [] syms) relocs) secs.
