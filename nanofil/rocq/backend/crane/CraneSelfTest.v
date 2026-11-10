(** # The C++ mappings against vm_compute

    [tests] names a value for each mapped function of CraneMap.v over
    numbers at and past the machine's widths, and [expected] is what
    [vm_compute] finds for them. selftest.cpp runs the extracted
    [tests] and compares. *)

From Crane Require Extraction.
From BackendCrane Require Import CraneMap.
From Stdlib Require Import OrderedType OrderedTypeEx String ZArith NArith PArith List Ascii Bool.
From Nanofil Require Import Term Maps.
From Backend Require Import Text Order IrText.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition zs : list Z :=
  [0; 1; -1; 2; -2; 3; 7; -7; 8; 10; 63; 64; 255; 256; -256; 1000; 4095; 65535; 65536;
   2147483647; 2147483648; -2147483648; 4294967295; 4294967296;
   9223372036854775807; 9223372036854775808; -9223372036854775808; -9223372036854775809;
   18446744073709551615; 18446744073709551616; 123456789012345678901234567890].

Definition b (x : bool) : string := if x then "t" else "f".
Definition c (x : comparison) : string := match x with Eq => "=" | Lt => "<" | Gt => ">" end.
Definition sep (xs : list string) : string := String.concat " " xs.
Definition un (f : Z -> string) : string := sep (map f zs).
Definition small : list Z := [0; 1; -1; 2; 3; -3; 7; 64; -64; 100; 4294967296; -9223372036854775808].
Definition bin (f : Z -> Z -> string) : string :=
  sep (flat_map (fun x => map (f x) small) zs).
Definition tiny : list Z := [0; 1; -1; 2; 3; -3; 7; 64; -64; 100; 1000; 5000].
Definition d := decimal.
Definition nat_s (n : nat) : string := d (Z.of_nat n).
Definition ns : list nat := [0; 1; 2; 3; 9; 10; 64; 255; 1000]%nat.
Definition nbin (f : nat -> nat -> string) : string := sep (flat_map (fun x => map (f x) ns) ns).
Definition strs : list string := [""; "a"; "b"; "ab"; "abc"; "abd"; "ret"; "rets"; "phi"; "Z"; "~"; "a b"].
Definition sbin (f : string -> string -> string) : string := sep (flat_map (fun x => map (f x) strs) strs).
Definition chars : list ascii := ["000"; "001"; "009"; "010"; " "; "0"; "9"; "A"; "a"; "z"; "~"; "127"; "128"; "200"; "255"]%char.

Definition tests (_ : unit) : list (string * string) :=
  [ ("decimal", un d);
    ("add", bin (fun x y => d (x + y)));
    ("sub", bin (fun x y => d (x - y)));
    ("mul", bin (fun x y => d (x * y)));
    ("div", bin (fun x y => d (x / y)));
    ("mod", bin (fun x y => d (x mod y)));
    ("quot", bin (fun x y => d (Z.quot x y)));
    ("rem", bin (fun x y => d (Z.rem x y)));
    ("opp", un (fun x => d (- x)));
    ("abs", un (fun x => d (Z.abs x)));
    ("succ", un (fun x => d (Z.succ x)));
    ("pred", un (fun x => d (Z.pred x)));
    ("eqb", bin (fun x y => b (x =? y)));
    ("ltb", bin (fun x y => b (x <? y)));
    ("leb", bin (fun x y => b (x <=? y)));
    ("gtb", bin (fun x y => b (x >? y)));
    ("geb", bin (fun x y => b (x >=? y)));
    ("compare", bin (fun x y => c (Z.compare x y)));
    ("eq_dec", bin (fun x y => b (if Z.eq_dec x y then true else false)));
    ("min", bin (fun x y => d (Z.min x y)));
    ("max", bin (fun x y => d (Z.max x y)));
    ("land", bin (fun x y => d (Z.land x y)));
    ("lor", bin (fun x y => d (Z.lor x y)));
    ("lxor", bin (fun x y => d (Z.lxor x y)));
    ("ldiff", bin (fun x y => d (Z.ldiff x y)));
    ("shiftl", bin (fun x y => if (-70 <? y) && (y <? 70) then d (Z.shiftl x y) else ""));
    ("shiftr", bin (fun x y => if (-70 <? y) && (y <? 70) then d (Z.shiftr x y) else ""));
    ("pow", bin (fun x y => if y <? 70 then d (x ^ y) else ""));
    ("log2", un (fun x => d (Z.log2 x)));
    ("div2", un (fun x => d (Z.div2 x)));
    ("even", un (fun x => b (Z.even x)));
    ("odd", un (fun x => b (Z.odd x)));
    ("sgn", un (fun x => d (Z.sgn x)));
    ("testbit", bin (fun x y => b (Z.testbit x y)));
    ("to_N", un (fun x => d (Z.of_N (Z.to_N x))));
    ("N.land", bin (fun x y => d (Z.of_N (N.land (Z.to_N x) (Z.to_N y)))));
    ("N.lor", bin (fun x y => d (Z.of_N (N.lor (Z.to_N x) (Z.to_N y)))));
    ("N.sub", bin (fun x y => d (Z.of_N (N.sub (Z.to_N x) (Z.to_N y)))));
    ("N.add", bin (fun x y => d (Z.of_N (N.add (Z.to_N x) (Z.to_N y)))));
    ("N.mul", bin (fun x y => d (Z.of_N (N.mul (Z.to_N x) (Z.to_N y)))));
    ("N.div", bin (fun x y => d (Z.of_N (N.div (Z.to_N x) (Z.to_N y)))));
    ("N.mod", bin (fun x y => d (Z.of_N (N.modulo (Z.to_N x) (Z.to_N y)))));
    ("N.compare", bin (fun x y => c (N.compare (Z.to_N x) (Z.to_N y))));
    ("N.eqb", bin (fun x y => b (N.eqb (Z.to_N x) (Z.to_N y))));
    ("N.leb", bin (fun x y => b (N.leb (Z.to_N x) (Z.to_N y))));
    ("N.ltb", bin (fun x y => b (N.ltb (Z.to_N x) (Z.to_N y))));
    ("Pos.add", bin (fun x y => d (Zpos (Pos.add (Z.to_pos x) (Z.to_pos y)))));
    ("Pos.mul", bin (fun x y => d (Zpos (Pos.mul (Z.to_pos x) (Z.to_pos y)))));
    ("Pos.sub", bin (fun x y => d (Zpos (Pos.sub (Z.to_pos x) (Z.to_pos y)))));
    ("Pos.compare", bin (fun x y => c (Pos.compare (Z.to_pos x) (Z.to_pos y))));
    ("Pos.eqb", bin (fun x y => b (Pos.eqb (Z.to_pos x) (Z.to_pos y))));
    ("Pos.succ", un (fun x => d (Zpos (Pos.succ (Z.to_pos x)))));
    ("Pos.pred", un (fun x => d (Zpos (Pos.pred (Z.to_pos x)))));
    ("Pos.size_nat", un (fun x => nat_s (Pos.size_nat (Z.to_pos x))));
    ("Pos.to_nat", sep (map (fun x => nat_s (Pos.to_nat (Z.to_pos x))) tiny));
    ("to_nat", sep (map (fun x => nat_s (Z.to_nat x)) tiny));
    ("of_nat", sep (map nat_s ns));
    ("N.to_nat", sep (map (fun x => nat_s (N.to_nat (Z.to_N x))) tiny));
    ("N.of_nat", sep (map (fun x => d (Z.of_N (N.of_nat x))) ns));
    ("Pos.of_nat", sep (map (fun x => d (Zpos (Pos.of_nat x))) ns));
    ("Pos.of_succ_nat", sep (map (fun x => d (Zpos (Pos.of_succ_nat x))) ns));
    ("Z.abs_nat", sep (map (fun x => nat_s (Z.abs_nat x)) tiny));
    ("nat.add", nbin (fun x y => nat_s (x + y)));
    ("nat.sub", nbin (fun x y => nat_s (x - y)));
    ("nat.mul", nbin (fun x y => nat_s (x * y)));
    ("nat.div", nbin (fun x y => nat_s (x / y)));
    ("nat.mod", nbin (fun x y => nat_s (x mod y)));
    ("nat.eqb", nbin (fun x y => b (Nat.eqb x y)));
    ("nat.leb", nbin (fun x y => b (Nat.leb x y)));
    ("nat.ltb", nbin (fun x y => b (Nat.ltb x y)));
    ("nat.compare", nbin (fun x y => c (Nat.compare x y)));
    ("nat.min", nbin (fun x y => nat_s (Nat.min x y)));
    ("nat.max", nbin (fun x y => nat_s (Nat.max x y)));
    ("nat.pred", sep (map (fun x => nat_s (Nat.pred x)) ns));
    ("nat.match", sep (map (fun x => match x with O => "O" | S y => nat_s y end) ns));
    ("nat.eq_dec", nbin (fun x y => b (if Nat.eq_dec x y then true else false)));
    ("str.eqb", sbin (fun x y => b (String.eqb x y)));
    ("str.compare", sbin (fun x y => c (String.compare x y)));
    ("str.append", sbin (fun x y => x ++ y));
    ("str.prefix", sbin (fun x y => b (String.prefix x y)));
    ("str.length", sep (map (fun x => nat_s (String.length x)) strs));
    ("str.dec", sbin (fun x y => b (if string_dec x y then true else false)));
    ("str.substring", sep (map (fun x => substring 1 2 x) strs));
    ("str.get", sep (map (fun x => match get 1 x with Some a => String a "" | None => "-" end) strs));
    ("str.index", sbin (fun x y => match index 0 x y with Some n => nat_s n | None => "-" end));
    ("str.list", sep (map (fun x => string_of_list_ascii (rev (list_ascii_of_string x))) strs));
    ("str.match", sep (map (fun x => match x with "" => "e" | String a r => String a "" ++ "|" ++ r end) strs));
    ("asc.nat", sep (map (fun a => nat_s (nat_of_ascii a)) chars));
    ("asc.N", sep (map (fun a => d (Z.of_N (N_of_ascii a))) chars));
    ("asc.of_nat", sep (map (fun n => nat_s (nat_of_ascii (ascii_of_nat n))) [0; 1; 65; 127; 128; 255; 256; 300]%nat));
    ("asc.of_N", sep (map (fun n => nat_s (nat_of_ascii (ascii_of_N (Z.to_N n)))) [0; 1; 65; 127; 128; 255; 256; 300]));
    ("asc.eqb", sep (flat_map (fun x => map (fun y => b (Ascii.eqb x y)) chars) chars));
    ("asc.compare", sep (flat_map (fun x => map (fun y => c (Ascii.compare x y)) chars) chars));
    ("asc.ltb", sep (flat_map (fun x => map (fun y => b (Ascii.ltb x y)) chars) chars));
    ("asc.leb", sep (flat_map (fun x => map (fun y => b (Ascii.leb x y)) chars) chars));
    ("asc.dec", sep (flat_map (fun x => map (fun y => b (if ascii_dec x y then true else false)) chars) chars));
    ("asc.match", sep (map (fun a => match a with Ascii b0 b1 b2 b3 b4 b5 b6 b7 => b b0 ++ b b1 ++ b b2 ++ b b3 ++ b b4 ++ b b5 ++ b b6 ++ b b7 end) chars));
    ("hash", sep (map (fun x => d (string_hash x 2)) strs));
    ("hash.big", sep (map (fun x => d (string_hash x 123456789012345678901234567890)) strs));
    ("hash.neg", sep (map (fun x => d (string_hash x (-5))) strs));
    ("name_eqb", sbin (fun x y => b (name_eqb (TAtom x) (TAtom y))));
    ("string_of_rev", sep (map (fun x => string_of_rev (list_ascii_of_string x)) strs));
    ("code", sep (map (fun a => nat_s (code a)) chars));
    ("byte", sep (map (fun n => nat_s (code (byte n))) [0; 1; 65; 127; 128; 255; 256; 300]%nat));
    ("length", sep (map (fun x => nat_s (List.length (list_ascii_of_string x))) strs));
    ("Pos.eq_dec", bin (fun x y => b (if Pos.eq_dec (Z.to_pos x) (Z.to_pos y) then true else false)));
    ("atom_compare", sbin (fun x y => c (atom_compare x y)));
    ("term_eqb", sbin (fun x y => b (term_eqb (TApp x [TAtom y; TInt 3]) (TApp y [TAtom x; TInt 3]))));
    ("zmap", let m := fold_left (fun m x => ZMap.add x (d x) m) small (ZMap.empty _) in
             sep (map (fun x => match ZMap.find x m with Some y => y | None => "-" end) (55 :: small)));
    ("zmap1", let m := ZMap.add 5 "five" (ZMap.empty _) in
             match ZMap.find 5 m with Some y => y | None => "-" end);
    ("zcard", let m := fold_left (fun m x => ZMap.add x (d x) m) small (ZMap.empty _) in nat_s (ZMap.cardinal m));
    ("zelems", let m := fold_left (fun m x => ZMap.add x (d x) m) small (ZMap.empty _) in sep (map snd (ZMap.elements m)));
    ("zcmp", bin (fun x y => match Z_as_OT.compare x y with OrderedType.LT _ => "<" | OrderedType.EQ _ => "=" | OrderedType.GT _ => ">" end));
    ("lookup", let l := fold_left (fun l x => put (TAtom x) x l) strs [] in
             sep (map (fun x => match lookup (TAtom x) l with Some y => y | None => "-" end) ("zz" :: strs)));
    ("key", sep (map (fun x => d (name_key (TAtom x))) strs));
    ("key2", sep (map (fun x => d (name_key (TApp x [TAtom x; TInt 5; TList [TInt 1; TAtom "q"]]))) strs));
    ("nm1", match nm_find (TAtom "a") (nm_add (TAtom "a") "va" nm_empty) with Some y => y | None => "-" end);
    ("nm2", let m := nm_add (TAtom "a") "va" nm_empty in nat_s (ZMap.cardinal m));
    ("nm3", let m := nm_add (TAtom "a") "va" nm_empty in
            match ZMap.find (name_key (TAtom "a")) m with Some l => nat_s (List.length l) | None => "-" end);
    ("nm4", let m := nm_of_list [(TAtom "a", "va")] in nat_s (ZMap.cardinal m));
    ("nm5", let m := fold_left (fun m p => nm_add (fst p) (snd p) m) [(TAtom "a", "va")] nm_empty in nat_s (ZMap.cardinal m));
    ("nm6", let m := nm_of_list [(TAtom "a", "va")] in match nm_find (TAtom "a") m with Some y => y | None => "-" end);
    ("nmap", let m := nm_of_list (map (fun x => (TAtom x, x)) strs) in
             sep (map (fun x => match nm_find (TAtom x) m with Some y => y | None => "-" end) ("zz" :: strs)))
  ].

Definition expected : list string := Eval vm_compute in map snd (tests tt).

Set Crane Format Style "None".
Set Crane Extraction Output Directory ".".

Crane Extraction "st" tests expected.
